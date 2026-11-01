use crate::model::{Result, SignedAct};
use cbcl_core::quorum::{BatchJournal, Event, Journal};
use fs2::FileExt;
use serde::{Deserialize, Serialize};
use std::{
    fs::{File, OpenOptions},
    io::{Read, Write},
    path::{Path, PathBuf},
};

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub context: String,
    pub validator: String,
    pub sequence: u64,
    pub event: Event,
    pub actor_signature: Option<Vec<u8>>,
}
pub struct DurableJournal {
    path: PathBuf,
    _lock: File,
    file: Option<File>,
    count: u64,
    context: String,
    validator: String,
    existed: bool,
    pub pending_act: Option<SignedAct>,
    pub pending_acts: std::collections::BTreeMap<String, SignedAct>,
    pub syncs: u64,
    pub costs: crate::profile::JournalCosts,
}
impl DurableJournal {
    pub fn open(path: &Path, context: &str, validator: &str) -> Result<(Self, Vec<Record>)> {
        let lock_path = path.with_extension("lock");
        let lock = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(lock_path)
            .map_err(|e| e.to_string())?;
        FileExt::try_lock_exclusive(&lock)
            .map_err(|e| format!("journal owner already active: {e}"))?;
        let existed = path.exists();
        let records = if existed {
            Self::read(path, context, validator)?
        } else {
            vec![]
        };
        let file = if existed {
            Some(
                OpenOptions::new()
                    .append(true)
                    .open(path)
                    .map_err(|e| e.to_string())?,
            )
        } else {
            None
        };
        Ok((
            Self {
                path: path.into(),
                _lock: lock,
                file,
                count: records.len() as u64,
                context: context.into(),
                validator: validator.into(),
                existed,
                pending_act: None,
                pending_acts: Default::default(),
                syncs: 0,
                costs: Default::default(),
            },
            records,
        ))
    }
    fn read(path: &Path, context: &str, validator: &str) -> Result<Vec<Record>> {
        let mut bytes = Vec::new();
        File::open(path)
            .and_then(|mut f| f.read_to_end(&mut bytes))
            .map_err(|e| e.to_string())?;
        // Never trim or silently discard a torn suffix during recovery.
        if !bytes.is_empty() && bytes.last() != Some(&b'\n') {
            return Err("incomplete journal suffix; refusing recovery".into());
        }
        let mut records: Vec<Record> = Vec::new();
        for line in bytes
            .strip_suffix(b"\n")
            .unwrap_or(&bytes)
            .split(|b| *b == b'\n')
            .filter(|_| !bytes.is_empty())
        {
            let record: Record = serde_json::from_slice(line).map_err(|e| e.to_string())?;
            if record.context != context
                || record.validator != validator
                || record.sequence != records.len() as u64
                || matches!(record.event, Event::Candidate(_)) != record.actor_signature.is_some()
            {
                return Err(
                    "journal identity, sequence or authentication envelope mismatch".into(),
                );
            }
            records.push(record);
        }
        Ok(records)
    }
    pub fn count(&self) -> u64 {
        self.count
    }
    fn fail_stop(error: std::io::Error) -> ! {
        // A failed write/sync may have committed bytes. Never return an ambiguous
        // append error to a live signer: stop and require complete-log recovery.
        eprintln!("fatal journal I/O; signer stopped: {error}");
        std::process::abort()
    }
}
impl Journal for DurableJournal {
    fn load(&self, context: &str, validator: &str) -> Result<Option<Vec<Event>>> {
        if context != self.context || validator != self.validator {
            return Err("wrong journal identity".into());
        }
        if !self.existed {
            return Ok(None);
        }
        Ok(Some(
            Self::read(&self.path, context, validator)?
                .into_iter()
                .map(|r| r.event)
                .collect(),
        ))
    }
    fn append(
        &mut self,
        context: &str,
        validator: &str,
        expected: Option<u64>,
        event: &Event,
    ) -> Result<()> {
        self.write_records(context, validator, expected, core::slice::from_ref(event))
    }
}
impl BatchJournal for DurableJournal {
    fn append_batch(
        &mut self,
        context: &str,
        validator: &str,
        expected: u64,
        events: &[Event],
    ) -> Result<()> {
        self.write_records(context, validator, Some(expected), events)
    }
}
impl DurableJournal {
    fn write_records(
        &mut self,
        context: &str,
        validator: &str,
        expected: Option<u64>,
        events: &[Event],
    ) -> Result<()> {
        if context != self.context
            || validator != self.validator
            || match expected {
                None => self.existed,
                Some(n) => !self.existed || n != self.count,
            }
        {
            return Err("journal compare-and-append conflict".into());
        }
        if events.is_empty() {
            return Ok(());
        }
        let encode_start = std::time::Instant::now();
        let mut bytes = Vec::new();
        for (offset, event) in events.iter().enumerate() {
            let actor_signature = match event {
                Event::Candidate(act) => Some(
                    self.pending_acts
                        .get(&act.address)
                        .or(self.pending_act.as_ref())
                        .filter(|s| s.act == *act)
                        .ok_or("missing signed actor envelope")?
                        .signature
                        .clone(),
                ),
                _ => None,
            };
            let record = Record {
                context: context.into(),
                validator: validator.into(),
                sequence: self.count + offset as u64,
                event: event.clone(),
                actor_signature,
            };
            serde_json::to_writer(&mut bytes, &record).map_err(|e| e.to_string())?;
            bytes.push(b'\n');
        }
        self.costs.encode.record(encode_start);
        let creating = self.file.is_none();
        if creating {
            self.file = Some(
                OpenOptions::new()
                    .create_new(true)
                    .append(true)
                    .open(&self.path)
                    .map_err(|e| e.to_string())?,
            )
        }
        let file = self.file.as_mut().expect("journal opened");
        let start = std::time::Instant::now();
        file.write_all(&bytes)
            .unwrap_or_else(|e| Self::fail_stop(e));
        self.costs.write.record(start);
        let start = std::time::Instant::now();
        file.sync_all().unwrap_or_else(|e| Self::fail_stop(e));
        self.costs.sync.record(start);
        if creating {
            #[cfg(unix)]
            File::open(self.path.parent().expect("journal directory"))
                .and_then(|d| d.sync_all())
                .unwrap_or_else(|e| Self::fail_stop(e));
        }
        self.count += events.len() as u64;
        self.syncs += 1;
        self.existed = true;
        Ok(())
    }
}
