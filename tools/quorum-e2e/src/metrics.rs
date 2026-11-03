use cbcl_core::quorum::Certificate;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
#[derive(Serialize, Deserialize)]
pub struct Outcome {
    pub sequence: usize,
    pub id: String,
    pub status: String,
    pub submitted_ms: Option<f64>,
    pub finality_ms: Option<f64>,
    pub scheduler_lateness_ms: f64,
    pub errors: usize,
    pub effects_certificate: Option<Certificate>,
}
fn rank(n: usize, percentile: usize) -> usize {
    (n * percentile).div_ceil(100)
}
fn conditional(sorted: &[f64], p: usize) -> Option<f64> {
    (!sorted.is_empty()).then(|| sorted[rank(sorted.len(), p) - 1])
}
pub fn summarize(rows: &[Outcome], timeout_ms: u64, seconds: f64) -> Value {
    let submitted = rows.iter().filter(|r| r.submitted_ms.is_some()).count();
    let mut latencies: Vec<_> = rows.iter().filter_map(|r| r.finality_ms).collect();
    latencies.sort_by(f64::total_cmp);
    let within = latencies.iter().filter(|ms| **ms <= 1000.0).count();
    let mut conditional_percentiles = serde_json::Map::new();
    let mut population = serde_json::Map::new();
    for p in [50, 95, 99] {
        conditional_percentiles.insert(format!("p{p}"), json!(conditional(&latencies, p)));
        let k = rank(submitted, p);
        population.insert(
            format!("p{p}"),
            if submitted == 0 {
                Value::Null
            } else if k <= latencies.len() {
                json!({"value":latencies[k-1],"right_censored":false})
            } else {
                json!({"value":null,"right_censored":true,"at_least":timeout_ms})
            },
        );
    }
    json!({"offered":rows.len(),"submitted":submitted,"finalized":latencies.len(),
        "stalled":submitted-latencies.len(),"client_overload":rows.len()-submitted,
        "finalized_within_one_second":within,
        "fraction_within_one_second_of_submitted": if submitted>0 {Some(within as f64/submitted as f64)}else{None},
        "fraction_within_one_second_of_offered": if !rows.is_empty(){Some(within as f64/rows.len() as f64)}else{None},
        "finalized_latency_ms":conditional_percentiles,"all_submitted_latency_ms":population,
        "measurement_seconds":seconds,"throughput_finalized_tps":latencies.len() as f64/seconds,
        "submitted_tps_over_measurement":submitted as f64/seconds,
        "max_scheduler_lateness_ms":rows.iter().map(|r|r.scheduler_lateness_ms).fold(0.0,f64::max),
        "transaction_error_responses":rows.iter().map(|r|r.errors).sum::<usize>()})
}
