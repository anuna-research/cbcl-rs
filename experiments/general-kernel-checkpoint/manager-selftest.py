"""Containment regression: group leader exit and monitor interruption."""
import json,os,signal,subprocess,time
from pathlib import Path
base=Path('.artifacts/manager-selftest');base.mkdir(parents=True,exist_ok=True)
script=base/'spawn.py'
script.write_text('import subprocess,sys\nfrom pathlib import Path\np=subprocess.Popen([sys.executable,"-c","import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)"])\nPath(".artifacts/manager-selftest/pid").write_text(str(p.pid))\n')
run=subprocess.run(['python3','run-managed.py','manager-selftest','python3',str(script)],stdout=subprocess.PIPE,text=True,timeout=12)
assert run.returncode==0,run.stdout
pid=int((base/'pid').read_text());state=subprocess.run(['ps','-o','stat=','-p',str(pid)],stdout=subprocess.PIPE,text=True).stdout.strip()
assert not state or state.startswith('Z'),('surviving descendant',pid,state)
results={'normalLeaderExitTerminatesDescendant':True,'descendantFinalState':state or 'absent','supervisorOutput':run.stdout}
script=base/'interrupt.py';pfile=base/'interrupt-pid'
pfile.unlink(missing_ok=True)
script.write_text('import signal,time,os\nfrom pathlib import Path\nsignal.signal(signal.SIGTERM,signal.SIG_IGN)\nPath(".artifacts/manager-selftest/interrupt-pid").write_text(str(os.getpid()))\ntime.sleep(60)\n')
runner=subprocess.Popen(['python3','run-managed.py','manager-interrupted-selftest','python3',str(script)],stdout=subprocess.PIPE,text=True)
try:
 for _ in range(50):
  if pfile.exists():break
  time.sleep(0.1)
 assert pfile.exists(),'child did not start'
 os.kill(runner.pid,signal.SIGINT)
 stdout,_=runner.communicate(timeout=12)
 assert runner.returncode!=0,'interrupted monitor reported success'
 pid=int(pfile.read_text());state=subprocess.run(['ps','-o','stat=','-p',str(pid)],stdout=subprocess.PIPE,text=True).stdout.strip()
 assert not state or state.startswith('Z'),('survivor after monitor exception',pid,state)
 results.update(monitorInterruptionTerminatesChild=True,interruptedSupervisorOutput=stdout)
finally:
 if runner.poll() is None:runner.kill();runner.wait()
Path('evidence/manager-selftest.json').write_text(json.dumps(results,indent=2)+'\n')
