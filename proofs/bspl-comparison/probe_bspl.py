"""Focused probes of unmodified local BSPL; run against an isolated source copy."""
import json, asyncio, contextlib, io
from pathlib import Path
from bspl.parsers.bspl import load_file, parse
from bspl.adapter.message import Message
from bspl.adapter.store import Store, Context
from bspl.adapter import Adapter
from bspl.verification import paths
from bspl.verification.refinement import refines
p=Path(__file__).resolve().parent
P=load_file(str(p/'purchase.bspl')).protocols['Purchase']
def msg(name,**kw):return Message(P.messages[name],kw,system='purchase')
h=Store(['purchase']);h.add(msg('Request',order='o1',item='book'));h.add(msg('Quote',order='o1',item='book',price=100))
good=msg('Accept',order='o1',item='book',price=100,accepted=True)
bad=msg('Accept',order='o1',item='book',price=1,accepted=True)
result={}
result['quote_value_binding']={'good_integrity':h.check_integrity(good),'changed_price_integrity':h.check_integrity(bad),'good_emission':h.check_emissions([good]),'changed_price_emission':h.check_emissions([bad])}
assert result['quote_value_binding']=={'good_integrity':True,'changed_price_integrity':False,'good_emission':True,'changed_price_emission':False}
result['duplicate_and_conflict']={'same_duplicate_before':h.is_duplicate(good)};h.add(good)
result['duplicate_and_conflict']['same_duplicate_after']=h.is_duplicate(good)
try:h.is_duplicate(bad)
except Exception as e:result['duplicate_and_conflict']['changed_duplicate_error']=str(e)
# Actual schema; deliberately supply only its first iterated input binding.
# Method-level reproduction, not a full Adapter.send exploit.
c=Context();first=next(iter(good.schema.ins));c._bindings[first]=good.payload[first]
result['dependency_checker_early_return']={'required_inputs':sorted(good.schema.ins),'first_iterated':first,'known':list(c.bindings),'all_required_known':good.schema.ins<=set(c.bindings),'returned':h.check_dependencies(good,c)}
assert result['dependency_checker_early_return']['returned'] is True
assert not result['dependency_checker_early_return']['all_required_known']
# Concrete receive path: an unseen message's inputs are not validated locally.
async def receive_probe():
 system={'purchase':{'protocol':P,'roles':{r:r.name for r in P.roles.values()}}}
 agents={r.name:[('127.0.0.1',8000+i)] for i,r in enumerate(P.roles.values())}
 a=Adapter('Seller',system,agents)
 signals=[]
 async def capture(e):signals.append(type(e).__name__)
 a.signal=capture
 m=msg('Accept',order='unseen',item='invented',price=1,accepted=True)
 await a.receive(m.serialize())
 return {'stored':any(x.payload==m.payload for x in a.history.messages()),'signals':signals,'history_had_quote':False,'scope':'receive permits consistent new knowledge; does not authenticate sender or prove remote sender dependencies'}
result['receive_unseen_input_values']=asyncio.run(receive_probe())
# Static model: compliant role-local emissions rather than arbitrary payload values.
result['static_purchase']={'safety':paths.safe(P),'liveness':paths.live(P)}
unsafe=parse('''Race { roles A, B parameters out id key, out x
A -> B: Start[out id key]
A -> B: Left[in id key, out x]
B -> A: Right[in id key, out x]
}''').protocols['Race']
result['static_conflicting_producers']=paths.safe(unsafe)
assert result['static_conflicting_producers']['safe'] is False
nonlive=parse('''Stuck { roles A, B parameters out id key, out x, out y
A -> B: Start[out id key]
A -> B: X[in id key, in y, out x]
B -> A: Y[in id key, in x, out y]
}''').protocols['Stuck']
result['static_circular_knowledge']=paths.live(nonlive)
assert result['static_circular_knowledge']['live'] is False
# nil is local absence: two senders can independently choose while unaware.
nilp=parse('''NilRace { roles A, B parameters out id key, out left, out right
A -> B: Start[out id key]
A -> B: L[in id key, out left, nil right]
B -> A: R[in id key, out right, nil left]
}''').protocols['NilRace'];start=paths.Emission(nilp.messages['Start']);path=(start,paths.Reception(start,nilp.roles['B']));left=paths.Emission(nilp.messages['L']);right=nilp.messages['R']
result['nil_is_local']={'right_enabled_after_left_sent_not_received':paths.viable(path+(left,),right)}
assert result['nil_is_local']['right_enabled_after_left_sent_not_received']
handoff=parse('''Handoff { roles A, B, C parameters out id key, out x, out y
A -> B: M[out id key, out x]
B -> C: N[in id key, in x, out y]
}''').protocols['Handoff'];m=paths.Emission(handoff.messages['M']);hp=(m,paths.Reception(m,handoff.roles['B']))
result['handoff']={'B_can_send_N_after_receiving_M':paths.viable(hp,handoff.messages['N']),'C_observed_M':bool(paths.known(hp,handoff.messages['M'].keys,handoff.roles['C']))}
assert result['handoff']=={'B_can_send_N_after_receiving_M':True,'C_observed_M':False}
# Existing repository's refinement example, no substitute definition.
q=load_file('/private/tmp/cbcl-bspl-source-audit/samples/refinement/concurrency-elimination.bspl').protocols
result['refinement_ship_first']=refines(paths.UoD(),q['Flexible-Purchase'].public_parameters.keys(),q['Ship-First'],q['Flexible-Purchase'])
assert result['refinement_ship_first']['ok']
print(json.dumps(result,indent=2,default=str))
