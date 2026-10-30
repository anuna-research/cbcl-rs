---
title: Collective actor Orientation review
mode: reference
---

# Collective actor Orientation review

The initial reader accidentally received the full spec; its result was discarded
as a blinded gate. Subsequent fresh readers received only extracted Orientation
text and used no tools. Their questions exposed missing descriptions of empty
business labels, quorum size, replay indexing and signed floor/cap arithmetic.
The Orientation was clarified before accepting comprehension evidence.

The final reader, `/root/collective_actor_orientation_pass`, correctly predicted
original-signer cancellation, operation-role checkpoint eligibility, unrestricted
Byzantine voting, 2f+1 quorum, receipt/rejection stuttering, replay persistence and
the explicit signature/binding assumptions. It predicted floor -10 / rights 5 /
cap -2 as admissible with displayed value -5 and headroom 3, and floor -10 / rights
0 / cap -12 as rejected. It selected
[[SPEC-028-collective-actor-refinement#CON-2800]] for request grammar and
[[SPEC-028-collective-actor-refinement#CON-2801]] for execution.

The reader left uncapped headroom representation to the execution contract;
that contract now states zero, inactive headroom. No posed behavior remained
ambiguous. The complete spec was not supplied to the final blinded reader.
