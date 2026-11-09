State observations (SPEC-038): `state_schema` marks current field values with
`"observation":"snapshot"`. An external effect fired on a snapshot has no
finality guarantee from the kernel. Use a reached threshold to establish a
stable successful fact, or wait for the declared freeze and inspect the folded
`{frozen, superseded, value}` result for its exact causal cut. A `freeze` entry
in the schema describes that capability; before the freezer arrives the value
is still a snapshot. Thresholds and frozen reads can report a terminal fault;
handle its evidence explicitly. The host remains responsible for effect
idempotency, delivery and any external transaction or finality policy.
