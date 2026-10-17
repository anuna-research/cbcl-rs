# Confused deputy

A program that holds authority from two sources and uses the wrong one on a
caller's behalf. Hardy's compiler wrote its billing file because a caller
named that file as an output. The compiler's own licence covered the write,
and nothing distinguished the two authorities.

The capability remedy is designation: every request names the authority it
uses, so a deputy cannot apply one principal's authority to another's
request. CBCL applies it with the `:under` attribute of
[[SPEC-020-capability-seats]]; see [[object-capability]].
