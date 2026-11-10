---
title: "Common Business Communication Language (CBCL): Safe Self-Extending Agent Communication"
abbrev: "CBCL"
category: info
docname: draft-oconnor-cbcl-01
submissiontype: IETF
number:
date:
consensus: true
v: 3
area: "Applications and Real-Time"
workgroup: "Independent Submission"
keyword:
 - agent communication
 - multi-agent systems
 - homoiconic
 - content type
 - language-theoretic security
venue:
  group: "Independent"
  type: "Individual Draft"
  mail: "hugo@anuna.io"

author:
 -
    fullname: Hugo O'Connor
    organization: Anuna Research
    email: "hugo@anuna.io"

normative:
  RFC2119:
  RFC8174:
  RFC6838:
  RFC5234:
  RFC7405:
  RFC8032:
  RFC6234:
  RFC9804:
  RFC9485:
  RFC3629:

informative:
  FIPA-ACL:
    title: "FIPA ACL Message Structure Specification"
    author:
      org: Foundation for Intelligent Physical Agents
    date: 2002
    target: "http://www.fipa.org/specs/fipa00061/"
  KQML:
    title: "KQML as an agent communication language"
    author:
      - ins: T. Finin
      - ins: Y. Labrou
      - ins: J. Mayfield
    date: 1994
    seriesinfo:
      Proceedings: "Third International Conference on Information and Knowledge Management"
  LANGSEC:
    title: "Security Applications of Formal Language Theory"
    author:
      - ins: L. Sassaman
      - ins: M. L. Patterson
      - ins: S. Bratus
      - ins: M. E. Locasto
    date: 2013-09
    seriesinfo:
      IEEE Systems Journal: "vol. 7, no. 3, pp. 489-500"
    target: "https://doi.org/10.1109/JSYST.2012.2222000"
  MCCARTHY-CBCL:
    title: "Common Business Communication Language"
    author:
      - ins: J. McCarthy
    date: 1982
    target: "https://www-formal.stanford.edu/jmc/cbcl2.pdf"
  RACKET-LANG:
    title: "Creating Languages in Racket"
    author:
      - ins: M. Flatt
    date: 2012
    seriesinfo:
      Communications of the ACM: "Vol. 55, No. 1"
    target: "https://doi.org/10.1145/2063176.2063195"
  CBCL-PAPER:
    title: "CBCL: Safe Self-Extending Agent Communication"
    author:
      - ins: H. O'Connor
    date: 2026-04
    seriesinfo:
      LangSec: "IEEE Security and Privacy Workshops (SPW)"
    target: "https://arxiv.org/abs/2604.14512"
  CALM:
    title: "Keeping CALM: When Distributed Consistency Is Easy"
    author:
      - ins: J. M. Hellerstein
      - ins: P. Alvaro
    date: 2020
    seriesinfo:
      Communications of the ACM: "Vol. 63, No. 9, pp. 72-81"
  EPP:
    title: "Multiparty Session Types and Endpoint Projection"
    author:
      - ins: K. Honda
      - ins: N. Yoshida
      - ins: M. Carbone
    date: 2008
    seriesinfo:
      POPL: "Proceedings of the 35th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages"

--- abstract

This document specifies CBCL (Common Business Communication Language), a
self-extensible agent communication language for autonomous multi-agent
systems. CBCL provides a minimal core vocabulary of performatives and a formal
mechanism for agents to define, exchange, and adopt domain-specific dialect
extensions at runtime without centralized coordination. All messages, including
dialect definitions, are S-expressions constrained to the deterministic
context-free language (DCFL) class, so message validity remains decidable as
the vocabulary grows. Six safety invariants are enforced by the same recognizer
that handles ordinary communication: three structural (no recursion, resource
bounds, core preservation), one cryptographic (integrity), one for optional
message contracts, and one for an optional multiparty role layer that supports
coordination-free endpoint projection. This specification defines CBCL message
syntax, dialect extension, contract and role semantics, content addressing, and
registers the application/cbcl media type.

--- middle

# Introduction

Agent communication languages (ACLs) enable autonomous software agents to
coordinate, negotiate, and exchange information in multi-agent systems. Existing
ACLs such as KQML {{KQML}} and FIPA-ACL {{FIPA-ACL}} provide fixed vocabularies
of performatives (communicative acts like inform, request, query) that must be
understood by all participants. While these languages have proven useful in
controlled environments, they face significant challenges in open, dynamic
systems where:

- Devices join and leave frequently (IoT swarms, edge computing)
- Domain vocabularies evolve rapidly (supply chains, emergency response)
- No single authority controls all participants (federated systems,
  cross-organizational coordination)
- Agents need specialized performatives for domain-specific tasks

The fundamental problem is the **static vocabulary limitation**: when agents
need new communicative capabilities, they must wait for out-of-band
standardization processes or rely on lowest-common-denominator abstractions that
reduce expressiveness.

Recent work has attempted to address this limitation by using natural language
or unrestricted schemas for agent communication, enabling greater flexibility.
However, this approach introduces a more severe problem: an **unbounded attack
surface**. When agents communicate through natural language prompts or
unrestricted data structures, determining whether a message is safe requires
solving undecidable problems. No amount of input validation can guarantee
security when the input language itself has unbounded computational complexity.
This tension between extensibility and security motivates CBCL's design.

This challenge was recognized early by McCarthy {{MCCARTHY-CBCL}}, who proposed a
"Common Business Communication Language" that would be "open ended so that as
programs improve, programs that can at first only order by stock numbers can
later be programmed to inquire about specifications and prices." McCarthy's
vision emphasized that effective agent communication requires both a stable
foundation and mechanisms for evolutionary growth.

Named in honor of McCarthy's work, CBCL aspires to this vision by making the
language self-extensible. Agents can define new domain-specific "dialects" (sets
of specialized performatives) and share them with peers as first-class CBCL
messages. Because dialect definitions are themselves valid CBCL messages with
the same S-expression syntax, an agent can transmit a dialect definition using
the same message-passing mechanism it uses for ordinary communication,
eliminating the need for a separate meta-language or trusted intermediaries.
This approach draws inspiration from Racket's #lang mechanism {{RACKET-LANG}},
adapted for distributed, multi-agent environments.

## Layering

CBCL is specified in three layers, each optional above the one below. An
implementation MAY conform at any layer; {{conformance}} defines what each
requires.

- **Core** ({{message-format}}, {{dialect-extension}}): the S-expression
  grammar, the eight core performatives, dialect definition and installation,
  and safety invariants R1 through R4. This layer is sufficient for
  point-to-point agent communication with an extensible vocabulary.
- **Contracts** ({{contracts}}): optional per-dialect declarations constraining
  the causal order in which performatives may occur and the shape of each
  expanded message, plus the three-valued verification verdict they produce.
  Invariant R5 governs their well-formedness.
- **Roles** ({{roles}}): an optional multiparty layer over contracts, giving
  each performative sender and recipient *roles*, so that a conversation can be
  projected onto each participant and verified locally without coordination.
  Invariant R6 governs its well-formedness.

{{content-addressing}} specifies the content addressing, attestation, and
selective-disclosure machinery the upper two layers depend on.

The theoretical framework for the core layer, including the DCFL preservation
argument, is developed in {{CBCL-PAPER}}.

## Terminology

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD",
"SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this
document are to be interpreted as described in BCP 14 {{RFC2119}} {{RFC8174}}
when, and only when, they appear in all capitals, as shown here.

Additionally, this document uses the following terms:

**Agent**: An autonomous software entity that can send and receive CBCL
messages.

**Performative**: A named message type denoting a communicative act (for
example tell, ask, reply). A performative is either *core* ({{core-performatives}})
or *custom* (introduced by a dialect).

**Dialect**: A named collection of performative definitions that extend the core
CBCL vocabulary, together with optional contract, role, and integrity
declarations.

**Template**: The pattern-substitution rule that maps an invocation of a dialect
performative to a core CBCL message.

**Homoiconicity**: The property that code and data share the same
representation, enabling programs to manipulate their own structure.

**Content address**: The digest that names a message ({{content-addressing}}).

**Thread**: A conversation context identified by a thread identifier, carried in
the `:thread` keyword parameter.

**Causal reference**: The `:caused-by` keyword parameter, naming the content
addresses of the messages a message causally depends on.

**Role**: A named participant position in a multiparty protocol, occupied by one
agent (a *singleton* role) or by several (an *indexed* role).

**Cast**: The assignment of agent keys to roles for one thread.

**Projection**: The derivation, from a whole-conversation protocol, of the
behaviour visible to a single role.

# CBCL Message Format {#message-format}

## Overview

CBCL messages use S-expression (symbolic expression) syntax, a notation
originating from Lisp that represents nested list structures. This choice
provides:

- Simple, unambiguous parsing
- Natural representation of nested message structures
- Human readability for debugging and logging
- Established parser implementations across languages

All CBCL messages are S-expressions, but not all S-expressions are valid CBCL
messages. Valid messages MUST conform to the grammar specified in this section
and satisfy the semantic constraints defined in {{core-semantics}}.

## Syntax Notation

The grammar in this specification uses Augmented Backus-Naur Form (ABNF) as
defined in {{RFC5234}}, including its core rules, with case-sensitive strings
from {{RFC7405}}. Every literal in the grammar is explicitly case-sensitive
(`%s"..."`). Core names, wrapper names, keywords, boolean literals, and
signature-suite names MUST NOT be case-folded.

A CBCL message is a sequence of octets that MUST be well-formed UTF-8
{{RFC3629}}. Recognition is defined over the resulting sequence of Unicode
scalar values. Input that is not well-formed UTF-8 MUST be rejected before
recognition begins.

Where a production admits any Unicode scalar value, this document writes
`UTF8-char`; in ABNF over octets this expands to the {{RFC3629}} encoding:

~~~abnf
UTF8-char  = %x00-7F / utf8-2 / utf8-3 / utf8-4

utf8-2     = %xC2-DF UTF8-tail
utf8-3     = %xE0 %xA0-BF UTF8-tail
           / %xE1-EC 2UTF8-tail
           / %xED %x80-9F UTF8-tail
           / %xEE-EF 2UTF8-tail
utf8-4     = %xF0 %x90-BF 2UTF8-tail
           / %xF1-F3 3UTF8-tail
           / %xF4 %x80-8F 2UTF8-tail
UTF8-tail  = %x80-BF
~~~

## Layer 1: S-Expression Syntax {#sexpr-grammar}

~~~abnf
; ================================================================
; Layer 1: S-expression syntax
; Reference: crates/cbcl-parser/src/parser.rs
; ================================================================

; A complete input is exactly one S-expression. Trailing content
; after the expression, other than whitespace, MUST be rejected.
cbcl-input   = WS s-expr WS

s-expr       = list / atom

list         = %s"(" *( WS s-expr ) WS %s")"

atom         = string / boolean / keyword / numeric / symbol

; -- Whitespace and comments -------------------------------------

WS           = *( wsp-char / comment )

wsp-char     = SP / HTAB / LF / FF / CR

FF           = %x0C                     ; form feed

; A comment runs to the next line feed, or to end of input.
comment      = %s";" *( UTF8-char-not-LF ) [ LF ]

UTF8-char-not-LF = %x00-09 / %x0B-7F / utf8-2 / utf8-3 / utf8-4

; -- Symbols -----------------------------------------------------

symbol       = 1*symbol-char

symbol-char  = ALPHA / DIGIT / %s"_" / %s"-" / %s"." / %s"/"
             / %s"!" / %s"?" / %s"+" / %s"*" / %s"<" / %s">" / %s"="
               / %s"@"

; -- Numbers -----------------------------------------------------
;
; Digit-led tokens, including "-" followed by DIGIT, MUST match
; numeric. The number production remains integer-only wherever used
; for bounds, repetition, arithmetic, or threshold parameters.
numeric      = number / float / decimal
number       = [ %s"-" ] 1*DIGIT
float        = [ %s"-" ] 1*DIGIT
               ( float-frac [ float-exp ] / float-exp )
float-frac   = %s"." *DIGIT
float-exp    = ( %s"e" / %s"E" ) [ %s"+" / %s"-" ] 1*DIGIT
decimal      = [ %s"-" ] 1*DIGIT [ %s"." 1*DIGIT ] %s"m"

; -- Strings -----------------------------------------------------

string       = DQUOTE *( string-char / escape ) DQUOTE

; any character except DQUOTE (%x22) and %x5C
string-char  = %x00-21 / %x23-5B / %x5D-7F
             / utf8-2 / utf8-3 / utf8-4

escape       = %x5C ( DQUOTE / %x5C / %s"n" / %s"r" / %s"t" )

; -- Booleans and keywords ---------------------------------------

boolean      = %s"#t" / %s"#f"
; A following delimiter or end of input is required by the normative
; scanner rule below; lookahead is not an ABNF operator.

delimiter    = wsp-char / %s"(" / %s")" / DQUOTE / %s";"

keyword      = %s":" 1*symbol-char
~~~

### Tokenization Rules {#tokenization}

The grammar above is recognized by a deterministic single-token-lookahead
scanner. Three of its rules are not expressible in ABNF alone and are normative:

1. **Dispatch is by first character, without backtracking.** `(` begins a list;
   `"` a string; `#` a boolean; `:` a keyword; a DIGIT, or `-` followed by a
   DIGIT, a number; any other character a symbol.

2. **Numeric tokens are maximal.** After digit-led dispatch, the scanner
   consumes through the next delimiter or end of input. The complete token
   MUST match `numeric`. Integers MUST fit the signed 64-bit range; floats MUST
   decode to finite IEEE 754 binary64 values. Decimals retain arbitrary
   precision without conversion through binary floating point. The decimal
   suffix is lowercase `m`, and decimal exponents are not permitted.
   Consequently `1-2`, `1-`, `1e`, `1e9999`, `1.m`, and `1e2m` are errors,
   not symbols. A `-` **not** followed by a DIGIT begins a symbol, so `-`,
   `-a`, `--3`, and `->` are symbols. Leading `+` and leading decimal points
   also select symbol recognition: `+1.0`, `.5`, and `-.5` are symbols.

3. **Boolean literals require a following delimiter.** `#` MUST be followed by
   exactly `t` or `f` and then by a delimiter or end of input. `#true`, `#tx`,
   and `#` alone MUST be rejected. (See {{divergences}}: the reference
   implementation does not currently enforce the delimiter.)

Escape sequences other than the five listed MUST be rejected. Implementations
MUST NOT repair an unrecognized escape by preserving it literally.

### Resource Bounding of Recognition

A conformant recognizer MUST bound its own recursion. The reference
implementation carries a *fuel* budget: one unit is consumed per S-expression
node entered, and the default budget is the input length in octets (minimum 1).
Because every node consumes at least one input octet, this budget can only be
exhausted by input that is already invalid, and recognition is O(n) in the input
length with recursion depth bounded by it.

Implementations MAY use any equivalent mechanism (an explicit stack, an explicit
depth counter) provided recognition terminates on every input and never consumes
unbounded stack.

## Layer 2: Message Grammar {#core-grammar}

~~~abnf
; ================================================================
; Layer 2: CBCL message grammar
; Reference: crates/cbcl-core/src/message.rs
;
; Dispatch is deterministic by head symbol:
;   "meta"        -> meta-message
;   "lang"        -> lang-message
;   "envelope"    -> wrapped-message
;   "signed"      -> wrapped-message
;   "with-limits" -> wrapped-message
;   "with-roles"  -> wrapped-message
;   otherwise     -> simple-message
; ================================================================

cbcl-message = simple-message / meta-message
             / lang-message / wrapped-message

; The head of every message MUST be a symbol. An empty list, or a
; list whose first element is a non-symbol, MUST be rejected.

; -- Simple messages ---------------------------------------------
;
; Recipient and content are both optional. The recipient position is
; recognized only as the first element after the performative, and
; only if it is an address group. An absent content is the empty
; list.

simple-message = %s"(" core-performative message-tail %s")"
custom-message = %s"(" custom-performative message-tail %s")"

message-tail = [ WS recipients ]
                     [ WS content ]
                     *( WS param )

; Custom messages are admitted only within lang scope. Wrappers carry
; that context through; a nested lang selects its own dialect.
scoped-message = simple-message / custom-message / meta-message
               / lang-message / scoped-wrapped-message

core-performative = %s"tell" / %s"ask" / %s"reply" / %s"hello"
                  / %s"bye" / %s"ok" / %s"error" / %s"cancel"

custom-performative = symbol
                    ; excludes core names and reserved heads
                    ; ("meta", "lang", or a wrapper-type);
                    ; requires an enclosing lang wrapper

recipients   = address / address-group

address      = %s"@" 1*symbol-char

address-group = %s"(" address *( WS address ) %s")"    ; non-empty

content      = s-expr
             ; MUST NOT be an address or an address-group

param        = keyword-param / positional-param

positional-param = s-expr
             ; MUST NOT be an address or an address-group

keyword-param = reserved-param / user-param

user-param   = keyword WS s-expr

; -- Reserved keyword parameters ---------------------------------

reserved-param = thread-param / sender-param / caused-by-param

thread-param   = %s":thread"  WS ( string / symbol )
sender-param   = %s":sender"  WS ( string / symbol )
caused-by-param = %s":caused-by" WS caused-by-value

caused-by-value = begin-ref / hash-ref / hash-list

begin-ref    = %s"begin" / DQUOTE %s"begin" DQUOTE

hash-ref     = string / symbol           ; a content address

hash-list    = %s"(" hash-ref *( WS hash-ref ) %s")"   ; non-empty

; -- Meta messages -----------------------------------------------

meta-message = %s"(" %s"meta" WS meta-operation *( WS s-expr ) %s")"

meta-operation = meta-query / meta-teach
               / dialect-definition / s-expr

meta-query   = %s"(" %s"query" WS s-expr %s")"

meta-teach   = %s"(" %s"teach" WS address WS s-expr %s")"

; -- Language-scoped messages ------------------------------------

lang-message = %s"(" %s"lang" WS dialect-name WS scoped-message
                   *( WS s-expr ) %s")"

dialect-name = symbol

; -- Wrapped messages --------------------------------------------
;
; The inner message is the LAST list-valued element. Every element
; before it is a wrapper parameter.

wrapped-message = %s"(" wrapper-type *( WS wrapper-param )
                      WS cbcl-message *( WS atom ) %s")"

scoped-wrapped-message = %s"(" wrapper-type *( WS wrapper-param )
                      WS scoped-message *( WS atom ) %s")"

wrapper-type = %s"envelope" / %s"signed" / %s"with-limits" /
               %s"with-roles"

wrapper-param = s-expr
~~~

### Recipients and Multicast

The recipient position accepts either a single address (`@bob`) or a non-empty
list of addresses (`(@bob @carol)`), the latter denoting multicast. A multicast
recipient set is unordered; implementations MUST serialize it in ascending
lexicographic order so that a message has one canonical byte encoding
({{canonical-form}}).

A performative addressed to no other participant simply carries no recipient
position.

Addresses are recognized structurally by the `@` sigil, so an address or a list
consisting only of addresses MUST be rejected in the content or positional
parameter position. Without this restriction, serialization would not be
injective: a content address group would re-parse as the recipient. A *mixed*
list such as `(introduce @bob)` is ordinary content; nested addresses inside
content are permitted, as is an `@` inside a string.

Note that the recipient is recognized only in the position immediately after the
performative. In `(tell "x" @bob)` the string is the content and `@bob` is an
address in positional-parameter position, which MUST be rejected.

### Reserved Keyword Parameters

`:thread`, `:sender`, and `:caused-by` are reserved. Implementations MUST lift
them out of the general parameter list into the corresponding structured message
fields, and MUST NOT retain them as ordinary parameters. All other keyword
parameters are retained in the order they appear.

A `:caused-by` list MUST NOT be empty, and each of its elements MUST be a string
or a symbol; a number, boolean, keyword, or nested list is an error.
Implementations MUST store multiple references in ascending lexicographic order
so that the encoding is canonical.

Content addresses contain a `:` separator ({{content-addressing}}), which is
**not** a `symbol-char`. Content addresses therefore MUST be written as strings
on the wire:

~~~
(tell @bob "hi" :caused-by "sha256:2b7f0e…")
(tell @bob "hi" :caused-by ("sha256:2b7f0e…" "sha256:91ac4d…"))
~~~

Writing a content address as a bare symbol produces two tokens (the symbol
`sha256` and the keyword `:2b7f0e…`) and MUST be rejected. See
{{divergences}}.

## Core Performatives {#core-performatives}

CBCL defines eight core performatives that constitute the minimal bootstrap
vocabulary. These MUST be understood by all conformant CBCL implementations:

**Information Exchange:**

- **tell**: Assert a proposition or communicate information to a recipient
- **ask**: Request information or pose a query to a recipient
- **reply**: Respond to a previous ask or tell message

**Session Management:**

- **hello**: Initiate a communication session
- **bye**: Terminate a communication session

**Control Flow:**

- **ok**: Acknowledge successful processing of a message
- **error**: Indicate an error condition or failed processing
- **cancel**: Request cancellation of a previous operation

### Custom Performatives {#custom-performatives}

A message whose head symbol is neither a reserved head nor a core performative
is a **custom performative** invocation. It MUST appear inside a
`(lang <dialect> …)` wrapper. A bare custom invocation MUST be rejected during
message recognition, even if exactly one installed dialect defines its name.

### Scoped Invocation {#invocation-scope}

A custom performative is resolved **only** against the dialect named by its
enclosing `lang` wrapper. If that dialect is not installed, or does not define
the performative, resolution fails. There is no fallback to another installed
dialect. Two dialects may define the same custom name: the wrapper selects
which definition is meant.

Ordinary wrappers such as `signed` preserve the enclosing scope. Nested
`lang` wrappers replace it with their own dialect name. Programmatically
constructed messages MUST obey the same rule as parsed messages: evaluation
MUST reject a custom invocation without a scope.

The core performatives are unaffected. R3 forbids extensions from redefining
them, and they resolve against the base dialect, including inside a `lang`
wrapper.


## Message Examples {#message-examples}

Simple tell message:

~~~
(tell @bob "The meeting is at 3pm")
~~~

Ask with parameters:

~~~
(ask @alice "What is the status of task-42?"
     :thread conversation-17
     :timeout 30)
~~~

Reply with threaded context:

~~~
(reply @alice "Task-42 is 75% complete"
       :thread conversation-17
       :in-reply-to msg-id-9874)
~~~

Multicast with a causal reference, scoped to the dialect defining `announce`:

~~~
(lang auction
  (announce (@bob @carol) "round 2 open"
            :thread auction-9
            :caused-by "sha256:2b7f0e…"))
~~~

Envelope with metadata:

~~~
(envelope :from @alice
          :to @bob
          :timestamp "2025-01-15T14:30:00Z"
  (tell @bob "Hello"))
~~~

# Dialect Extension Mechanism {#dialect-extension}

## Overview

Dialects enable agents to extend CBCL's vocabulary with domain-specific
performatives while maintaining parsing determinism and safety properties. A
dialect definition is itself a CBCL message that can be transmitted, verified,
and installed by receiving agents.

## Layer 3: Dialect Definition Grammar {#dialect-grammar}

~~~abnf
; ================================================================
; Layer 3: Dialect definition grammar
;
; Entered via (meta (define ...)), (meta (teach @peer ...)), or a
; standalone (define ...) form.
; Reference: crates/cbcl-parser/src/dialect_parser.rs
;
; Positional args: (define <name> <extends-list> <author> ...)
; followed by optional clauses in any order.
; ================================================================

dialect-definition = %s"(" %s"define" WS dialect-name
                     WS extends-list WS author
                     *( WS dialect-clause ) %s")"

extends-list = %s"(" *( WS symbol ) %s")"

author       = symbol / string

dialect-clause = extend-clause / protocol-clause / shape-clause / type-decl
               / state-clause / state-bounds-clause
               / resource-clause / examples-clause
               / signature-clause / hash-clause
               / sig-algorithm-clause / roles-clause
               / causal-locality-clause

; -- Performative extension --------------------------------------
;
; Exactly one template form. The :from/:to annotations are the
; role layer (Section "Multiparty Role Layer") and may appear
; before or after the template.

extend-clause = %s"(" %s"extend" WS perf-name WS param-list
                    1*( WS extend-item ) %s")"

extend-item  = role-from / role-to / template

role-from    = %s":from" WS role-name
role-to      = %s":to" WS ( role-name / role-set )
role-set     = %s"(" *( WS role-name ) %s")"

perf-name    = symbol
role-name    = symbol
param-list   = %s"(" *( WS symbol ) %s")"
template     = s-expr

; -- Resource requirements ---------------------------------------

resource-clause = %s"(" %s":resource-requirements"
                  WS resource-alist %s")"

resource-alist = %s"(" *( WS resource-pair ) %s")"

resource-pair = %s"(" resource-key WS number %s")"

resource-key = %s"max-depth" / %s"max-expansion-size"
             / %s"verification-time"

; -- Integrity and metadata --------------------------------------

examples-clause      = %s"(" %s":examples" *( WS s-expr ) %s")"

signature-clause     = %s"(" ( %s":signature" / %s":signed" )
                       WS ( string / symbol ) %s")"

hash-clause          = %s"(" %s":hash" WS ( string / symbol ) %s")"

sig-algorithm-clause = %s"(" %s":protocol" WS ( string / symbol )
               %s")"

; -- Role layer --------------------------------------------------

roles-clause = %s"(" %s":roles" WS role-decl-list %s")"

role-decl-list = %s"(" role-decl *( WS role-decl ) %s")"

role-decl    = role-name                      ; singleton role
             / %s"(" %s"*" WS role-name %s")"       ; indexed role

causal-locality-clause = %s"(" %s":causal-locality"
                         WS ( %s"derive" / %s"reject" ) %s")"

; -- Contracts (see Section "Message Contracts") -----------------

protocol-clause = %s"(" %s"protocol" 1*( WS then-clause ) %s")"

then-clause  = %s"(" %s"then" 2*( WS protocol-step ) %s")"

protocol-step = node-ref / repeat-form

node-ref     = perf-name
             / %s"(" %s"any" WS perf-name 1*( WS perf-name ) %s")"
             / %s"(" %s"all" WS perf-name 1*( WS perf-name ) %s")"

repeat-form  = %s"(" %s"repeat" WS positive-number
                   1*( WS protocol-step ) %s")"

positive-number = 1*DIGIT              ; MUST be greater than zero

shape-clause = %s"(" %s"shape" WS perf-name 1*( WS shape-rule ) %s")"

shape-rule   = require-rule / optional-rule / depth-rule

require-rule = %s"(" %s"require" WS keyword [ WS type-expr ]
                   *( WS shape-rule ) %s")"

optional-rule = %s"(" %s"optional" WS keyword [ WS type-expr ]
                    [ WS default-value ] *( WS shape-rule ) %s")"

depth-rule   = %s"(" %s"max-depth" WS number %s")"

type-decl    = %s"(" %s"type" WS local-type-name WS type-expr %s")"
type-expr    = builtin-type / local-type-name
             / %s"(" %s"one-of" 1*( WS atom ) %s")"
             / %s"(" %s"string" 1*( WS string-rule ) %s")"
             / %s"(" %s"list" 1*( WS length-rule ) %s")"
             / %s"(" numeric-base 1*( WS numeric-bound ) %s")"
             / %s"(" ( %s"and" / %s"or" ) 2*( WS type-expr ) %s")"
builtin-type = %s"string" / %s"hlc" / %s"number" / %s"integer"
             / %s"float" / %s"decimal" / %s"nonnegative" / %s"bool"
             / %s"symbol" / %s"keyword" / %s"list"
local-type-name = symbol  ; bounded lowercase name, excluding reserved names
numeric-base = %s"number" / %s"integer" / %s"float" / %s"decimal"
comparator   = %s">=" / %s">" / %s"<=" / %s"<"
numeric-bound = %s"(" comparator WS numeric %s")"
string-rule  = matches-rule / length-rule
matches-rule = %s"(" %s"matches" WS string %s")"
length-rule  = %s"(" %s"length" 1*( WS length-bound ) %s")"
length-bound = %s"(" comparator WS number %s")" ; nonnegative i64
default-value = %s"(" %s"default" WS s-expr %s")"
~~~

A clause whose head is an unrecognized keyword MUST be rejected. Implementations
MUST NOT silently ignore an unknown clause: a definition carrying a clause the
receiver does not understand is a definition the receiver cannot claim to have
installed.

Note the two distinct clauses spelled with the word "protocol". The keyword form
`(:protocol "ed25519")` names the *signature algorithm* used for the dialect's
integrity fields; the symbol form `(protocol (then …) …)` declares the dialect's
*causal protocol* ({{causal-protocols}}). They are unrelated. Implementations
MUST dispatch on whether the head is a keyword or a symbol.

## Dialect Definition

A dialect definition uses positional arguments followed by optional clauses:

- **dialect-name** (positional, REQUIRED): a unique dialect name
- **extends-list** (positional, REQUIRED): list of parent dialects, typically
  `(cbcl)` for core extensions
- **author** (positional, REQUIRED): author identifier for provenance tracking
- **extend clauses** (OPTIONAL, repeatable): performative definitions
- **:resource-requirements** (OPTIONAL): resource limits as an association list
- **:roles**, **:causal-locality** (OPTIONAL): role layer ({{roles}})
- **protocol**, **shape** (OPTIONAL): contracts ({{contracts}})
- **state**, **:state-bounds** (OPTIONAL): state rules ({{state}}); a state
  clause requires a protocol with exactly one opener and a shape for every
  keyword it reads
- **:examples** (OPTIONAL): S-expressions illustrating intended expansion
- **:signature**, **:hash**, **:protocol** (OPTIONAL): integrity fields

Example dialect definition:

~~~
(meta
  (define logistics-dialect
    (cbcl)
    @logistics-consortium
    (:resource-requirements
      ((max-depth 16)
       (max-expansion-size 4096)
       (verification-time 1000)))

    (extend track-shipment (package-id route priority)
      (tell @tracking-service
            (shipment-request
              :package package-id
              :route route
              :priority priority)
            :domain logistics))

    (extend confirm-delivery (package-id recipient timestamp)
      (tell recipient
            (delivery-confirmed
              :package package-id
              :time timestamp)
            :domain logistics))

    (:examples
      (track-shipment "PKG-42" "A->B" "normal")
      (tell @tracking-service
        (shipment-request
          :package "PKG-42"
          :route "A->B"
          :priority "normal")
        :domain logistics))))
~~~

The OPTIONAL `:examples` clause carries semantic meaning: each input/output pair
illustrates what the dialect author intends a performative to do in a concrete
scenario. Examples are the primary mechanism for communicating intended
semantics between agents. A receiving agent SHOULD evaluate the examples against
its own expander and compare the result with the expected output before claiming
dialect support; this catches template misconfiguration and parameter-type
disagreement, the most common interoperability failures, though it cannot detect
deeper semantic divergence.

## Safety Invariants {#safety-invariants}

Implementations MUST verify the following before installing a dialect. R1
through R4 apply to every dialect; R5 and R6 apply only when the corresponding
optional clauses are present.

### R1 - No Recursion

Extension definitions MUST use only pattern-template transformations. Direct and
mutual recursion are forbidden: no performative name may appear in its own
template, and the dependency graph over performative templates MUST be acyclic.
Iteration and reflection are prohibited.

### R2 - Resource Bounds {#r2}

Every dialect has resource limits, declared through the
`:resource-requirements` clause. Each is a positive integer within a hard system
limit:

| Key | Meaning | Range | Default if omitted |
|---|---|---|---|
| `max-depth` | maximum nesting depth of expanded messages | 1-64 | 16 |
| `max-expansion-size` | maximum cumulative expansion, in octets | 1-8192 | 1024 |
| `verification-time` | verification budget, in milliseconds | 1-1000 | 50 |

A dialect declaring a value of zero, a negative value, or a value above the
system limit MUST be rejected. The `:resource-requirements` clause itself is
OPTIONAL; a dialect that omits it, or that omits individual keys, takes the
defaults above, which are within the limits by construction. An unrecognized key
inside the association list is ignored.

The limits are enforced at both definition time and runtime: a template
expansion that would exceed the declared depth or cumulative size MUST be
abandoned with an error rather than completed.

### R3 - Core Preservation

Dialects MUST NOT redefine core performatives (tell, ask, reply, hello, bye, ok,
error, cancel).

### R4 - Provenance and Integrity

Dialect definitions MUST include author identification. When transmitted between
agents, dialect definitions SHOULD be cryptographically signed to ensure:

- **Authenticity**: the dialect came from the claimed author
- **Integrity**: the definition has not been modified in transit
- **Non-repudiation**: the author cannot deny creating the dialect

A dialect's identity is the content hash of its canonical encoding
({{canonical-form}}), not its name. Two dialects sharing a name but differing in
hash MUST be rejected at installation, which is what mitigates name collision
and downgrade attempts. Because the `lang` tag dispatches by name, an agent MUST
NOT hold two dialects with the same name.

Installation accepts a dialect whose signature verifies, and MAY accept an
unsigned dialect from a trusted local source, but MUST reject one whose
signature is present and invalid. Signature verification MUST precede every
other safety check, so that authorship and bit-exact contents are established
before any further work is done on attacker-supplied input.

### R5, R6, and R7

R5 (contract well-formedness) is specified in {{r5}}; R6 (multiparty
well-formedness) in {{r6}}; R7 (state well-formedness) in {{state}}.

## Expansion Semantics {#expansion}

Dialect performatives expand through pattern-template substitution. An extend
clause defines a new performative name, a parameter list, and a template
expression that becomes the expansion.

### Parameter Binding

Parameters are bound **positionally**. The nth symbol in the parameter list is
bound to the nth argument of the invocation. Arguments beyond the parameter list
are not bound to any name.

A parameter with no corresponding argument remains **unbound**, and an unbound
parameter name is *not* substituted: it survives into the expansion as a bare
symbol. Expanding `(extend p (x y) (tell @svc (req :x x :y y)))` with the single
argument `"only-x"` yields `(tell @svc (req :x "only-x" :y y))`. Implementations
MUST NOT treat an unbound parameter as nil or as the empty list. Senders SHOULD
supply an argument for every declared parameter, and receivers SHOULD reject an
expansion containing a residual parameter symbol, which shape constraints
({{contracts}}) will catch when a type is declared for the affected field.

CBCL has no keyword-argument or optional-parameter mechanism in parameter lists.
A dialect requiring an optional value declares it as an ordinary positional
parameter and selects between alternatives with a top-level `cond`
({{template-forms}}).

### Template Forms {#template-forms}

The template language supports exactly four constructs. It is deliberately not
Turing-complete: it has flat pattern matching, finite conditional branching, and
one-shot substitution. Expansion is single-pass — an expanded result is not fed
back through the expander — so expansion terminates in time linear in the
template size plus the substituted argument size, bounded by the declared limits
of {{r2}}.

1. **Substitution.** Any symbol occurring in the template that matches a
   parameter name is replaced by the bound argument. All other expressions are
   preserved literally.

2. **`(literal expr)`.** Substitutes bindings within `expr` and yields it
   directly. Used where a form would otherwise be mistaken for a special form.

3. **`(cond (test body) … (else body))`.** Evaluates each clause's test in order
   and yields the body of the first that holds; `else` always holds. If no
   clause holds and there is no `else`, expansion fails. Three tests are
   defined:

   - `(= var value)` — the bound value of `var` equals `value`
   - `(member var (value …))` — the bound value of `var` equals some listed
     value
   - `(type? var type-name)` — the bound value of `var` has the named type, one
     of `string`, `integer`, `number`, `float`, `decimal`, `bool`, `symbol`, `keyword`, `list`

   A test of any other form is false.

4. **Sequences.** A list whose every element is itself a `literal` or `cond`
   form expands to the concatenation of those elements' expansions.

### Where Special Forms Are Recognized {#special-form-scope}

Special forms are recognized **only in head position of the template itself**,
or as elements of a sequence template. They are *not* recognized in nested
position.

A `cond` appearing inside an otherwise ordinary template is therefore not
evaluated. It is treated as ordinary structure: parameter symbols within it are
substituted, and the `cond` form itself is copied verbatim into the expansion.
Expanding

~~~
(extend p (x)
  (tell @svc (req :v (cond ((= x ()) "default") (else x)))))
~~~

with the argument `()` yields

~~~
(tell @svc (req :v (cond ((= () ()) "default") (else ()))))
~~~

which is a well-formed message carrying a literal `cond` list as data — almost
certainly not what the author intended.

A dialect that needs conditional expansion MUST therefore lift the `cond` to the
top of the template and place a complete message in each branch:

~~~
(extend p (x)
  (cond ((= x ()) (tell @svc (req :v "default")))
        (else     (tell @svc (req :v x)))))
~~~

This restriction is what keeps expansion single-pass and its cost linear: the
expander never needs to search a template for evaluable subforms. Dialect authors
SHOULD declare shape constraints on conditional fields, so that a mistakenly
nested special form is caught at contract-check time rather than delivered.

### Example

Given the definition:

~~~
(extend track-shipment (package-id route priority)
  (cond
    ((= priority ())
     (tell @tracking-service
           (shipment-request
             :package package-id
             :route route
             :priority "normal")
           :domain logistics))
    (else
     (tell @tracking-service
           (shipment-request
             :package package-id
             :route route
             :priority priority)
           :domain logistics))))
~~~

The invocation:

~~~
(track-shipment "PKG-12345" "A->B" "urgent")
~~~

expands to:

~~~
(tell @tracking-service
      (shipment-request
        :package "PKG-12345"
        :route "A->B"
        :priority "urgent")
      :domain logistics)
~~~

and the invocation `(track-shipment "PKG-12345" "A->B" ())` expands to the same
message with `:priority "normal"`.

## Dialect Usage {#dialect-usage}

Once installed, a dialect performative MUST be invoked within a lang-scoped
message, which fixes which dialect defines it ({{invocation-scope}}):

~~~
(lang logistics-dialect
  (track-shipment "PKG-12345" "warehouse-A->depot-B" "urgent"))
~~~

The `lang` tag is the deterministic dispatch token: the recognizer selects the
subgrammar by consuming `lang` and the dialect name, with no lookahead beyond
that. This is what makes DCFL preservation straightforward
({{langsec-security}}).

Scoping is a syntactic requirement, rechecked during evaluation for messages
constructed programmatically. An unscoped custom invocation is malformed
and MUST NOT be expanded. {{shadowing}} sets out why that matters.

## Dialect Discovery

Agents can query peers for dialect capabilities:

~~~
(meta (query (speak? logistics-dialect)))
~~~

Response:

~~~
(reply @querying-agent "yes"
       :dialects (logistics-dialect planning-dialect))
~~~

## Dialect Teaching

Agents can share dialect definitions with peers. When transmitting to untrusted
agents, dialect definitions SHOULD be cryptographically signed:

~~~
(meta (teach @bob
  (signed "base64-encoded-signature"
    (define logistics-dialect
      (cbcl)
      @logistics-consortium
      (:resource-requirements
        ((max-depth 16)
         (max-expansion-size 4096)
         (verification-time 1000)))
      ; ... performative definitions ...
    ))))
~~~

The receiving agent MUST:

1. Verify the cryptographic signature (if present)
2. Check that the author matches the signing key
3. Verify the applicable safety invariants (R1-R3, and R5-R6 if declared)
4. Apply local trust policies

The receiving agent MAY reject the dialect based on:

- Invalid or missing signature
- Untrusted author
- Resource constraint violations
- Local security policy

# Message Contracts {#contracts}

A dialect MAY declare, alongside its performatives, two kinds of contract: a
**causal protocol** constraining the order in which its performatives may occur,
and **shape constraints** on the parameters each expanded message must carry.
Both are optional; a dialect declaring neither is governed by R1-R4 alone. A
third, optional layer, **state rules** ({{state}}), gives accepted messages a
transition semantics and requires both contracts for the performatives it reads.

Contracts extend CBCL's syntactic safety toward protocol correctness while
remaining within DCFL and requiring no coordination between participants.

## Causal Protocols {#causal-protocols}

A causal protocol is a directed acyclic graph over performative *types*, rooted
at the distinguished node `begin`. It is declared as a set of `then` chains:

~~~
(protocol
  (then begin propose-choreography prefer)
  (then (all propose-choreography prefer) request-policy)
  (then request-policy commit-policy)
  (then commit-policy (any at choose))
  (then (any at choose) observe-outcome)
  (then observe-outcome terminate))
~~~

A variadic chain desugars to pairwise edges: `(then a b c)` declares the edges
a→b and b→c. Two grouping forms may appear at either end of an edge, and each
takes **two or more** members:

- On the predecessor side, `(any p q …)` permits a cited predecessor of any
  listed type; `(all p q …)` requires evidence for every listed type.
- On the successor side, both forms generate the listed outgoing dependency
  edges. `any` expresses the sender's obligation to choose one alternative;
  `all` expresses the intent to emit every branch. Causal verification does
  not enforce successor exclusivity or guarantee eventual emission.

For example, both `accept` and `decline` can independently cite one valid
`offer` and satisfy their causal checks. Discovering a sibling later does not
retroactively invalidate either causal verdict. Chooser coherence identifies
the role responsible for choosing; it does not supply mutual exclusion.
Applications requiring a single business outcome need a separately specified
authorization or conflict-resolution policy.

`(repeat k step …)` may appear in step position inside a `then` chain and
nowhere else. `k` MUST be a positive integer. The form is macro-expanded once,
at parse time, into `k` sequential copies of its body spliced into the enclosing
chain, so all later checking runs over the expanded protocol. Copy *i* of step
`x` is named `x#i`. Because `#` is outside the symbol alphabet
({{sexpr-grammar}}), a synthesized copy name cannot collide with any
user-declared performative. Expansion is charged against a budget equal to the
largest `max-expansion-size` any dialect may declare, and an expansion exceeding
it MUST be rejected before being materialized.

Each message declares its position in the graph with the `:caused-by` keyword
parameter, naming the content addresses of its predecessors. The messages of a
conversation therefore form a hash-linked DAG that is tamper-evident and
independently verifiable.

## Shape Constraints

A shape constraint pins the keyword parameters an expanded message of a given
performative must carry, with optional type constraints:

~~~
(shape prefer
  (require :proto string)
  (require :role symbol)
  (require :outcome list)
  (require :utility integer))
~~~

`require` demands the parameter be present; `optional` permits it and MAY supply
a default; `max-depth` bounds the nesting of the checked message. Rules may nest,
constraining structure within a parameter's value. Type names are `string`,
`hlc`, `integer`, `number`, `float`, `decimal`, `nonnegative`, `bool`, `symbol`, `keyword`,
and `list`. `integer` accepts signed 64-bit integer atoms; `nonnegative` further
requires an integer value greater than or equal to zero. `float` and `decimal`
accept their respective numeric atoms without cross-type coercion. `hlc` checks
the canonical host-supplied hybrid logical clock string format.

`number` accepts integer, float, and decimal atoms without conversion. Local
`type` declarations introduce aliases, `one-of` scalar enumerations, numeric
bounds, string patterns, string/list lengths, and `and`/`or` composition.
Declarations resolve from the complete dialect; authors need not order them.
Patterns follow I-Regexp ({{RFC9485}}), with full-string matching and pinned Unicode
16.0.0 properties. String length counts Unicode scalar values; list length counts
immediate elements. Defaults use `(default value)` and are checked at installation.
The SPEC-040 profile imposes finite compilation, input, and work limits; resource
exhaustion is an operational `resource-limit`, not a failed value predicate.
Signing form 6 binds the profile and type definitions, requiring explicit signature
and self-address reissue for existing development dialects.

Shape checking is applied to the *expanded* message, non-recursively. Dialect
authors should therefore surface contract-relevant keyword parameters at the top
level of the expanded `tell` or `ask` rather than nesting them inside an inner
content form.

## R5 - Contract Well-Formedness {#r5}

When a dialect declares `protocol` or `shape` clauses, installation MUST verify
all of the following. Each check terminates in time linear in the size of the
dialect.

1. **Acyclicity**: the causal protocol contains no cycle.
2. **Reachability**: every declared step is reachable from `begin`.
3. **Performative definedness**: every performative named in the protocol is
   defined by the dialect or by an ancestor named in its extends-list.
4. **Step uniqueness**: no step is declared twice.
5. **Depth conformance**: shape constraints respect the dialect's declared
   `max-depth` from {{r2}}.

A dialect failing any check MUST NOT be installed.

## Verification Verdicts {#verdicts}

Verifying a message against a causal protocol yields one of three verdicts:

- **Valid**: every cited predecessor is present in the receiver's message store
  and has the type the protocol requires.
- **Violation**: a cited predecessor is present but has the wrong type, or the
  citation is malformed.
- **Unknown**: a cited predecessor is not present. The verdict is undecidable
  with the receiver's current state.

`Unknown` is the substantive case. Messages arrive out of order, so a receiver
that has not yet seen a predecessor cannot distinguish "not yet delivered" from
"never sent". Implementations MUST treat `Unknown` as undecided, MUST NOT
promote it to `Valid`, and SHOULD hold the message pending further arrivals
under a policy the deployment sets.

The operational combination rules are the following truth tables. `V`, `U`,
and `X` denote `Valid`, `Unknown`, and `Violation`, respectively; diagnostic
details attached to a violation do not change its verdict class.

| conjunction (`all`) | V | U | X |
|---|---|---|---|
| V | V | U | X |
| U | U | U | X |
| X | X | X | X |

| disjunction (`any`) | V | U | X |
|---|---|---|---|
| V | V | V | V |
| U | V | U | U |
| X | V | U | X |

These are strong Kleene conjunction and disjunction: min and max in the
truth order `Violation < Unknown < Valid`. Disjunction has identity
`Violation`, and conjunction has identity `Valid`. A failed alternative
combined with an unresolved one remains unresolved; the latter may still
succeed. These operations do not compute the bounds of the knowledge order.
In the knowledge order, `Unknown` is below both terminal verdicts, and
`Valid` and `Violation` are incomparable.
Their knowledge-order greatest lower bound is `Unknown`, whereas operational
conjunction of those two values is `Violation`. The knowledge order is a
meet-semilattice with bottom and has no join for the two terminal values.
The truth-order algebra is a bounded distributive lattice at the verdict-class
level, satisfying absorption and distributivity. Implementations MUST use
the tables above rather than substitute knowledge-order meet or join.

Store-growth claims apply to the specified verifier with immutable,
content-address-authenticated evidence and a fixed installed protocol and
thread context. Missing evidence can become available as the store grows;
this does not authorize arbitrary policy changes or treating an undecided
message as accepted. Replicas with the same evidence and context compute the
same verdict. They merge evidence and reverify, rather than attempting a
knowledge-order join of terminal verdicts. Both strong Kleene operations
are monotone under the knowledge order. For a fixed set of alternatives
whose terminal verdicts are stable, disjunction returns `Valid` once any
alternative is valid, `Violation` only when every alternative is a violation,
and `Unknown` otherwise. A convergence claim for a concrete causal verifier
still requires its evidence and admissible-transition assumptions; it does
not follow from the tables alone. A coordination-free convergence argument
using CALM {{CALM}} requires a monotone computation over growing evidence;
these tables alone do not establish that premise.

## State Rules {#state}

A dialect MAY declare a `state` clause naming the fields of an instance's state
and, for each, one rule from a closed vocabulary that says how accepted
messages of a given performative move the field. An *instance* is one thread;
its *opener* is the one performative whose predecessor is `begin`. The state of
an instance is a function of the set of accepted messages of its thread and of
nothing else.

~~~ abnf
state-clause   = %s"(" %s"state" 1*( WS state-entry ) %s")"
state-entry    = %s"(" field WS rule %s")"
               / %s"(" %s"domain" WS perf-name WS keyword WS field
               %s")"
; [a-z][a-z0-9-]{0,47}, unique in the clause
field          = symbol

rule           = bounded-counter-rule
               / %s"(" %s"last"              WS perf-name WS keyword
               %s")"
               / %s"(" %s"latest-per-signer" WS perf-name WS keyword
               %s")"
               / %s"(" %s"latest-per-key"    WS perf-name WS keyword
               WS keyword %s")"
               / %s"(" %s"exists"            WS perf-name %s")"
               / %s"(" %s"count"             WS perf-name %s")"
               / %s"(" %s"progress"          WS perf-name %s")"
               / %s"(" %s"events"            WS perf-name WS keyword
               %s")"
               / %s"(" %s"set-union"         WS perf-name WS keyword
               %s")"
               / %s"(" %s"values"            WS perf-name WS keyword
               %s")"
               / %s"(" %s"values-per-key"    WS perf-name WS keyword
               WS keyword
                                         [ WS perf-name ] %s")"
               / %s"(" %s"register-per-key"  WS perf-name WS keyword
               WS keyword
                                         [ WS perf-name ] %s")"
               / %s"(" %s"observed-set"      WS perf-name WS
               perf-name WS keyword %s")"
               / %s"(" %s"counter"           WS perf-name WS
               perf-name WS keyword %s")"
               / %s"(" %s"histogram"         WS field %s")"
               / %s"(" %s"sum"               WS field %s")"

bounded-counter-rule = %s"(" %s"bounded-counter" 1*( WS
               bounded-counter-option ) %s")"
bounded-counter-option = %s"(" %s"ownership" WS ( %s"account" /
               %s"collective" ) %s")"
                       / %s"(" %s"certification" WS
               certification-profile %s")"
                       / %s"(" %s"initial" WS perf-name WS keyword
               %s")"
                       / %s"(" %s"floor" WS number %s")"
                       / %s"(" %s"ceiling" WS number %s")"
                       / %s"(" %s"initial-rights" WS perf-name WS
               keyword %s")"
                       / %s"(" %s"initial-headroom" WS perf-name WS
               keyword %s")"
                       / %s"(" %s"issuers" WS ( role-name / %s"()" )
               %s")"
                       / %s"(" %s"increment" WS perf-name WS keyword
               %s")"
                       / %s"(" %s"decrement" WS perf-name WS keyword
               %s")"
                       / %s"(" %s"transfer" WS perf-name WS keyword
               WS keyword %s")"
                       / %s"(" %s"transfer-headroom" WS perf-name WS
               keyword WS keyword %s")"

certification-profile = %s"host-gate"
                      / %s"quorum-budget" *( WS committee-option )
committee-option = %s"(" %s"validators" 1*( WS address ) %s")"
                 / %s"(" %s"faults" WS number %s")"

state-bounds-clause = %s"(" %s":state-bounds" *( WS state-bound )
               %s")"
state-bound    = %s"(" ( %s"max-string" / %s"max-list" /
               %s"max-number"
                     / %s"max-fields" ) WS number %s")"
~~~

The bounded-counter declaration has two ownership modes. Omitted ownership
means `account`; omitted certification means `host-gate`. Options MUST NOT be
duplicated, and unknown options MUST be rejected. `floor`, `issuers`,
`increment`, and `decrement` are required. Account mode also requires
`initial-rights` and `transfer`, rejects `initial`, and requires `ceiling` and
`initial-headroom` either together or both absent. Initial headroom uses the
same opener as initial rights and a distinct keyword. `transfer-headroom`
requires a ceiling. Collective mode instead requires scalar `initial`, rejects
the account allocation and transfer options, and requires explicit
`quorum-budget` certification.

The host-gate profile associates increment, decrement and transfer acts with
account rights and optional ceiling headroom. Its resource verdict is separate
from protocol admission. Resource references use compiler-owned `:escrow-prev`
and `:escrow-deps` fields; they do not change `:caused-by`. Observations are
tagged ready, pending or fault values. Hard bounds depend on authenticated
accepted history and nonforking durable account issuance; an ordinary fold
does not establish those host guarantees.

`quorum-budget` selects the reference implementation's multi-parent resource
DAG runtime. A resolved committee has exactly `3f+1` distinct validator keys
and requires `2f+1` distinct authenticated votes; `faults` is a nonnegative
32-bit integer. For an explicit roster and omitted `faults`, `f` is
`floor((n-1)/3)`, and the roster MUST still satisfy `n = 3f+1`. An omitted
roster requires instance-bound committee resolution before use. Each committee
option may occur at most once. This declaration does not itself authenticate
votes or make a stateless fold a validator.

This document records the quorum declaration syntax and profile selection;
it does not standardize the validator journal, vote/certificate transport,
version-adoption protocol, or durable owner driver. Those remain a reference
implementation extension, described in its quorum runtime API. Implementations
without that runtime MUST reject execution of a quorum counter rather than
silently substitute host-gate certification. No cross-implementation quorum
wire interoperability is claimed by this media-type specification.

Ordinary data rules select accepted acts and apply deterministic reductions. `acts v` is the
set of accepted messages of performative `v` in the thread, minus those a
`domain` entry excludes; `current v k d` is the subset of `acts v` that no
accepted message of `v`, or of the delete performative `d`, names in its
`:replaces` field for the same key `k`. A reduction picks the message of
greatest content address, counts a set, tests membership of a value, collects
distinct values, or sums an integer field. These data reductions do not consult a clock or timestamp; content-address
order breaks ties. `progress` instead observes established protocol positions,
as defined below.

`:replaces` is a reserved keyword of type `list` that installation adds to the
shape of every performative a `latest-per-signer`, `values`, `values-per-key`,
`register-per-key`, or `observed-set` rule names as a writer, delete, or remove performative. An author
MUST NOT declare it, a rule MUST NOT read it, and a sending host fills it with
the content addresses of the current writes for the message's key. A message
that carries `:replaces` is thereby a replacement of those writes; a write no
accepted message names stays current whatever else is accepted.

For `latest-per-signer`, replacement is scoped to the authenticated signer:
only another accepted write of the same performative by the same signer can
supersede a cited write. A different signer naming that address cannot remove
it. The host supplies the signer's observed current write addresses in
`:replaces`; unseen concurrent writes remain current. The result is a map
from signer to the selected field of that signer's greatest-address current
write. Thus a causally replacing write supersedes its target even when its
address sorts lower; address order resolves only the remaining concurrent ties.

`(progress v)` returns the greatest established occurrence rank of `v` in the
expanded finite protocol, or zero if none is established. R7 MUST reject it
unless `v` occurs and its occurrences are totally ordered by causal
reachability. Ranks are 1 through N among occurrences of `v`; intervening
performatives do not add ranks. Positions are resolved from same-thread
accepted causal evidence, including the sealed cast when roles are present,
not from a caller-supplied number. Unresolved or invalid positions contribute
nothing. Unlike data selections, progress observes all accepted acts without
application-data `domain` filtering. Concurrent messages at rank N still yield
N, not a count of messages. Progress elects no branch and grants no mutual
exclusion for business actions.

A `domain` entry names a `string` keyword of a performative and a list-valued
field defined by a rule over the opener only. An accepted message whose keyword
value is not an element of that list is accepted but contributes to no field;
the filter does not affect `progress`. Admission does not consult folded
application state; it may still require accepted causal predecessors.

**R7 - State Well-Formedness.** When a dialect declares a `state` clause,
installation MUST verify that every performative a rule names is defined by the
dialect; that every keyword a rule reads is a required keyword of that
performative's shape, with a scalar type where the rule requires a scalar
(`integer`, or a contract proven integer-only, for `counter` and `sum`); that the dialect declares a protocol with
exactly one opener; that `histogram` and `sum` name a map-valued field defined
earlier in the clause; that no author-declared shape carries `:replaces`; and
that a delete performative carries exactly its key. A dialect failing any check
MUST NOT be installed. A `:state-bounds` clause MAY tighten, and MUST NOT
loosen, the default bounds on the strings (2048 octets), lists (64 elements),
numbers (10^12), and keyword count (32) of a state-bearing message; a message
exceeding a bound is a shape violation blamed on the sender.

Because every rule is a function of the accepted set, the state of an instance
is independent of arrival order and of duplicate delivery, and two participants
holding the same accepted messages compute the same state without coordination.
A dialect's identity, for the purpose of naming it by content address, is the
hash of its canonical form with the name slot empty, spelled `sha256-` followed
by the lowercase hexadecimal digest; a name beginning with `sha256-` claims to
be that self-address and installation MUST reject it unless it is.

# Multiparty Role Layer {#roles}

The role layer is an OPTIONAL extension of contracts. It is activated by a
`:roles` clause on a dialect, and it turns a whole-conversation protocol into
something each participant can verify locally.

Its purpose is *coordination-free endpoint projection* {{EPP}}: given a protocol
over roles, each participant derives the fragment visible to its own role and
checks only that fragment, and the resulting local verdicts agree with what a
verifier holding the entire conversation would conclude. There is no central
compiler and no ordered transport.

## Roles, Annotations, and Casts

A dialect declares its roles, each either **singleton** (one occupant) or
**indexed** (one or more occupants, written `(* name)`):

~~~
(:roles (auctioneer (* bidder)))
~~~

Each performative in the protocol is annotated with the role that sends it and
the role or roles that receive it. Both annotations MUST be present or both
absent; half an annotation is malformed:

~~~
(extend bid (amount) :from bidder :to auctioneer
  (tell @auctioneer (bid-amount :value amount) :domain auction))
~~~

A `:to` value may be a single role, a list of roles (multicast), or the empty
list `()` for a terminal act addressed to no other role.

Roles are bound to concrete agent keys, for one thread, by a **cast** nominated
at the thread's causal root using the `with-roles` wrapper:

~~~
(with-roles ((auctioneer @alice) (bidder @bob @carol))
  (signed "…"
    (open-auction "lot-7" :thread auction-9 :caused-by "begin")))
~~~

Every declared role MUST be bound exactly once. A singleton role takes exactly
one key; an indexed role takes one or more, and that membership is *sealed* —
occupant-dependent checks read it only from the cast, never inferring it from
traffic. The cast is tamper-evident because the root's content address anchors
every subsequent `:caused-by` link.

The wrapper MAY carry a dialect pin immediately after the bindings, committing
the thread to one exact dialect version:

~~~
(with-roles (…) :dialect "sha256:9f2c…" (signed "…" (…)))
~~~

If the pin differs from the content hash of the installed dialect, the thread
MUST be rejected.

## R6 - Multiparty Well-Formedness {#r6}

When a dialect's protocol carries role annotations, installation MUST verify all
six conditions below. Verification is O(|P|² · |R|) table lookups in the number
of performatives and roles.

1. **Role completeness**: every performative in the protocol carries both
   `:from` and `:to`. A performative carrying an annotation when the dialect
   declares no `:roles` is equally an error.
2. **Role declaredness**: every role named by `:from` or `:to` is declared in
   `:roles`.
3. **Chooser coherence**: the members of every `(any …)` choice share one sender
   role. Otherwise no single participant decides the branch and the choice is
   unimplementable.
4. **Causal locality**: for every performative, each of its endpoint roles is
   also an endpoint role of every predecessor type its `:caused-by` clause may
   name.
5. **Role reachability**: every declared role is an endpoint of some
   performative reachable from `begin`. A role that never acts or observes is a
   specification error.
6. **Single decider**: every choice point has exactly one deciding role.

Additionally, at thread open, per-occupant causal locality is checked against
the sealed cast: condition 4 must hold not merely role-wise but for each
occupant of each indexed role.

## Causal Locality and the Splicing Boundary {#splicing}

Condition 4 is the load-bearing one, and it deserves explanation because it
looks like a restriction that could be relaxed.

Role-local verification works by each role checking the predecessors of the
messages it holds. If a message cites a predecessor the verifying role never
received — because the projection erased an intervening message it is not party
to — the role cannot decide the verdict. It is not merely slow to decide: it can
*never* decide, because a content address is **type-opaque**. Holding a bare
`:caused-by` citation tells a role nothing about the cited message's
performative type, which is exactly what the verdict depends on. The verdict
stays `Unknown` permanently.

Causal locality is therefore not a convenience. It is the weakest condition
under which coordination-free role-local verification is sound: role-local
verification decides every message in a closed configuration exactly when every
cited predecessor is role-local.

The only sound remedy for a role that must verify a message whose predecessor it
does not hold is to deliver that predecessor in *type-tagged* form — either the
full message or a redacted envelope ({{envelopes}}) — which is what the
`(:causal-locality derive)` mode does: it derives, at install time, a
deterministic routing table sending redacted envelopes to the roles that need
them. An envelope recipient counts as an endpoint role for observability only;
payload `:to` sets are untouched.

The default mode is `reject`: a dialect that is not causally local MUST be
rejected at installation.

# Content Addressing, Attestation, and Evidence {#content-addressing}

## Canonical Form {#canonical-form}

CBCL uses the canonical list/octet-string framing of {{RFC9804}}, with the
following REQUIRED injective mapping of its typed atoms to octet strings.
All text is UTF-8; lengths count octets, including the type-tag octet.

| Atom | Octet string before length framing |
|---|---|
| symbol `s` | ASCII `S` followed by the bytes of `s` |
| keyword `:k` | ASCII `K` followed by the bytes of `k`, without the colon |
| string `s` | ASCII `Q` followed by the decoded bytes of `s` |
| integer `n` | ASCII `N` followed by minimal signed decimal ASCII of `n` |
| float `f` | ASCII `F` followed by the canonical float text specified below |
| decimal `d` | ASCII `D` followed by the normalized exact decimal text, without `m` |
| boolean true / false | ASCII `Bt` / `Bf` |

An atom is encoded as its octet-string length in decimal ASCII with no leading
zeros, a colon, and the octet string. Zero is spelled `0`; integers have no
leading plus or zeros, and negative zero normalizes to zero. A list is `(`,
the concatenated canonical encodings of its children, and `)`, with no spaces.
Floats serialize in fixed-point decimal notation with shortest round-tripping
digits for their binary64 value. Integral float values retain `.0`, and negative
zero normalizes to `0.0`; for example, `1e2` serializes as `100.0`.
Decimals remove leading integer zeroes and trailing fractional zeroes, discard an
empty fractional part, and normalize negative zero to zero. Their human-readable
serialization retains `m`; their canonical tagged octets omit that suffix.
Thus `001.2500m` serializes as `1.25m` and contributes octets `D1.25`.

Strings are not Unicode-normalized. A symbol and a string with the same text
MUST remain distinct. Integer, float, and decimal atoms also remain distinct
even when their mathematical values agree. For example:

| Input | Canonical octets, shown as ASCII |
|---|---|
| `alice` | `6:Salice` |
| `"alice"` | `6:Qalice` |
| `:x` | `2:Kx` |
| `-0` | `2:N0` |
| `1.25` | `5:F1.25` |
| `001.2500m` | `5:D1.25` |
| `#t` | `2:Bt` |
| `(tell "hi")` | `(5:Stell3:Qhi)` |

For messages, canonical field extraction operates on the structured message,
not on an arbitrary surface spelling. Multicast recipient sets and
multi-element `:caused-by` lists use ascending lexicographic order. In a simple
message, the reserved sender and thread fields are represented internally as
strings; causal references are represented as symbols, including a hash whose
wire representation is a string. This internal symbol is an encoding value,
not an instruction to parse a colon-bearing symbol from wire text.

## Content Addresses

A message's content address is the typed Merkle root defined below, rendered
as `sha256:` and exactly 64 lowercase hexadecimal characters. It is a string
on the wire. It is not the flat SHA-256 hash of the serialized message.

For a simple message, construct these six field values in order. `opt(x)` is
the one-element list `(x)` when present and the empty list `()` when absent.
`enc` is the typed canonical encoding above.

| i | Domain tag (a symbol) | Field value |
|---|---|---|
| 0 | `cbcl-taddr-v1/field-0-performative` | performative symbol |
| 1 | `cbcl-taddr-v1/field-1-from` | `opt(sender-string)` |
| 2 | `cbcl-taddr-v1/field-2-to` | sorted list of recipient symbols |
| 3 | `cbcl-taddr-v1/field-3-caused-by` | `opt(causal-reference)` |
| 4 | `cbcl-taddr-v1/field-4-thread` | `opt(thread-string)` |
| 5 | `cbcl-taddr-v1/field-5-payload` | list of content followed by remaining parameter expressions |

A causal reference is the symbol `begin`, a single hash symbol, or a sorted
list of hash symbols. A message with absent content uses the empty list as its
content value. The payload excludes reserved parameters lifted into the
structured header and retains the order of the remaining parameters.

For a non-simple message, field 0 is the symbol `meta`, `lang`, or its wrapper
name; fields 1 through 4 are empty lists; field 5 is a one-element list
containing its structured S-expression representation. Wrappers are therefore
committed as wrappers, not silently stripped before hashing.

Compute `l_i = SHA256(0x00 || enc((tag_i field_i)))`, using SHA-256
{{RFC6234}}. Let
`H(a,b) = SHA256(0x01 || a || b)`, where `a` and `b` are raw 32-octet digests,
not hexadecimal strings. The tree topology is exactly:

~~~
n0   = H(l0, l1)
n1   = H(l2, l3)
n2   = H(l4, l5)
m0   = H(n0, n1)
root = H(m0, n2)
~~~

There is no padding or leaf duplication. The domain tags, field types,
optional-field framing, and topology are part of this construction and MUST
NOT vary between implementations.

For the simple message `(tell "hi")`, the six field values are the symbol
`tell`, four empty lists, and the one-element list containing the string
`"hi"`, respectively. Its address is:

~~~
sha256:51ab48a6af30fb4e0023222c4bc90d788c0748a34faac9b7609eaaf844ad7a05
~~~

For example, opening its thread field (index 4, value `()`) has these two
sibling digests in bottom-up order:

~~~
right: 6f766fcaee1c8b1450bd7659ececdd2b9ab4991641d1cba42563e5046fc032e7
left:  3b0ebf787f1335404c34be9293401f6cc518cc6e511cd6396f1bf0b818808545
~~~

### Field Openings

An opening contains a field index, its typed field value, and a bottom-up list
of sibling digests with their left/right sides. Starting from the field's leaf
digest, a verifier hashes each sibling on its declared side and MUST obtain
the claimed root. The path length and sides MUST match that field's position
in the fixed tree: fields 0 through 3 have three siblings; fields 4 and 5 have
two. Out-of-range fields, malformed digests, and mismatching paths are rejected.

| Field | Sibling sides, bottom-up |
|---|---|
| 0 | right, right, right |
| 1 | left, right, right |
| 2 | right, left, right |
| 3 | left, left, right |
| 4 | right, left |
| 5 | left, left |

An opening proves a field value relative to a root; sender authentication
additionally requires an authenticated root and a verified binding to the
signing key. A type opening alone does not establish the sender, thread,
endpoints, or predecessor references. A role verifier MUST obtain authenticated
evidence for every field its checks use. Completion checks that need payload
grammaticality additionally require payload disclosure.

## Attestation Disciplines

CBCL is algorithm-agnostic for signing. Implementations MUST support at least
one signature algorithm and SHOULD support Ed25519 {{RFC8032}} as a baseline for
interoperability. Deployments MAY use ECDSA or post-quantum schemes without
protocol changes.

Three signing disciplines are defined. A message or envelope MUST carry an
explicit discipline marker, and verification MUST dispatch on that marker rather
than inferring it. A signature made under one discipline MUST NOT satisfy
verification under another; the mismatch is a typed rejection.

- **v1** signs the full canonical octets of the message. Verification requires
  the whole message, including payload.
- **v2** signs the canonical octets of a domain-tagged attestation naming the
  header fields only:

  ~~~
  (cbcl-attest-v2 <suite> <hash> <perf-name> <from-key> (<to-key>*)
                  <thread> [<caused-ref>])
  ~~~

  The attestation is never transmitted; both a full-message holder and an
  envelope holder reconstruct the identical preimage. Verification therefore
  never requires the payload.

  In that preimage, the domain tag, suite, hash, performative, sender and
  recipient keys are symbol atoms; the thread is a string atom. Sender and
  recipient keys use suite-explicit canonical spelling, and the recipient list
  is sorted by (suite, name). An absent causal reference contributes no element;
  a present one contributes the symbol `begin`, a hash symbol, or a sorted list
  of hash symbols. These internal symbols use the typed canonical encoder, not
  the wire lexer.

- **v3** signs a domain-tagged commitment to the typed Merkle root alone:

  ~~~
  (cbcl-attest-v3 <suite> <root>)
  ~~~

  Signature verification needs the suite, root, signature, and the sender's
  authenticated verification key. This authenticates the root commitment.
  Authenticating any disclosed field additionally requires its verified Merkle
  opening; a root signature alone does not authenticate accompanying header
  claims. The suite and root in the preimage are symbol atoms, using the typed
  canonical encoding above, regardless of their transport spelling.

### Suite-Typed Key Identity

Key material carries a signature-suite identifier as part of its identity, so
that an agent's Ed25519 identity and its post-quantum identity are distinct
principals. The canonical spelling is `@suite:name`; an omitted suite normalizes
to `ed25519`, so `@alice` and `@ed25519:alice` are one identity. Equality is over
the (suite, name) pair, never the surface spelling, so a spelling alias can
neither evade equivocation detection nor spuriously fail a comparison.

Because `:` is not a symbol character, a key identifier carrying an explicit
suite MUST be written as a string wherever it appears in a field position. See
{{divergences}}.

## Redacted Envelopes {#envelopes}

There are two payload-free evidence forms, with distinct verification rules.

- A **v2 redacted envelope** carries the content address, performative name,
  sender key, recipient set, thread, optional causal reference, and signature.
  The verifier reconstructs the v2 attestation from these exact fields and
  verifies its signature. No Merkle openings are needed because v2 directly
  signs the header claims.
- A **v3 opened envelope** carries the signature suite, typed root, root
  signature, and field openings. Full header disclosure opens fields 0 through
  4; field 5 remains sealed. A narrower disclosure MAY omit fields, but an
  omitted field is unavailable evidence, not an authenticated absence.

Both forms MUST identify their discipline explicitly. The verifier MUST NOT
interpret a v3 root signature as a v2 header signature. For v3, it MUST verify
the root signature and each supplied opening before using the disclosed field.
It MUST reject duplicate or malformed field disclosures and MUST NOT promote
an unproved header claim to authenticated evidence. A consumer MUST require
all fields needed by its particular safety check; missing fields cannot yield
`Valid` merely because the root signature verifies. Opening the sender field
does not replace checking that it matches the authenticated signing identity.

An envelope widens evidence without disclosing payload. It does disclose the
opened metadata: type, speaker, audience, thread, and causal position may
themselves be sensitive. Size is independent of the redacted payload, but
depends on the disclosed metadata and recipient/reference counts. Malformed
addresses, excessive recipient counts under the receiver's configured bound,
and fields outside the selected evidence form MUST be rejected, never repaired.
Completion checks requiring payload grammaticality MUST still require the full
message or the authenticated payload disclosure those checks consume.

These definitions specify the authenticated evidence objects and verification
requirements. The generic `envelope` wrapper in {{core-grammar}} is not itself
a wire grammar for v2 or v3 evidence. A transport profile carrying these objects
MUST specify its discipline marker, signature encoding, and field/opening
serialization; this document does not define that transport profile.

## Equivocation

Because a message's content address commits to its sender, thread, and causal
position, two distinct messages signed by the same key at the same causal
position are detectable by any participant holding both. Implementations SHOULD
retain the signed evidence of such a pair: it is a non-repudiable proof of
equivocation attributable to a specific key, and it is what makes accountability
possible in a system with no central authority.

# Core Semantics {#core-semantics}

## Agent State Model

A CBCL agent maintains:

- **Beliefs** (B): a set of propositions the agent holds as true
- **Dialects** (D): a set of installed dialect definitions, uniquely named
- **Conversations** (C): active dialogue contexts indexed by thread identifiers
- **Message store** (S): an append-only set of received messages and envelopes,
  indexed by content address and thread

## Message Processing {#lifecycle}

Upon receiving a CBCL message, an agent:

1. **Parse**: verify syntactic validity according to {{sexpr-grammar}} and
   {{core-grammar}}
2. **Classify**: determine the message category by head symbol
3. **Verify**: for meta define and teach messages, check the applicable safety
   invariants and the signature
4. **Expand**: for lang messages, expand the invocation under the dialect's
   resource context
5. **Check contracts**: where the dialect declares them, verify the causal
   protocol ({{verdicts}}) and shape constraints
6. **Update state**: modify beliefs, conversations, store, or dialect set
7. **Generate response**: optionally produce reply messages

The pipeline is total: every input produces either a well-typed result or a
well-typed error. It MUST be fail-closed — no path from receive to deliver may
skip a step, and no step may be partially applied.

## Performative Semantics

**tell(recipient, content, params)**:

- Add content to the agent's belief set
- If threaded, update conversation state
- Send content to recipient

**ask(recipient, query, params)**:

- Create expectation for reply
- Send query to recipient
- If threaded, associate with conversation

**reply(content, params)**:

- Satisfy pending expectation (if any)
- Communicate response to original asker

**meta(operation)**:

- For define: verify and install dialect
- For query: check dialect availability
- For teach: verify, then install a dialect definition received from a peer

Session management and control flow performatives follow conventional semantics
for initiation, termination, acknowledgment, error reporting, and cancellation.

## Threading and Conversation Context

Messages MAY include a `:thread` parameter to associate them with ongoing
conversations. Thread identifiers are arbitrary strings or symbols chosen by the
initiating agent. Implementations SHOULD maintain conversation state (message
history, expectations, context) per thread.

Where the role layer is in use, the thread identifier is the scope of a cast:
the role-to-key assignment holds for one thread and MUST NOT be carried across
threads.

## Error Handling {#error-handling}

When an agent cannot process a message, it SHOULD respond with an error message
indicating the reason:

~~~
(error @sender "Unknown dialect: advanced-planning"
       :in-reply-to msg-id-4567)
~~~

Common error conditions include:

- Syntactic invalidity
- Unknown dialect reference
- Resource limit violations
- Semantic constraint violations
- Contract violations

An implementation MUST distinguish a contract *violation* from an *undecided*
verdict ({{verdicts}}). Reporting `Unknown` as an error is incorrect: it
converts a transient absence of evidence into a permanent negative conclusion,
and in an unordered transport that will happen routinely.

# Conformance {#conformance}

An implementation conforming at **Core** level MUST:

- Recognize {{sexpr-grammar}} and {{core-grammar}} exactly, rejecting every
  input outside them
- Bound recognition as described in {{sexpr-grammar}}
- Implement the eight core performatives
- Verify R1 through R4 before installing any dialect
- Enforce declared resource bounds at expansion time

An implementation conforming at **Contracts** level MUST additionally implement
{{contracts}}, including R5 and the three-valued verdict.

An implementation conforming at **Roles** level MUST additionally implement
{{roles}}, including all six R6 conditions, and MUST implement the content
addressing of {{content-addressing}}.

An implementation at any level MUST use exactly one recognizer for the
S-expression layer. Where an implementation exposes S-expression parsing as
library API, that API MUST recognize the same language as the recognizer used on
the trust boundary. Two recognizers that disagree on any input constitute a
parser differential and defeat the guarantee this specification exists to
provide.

# Security Considerations {#security-considerations}

This section analyzes CBCL's security properties and compares them with
contemporary agent communication approaches. We first describe the threat model
that motivates CBCL's design ({{threat-model}}), then detail CBCL's specific
security mechanisms ({{langsec-security}} through {{privacy}}).

## Threat Model: The Unbounded Attack Surface Problem {#threat-model}

Contemporary agent communication protocols face a fundamental security
challenge: they use natural language or unrestricted JSON schemas as their
communication substrate, creating an unbounded attack surface that cannot be
secured through conventional means. CBCL's design directly addresses this threat
model.

The threat model assumes agents operating in open Byzantine environments where
(1) untrusted peers may send maliciously crafted messages designed to exploit
parser differentials, trigger resource exhaustion, or inject unintended
computation; (2) dialect definitions arrive from potentially adversarial sources
and constitute executable extensions to the receiver's behavior; and (3) no
central authority controls participant conduct or vocabulary evolution.

When agents communicate through natural language prompts (as in many LLM-based
systems) or unrestricted data structures (as in protocols like MCP), the space of
possible malicious inputs is infinite. No finite amount of input validation can
guarantee safety because:

- **Undecidability**: determining whether a natural language message will cause
  harmful behavior requires solving the halting problem. Static analysis cannot
  determine if arbitrary code execution, resource exhaustion, or security
  violations will occur.

- **Semantic Ambiguity**: natural language inherently carries multiple
  interpretations. An adversary can craft messages that appear benign to one
  component while triggering malicious behavior in another, creating parser
  differentials at the semantic level.

- **Unbounded Composition**: when agents can invoke arbitrary tools or execute
  arbitrary code in response to messages, the attack surface expands to include
  all possible compositions of system capabilities.

- **Context Injection**: without formal boundaries between message structure and
  content, attackers can inject commands that escape intended interpretations
  (prompt injection, command injection, and SQL injection are instances of this
  general problem).

### Concrete Vulnerabilities

Current agent protocols exhibit specific exploitable patterns:

- **Tool Poisoning**: malicious prompts embedded in tool descriptions influence
  agent behavior in subsequent interactions
- **Credential Theft**: unrestricted tool invocation enables access to sensitive
  configuration and authentication data
- **Command Injection**: natural language instructions can be crafted to execute
  arbitrary system commands
- **Resource Exhaustion**: unbounded message interpretation enables algorithmic
  complexity attacks

These are not implementation bugs that can be patched; they are consequences of
using undecidable input languages.

## Language-Theoretic Security {#langsec-security}

CBCL's design follows language-theoretic security (LangSec) principles
{{LANGSEC}}, which recognize that ambiguous input parsing creates the possibility
for "weird machines": unintended computational artifacts that attackers can
exploit to achieve behavior beyond the system's intended functionality. By
constraining all messages and dialect extensions to deterministic context-free
languages (DCFL), CBCL bounds this surface.

DCFL preservation is maintained through three mechanisms: (1) the base grammar is
LR(1) parseable by construction, indeed LL(1); (2) dialect extensions add only
finite pattern-template substitutions, and every dialect invocation to be
expanded appears inside a `lang` wrapper, so a deterministic pushdown automaton
dispatches to the appropriate subgrammar by consuming the `lang` tag and the
dialect name with no additional lookahead; and (3) resource bounds prevent
unbounded expansion. The extended language therefore remains in DCFL regardless
of how many dialects are installed, provided dialect names are unique per agent.

DCFL preservation extends to the role layer. Role annotations inhabit the
existing S-expression grammar and add no new surface forms. The trace languages
of causal protocols are regular, hence trace-DCFL, and projecting a protocol onto
a role adds no recognizer: role-local verification needs no machine class beyond
what the global protocol already has.

This preservation ensures:

- **Parser Equivalence**: all conformant implementations parse messages
  identically, eliminating parser differential attacks

- **Decidability**: message validity is decidable in polynomial time — O(n) for
  parsing, O(d²) for dialect verification in the dialect size d, and O(|P|² · |R|)
  table lookups for the role checks

- **Bounded Complexity**: resource exhaustion attacks are prevented through
  static limits declared in dialect definitions

- **Structural Isolation**: message structure is syntactically distinct from
  content, preventing injection attacks

This approach transforms an unbounded attack surface into a finite, analyzable
one. Every CBCL message can be checked for structural safety before processing, a
property impossible with natural language protocols.

### Scope of the Guarantee

The guarantee is precise and bounded, and overstating it would be its own
security problem. CBCL guarantees that the *message recognition and expansion
pipeline* admits no weird machines: the recognizer is deterministic and total,
and the template expander is not Turing-complete. Weird machines can still arise
in layers outside CBCL's scope — tool backends, agent action semantics, the
application logic that consumes a delivered message. CBCL bounds what agents can
*express* to each other; it does not bound what an agent does in response.

Similarly, CBCL constrains dialect *safety*, not dialect *quality*. Nothing
prevents propagation of redundant or poorly designed dialects. Agents can
uninstall unhelpful dialects, but the protocol defines no curation mechanism.

## Parser Uniqueness

Because parser equivalence is the property that eliminates differential attacks,
it is also the property most easily lost in implementation. The failure mode is
not usually a second *implementation* of the protocol, which is scrutinized; it
is a second recognizer inside a single implementation — a convenience parser for
tests and configuration, written permissively because its only job is to accept
the literals the author typed, then exported as library surface.

Implementations MUST have exactly one S-expression recognizer reachable from any
API. Test suites that model reception "over the wire" MUST exercise the
recognizer that actually guards the trust boundary, and implementations SHOULD
carry a differential test asserting agreement between every parsing entry point
they expose.

## Performative Shadowing {#shadowing}

This is the attack the scoping requirement of {{invocation-scope}} exists to
prevent, recorded because the rejection looks like pedantry until the attack is
stated.

Suppose an unqualified performative name were resolved by preferring the most
recently installed dialect that defines it. An agent has `alpha` installed,
defining `announce`, and `(announce "…")` expands to a `tell` addressed to
`@alpha-svc`. An adversary teaches the agent a dialect `beta` that also defines
`announce`, expanding to a `tell` addressed to `@beta-svc`. From that point the
*same* unscoped message expands to a different recipient. Nothing in the message
changed; nothing was overwritten; no verification failed.

The adversary's dialect need not violate any safety invariant. R1 through R3
constrain a dialect's *own* structure, not its relationship to dialects already
installed, and R3 protects only the eight core performatives. So a wholly
conformant dialect, accepted by every check in {{safety-invariants}}, silently
redirects traffic — and it redirects messages composed *before* it arrived,
which is what makes this a live-traffic attack rather than a configuration
error.

The defence is mandatory scoping ({{invocation-scope}}). Unqualified custom
names are rejected regardless of the installed dialect set. A scoped invocation
resolves only in its named dialect, so installing another dialect that defines
the same name cannot change its resolution.

Deployments SHOULD additionally:

1. **Scope every invocation.** A `(lang <dialect> …)` wrapper pins resolution to
   one dialect, so the expansion is a function of the message rather than of the
   receiver's dialect set, and remains correct even as that set grows. Where the
   thread also carries a dialect pin ({{roles}}), the binding is to one exact
   dialect *version* by content hash.
2. **Treat a shadowing installation as a trust event.** A dialect defining a
   performative name another installed dialect already defines SHOULD require
   explicit operator consent, and MUST at minimum be recorded in the audit log
   of {{provenance-and-trust}} — it is a bid to influence how existing messages
   are read.
3. **Record the resolved dialect** in any audit record of an expansion, so that
   which definition applied is reconstructible after the fact.

## Dialect Verification

Implementations MUST verify dialect definitions before installation to prevent:

- **Recursive Exploits**: dialect definitions that cause infinite expansion
- **Resource Exhaustion**: extensions that exceed declared resource bounds
- **Core Corruption**: attempts to redefine bootstrap performatives
- **Unimplementable Contracts**: protocols whose choices have no single decider,
  or which are not causally local, and which would therefore leave participants
  permanently undecided

The verification process MUST complete in bounded time and reject definitions
that fail constraint checks.

## Provenance and Trust

Dialect definitions represent executable extensions to an agent's behavior.
Ensuring their integrity and authenticity is critical for system security.

Implementations MUST:

- Verify dialect authorship through the author field
- Reject dialects that fail integrity checks
- Reject a dialect whose name collides with an installed dialect of a different
  content hash

Implementations SHOULD:

- Require cryptographic signatures for dialects from untrusted sources
- Verify signatures using the author's public key before installation
- Maintain a trust policy specifying which authors are authorized to define
  dialects
- Maintain an audit log of dialect installations and their sources
- Allow users to configure trust anchors and rejection policies

### Signature Verification

Dialect signatures MUST be computed over the canonical form of the dialect
S-expression as defined in {{RFC9804}} ({{canonical-form}}).

When a signed dialect is received, implementations SHOULD:

1. Extract the signature and dialect definition
2. Convert the dialect definition to canonical form
3. Verify the signature using the author's public key
4. Confirm the signing key matches the declared author
5. Check that the author is trusted per local policy
6. Only install if all checks pass

Unsigned dialects MAY be accepted from trusted local sources but SHOULD be
rejected when received over the network from unknown agents.

Authentication and authorization infrastructure (key distribution, certificate
authorities, web-of-trust, revocation) is expected to be provided by
deployment-specific infrastructure or higher-layer protocols.

## Content Validation

Agents SHOULD validate message content against expected schemas or types before
acting on information. The tell performative conveys information but does not
imply the receiver must accept it as true without verification.

## Denial of Service

Implementations MUST enforce resource limits specified in dialect definitions to
prevent:

- Excessive parsing depth
- Unbounded message expansion
- Computational complexity attacks

Messages exceeding configured limits MUST be rejected with appropriate error
responses.

The with-limits message wrapper allows senders to *request* specific resource
constraints for message processing:

- `:timeout` — wall-clock timeout in milliseconds for message evaluation
- `:max-depth` — maximum nesting depth for parsing and template expansion
  (system maximum: 64)
- `:max-expansion-size` — maximum cumulative size of template expansions in
  octets (system maximum: 8192)

Receivers MAY honor, reduce, or ignore these limits based on local policy. The
limits are hints for resource-constrained processing and provide no security
guarantee unless enforced by the receiver. A receiver MUST NOT raise its own
limits on a sender's request.

## Privacy Considerations {#privacy}

CBCL messages may contain sensitive information. Deployments requiring
confidentiality MUST use transport-layer security (for example TLS) or
message-layer encryption. This specification does not define encryption
mechanisms, which are expected to be provided by the deployment environment.

Two mechanisms in this document bear directly on privacy and are easily
misread as stronger than they are:

- **Redacted envelopes** ({{envelopes}}) disclose metadata, not nothing. Type,
  speaker, audience, thread, and causal position remain visible. In protocols
  where the *type* of a message is the sensitive fact — a `reject` where an
  `accept` was hoped for — an envelope leaks the outcome while withholding the
  payload.
- **Field openings** ({{content-addressing}}) are transferable. An opening
  verifies against the content address alone, so any holder can prove the opened
  field to any third party without the sender's participation. That is the point,
  and it is also the risk: a field opened to one recipient is effectively opened
  to everyone that recipient chooses to tell.

Deployments SHOULD treat the choice of which fields are leaves as a privacy
decision, not merely an efficiency one.

# IANA Considerations

## Media Type Registration

This section registers the application/cbcl media type according to {{RFC6838}}.

Type name: application

Subtype name: cbcl

Required parameters: None

Optional parameters:

- charset: character encoding. The only permitted value is UTF-8, which is also
  the default; CBCL input MUST be well-formed UTF-8 {{RFC3629}}.
- version: CBCL specification version (default: 1.0)

Encoding considerations: 8bit. CBCL messages are UTF-8 encoded text containing
S-expressions.

Security considerations: See {{security-considerations}} of this document.

Interoperability considerations: CBCL requires parsers supporting S-expression
syntax and conformance to the grammar in {{sexpr-grammar}} and
{{core-grammar}}. Implementations should verify dialect definitions before use.
Implementations at different conformance levels ({{conformance}}) interoperate
at the lower of the two levels.

Published specification: This document (draft-oconnor-cbcl).

Applications that use this media type: Multi-agent systems, autonomous agent
coordination platforms, IoT device communication, distributed AI systems.

Fragment identifier considerations: Not applicable. CBCL messages are atomic
communication units.

Additional information:

- Deprecated alias names: None
- Magic number(s): Messages begin with opening parenthesis "(" (0x28)
- File extension(s): .cbcl
- Macintosh file type code(s): TEXT

Person & email address to contact for further information:
Hugo O'Connor <hugo@anuna.io>

Intended usage: COMMON

Restrictions on usage: None

Author: Hugo O'Connor

Change controller: IETF (if published as RFC)

Provisional registration? No

# Implementation Considerations

## Parser Requirements

Conformant CBCL parsers MUST:

- Support S-expression syntax as defined in {{sexpr-grammar}}
- Enforce nesting depth limits (system maximum 64; see {{r2}})
- Reject malformed messages with clear error indications
- Complete parsing in bounded time
- Reject, never repair, malformed input. In particular an unrecognized escape
  sequence, an unterminated string, an out-of-range integer, an overflowing float,
  a malformed decimal, and a character
  outside the symbol alphabet are all errors.

## Dialect Registry

Implementations MAY maintain local or shared registries of known dialects for
discovery and reuse. Registry mechanisms are outside the scope of this
specification.

## Interoperability

Agents with different dialect sets can still communicate using core
performatives. Applications SHOULD design protocols that gracefully degrade when
specialized dialects are unavailable.

## Expressiveness Ceiling

The DCFL restriction means some patterns cannot be expressed in dialect
templates. Concrete examples of inexpressible transformations include recursive
data transformations over structures of arbitrary depth; cross-field references
where one parameter's value depends on another's; iteration or aggregation over
variable-length collections; and context-sensitive validation such as checking a
reply's thread identifier against an earlier message.

This ceiling is deliberate: it exists precisely to bound the attack surface.
CBCL restricts itself to *paraphrastic* extension — defining new constructs in
terms of existing ones — and excludes extensions that add orthogonal features or
alter interpretation rules. Agents requiring such patterns MUST implement them in
application logic outside the CBCL layer.

## Extensibility

While this specification defines core CBCL, future extensions may include:

- Additional core performatives (requires specification update)
- Standard dialect libraries for common domains
- Additional attestation disciplines
- Additional signature suites

# Examples {#examples}

## Basic Communication

Two agents exchanging information:

~~~
; Alice greets Bob
(hello @bob)

; Bob responds
(hello @alice)

; Alice asks a question
(ask @bob "What is the temperature?"
     :thread weather-chat-1)

; Bob replies
(reply @alice "23 degrees Celsius"
       :thread weather-chat-1)

; Alice acknowledges
(ok @bob :thread weather-chat-1)

; Conversation ends
(bye @bob)
~~~

Note: the examples above show the core message content. In practice these
messages would typically be wrapped in envelope structures carrying `:from`,
`:to`, and `:timestamp` metadata (see {{message-examples}}).

## Dialect Definition and Use

Defining a planning dialect:

~~~
(meta
  (define planning-dialect
    (cbcl)
    @ai-research-lab
    (:resource-requirements
      ((max-depth 20)
       (max-expansion-size 4096)
       (verification-time 1000)))

    (extend propose-action (action preconditions effects)
      (tell @planner
            (action-proposal
              :action action
              :requires preconditions
              :achieves effects)
            :domain planning))

    (extend query-plan (goal constraints)
      (ask @planner
           (plan-request
             :goal goal
             :constraints constraints)
           :domain planning))))
~~~

Using the dialect:

~~~
(lang planning-dialect
  (propose-action
    "move-box-A-to-shelf-3"
    ("box-A-location-known" "robot-arm-free")
    ("box-A-on-shelf-3")))
~~~

Expanded message:

~~~
(tell @planner
      (action-proposal
        :action "move-box-A-to-shelf-3"
        :requires ("box-A-location-known" "robot-arm-free")
        :achieves ("box-A-on-shelf-3"))
      :domain planning)
~~~

## A Contract-Bearing Dialect

A dialect declaring both a causal protocol and shape constraints:

~~~
(define escrow (cbcl) @escrow-wg
  (:resource-requirements
    ((max-depth 12)
     (max-expansion-size 2048)
     (verification-time 100)))

  (extend offer (deal-id terms)
    (tell @escrow-agent :deal deal-id :terms terms :domain escrow))
  (extend accept (deal-id)
    (tell @escrow-agent :deal deal-id :domain escrow))
  (extend decline (deal-id reason)
    (tell @escrow-agent
          :deal deal-id :reason reason :domain escrow))
  (extend settle (deal-id receipt)
    (tell @escrow-agent
          :deal deal-id :receipt receipt :domain escrow))

  (protocol
    (then begin offer)
    (then offer (any accept decline))
    (then accept settle))

  (shape offer   (require :deal string) (require :terms list))
  (shape accept  (require :deal string))
  (shape decline (require :deal string) (require :reason string))
  (shape settle  (require :deal string) (require :receipt list)))
~~~

A conforming trace, with each message citing its predecessor by content address:

~~~
(lang escrow (offer  "d-1" (100 "AUD") :caused-by "begin"))
(lang escrow (accept "d-1"             :caused-by "sha256:2b7f0e…"))
(lang escrow (settle "d-1" (receipt-7) :caused-by "sha256:91ac4d…"))
~~~

## A Role-Bearing Dialect

The same protocol with roles, so that each participant can verify locally:

~~~
(define escrow-roles (cbcl) @escrow-wg
  (:roles (buyer seller))
  (:causal-locality reject)
  (:resource-requirements
    ((max-depth 12)
     (max-expansion-size 2048)
     (verification-time 100)))

  (extend offer (deal-id terms) :from seller :to buyer
    (tell @buyer :deal deal-id :terms terms :domain escrow))
  (extend accept (deal-id) :from buyer :to seller
    (tell @seller :deal deal-id :domain escrow))
  (extend decline (deal-id reason) :from buyer :to seller
    (tell @seller :deal deal-id :reason reason :domain escrow))
  (extend settle (deal-id receipt) :from seller :to buyer
    (tell @buyer :deal deal-id :receipt receipt :domain escrow))

  (protocol
    (then begin offer)
    (then offer (any accept decline))
    (then accept settle)))
~~~

The choice `(any accept decline)` is chooser-coherent: both alternatives are
sent by `buyer`, so exactly one participant decides the branch. Every
performative's endpoints are `{buyer, seller}`, so the protocol is causally
local and both roles can verify every message they receive.

Opening a thread nominates the cast:

~~~
(with-roles ((buyer @alice) (seller @bob))
  (signed "…"
    (lang escrow-roles
      (offer "d-1" (100 "AUD") :thread deal-1 :caused-by "begin"))))
~~~

## Error Handling Example {#error-handling-example}

~~~
; Agent attempts to use an uninstalled dialect
(lang unknown-dialect
  (custom-action "data"))

; Recipient responds with error
(error @sender "Dialect not installed: unknown-dialect"
       :code "UNKNOWN_DIALECT"
       :in-reply-to msg-id-7890)
~~~

## Wrapped Messages

Signed and enveloped message:

~~~
(envelope
  :from @alice
  :to @bob
  :timestamp "2025-01-15T10:30:00Z"
  (signed "base64-signature-data-here"
    (tell @bob "Confidential information"
          :classification "restricted")))
~~~

Resource-limited message:

~~~
(with-limits :timeout 100 :max-depth 10 :max-expansion-size 4096
  (ask @reasoner
       "Compute optimal path given constraints"
       :constraints (very-complex-constraint-data)))
~~~

--- back

# Acknowledgments
{:numbered="false"}

This work is named after John McCarthy's visionary 1982 proposal for a "Common
Business Communication Language" and builds upon the foundational principles of
Lisp, particularly S-expressions and homoiconicity. The Lisp community's decades
of work on extensible, self-modifying systems provided the conceptual foundation
for CBCL's self-bootstrapping design.

This work builds on decades of research in agent communication languages,
particularly KQML and FIPA-ACL. The language-theoretic security principles are
inspired by the LangSec community and the work of Len Sassaman, Meredith L.
Patterson, and Dr Sergey Bratus. Matthew Flatt's work on Racket's #lang mechanism
demonstrated how language extensibility could be systematized. The role layer's
correspondence result follows the multiparty session type and endpoint projection
tradition. Thanks to the multi-agent systems research community for foundational
work in this area.

Thanks to the Science and Industry Endowment Fund and CSIRO's Data61 for
providing the initial spark in identifying the problem domain in critical
agricultural based use-cases. In particular thanks to Data61 for the opportunity
to be a part of the Software Systems research team and Dr Adnene Guabtni for
their support. Thanks to Ric Richardson and the team at the Office for Innovation
for championing this effort.

Thanks to Claire Barnes, David Factor, DZJ, Mat Mytka, Cath Thompson, Mark Pesce,
Ron Tucker, Prof. Ingo Weber, Dr Max Ott, Dr Mark Staples, Dr Ho-Pun Lam, Steve
Brodie, Alistair Reid, Geoff Huntley, Dr Quinghua Lu, Dr Liming Zhu, Dylan Scott,
Max von Hippel, Evan Miyazono, Max Kaye, Andrew Mugridge and Marc Ahrens for
helpful and informative discussions and encouragement over the past decade.
Special thanks to my family for their support.

# Implementation Status
{:numbered="false"}

Note to RFC Editor: Please remove this section before publication.

A reference implementation in Rust (cbcl-rs) is available as a Cargo workspace of
six crates:

| Crate | Role |
|---|---|
| cbcl-core | types, safety invariants R1-R6, role layer and projection, contracts, template expansion, content addressing, gossip, evaluator |
| cbcl-parser | S-expression, message, dialect, protocol and shape parsers; verified pipeline |
| cbcl-cli | command-line interface: parse, verify, agent REPL, gossip simulation |
| cbcl-wasm | WebAssembly bindings |
| cbcl-ffi | C FFI bindings |
| cbcl-erl | Erlang/BEAM NIF bindings |

The core crates are `no_std + alloc` compatible and use `#![forbid(unsafe_code)]`.
Effectful code lives in shell crates that import the core, never the reverse.

At the revision this draft was prepared against, the workspace comprises roughly
38,000 lines under `crates/*/src` including inline unit tests, and its suite runs
1,350 tests across 32 suites with none failing. Testing includes property-based
tests, differential tests against the Lean-extracted parser, libFuzzer targets on
the parser trust boundary, and mutation testing on critical-path modules.

A Lean 4 formalization accompanies it: 32 files, roughly 10,500 lines, 342
theorems and 664 declarations in total, with zero `sorry` gaps and no custom
axioms (only `propext`, `Classical.choice`, and `Quot.sound`). It covers parser
soundness and completeness, the R1-R3 checkers against their contracts, template
expansion termination, pipeline totality, deterministic-union DCFL preservation,
the causal-verification monotonicity results, the endpoint-projection
correspondence, the splicing analysis, a temporal bridge to conformant
executions, and DCFL preservation at the role layer. A verified parser binary is
extracted from the proofs.

The current Lean atom and parser models cover the integer numeric fragment.
The reference Rust implementation additionally recognizes float and decimal atoms;
those extensions do not yet carry equivalent Lean parser and canonicalization proofs.

Implementation repository: https://git.anuna.io/anuna-research/cbcl-rs

## Divergences from this specification {#divergences}
{:numbered="false"}

Note to RFC Editor: Please remove this section before publication.

The grammar above was derived from the reference implementation. Four points
where this document specifies behaviour the implementation does not yet exhibit
are recorded here so that neither is mistaken for the other. All four are
tracked in the implementation's issue tracker.

1. **Content addresses in field positions.** This document requires content
   addresses to be written as strings, because `:` is not in the symbol
   alphabet. The implementation follows this for `:caused-by`, but the redacted
   envelope form, the suite-typed key spelling `@suite:name`, and the
   `with-roles` `:dialect` pin each expect a bare symbol, which the recognizer
   on the trust boundary cannot produce. Those three forms are currently
   unreachable from the wire.

2. **A second recognizer.** The implementation exposes a second, more permissive
   S-expression recognizer as library API alongside the one used on the trust
   boundary. They disagree on the symbol alphabet, on comment handling, and on
   whether an unrecognized escape is rejected or preserved. {{conformance}}
   requires exactly one.

3. **Boolean delimiters.** {{tokenization}} requires a boolean literal to be
   followed by a delimiter. The implementation does not check this, so `#true`
   is accepted as `#t` followed by the symbol `rue` rather than rejected.

4. **Trailing elements.** The implementation silently ignores elements after the
   operation in a `meta` message, after the inner message in a `lang` message,
   and after the inner message in a wrapper. The grammar in {{core-grammar}}
   records this behaviour; implementations SHOULD reject rather than ignore.

Earlier revisions of this draft documented an `&key` marker for optional
keyword parameters in dialect parameter lists, and an `(or a b)` template form.
Neither exists: `&` is outside the symbol alphabet, so `&key` cannot be written
at all, and parameter binding is positional. {{expansion}} documents the
template language the implementation actually provides.

# Design Rationale
{:numbered="false"}

**Why S-Expressions?**

S-expressions provide:

- **Simplicity**: minimal syntax rules, easy to parse
- **Homoiconicity**: code and data have the same representation
- **Nested Structure**: natural for representing message hierarchies
- **Established**: decades of tooling and parser implementations
- **Unambiguous**: no grammar-level parser differential vulnerabilities

**Why DCFL Constraints?**

Deterministic context-free language constraints ensure:

- **Security**: eliminates "weird machine" attack surfaces in the recognition
  and expansion pipeline
- **Decidability**: parsing and verification complete in polynomial time
- **Interoperability**: all implementations parse identically
- **Practicality**: sufficient expressiveness for agent coordination

DCFL is the minimal class supporting nested structure with parser equivalence.
Regular languages cannot express the nesting that envelopes and dialect scoping
require. General context-free grammars admit ambiguity, and therefore parser
differentials. Context-sensitive membership is PSPACE-complete and Type 0 is
undecidable; both exceed the recognizer complexity LangSec considers tractable
for full input validation.

**Why Homoiconic Dialects?**

Making dialect definitions themselves CBCL messages enables:

- **No Separate Meta-Language**: a single coherent framework, and no second
  attack surface
- **Transmissibility**: dialects spread like any other message
- **Peer-to-Peer**: no centralized registry required
- **Self-Describing**: definitions carry their own semantics

**Why Explicit Recipients in Every Message?**

All CBCL messages may include an explicit recipient field (not just in transport
headers) to enable:

- **Connection Multiplexing**: multiple agents can share a single transport
  connection, with routing based on message content
- **Transport Independence**: messages are self-describing and can be forwarded
  through intermediaries without transport-layer inspection
- **Store-and-Forward**: message queues and relays can route based on CBCL
  message content alone
- **Audit Integrity**: the complete message record includes addressing
  information independent of transport logs

This design parallels email (RFC 822 headers vs. SMTP envelope) and HTTP/2
multiplexing.

**Why a Three-Valued Verdict?**

A two-valued verdict would force a receiver that has not yet seen a message's
predecessor to answer "invalid", which in any unordered transport is wrong far
more often than it is right. Making "undecided" a first-class verdict lets a
receiver defer acceptance until the required evidence is available. Replicas
with the same authenticated evidence and fixed context compute the same
verdict; the operational tables and limits on monotonicity claims are stated
in {{verdicts}}. Implementations must handle a verdict that may never resolve,
which is precisely the situation {{splicing}} analyses.

**Separation of Concerns**

This specification intentionally omits:

- **Authentication**: use TLS, PKI, or application-specific mechanisms
- **Authorization**: policy decisions belong to agent implementations
- **Transport**: CBCL is transport-agnostic (HTTP, WebSocket, MQTT, etc.)
- **Encryption**: use transport-layer or message-layer encryption

This separation allows CBCL to serve as a versatile content type across diverse
deployment scenarios.
