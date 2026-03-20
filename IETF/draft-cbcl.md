---
title: "CBCL: Safe Self-Extending Agent Communication"
abbrev: "CBCL"
category: info
docname: draft-cbcl-00
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
  RFC6838:
  RFC5234:
  RFC8032:
  RFC9804:

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

--- abstract

This document specifies CBCL (CBCL-Based Communication Language), a self-extensible agent communication language designed for autonomous multi-agent systems. CBCL provides a minimal core vocabulary of performatives and a formal mechanism for agents to define, exchange, and adopt domain-specific dialect extensions at runtime without requiring centralized coordination. The language uses S-expression syntax and enforces bounded parsing complexity through static resource limits to ensure security and interoperability. This specification defines CBCL message syntax, core semantics, dialect extension mechanisms, and registers the application/cbcl media type.

--- middle

# Introduction

Agent communication languages (ACLs) enable autonomous software agents to coordinate, negotiate, and exchange information in multi-agent systems. Existing ACLs such as KQML {{KQML}} and FIPA-ACL {{FIPA-ACL}} provide fixed vocabularies of performatives (communicative acts like inform, request, query) that must be understood by all participants. While these languages have proven useful in controlled environments, they face significant challenges in open, dynamic systems where:

- Devices join and leave frequently (IoT swarms, edge computing)
- Domain vocabularies evolve rapidly (supply chains, emergency response)
- No single authority controls all participants (federated systems, cross-organizational coordination)
- Agents need specialized performatives for domain-specific tasks

The fundamental problem is the **static vocabulary limitation**: when agents need new communicative capabilities, they must wait for out-of-band standardization processes or rely on lowest-common-denominator abstractions that reduce expressiveness.

Recent work has attempted to address this limitation by using natural language or unrestricted schemas for agent communication, enabling greater flexibility. However, this approach introduces a more severe problem: an **unbounded attack surface**. When agents communicate through natural language prompts or unrestricted data structures, determining whether a message is safe requires solving undecidable problems. No amount of input validation can guarantee security when the input language itself has unbounded computational complexity. This fundamental tension between extensibility and security motivates CBCL's design.

This challenge was recognized early by McCarthy {{MCCARTHY-CBCL}}, who proposed a "Common Business Communication Language" that would be "open ended so that as programs improve, programs that can at first only order by stock numbers can later be programmed to inquire about specifications and prices." McCarthy's vision emphasized that effective agent communication requires both a stable foundation and mechanisms for evolutionary growth.

Named in honor of McCarthy's pioneering work, CBCL (CBCL-Based Communication Language) aspires to this vision by making the language self-extensible. Agents can define new domain-specific "dialects" (sets of specialized performatives) and share them with peers as first-class CBCL messages. Because dialect definitions are themselves valid CBCL messages with the same S-expression syntax, an agent can transmit a dialect definition using the same message-passing mechanism it uses for ordinary communication, eliminating the need for a separate meta-language or trusted intermediaries. This approach draws inspiration from Racket's #lang mechanism {{RACKET-LANG}}, which demonstrates how language extensibility can be systematized through first-class language definitions, while adapting these principles for distributed, multi-agent environments.

This specification focuses on CBCL as a content type for agent communication, defining message syntax and core semantics while leaving authentication, authorization, and transport-layer security to other specifications.

## Terminology

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in BCP 14 {{RFC2119}} when, and only when, they appear in all capitals, as shown here.

Additionally, this document uses the following terms:

**Agent**: An autonomous software entity that can send and receive CBCL messages.

**Performative**: A communicative act that an agent can perform (e.g., tell, ask, reply).

**Dialect**: A named collection of performative definitions that extend the core CBCL vocabulary.

**Homoiconicity**: The property that code and data share the same representation, enabling programs to manipulate their own structure.

# CBCL Message Format

## Overview

CBCL messages use S-expression (symbolic expression) syntax, a notation originating from Lisp that represents nested list structures. This choice provides:

- Simple, unambiguous parsing
- Natural representation of nested message structures
- Human readability for debugging and logging
- Established parser implementations across languages

All CBCL messages are S-expressions, but not all S-expressions are valid CBCL messages. Valid messages must conform to the grammar specified in this section and satisfy semantic constraints defined in {{core-semantics}}.

## Syntax Notation

The grammar in this specification uses Augmented Backus-Naur Form (ABNF) as defined in {{RFC5234}}.

## Core Grammar {#core-grammar}

The following grammar uses core rules from {{RFC5234}}:

~~~abnf
SP           = %x20                    ; space
HTAB         = %x09                    ; horizontal tab
WSP          = SP / HTAB               ; whitespace
ALPHA        = %x41-5A / %x61-7A       ; A-Z / a-z
DIGIT        = %x30-39                 ; 0-9
DQUOTE       = %x22                    ; " (double quote)

; CBCL Message Grammar

cbcl-message = simple-message / meta-message /
               lang-message / wrapped-message

; Simple messages use core performatives
simple-message = "(" performative SP recipient
                 [SP content] *(SP parameter) ")"

performative = "tell" / "ask" / "reply" /
               "hello" / "bye" /
               "ok" / "error" / "cancel"

recipient = agent-id

content = string / s-expr

parameter = keyword SP value

; Meta messages for dialect operations
meta-message = "(" "meta" SP meta-operation ")"

meta-operation = define-dialect / query-dialect /
                 teach-dialect

define-dialect = "(" "define" SP dialect-name
                 *(SP dialect-clause) ")"

query-dialect = "(" "query" SP "(" capability-query ")" ")"

teach-dialect = "(" "teach" SP recipient SP dialect-def ")"

capability-query = "speak?" SP dialect-name

; Language-scoped messages
lang-message = "(" "lang" SP dialect-name SP inner-message ")"

inner-message = cbcl-message

; Message wrappers
wrapped-message = envelope-message / signed-message /
                  limited-message

envelope-message = "(" "envelope" *(SP envelope-param)
                   SP cbcl-message ")"

envelope-param = ":from" SP agent-id /
                 ":to" SP agent-id /
                 ":timestamp" SP timestamp

signed-message = "(" "signed" SP signature SP
                 cbcl-message ")"

limited-message = "(" "with-limits" *(SP limit-param)
                  SP cbcl-message ")"

limit-param = ":timeout" SP integer /
              ":max-depth" SP integer /
              ":max-expansion-size" SP integer

; Dialect definition structure
dialect-clause = extends-clause / extend-clause /
                 resource-clause / author-clause /
                 examples-clause / signature-clause /
                 hash-clause / protocol-clause

extends-clause = ":extends" SP dialect-name

extend-clause = "(" "extend" SP new-perf-name
                SP param-list SP expansion ")"

resource-clause = ":resources" SP resource-spec

author-clause = ":author" SP agent-id

examples-clause = ":examples" 1*(SP s-expr)

signature-clause = ":signature" SP string

hash-clause = ":hash" SP string

protocol-clause = ":protocol" SP string

; Basic types
agent-id = "@" identifier

dialect-name = identifier

new-perf-name = identifier

keyword = ":" identifier

identifier = 1*( ALPHA / DIGIT / "-" / "_" )

string = DQUOTE *string-char DQUOTE

string-char = %x20-21 / %x23-5B / %x5D-7E /  ; printable ASCII
              %x5C escaped /                  ; escaped characters
              utf8-2 / utf8-3 / utf8-4        ; UTF-8 sequences

escaped = %x22 / %x5C / %x6E / %x72 / %x74  ; \" \\ \n \r \t

utf8-2 = %xC2-DF utf8-tail
utf8-3 = %xE0-EF 1*2utf8-tail
utf8-4 = %xF0-F4 1*3utf8-tail
utf8-tail = %x80-BF

integer = ["-"] 1*DIGIT

decimal = ["-"] 1*DIGIT "." 1*DIGIT

number = decimal / integer

boolean = "#t" / "#f"

symbol = identifier / quoted-symbol

quoted-symbol = "'" identifier

timestamp = date-time  ; As defined in RFC 3339, Section 5.6

signature = base64-string

s-expr = "(" *( s-expr / atom ) ")"

atom = identifier / string / number / boolean / symbol

value = atom / s-expr

; Parameter list for dialect extension definitions
param-list = "(" *( formal-param ) ")"

formal-param = identifier /
               "&key" SP identifier /
               "&optional" SP identifier /
               "&rest" SP identifier

; Template expansion language
expansion = template-expr

template-expr = literal-template / substitution-template /
                conditional-template / sequence-template

literal-template = cbcl-message

substitution-template = param-ref / tagged-substitution

param-ref = identifier

tagged-substitution = keyword SP param-ref

; Bounded conditional (no recursion)
conditional-template = "(" "cond" 1*( condition-clause )
                       [default-clause] ")"

condition-clause = "(" condition SP template-expr ")"

default-clause = "(" "else" SP template-expr ")"

condition = equality-test / membership-test / type-test

equality-test = "(" "=" SP param-ref SP value ")"

membership-test = "(" "member" SP param-ref SP value-list ")"

type-test = "(" "type?" SP param-ref SP type-name ")"

sequence-template = "(" 1*template-expr ")"

value-list = "(" *value ")"

type-name = "string" / "number" / "boolean" / "symbol" /
            "list" / "agent"

; Comment syntax (whitespace-equivalent)
comment = ";" *(%x20-7E) CRLF

resource-spec = "(" *(resource-limit) ")"

resource-limit = ":max-depth" SP integer /
                 ":max-expansion-size" SP integer /
                 ":max-verify-time" SP integer

base64-string = 1*( ALPHA / DIGIT / "+" / "/" / "=" )
~~~

## Core Performatives

CBCL defines eight core performatives that constitute the minimal bootstrap vocabulary. These performatives MUST be understood by all conformant CBCL implementations:

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

Envelope with metadata:

~~~
(envelope :from @alice
          :to @bob
          :timestamp "2025-01-15T14:30:00Z"
  (tell @bob "Hello"))
~~~

# Dialect Extension Mechanism {#dialect-extension}

## Overview

Dialects enable agents to extend CBCL's vocabulary with domain-specific performatives while maintaining parsing determinism and security properties. A dialect definition is itself a CBCL message that can be transmitted, verified, and installed by receiving agents.

## Dialect Definition

A dialect definition specifies:

- A unique dialect name
- The dialect it extends (typically "cbcl" for core extensions)
- Author identifier for provenance tracking
- A set of performative definitions (extend clauses)
- Resource constraints for verification and execution
- Optional examples illustrating intended expansion semantics
- Optional signature and hash for integrity verification

Example dialect definition:

~~~
(meta
  (define logistics-dialect
    :extends cbcl
    :author @logistics-consortium
    :resources (:max-depth 16
                :max-expansion-size 4096
                :max-verify-time 1000)

    (extend track-shipment
            (package-id &key route priority)
      (tell @tracking-service
            (shipment-request
              :package package-id
              :route route
              :priority (or priority "normal"))
            :domain logistics))

    (extend confirm-delivery
            (package-id recipient timestamp)
      (tell recipient
            (delivery-confirmed
              :package package-id
              :time timestamp)
            :domain logistics))

    :examples
      (track-shipment "PKG-42" :route "A->B")
      (tell @tracking-service
        (shipment-request
          :package "PKG-42"
          :route "A->B"
          :priority "normal")
        :domain logistics)))
~~~

The optional `:examples` clause carries semantic meaning: each input/output pair illustrates what the dialect author intends a performative to do in a concrete scenario. Examples serve as the primary mechanism for communicating intended semantics between agents. A receiving agent can evaluate the examples against its own expander to verify mechanical agreement before claiming dialect support.

## Dialect Verification Constraints

To ensure safety and maintain DCFL parsing bounds, dialect definitions MUST satisfy these constraints:

**R1 - Declarative Only**: Extension definitions MUST use only pattern-template transformations. Recursion, iteration, and reflection are prohibited.

**R2 - Resource Bounds**: Dialect definitions MUST declare resource limits:

- :max-depth - Maximum nesting depth of expanded messages (integer, RECOMMENDED: ≤ 32 levels)
- :max-expansion-size - Maximum size of expanded message (integer, measured in characters, RECOMMENDED: ≤ 8192)
- :max-verify-time - Maximum time to verify dialect definition (integer, measured in milliseconds, RECOMMENDED: ≤ 5000)

**R3 - Core Preservation**: Dialects MUST NOT redefine core performatives (tell, ask, reply, hello, bye, ok, error, cancel).

**R4 - Provenance and Integrity**: Dialect definitions MUST include author identification. When transmitted between agents, dialect definitions SHOULD be cryptographically signed to ensure:
- **Authenticity**: The dialect came from the claimed author
- **Integrity**: The definition has not been modified in transit
- **Non-repudiation**: The author cannot deny creating the dialect

Implementations MUST verify these constraints before installing a dialect. Implementations SHOULD verify cryptographic signatures when present and reject unsigned dialects from untrusted sources.

### Expansion Semantics

Dialect performatives expand through pattern-template substitution. An extend clause defines:

1. A new performative name
2. A parameter list specifying positional and keyword arguments
3. A template expression that becomes the expansion

Parameter lists use the following syntax:

- Simple identifiers bind positional arguments (e.g., package-id)
- &key introduces keyword arguments (e.g., &key route priority)
- All parameters before &key are required positional parameters
- All parameters after &key are optional keyword parameters

Template expansion follows these rules:

- Identifiers matching parameter names are replaced with argument values
- Keyword parameters not provided by the caller evaluate to nil (empty list)
- The (or expr1 expr2) form evaluates to expr1 if non-nil, else expr2
- All other expressions are preserved literally
- Expansion is non-recursive: expanded messages are not re-expanded

Example:

Given the definition:
~~~
(extend track-shipment
        (package-id &key route priority)
  (tell @tracking-service
        (shipment-request
          :package package-id
          :route route
          :priority (or priority "normal"))
        :domain logistics))
~~~

The call:
~~~
(track-shipment "PKG-12345" :route "A->B" :priority "urgent")
~~~

Expands to:
~~~
(tell @tracking-service
      (shipment-request
        :package "PKG-12345"
        :route "A->B"
        :priority "urgent")
      :domain logistics)
~~~

The call:
~~~
(track-shipment "PKG-12345" :route "A->B")
~~~

Expands to:
~~~
(tell @tracking-service
      (shipment-request
        :package "PKG-12345"
        :route "A->B"
        :priority "normal")
      :domain logistics)
~~~

## Dialect Usage

Once installed, dialect performatives can be used within lang-scoped messages:

~~~
(lang logistics-dialect
  (track-shipment "PKG-12345"
                  :route "warehouse-A->depot-B"
                  :priority "urgent"))
~~~

This expands to:

~~~
(tell @tracking-service
      (shipment-request
        :package "PKG-12345"
        :route "warehouse-A->depot-B"
        :priority "urgent")
      :domain logistics)
~~~

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

Agents can share dialect definitions with peers. When transmitting to untrusted agents, dialect definitions SHOULD be cryptographically signed:

~~~
(meta (teach @bob
  (signed "base64-encoded-signature"
    (define logistics-dialect
      :extends cbcl
      :author @logistics-consortium
      :resources (:max-depth 16
                  :max-expansion-size 4096
                  :max-verify-time 1000)
      ; ... performative definitions ...
    ))))
~~~

The receiving agent MUST:
1. Verify the cryptographic signature (if present)
2. Check that the author matches the signing key
3. Verify dialect constraints (R1-R3)
4. Apply local trust policies

The receiving agent MAY reject the dialect based on:
- Invalid or missing signature
- Untrusted author
- Resource constraint violations
- Local security policy

# Core Semantics {#core-semantics}

## Agent State Model

A CBCL agent maintains:

- **Beliefs** (B): A set of propositions the agent holds as true
- **Dialects** (D): A set of installed dialect definitions
- **Conversations** (C): Active dialogue contexts indexed by thread identifiers

## Message Processing

Upon receiving a CBCL message, an agent:

1. **Parse**: Verify syntactic validity according to the grammar in {{core-grammar}}
2. **Verify**: Check semantic constraints (e.g., dialect exists for lang messages)
3. **Interpret**: Execute performative semantics
4. **Update State**: Modify beliefs, conversations, or dialect set as appropriate
5. **Generate Response**: Optionally produce reply messages

## Performative Semantics

**tell(recipient, content, params)**:
- Add content to agent's belief set
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
- For teach: transmit dialect definition

Session management and control flow performatives follow conventional semantics for initiation, termination, acknowledgment, error reporting, and cancellation.

## Threading and Conversation Context

Messages MAY include a :thread parameter to associate them with ongoing conversations. Thread identifiers are arbitrary strings chosen by the initiating agent. Implementations SHOULD maintain conversation state (message history, expectations, context) per thread.

## Error Handling

When an agent cannot process a message, it SHOULD respond with an error message indicating the reason:

~~~
(error @sender "Unknown dialect: advanced-planning"
       :in-reply-to msg-id-4567)
~~~

Common error conditions include:
- Syntactic invalidity
- Unknown dialect reference
- Resource limit violations
- Semantic constraint violations

# Security Considerations {#security-considerations}

This section analyzes CBCL's security properties and compares them with contemporary agent communication approaches. We first describe the threat model that motivates CBCL's design ({{threat-model}}), then detail CBCL's specific security mechanisms ({{langsec-security}} through {{privacy}}).

## Threat Model: The Unbounded Attack Surface Problem {#threat-model}

Contemporary agent communication protocols face a fundamental security challenge: they use natural language or unrestricted JSON schemas as their communication substrate, creating an unbounded attack surface that cannot be secured through conventional means. CBCL's design directly addresses this threat model.

When agents communicate through natural language prompts (as in many LLM-based systems) or unrestricted data structures (as in protocols like MCP), the space of possible malicious inputs is infinite. No finite amount of input validation can guarantee safety because:

- **Undecidability**: Determining whether a natural language message will cause harmful behavior requires solving the halting problem. Static analysis cannot determine if arbitrary code execution, resource exhaustion, or security violations will occur.

- **Semantic Ambiguity**: Natural language inherently carries multiple interpretations. An adversary can craft messages that appear benign to one component while triggering malicious behavior in another, creating parser differentials at the semantic level.

- **Unbounded Composition**: When agents can invoke arbitrary tools or execute arbitrary code in response to messages, the attack surface expands to include all possible compositions of system capabilities. Each new tool or capability creates new attack vectors.

- **Context Injection**: Without formal boundaries between message structure and content, attackers can inject commands that escape intended interpretations (prompt injection, command injection, SQL injection are instances of this general problem).

### Concrete Vulnerabilities

Current agent protocols exhibit specific exploitable patterns:

- **Tool Poisoning**: Malicious prompts embedded in tool descriptions influence agent behavior in subsequent interactions
- **Credential Theft**: Unrestricted tool invocation enables access to sensitive configuration and authentication data
- **Command Injection**: Natural language instructions can be crafted to execute arbitrary system commands
- **Resource Exhaustion**: Unbounded message interpretation enables algorithmic complexity attacks

These are not implementation bugs that can be patched; they are fundamental consequences of using undecidable input languages.

## Language-Theoretic Security {#langsec-security}

CBCL's design follows language-theoretic security (LangSec) principles {{LANGSEC}}, which recognize that ambiguous input parsing creates the possibility for "weird machines": unintended computational artifacts that attackers can exploit to achieve behavior beyond the system's intended functionality. By constraining all messages and dialect extensions to deterministic context-free languages (DCFL), CBCL ensures:

DCFL preservation is maintained through three mechanisms: (1) the base grammar is LR(1) parseable by construction, (2) dialect extensions add only finite pattern-template substitutions that map to existing DCFL productions, and (3) resource bounds prevent unbounded expansion. Since DCFL is closed under finite union with regular languages and substitution of DCFL languages, the extended language remains in DCFL regardless of how many dialects are installed. A formal proof of this property is provided in the companion academic paper.

This DCFL preservation ensures:

- **Parser Equivalence**: All conformant implementations parse messages identically, eliminating parser differential attacks

- **Decidability**: Message validity is decidable in polynomial time (O(n) for parsing, O(d²) for dialect verification where d is dialect size)

- **Bounded Complexity**: Resource exhaustion attacks are prevented through static limits declared in dialect definitions

- **Structural Isolation**: Message structure is syntactically distinct from content, preventing injection attacks

This approach transforms an unbounded attack surface into a finite, analyzable one. Every CBCL message can be verified for safety before processing, a property impossible with natural language protocols.

## Dialect Verification

Implementations MUST verify dialect definitions before installation to prevent:

- **Recursive Exploits**: Dialect definitions that cause infinite expansion
- **Resource Exhaustion**: Extensions that exceed declared resource bounds
- **Core Corruption**: Attempts to redefine bootstrap performatives

The verification process SHOULD complete in bounded time (recommended: < 5 seconds) and reject definitions that fail constraint checks.

## Provenance and Trust

Dialect definitions represent executable code that extends an agent's behavior. Ensuring their integrity and authenticity is critical for system security.

Implementations MUST:

- Verify dialect authorship through the :author field
- Reject dialects that fail integrity checks

Implementations SHOULD:

- Require cryptographic signatures for dialects from untrusted sources
- Verify signatures using the author's public key before installation
- Maintain a trust policy specifying which authors are authorized to define dialects
- Compute and verify content hashes to detect tampering
- Maintain an audit log of dialect installations and their sources
- Allow users to configure trust anchors and rejection policies

### Signature Scheme

CBCL is algorithm-agnostic for dialect signing. The reference implementation defines an abstract Signer interface (trait) that accepts arbitrary signature algorithms. Dialect definitions identify the signing algorithm via metadata, allowing deployments to use Ed25519 {{RFC8032}}, ECDSA, or post-quantum schemes without protocol changes.

Implementations MUST support at least one signature algorithm and SHOULD support Ed25519 as a baseline for interoperability. Implementations MAY support additional signature algorithms as needed for specific deployment environments.

### Signature Verification

Dialect signatures MUST be computed over the canonical form of the dialect S-expression as defined in {{RFC9804}}. The canonical form ensures that semantically identical dialects produce identical signatures regardless of formatting variations (whitespace, comments, etc.).

The signature value in the signed wrapper is a base64-encoded byte string whose length depends on the algorithm used.

When a signed dialect is received, implementations SHOULD:

1. Extract the signature and dialect definition
2. Convert the dialect definition to canonical form per {{RFC9804}}
3. Verify the signature using the author's public key
4. Confirm the signing key matches the declared author
5. Check that the author is trusted per local policy
6. Only install if all checks pass

The canonical form represents each string in verbatim mode and each list with no whitespace separating elements, ensuring a unique byte representation for signature verification.

Unsigned dialects MAY be accepted from trusted local sources but SHOULD be rejected when received over the network from unknown agents.

Authentication and authorization mechanisms (key distribution, certificate authorities, web-of-trust) are expected to be provided by deployment-specific infrastructure or higher-layer protocols.

## Content Validation

Agents SHOULD validate message content against expected schemas or types before acting on information. The tell performative conveys information but does not imply the receiver must accept it as true without verification.

## Denial of Service

Implementations MUST enforce resource limits specified in dialect definitions to prevent:

- Excessive parsing depth
- Unbounded message expansion
- Computational complexity attacks

Messages exceeding configured limits SHOULD be rejected with appropriate error responses.

The with-limits message wrapper allows senders to request specific resource constraints for message processing:

- :timeout - Wall-clock timeout in milliseconds for message evaluation
- :max-depth - Maximum nesting depth for parsing and template expansion (maximum 64 levels)
- :max-expansion-size - Maximum cumulative size of template expansions in characters

Receivers MAY choose to honor, reduce, or ignore these limits based on local policy. The limits serve as hints for resource-constrained processing and provide no security guarantee unless enforced by the receiver.

## Privacy Considerations {#privacy}

CBCL messages may contain sensitive information. Deployments requiring confidentiality MUST use transport-layer security (e.g., TLS) or message-layer encryption (e.g., via wrapped-message constructs). This specification does not define encryption mechanisms, which are expected to be provided by the deployment environment.

# IANA Considerations

## Media Type Registration

This section registers the application/cbcl media type according to {{RFC6838}}.

Type name: application

Subtype name: cbcl

Required parameters: None

Optional parameters:

- charset: Character encoding (default: UTF-8)
- version: CBCL specification version (default: 1.0)

Encoding considerations: 8bit or binary. CBCL messages are UTF-8 encoded text containing S-expressions.

Security considerations: See {{security-considerations}} of this document.

Interoperability considerations: CBCL requires parsers supporting S-expression syntax and conformance to DCFL constraints. Implementations should verify dialect definitions before use.

Published specification: This document (draft-cbcl).

Applications that use this media type: Multi-agent systems, autonomous agent coordination platforms, IoT device communication, distributed AI systems.

Fragment identifier considerations: Not applicable. CBCL messages are atomic communication units.

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

- Support S-expression syntax as defined in {{core-grammar}}
- Enforce nesting depth limits (RECOMMENDED: max 32 levels)
- Reject malformed messages with clear error indications
- Complete parsing in bounded time

## Dialect Registry

Implementations MAY maintain local or shared registries of known dialects for discovery and reuse. Registry mechanisms are outside the scope of this specification.

## Interoperability

Agents with different dialect sets can still communicate using core performatives. Applications SHOULD design protocols that gracefully degrade when specialized dialects are unavailable.

## Extensibility

While this specification defines core CBCL, future extensions may include:

- Additional core performatives (requires specification update)
- Standard dialect libraries for common domains
- Enhanced signature and encryption schemes
- Formal semantics for verification

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

Note: The examples above show the core message content. In practice, these messages would typically be wrapped in envelope structures that include :from, :to, and :timestamp metadata (see {{message-examples}}).

## Dialect Definition and Use

Defining a planning dialect:

~~~
(meta
  (define planning-dialect
    :extends cbcl
    :author @ai-research-lab
    :resources (:max-depth 20
                :max-expansion-size 4096
                :max-verify-time 2000)

    (extend propose-action
            (action preconditions effects)
      (tell @planner
            (action-proposal
              :action action
              :requires preconditions
              :achieves effects)
            :domain planning))

    (extend query-plan
            (goal constraints)
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
    (list "box-A-location-known" "robot-arm-free")
    (list "box-A-on-shelf-3")))
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

## Error Handling

~~~
; Agent attempts to use unknown dialect
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

This work is named after John McCarthy's visionary 1982 proposal for a "Common Business Communication Language" and builds upon the foundational principles of Lisp, particularly S-expressions and homoiconicity. The Lisp community's decades of work on extensible, self-modifying systems provided the conceptual foundation for CBCL's self-bootstrapping design.

This work builds on decades of research in agent communication languages, particularly KQML and FIPA-ACL. The language-theoretic security principles are inspired by the LangSec community and the work of Len Sassaman, Meredith L. Patterson, and Dr Sergey Bratus. Matthew Flatt's work on Racket's #lang mechanism demonstrated how language extensibility could be systematized. Thanks to the multi-agent systems research community for foundational work in this area.

Thanks to the Science and Industry Endowment Fund and CSIRO's Data61 for providing the initial spark in identifying the problem domain in critical agricultural based use-cases. In particular thanks to Data61 for the opportunity to be a part of the Software Systems research team and Dr Adnene Guabtni for their support. Thanks to Ric Richardson and the team at the Office for Innovation for championing this effort. 

Thanks to Claire Barnes, David Factor, DZJ, Mat Mytka, Cath Thompson, Mark Pesce, Ron Tucker, Prof. Ingo Weber, Dr Max Ott, Dr Mark Staples, Dr Ho-Pun Lam, Steve Brodie, Alistair Reid, Geoff Huntley, Dr Quinghua Lu, Dr Liming Zhu, Dylan Scott, Max von Hippel, Evan Miyazono, Max Kaye, Andrew Mugridge and Marc Ahrens for helpful and informative discussions and encouragement over the past decade. Special thanks to my family for their support.

# Implementation Status
{:numbered="false"}

Note to RFC Editor: Please remove this section before publication.

A reference implementation in Rust (cbcl-rs, ~11,000 lines) is available as a Cargo workspace with five crates (cbcl-core, cbcl-parser, cbcl-cli, cbcl-ffi, cbcl-wasm), demonstrating:

- Complete CBCL parser and message processor
- Dialect verification engine (R1-R3 constraints)
- Bounded template expansion with resource enforcement
- Epidemic gossip protocol for dialect propagation
- C FFI and WebAssembly bindings
- Property-based and differential tests, fuzz targets

A Lean 4 formalization (~4,900 lines, 212 machine-checked theorems, zero sorry gaps) provides formal proofs of parser correctness, safety constraint verification, pipeline totality, and DCFL preservation. A verified parser binary (cbcl-parse) is extracted from the proofs.

Implementation repository: https://codeberg.org/anuna/cbcl-rs

# Design Rationale
{:numbered="false"}

**Why S-Expressions?**

S-expressions provide:

- **Simplicity**: Minimal syntax rules, easy to parse
- **Homoiconicity**: Code and data have the same representation
- **Nested Structure**: Natural for representing message hierarchies
- **Established**: Decades of tooling and parser implementations
- **Unambiguous**: No parser differential vulnerabilities

**Why DCFL Constraints?**

Deterministic context-free language constraints ensure:

- **Security**: Eliminates "weird machine" attack surfaces
- **Decidability**: Parsing and verification complete in polynomial time
- **Interoperability**: All implementations parse identically
- **Practicality**: Sufficient expressiveness for agent coordination

**Why Homoiconic Dialects?**

Making dialect definitions themselves CBCL messages enables:

- **No Separate Meta-Language**: Single coherent framework
- **Transmissibility**: Dialects spread like any other message
- **Peer-to-Peer**: No centralized registry required
- **Self-Describing**: Definitions carry their own semantics

**Why Explicit Recipients in Every Message?**

All CBCL messages include an explicit recipient field (not just in transport headers) to enable:

- **Connection Multiplexing**: Multiple agents can share a single transport connection, with routing based on message content
- **Transport Independence**: Messages are self-describing and can be forwarded through intermediaries without transport-layer inspection
- **Store-and-Forward**: Message queues and relays can route based on CBCL message content alone
- **Audit Integrity**: The complete message record includes addressing information independent of transport logs

This design parallels email (RFC 822 headers vs. SMTP envelope) and HTTP/2 multiplexing.

**Separation of Concerns**

This specification intentionally omits:

- **Authentication**: Use TLS, PKI, or application-specific mechanisms
- **Authorization**: Policy decisions belong to agent implementations
- **Transport**: CBCL is transport-agnostic (HTTP, WebSocket, MQTT, etc.)
- **Encryption**: Use transport-layer or message-layer encryption

This separation allows CBCL to serve as a versatile content type across diverse deployment scenarios.
