# EPP Correspondence (standalone paper proof) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Develop and verify the EPP correspondence theorem as a self-contained, compiling LaTeX proof document in `cbcl-rs`, ready to be ported into the paper later.

**Architecture:** Causal-configuration semantics (runs = down-closed message sets), two-level validity (monotone safety + terminal completion), projection lifted to runs, gluing as union-by-hash over compatible families. The theorem is a bijection between valid global runs and compatible valid local families. Paper-level proof only this milestone; Lean is next.

**Tech Stack:** LaTeX (article class), built with `tectonic`. Target: `proofs/epp-correspondence/proof.tex` (standalone — NOT the paper's `main.tex`). Design spec: `proofs/epp-correspondence/design.md`.

## Global Constraints

- **Repo/branch:** all work on the local-only branch `epp-correspondence-proof` in `cbcl-rs`. **NEVER push.** No `git push` in any task.
- **Target file:** `proofs/epp-correspondence/proof.tex` only. Build (from `proofs/epp-correspondence/`): `tectonic proof.tex` — must exit 0 after every task; no `error`/`undefined reference` in the log.
- **Self-contained:** the doc cannot reference the paper. Reused CBCL results are **stated in a Preliminaries (recap) section** (Task 1) as labelled definitions/lemmas taken as given; later tasks `\ref` those labels. Recap labels: `def:proj`, `def:projectable`, `def:rolelocal`, `lat:lattice`, `thm:equiv`, `prop:mono`, `prop:dcfl`, `def:r6`.
- One sentence per line in `proof.tex`.
- Verdict order is **valid-sticky**: only `Valid` is permanent; `Unknown`/`Violation` tentative. Never write "Violation is stable."
- Messages may be **multi-recipient** (`to(m)` a set); roles may be **multi-occupant** (pooled `(any role[*])` / indexed `(all role[*])`). Every definition and proof must hold in these cases.
- The completeness direction is **conditioned on compatibility** — state the caveat; do not claim it unconditionally.
- R6 is **unchanged**. If a proof cannot close without strengthening R6, STOP, record it, surface it — do not silently add hypotheses.
- A "proof-obligation self-check" closes every proof task: list each step's justification and confirm it names an already-established (recap or earlier-task) result. Any unjustified step ⇒ not done.
- New blocks are **appended** to `proof.tex` (before `\end{document}`) in task order.

---

### Task 1: Standalone skeleton + Preliminaries recap + substrate + configurations

**Files:**
- Create: `proofs/epp-correspondence/proof.tex`

**Interfaces:**
- Produces: a compiling standalone doc; recap labels `def:proj`, `def:projectable`, `def:rolelocal`, `lat:lattice`, `thm:equiv`, `prop:mono`, `prop:dcfl`, `def:r6`; substrate notation; `def:config`.

- [ ] **Step 1: Create the preamble + recap + substrate**

```latex
\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\newcommand{\code}[1]{\texttt{#1}}
\newcommand{\caused}{\code{:caused-by}}
\theoremstyle{definition}
\newtheorem{definition}{Definition}
\theoremstyle{plain}
\newtheorem{theorem}{Theorem}
\newtheorem{proposition}{Proposition}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}
\title{The Endpoint-Projection Correspondence for CBCL\\(standalone proof development)}
\author{Anuna Research}
\date{\today}
\begin{document}
\maketitle

\section{Preliminaries (recap)}
\label{sec:prelim}
We recall, without proof, the CBCL results this development builds on; they are
established in the paper and the mechanized R1--R5 development.

\begin{definition}[Projection on protocols]
\label{def:proj}
$\mathrm{project}(P,r)$ maps a role-annotated protocol $P$ and role $r$ to a local
protocol whose steps are tagged from $r$'s viewpoint: a performative with
$\mathrm{from}=r$ is a \emph{Send}, one with $r\in\mathrm{to}$ a \emph{Recv}, and one in
which $r$ neither sends nor receives a \emph{bystander}, erased with its causal edges
spliced (transitively closed) through the erasure.
\end{definition}

\begin{definition}[Projectability]
\label{def:projectable}
$P$ is \emph{projectable onto $r$} iff $r$'s local protocol references, as a
predecessor, only performatives that $r$ itself sends or receives.
\end{definition}

\begin{definition}[Role-local verification]
\label{def:rolelocal}
On an incoming message $m$, the verifier checks role conformance (a signature predicate
on immutable fields) and runs the causal verifier against $\mathrm{project}(P,r)$ and
$r$'s store.
\end{definition}

\begin{definition}[Valid-sticky verdict lattice]
\label{lat:lattice}
Verdicts are $\mathit{Unknown}$ (bottom) and the incomparable maximal $\mathit{Valid}$,
$\mathit{Violation}$ (a flat lattice; no top).
\code{(all \ldots)} composes by meet, \code{(any \ldots)} by join.
Under store growth a verdict moves up from $\mathit{Unknown}$; $\mathit{Valid}$ is
permanent, $\mathit{Violation}$ permanent only once all alternatives of a containing
\code{(any \ldots)} have resolved.
\end{definition}

\begin{theorem}[Projectability $\equiv$ local verifiability]
\label{thm:equiv}
If $P$ is projectable onto $r$, then verification of any $r$-relevant message over
$\mathrm{project}(P,r)$ and $r$'s local store never returns $\mathit{Unknown}$ for a
predecessor $r$ cannot eventually observe.
\end{theorem}

\begin{proposition}[Monotonicity, valid-sticky]
\label{prop:mono}
Role-local verification is monotone into the verdict lattice in the valid-sticky order:
$\mathit{Valid}$ is stable under store growth; $\mathit{Unknown}$ and $\mathit{Violation}$
are tentative.
\end{proposition}

\begin{proposition}[DCFL preservation]
\label{prop:dcfl}
Each local protocol's accepted language is regular, hence DCFL; projection adds no
recogniser.
\end{proposition}

\begin{definition}[R6 well-formedness]
\label{def:r6}
A role-annotated protocol satisfies \emph{R6} iff it is role-complete, chooser-coherent,
projectable onto every role, every role is reachable from \code{begin}, and every choice
is decided by a single agent.
\end{definition}

\section{Formal Model}
\label{sec:model}

\subsection{Substrate}
A \emph{message} $m$ carries a content hash $h(m)$, a performative type $\tau(m)$, a
sender role $\mathrm{from}(m)$, a set of recipient roles $\mathrm{to}(m)$, and a set of
predecessor hashes $\mathrm{pred}(m)$; all references are thread-scoped.
A protocol $P$ (satisfying R6, Def~\ref{def:r6}) fixes, per performative, its predecessor
clauses (\code{(any \ldots)}/\code{(all \ldots)}) and sender/recipient roles.

\begin{definition}[Configuration]
\label{def:config}
A \emph{configuration} $C$ is a finite set of messages.
$C$ is \emph{closed} iff causally down-closed: for every $m\in C$ and
$\hbar\in\mathrm{pred}(m)$ there is $m'\in C$ with $h(m')=\hbar$.
\end{definition}

A configuration need not be closed: a dangling predecessor leaves the dependent message
at $\mathit{Unknown}$, never $\mathit{Violation}$.
Global executions of interest are closed configurations.

\end{document}
```

- [ ] **Step 2: Build** — from `proofs/epp-correspondence/`: `tectonic proof.tex`. Expected: exit 0; no `error`/`undefined`.

- [ ] **Step 3: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: standalone skeleton, recap, substrate, configurations"
```

---

### Task 2: Two-level validity (safety + completion)

**Files:** Modify `proof.tex` — insert before `\end{document}`.
**Interfaces:** Consumes `def:config`, `lat:lattice`, `def:r6`, `def:rolelocal`. Produces `def:psafe`, `prop:safe-mono`, `def:pcomplete`.

- [ ] **Step 1: Insert** (immediately before `\end{document}`)

```latex
\subsection{Global validity}
We use two levels: a monotone safety core and a terminal completion predicate.

\begin{definition}[Safety]
\label{def:psafe}
A configuration $C$ is \emph{$P$-safe} iff no $m\in C$ has verdict $\mathit{Violation}$
under $P$ with store $C$; $\mathit{Unknown}$ is tolerated.
\end{definition}

\begin{proposition}[Safety is subset-closed]
\label{prop:safe-mono}
If $C\subseteq C'$ and $C'$ is $P$-safe then $C$ is $P$-safe.
\end{proposition}
\begin{proof}
A $\mathit{Violation}$ depends only on immutable fields of $m$ and on predecessors
present in the store (Def~\ref{def:rolelocal}); deleting messages can only turn a
resolved predecessor absent, i.e.\ $\mathit{Valid}/\mathit{Violation}\to\mathit{Unknown}$
(Def~\ref{lat:lattice}), never create a new $\mathit{Violation}$.
Hence no $m\in C$ is a $\mathit{Violation}$ under $C$.
\end{proof}

\begin{definition}[Completion]
\label{def:pcomplete}
A closed configuration $C$ is \emph{$P$-complete} iff it is $P$-safe and every obligation
is discharged: for each taken branch every required performative is present; every indexed
(\code{(all role[*])}) fan-in whose membership is sealed has all members present and
$\mathit{Valid}$; and every pooled (\code{(any role[*])}) obligation has at least one
occupant.
\end{definition}
```

- [ ] **Step 2: Self-check** — justifications name `def:rolelocal`, `lat:lattice` ✓.
- [ ] **Step 3: Build** — `tectonic proof.tex` → exit 0.
- [ ] **Step 4: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: two-level validity (safety + completion)"
```

---

### Task 3: Run projection + local validity

**Files:** Modify `proof.tex`.
**Interfaces:** Consumes `def:proj`, `def:psafe`, `def:pcomplete`, `thm:equiv`, `def:rolelocal`. Produces `def:run-proj`, `def:localvalid`.

- [ ] **Step 1: Insert** (before `\end{document}`)

```latex
\subsection{Local executions}
Projection lifts from protocols (Def~\ref{def:proj}) to runs.

\begin{definition}[Run projection]
\label{def:run-proj}
For a configuration $C$ and role $r$, $\mathrm{project}(C,r)$ is the set of $m\in C$ with
$\mathrm{from}(m)=r$ or $r\in\mathrm{to}(m)$, with bystanders erased and causal edges
spliced through the erasure, as in Def~\ref{def:proj}.
\end{definition}

\begin{definition}[Local validity]
\label{def:localvalid}
A local run $L$ is \emph{locally $P$-safe for $r$} iff no $m\in L$ is $\mathit{Violation}$
under $\mathrm{project}(P,r)$ with store $L$ (Def~\ref{def:rolelocal});
\emph{locally complete for $r$} iff it additionally discharges every obligation of
$\mathrm{project}(P,r)$ restricted to $r$ (cf.\ Def~\ref{def:pcomplete}).
\end{definition}

By Theorem~\ref{thm:equiv}, when $P$ satisfies R6 a locally $P$-safe run carries no
spurious $\mathit{Unknown}$ for a predecessor $r$ cannot observe.
```

- [ ] **Step 2: Build** — `tectonic proof.tex` → exit 0.
- [ ] **Step 3: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: run projection and local validity"
```

---

### Task 4: Compatibility + gluing

**Files:** Modify `proof.tex`.
**Interfaces:** Consumes `def:config`, `def:localvalid`. Produces `def:compatible`, `def:glue`, `lem:glue-closed`.

- [ ] **Step 1: Insert** (before `\end{document}`)

```latex
\subsection{Gluing}

\begin{definition}[Family and compatibility]
\label{def:compatible}
A \emph{family} $F=\{L_r\}_{r}$ has one local run per role.
$F$ is \emph{compatible} iff:
\emph{(Agreement)} messages occurring in two runs with equal hash are identical;
\emph{(Coverage)} for every $m\in L_r$ and every $r'\in\{\mathrm{from}(m)\}\cup\mathrm{to}(m)$,
$m\in L_{r'}$, and every $\hbar\in\mathrm{pred}(m)$ resolves to a message present in $L_r$.
\end{definition}

\begin{definition}[Gluing]
\label{def:glue}
$\mathrm{glue}(F)=\bigcup_r L_r$, deduplicated by hash.
\end{definition}

\begin{lemma}[Glue is well-defined and closed]
\label{lem:glue-closed}
For a compatible family $F$, $\mathrm{glue}(F)$ is a configuration and is closed.
\end{lemma}
\begin{proof}
Well-defined: equal-hash messages are identical by Agreement, so the deduplicated union
is a set of messages.
Closed: for $m\in\mathrm{glue}(F)$, $m\in L_r$ for some $r$; by Coverage every
$\hbar\in\mathrm{pred}(m)$ resolves to some $m'\in L_r\subseteq\mathrm{glue}(F)$.
\end{proof}
```

- [ ] **Step 2: Self-check** — Coverage quantifies over all of `to(m)`, so multi-recipient handled ✓.
- [ ] **Step 3: Build** — `tectonic proof.tex` → exit 0.
- [ ] **Step 4: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: compatibility and gluing"
```

---

### Task 5: Reconciliation lemma (load-bearing)

**Files:** Modify `proof.tex`.
**Interfaces:** Consumes `def:run-proj`, `def:glue`, `def:compatible`, `def:projectable`, `def:r6`, `def:proj`. Produces `lem:reconcile`.

- [ ] **Step 1: State and prove** (before `\end{document}`)

```latex
\begin{lemma}[Spliced--global reconciliation]
\label{lem:reconcile}
Let $P$ satisfy R6 and $r$ a role.
\textup{(i)} For a closed configuration $C$ and $m\in\mathrm{project}(C,r)$, the
predecessors of $m$ named in $\mathrm{project}(P,r)$ resolve within
$\mathrm{project}(C,r)$, to the same messages (by hash) as $m$'s $P$-predecessors in $C$
after splicing erased bystanders.
\textup{(ii)} For a compatible family $F$ and $m\in L_r$, the spliced predecessors of $m$
in $\mathrm{project}(P,r)$ resolve, via Coverage, to the same messages in
$\mathrm{glue}(F)$ that witness $m$'s $P$-predecessors globally.
\end{lemma}
\begin{proof}
By projectability (Def~\ref{def:projectable}, from R6, Def~\ref{def:r6}) every predecessor
named in $\mathrm{project}(P,r)$ is a performative $r$ sends or receives, hence present in
the local run whenever its global witness is; splicing (Def~\ref{def:proj},
Def~\ref{def:run-proj}) composes exactly the erased bystander edges, and content hashes
identify messages, so the spliced local witness and the global witness coincide.
\textup{(i)} uses closure of $C$; \textup{(ii)} uses Coverage (Def~\ref{def:compatible})
for presence and Agreement for hash identity.
\end{proof}
```

- [ ] **Step 2: Proof-obligation self-check (CRITICAL)** — tie each sub-claim to a result: projectability⇒r-observable (`def:projectable`); splicing=erased-edge composition (`def:proj`/`def:run-proj`); hash identity=Agreement (`def:compatible`); presence=closure(i)/Coverage(ii). **If any sub-claim has no justification, STOP and surface — the model needs revision; do not patch silently.**
- [ ] **Step 3: Build** — `tectonic proof.tex` → exit 0.
- [ ] **Step 4: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: spliced/global reconciliation lemma"
```

---

### Task 6: EPP correspondence theorem + soundness proof

**Files:** Modify `proof.tex` — add `\section{The correspondence}`.
**Interfaces:** Consumes `def:psafe`, `def:pcomplete`, `def:run-proj`, `def:localvalid`, `lem:reconcile`, `def:rolelocal`. Produces `thm:epp`; part (1) proved.

- [ ] **Step 1: Add theorem statement + soundness proof** (before `\end{document}`)

```latex
\section{The correspondence}
\label{sec:corr}

\begin{theorem}[EPP correspondence]
\label{thm:epp}
Let $P$ satisfy R6.
\begin{enumerate}
\item[(1)] \emph{Soundness.} If $C$ is a $P$-safe (resp.\ $P$-complete) closed
configuration, then for every role $r$, $\mathrm{project}(C,r)$ is locally $P$-safe
(resp.\ locally complete) for $r$.
\item[(2)] \emph{Completeness.} If $F=\{L_r\}$ is a \emph{compatible} family with each
$L_r$ locally $P$-safe (resp.\ locally complete), then $\mathrm{glue}(F)$ is a $P$-safe
(resp.\ $P$-complete) closed configuration.
\item[(3)] \emph{Exactness.} On valid objects $\mathrm{project}$ and $\mathrm{glue}$ are
mutually inverse: $\mathrm{glue}(\{\mathrm{project}(C,r)\}_r)=C$ for $P$-safe closed $C$,
and $\mathrm{project}(\mathrm{glue}(F),r)=L_r$ for compatible $F$.
\end{enumerate}
\end{theorem}

\begin{proof}[Proof of (1)]
Safety: take $m\in\mathrm{project}(C,r)$; by Lemma~\ref{lem:reconcile}(i) its
$\mathrm{project}(P,r)$-predecessors resolve within $\mathrm{project}(C,r)$ to the
messages witnessing $m$'s $P$-predecessors in $C$.
As $C$ is $P$-safe, $m$ is non-$\mathit{Violation}$ there; role conformance is a
per-message predicate on immutable fields (Def~\ref{def:rolelocal}), unaffected by
projection, so $m$ is non-$\mathit{Violation}$ locally.
Completion: every obligation of $\mathrm{project}(P,r)$ is the $r$-restriction of an
obligation of $P$, and sealing is preserved under projection, so a discharged global
obligation projects to a discharged local one.
\end{proof}
```

- [ ] **Step 2: Self-check** — cites `lem:reconcile`(i), `def:psafe`/`def:pcomplete`, `def:rolelocal`; completion names pooled + indexed cases.
- [ ] **Step 3: Build** — `tectonic proof.tex` → exit 0, no undefined refs.
- [ ] **Step 4: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: EPP correspondence theorem + soundness"
```

---

### Task 7: Completeness proof (conditioned on compatibility)

**Files:** Modify `proof.tex` — append after soundness proof.
**Interfaces:** Consumes `lem:glue-closed`, `lem:reconcile`, `def:psafe`, `def:pcomplete`, `def:compatible`. Produces proof of `thm:epp`(2).

- [ ] **Step 1: Add completeness proof + caveat** (before `\end{document}`)

```latex
\begin{proof}[Proof of (2)]
$\mathrm{glue}(F)$ is a closed configuration by Lemma~\ref{lem:glue-closed}.
Safety: take $m\in\mathrm{glue}(F)$, so $m\in L_r$ for some $r$; by
Lemma~\ref{lem:reconcile}(ii) its $P$-predecessors are present in $\mathrm{glue}(F)$ and
coincide (Agreement) with those witnessing $m$ locally, where $m$ is non-$\mathit{Violation}$
by local safety; role conformance is unchanged by gluing.
Completion: were some obligation of $P$ undischarged in $\mathrm{glue}(F)$ (a required
step or sealed-fan-in member absent, or a pooled obligation with no occupant), its
responsible role $r'$ would have an undischarged obligation in $\mathrm{project}(P,r')$,
so $L_{r'}$ is not locally complete (Def~\ref{def:pcomplete}), contradiction.
\end{proof}

\noindent
The completeness direction is conditioned on \emph{compatibility} (Def~\ref{def:compatible}):
a meta-level gluing precondition, not a property a single endpoint verifies from its own
view.
This is where bundle-omission is neutralised---an omitted branch violates Coverage, or
surfaces as a locally undischarged sealed obligation---and is why no strengthening of R6
is required.
```

- [ ] **Step 2: Proof-obligation self-check (CRITICAL)** — closure⇐`lem:glue-closed`; presence/identity⇐`lem:reconcile`(ii)+Agreement; completion contrapositive⇐`def:pcomplete`. **Verify the contrapositive holds for pooled `(any role[*])`** (absence = no occupant acted). If pooled roles break it, STOP and surface.
- [ ] **Step 3: Build** — `tectonic proof.tex` → exit 0.
- [ ] **Step 4: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: completeness proof (conditioned on compatibility)"
```

---

### Task 8: Exactness (round-trip) proof + bijection corollary

**Files:** Modify `proof.tex` — append after completeness proof.
**Interfaces:** Consumes `def:run-proj`, `def:glue`, `def:compatible`, `lem:reconcile`. Produces proof of `thm:epp`(3); `cor:bijection`.

- [ ] **Step 1: Add exactness proof + corollary** (before `\end{document}`)

```latex
\begin{proof}[Proof of (3)]
$\mathrm{glue}(\{\mathrm{project}(C,r)\}_r)\subseteq C$ since each
$\mathrm{project}(C,r)\subseteq C$; conversely every $m\in C$ has a sender or a recipient
role $r$ with $m\in\mathrm{project}(C,r)$, so $C\subseteq\mathrm{glue}(\cdots)$; equality
follows, hashes identifying duplicates.
Conversely $\mathrm{project}(\mathrm{glue}(F),r)$ keeps exactly the messages with
$\mathrm{from}=r$ or $r\in\mathrm{to}$ lying in some $L_{r'}$; by Coverage these are
exactly the messages of $L_r$, and splicing reproduces $L_r$'s edges, so
$\mathrm{project}(\mathrm{glue}(F),r)=L_r$.
\end{proof}

\begin{corollary}[Bijection]
\label{cor:bijection}
For $P$ satisfying R6, $\mathrm{project}$ and $\mathrm{glue}$ are mutually inverse
bijections between $P$-safe (resp.\ $P$-complete) closed configurations and compatible
families of locally $P$-safe (resp.\ locally complete) runs.
The endpoints realise \emph{exactly} $P$.
\end{corollary}
```

- [ ] **Step 2: Self-check** — cites `def:run-proj`, `def:glue`, Coverage, `lem:reconcile`; assumes every message has a sender and $\ge 1$ recipient (state it).
- [ ] **Step 3: Build** — `tectonic proof.tex` → exit 0.
- [ ] **Step 4: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: exactness (round-trip) + bijection corollary"
```

---

### Task 9: Multi-occupant / multi-recipient hardening pass

**Files:** Modify `proof.tex` — touch-ups as needed.
**Interfaces:** Consumes all prior. Produces no new labels.

- [ ] **Step 1: Audit** — record (in this checkbox's notes) that (a) `to(m)` as a set is handled (Coverage; "≥1 recipient"); (b) pooled `(any role[*])` discharge correctly in completion + completeness; (c) indexed `(all role[*])` sealing is used in `def:pcomplete` and the completeness contrapositive.
- [ ] **Step 2: Patch any gap** — minimal edits; if none, record "no changes needed" and skip to Step 4.
- [ ] **Step 3: Build** — `tectonic proof.tex` → exit 0.
- [ ] **Step 4: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: multi-occupant / multi-recipient hardening"
```

---

### Task 10: Closing note (paper port + Lean next) + final consistency build

**Files:** Modify `proof.tex` — add `\section{Notes}`.
**Interfaces:** Consumes `thm:epp`, `cor:bijection`.

- [ ] **Step 1: Add closing note** (before `\end{document}`)

```latex
\section{Notes}
\label{sec:notes}
This development is standalone (recap, Section~\ref{sec:prelim}); when ported into the
paper, the recap maps onto the existing labelled results and Theorem~\ref{thm:epp}
replaces the former conjecture.
The completeness direction (Theorem~\ref{thm:epp}(2)) is conditioned on compatibility;
making compatibility endpoint-checkable is future work.
Mechanizing Theorem~\ref{thm:epp} in Lean~4, on top of the existing machine-checked
R1--R5 development, is the next milestone.
```

- [ ] **Step 2: Final build + reference check** — `tectonic proof.tex`; check log for `undefined`/`multiply defined`. Expected: exit 0, none.
- [ ] **Step 3: Commit (NO push)**

```bash
git add proofs/epp-correspondence/proof.tex
git commit -m "epp-proof: closing note (paper port + Lean next)"
```

---

## Self-Review (completed by plan author)

- **Coverage:** Formal Model → Tasks 1–4; reconciliation lemma → Task 5; theorem (soundness/completeness/exactness) → Tasks 6–8; multi-occupant/multi-recipient → baked in + audited Task 9; standalone recap + paper-port + Lean-next framing → Tasks 1 & 10.
- **Placeholders:** only Task 9 Step 2 lacks a code block (audit-dependent, by design).
- **Label consistency:** recap labels → new labels (`def:config`,`def:psafe`,`prop:safe-mono`,`def:pcomplete`,`def:run-proj`,`def:localvalid`,`def:compatible`,`def:glue`,`lem:glue-closed`,`lem:reconcile`,`thm:epp`,`cor:bijection`) consistent.
- **Risk gates:** Tasks 5/7 STOP-and-surface if a proof can't close without changing R6 or breaking cardinality cases.
