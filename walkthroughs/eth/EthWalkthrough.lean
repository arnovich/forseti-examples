import Solution
import Given.End
import Printed.End
import Eight.SecCrossing_Identity
import Eight.SecCrossing_LemPieces
import SparsificationLemma.Main
import Exits.End
import FromPrinted.SplitSat
import FromPrinted.Count
import FixedWidthSteps.Main
import PiecesCounted.Half
import PrintedOrder.Close
import CountedRoute.Main

/-!
# A 2^o(n) time algorithm for 3-SAT: a guided walkthrough

This notebook walks through the paper "A $2^{o(n)}$ Time Algorithm for 3-SAT"
(Claude, Anthropic, dated October 26, 2026) and its Lean 4 formalization, the
project `eth` in the repository
[`anthropics/formal-math`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth)
at commit `16a5ce4`.
It covers the main text (Theorem 1, the failure of ETH, Theorem 2,
Definitions 1 to 6, the eight-square identity, Lemmas 1, 2 and 4,
Proposition 3, Algorithm 1, Corollaries 5 and 6) and Appendices A to D, each
appendix as one step.

**What is proved.** The project proves two propositions, stated in the one
file a reader must trust, [`MainResults.lean`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/MainResults.lean), which imports only Mathlib and
contains no proofs: `MainResults.MainTheorem` (Theorem 1) and
`MainResults.ETHIsFalse` (the Exponential Time Hypothesis fails). The proofs
are in [`Solution.lean`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/Solution.lean) and the folder [`proof/`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof). Every other statement below is
one of the project's own intermediate theorems, chosen through its index of
the paper, [`proof/PaperIndex.lean`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/PaperIndex.lean), whose recorded differences from the paper
are repeated here.

**How to read the claims.** Each claim below restates the type of one of the
project's theorems, word for word, and is proved by that theorem with
`exact`. A claim adds nothing to the project: it shows where a statement of
the paper lives in Lean and what Lean actually says.

**Status: unchecked.** The project pins Lean `v4.33.1`; Glitnir supports only
Lean `4.35.0`, so Glitnir cannot check this walkthrough, and no claim below
has a checking status. The project and Mathlib were not built for this
walkthrough, so this file has not been compiled either. Only a text
comparison with the project's source (the walkthrough helper's `check`) has
been run. The project's [README](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/README.md) reports its own build and axiom check: both
main theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

**Attribution and licence.** The paper and its formalization are
Copyright 2026 Anthropic, PBC, released under the Apache License 2.0 (see
[`LICENSE`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/LICENSE) and [`NOTICE`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE) in the project). The paper and the Lean development were
written by AI models; the paper's Appendix E says that, when it was written, no
person was known to have checked the Lean development. This walkthrough
restates the paper in its own words and changes nothing in the project.

![How the proof fits together](assets/map.svg)

The map shows each statement above the statements its proof uses directly;
`map.html` beside this file is the clickable version, with each statement, its
Lean declarations and links to the paper's pages and the source lines.

## The strategy in one page

**From formulas to sums of products.** The number of satisfying assignments of
a CNF is a sum, over settings of local variables at each clause, of a product
of node weights $W_a$ and pairwise consistency tests $\Psi_{a,b}$ (the value
of a "network", Definition 2). After sparsification (Lemma 4) there are only
$O(n)$ clauses, so only $O(n)$ bits cross between clauses.

**The cost of an edge.** An edge "factors through $c$ bits" (Definition 1) if
its test is a sum over $2^c$ products of a function of one end and a function
of the other. Cutting a network along such edges costs a factor $2^c$. The
normal form of the recursion is the $(K,\lambda)$-clique (Definition 3): $K$
nodes, $\lambda$ bits on every edge, arbitrary integer tables. A pair
$(K,e)$ is "achievable" (Definition 4) if cliques on $K$ nodes are evaluated
in time about $2^{eK^2\lambda}$; brute force gives $e = \tfrac12$.

**Grouping.** Lemma 1 evaluates any network on $g = 3K^8$ nodes with an
algorithm for $K$-cliques, by grouping the $g$ nodes into $K$ balanced groups.

**The new idea.** Place $g^2$ clique nodes on a $g \times g$ grid. Every edge
that changes both row and column is a diagonal of exactly one rectangle. The
eight-square identity rewrites the two equality tests of a rectangle's
diagonals as a sum of a term that is cheap when rows are merged and a term
that is cheap when columns are merged; grouping these terms (Definition 5,
Lemma 2) gives a polynomial number of terms, in each of which merging rows or
columns costs at most $\tfrac{11}{12}$ of the bits. So one level turns an
exponent $e$ for $K$ nodes into about $\tfrac{11}{12}e$ for $9K^{16}$ nodes
(Proposition 3), and the infimum $e^*$ of achievable exponents is $0$.

**Consequences.** For any $\delta > 0$ choose a level with a small enough
exponent: Theorem 2 counts 3-SAT solutions in time $O(2^{\delta n})$, which
refutes ETH, and Corollaries 5 and 6 extend this to $k$-SAT, SETH and #ETH.
The appendices let $K$ grow with the input, use better pieces with
$\rho = 1/\sqrt 2$ and a variable-based network, and obtain the explicit rate
of Theorem 1.

**Where Lean takes another route.** The Lean proof of the Main Theorem follows
the route of Corollary 11 (Appendix D), with five recorded differences, and
the Lean proof that ETH fails is drawn from the Main Theorem, not from
Theorem 2. Several statements are proved in Lean only in a **deciding** form,
where the paper counts. Every such difference is noted at its statement below.
-/

namespace EthWalkthrough

/-!
## What is claimed: Theorem 1, Theorem 2 and the failure of ETH {fold}

The paper's three headline statements and their Lean forms. Lean states the
Main Theorem and the failure of ETH for one Mathlib Turing machine, counting
its steps, and proves Theorem 2 only for deciding satisfiability.

### Theorem 1 (the Main Theorem)

One deterministic algorithm counts the satisfying assignments of a $k$-CNF
with $m$ clauses in which $n$ variables occur, in time
$2^{O(\min\{k^2 n \log\log n/\sqrt{\log n},\ km/\sqrt{\log m}\})}$, where the
$O$ hides an absolute constant (paper, §1, pp. 1–2).

**Idea.** The bound in $m$ comes from Theorem A of Appendix A with the pieces of
Appendix B; the bound in $n$ from Theorem D of Appendix D, which uses the
counting sparsification of Appendix C; Corollary 11 runs both algorithms in
alternation and stops with the first answer.

**In Lean** (`MainResults.MainTheorem`, [`MainResults.lean`, line 177](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/MainResults.lean#L177)): there are
one machine of Mathlib's kind `Turing.FinTM2` with finite stack alphabets and
one constant $C$, both fixed before $k$ and the formula, such that for every
$k \ge 1$, $n \ge 4$ and every formula on $x_0,\dots,x_{n-1}$ in which every
variable occurs, with clauses of at most $k$ literals, no clause written twice
and $m \ge 2$ clauses, the machine started on the word $1^k 0\, 1^n 0$
followed by $k$ slots of $\lfloor\log_2 2n\rfloor + 1$ bits per clause halts
with the count in $n+1$ bits within
$\lfloor 2^{C\min\{km/\sqrt{\log m},\ k^2 n\log\log n/\sqrt{\log n}\}}\rfloor$
steps. Differences from the paper (its Appendix E lists them): steps of a
Turing machine, not word-RAM time; the ranges $k \ge 1$, $m \ge 2$, $n \ge 4$
are explicit, as in Corollary 11, where the paper leaves them to its $O$; the
input is a fixed word; a clause is a list of literals and may be empty or
repeat a literal, where the paper has nonempty sets; nothing is said about
inputs outside the hypotheses. The constant $C$ is not explicit.

**The proof** ([`Solution.lean`, line 44](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/Solution.lean#L44)) is `CountedRoute.mainTheoremHolds`
by unfolding definitions. It follows the route of Corollary 11, but not the
printed proof step for step: the head of the project's [index](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/PaperIndex.lean) lists five
differences, among them that running two machines in alternation costs a
constant power rather than a constant factor, that costs are carried by a
padding string of blank symbols as a budget of time, and that the pieces of
Theorem B write $2^{c\lambda}$ symbols and then do all their work in one step.
-/

/-- **Theorem 1 (Main Theorem)**: one Turing machine and one constant $C$
count the satisfying assignments of every $k$-CNF with $m \ge 2$ clauses in
which all $n \ge 4$ variables occur, within
$2^{C\min\{km/\sqrt{\log m},\,k^2 n\log\log n/\sqrt{\log n}\}}$ steps. -/
theorem mainTheorem : MainResults.MainTheorem := by
  exact MainResults.mainTheorem

/-!
### Theorem 2

For every $\delta > 0$ a deterministic algorithm counts the satisfying
assignments of a 3-CNF on $n$ variables, with any number of clauses, in time
$O(2^{\delta n})$ (paper, §2, p. 4; proved in §6, pp. 19–20). It is the
simplified form of Theorem 1 that the main text proves.

**Idea.** Fix $\delta$. Sparsify (Lemma 4 with $\varepsilon = \delta/3$) into at
most $2^{\delta n/3}$ formulas with $m \le Mn$ clauses. Since $e^* = 0$
(Proposition 3), some $(K, \delta'/12)$ with $\delta' = \delta/(3M)$ and
$K \ge 72/\delta'$ is achievable. Split the clauses of each formula into
$g = 3K^8$ clusters, link the occurrences of each variable by a chain of
equality tests (fewer than $3m$ bits in all), and evaluate the resulting
network with Lemma 1; its cost is $O(2^{\delta' m})$ up to polynomial
factors, and $\delta' m \le \delta n/3$.

**In Lean** (`Sat3.ThmEveryDelta`,
[`proof/statements/ThmEveryDeltaStatement.lean`, line 58](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/ThmEveryDeltaStatement.lean#L58)): **only the decision form** — for every $\delta > 0$ one Turing machine
with finite alphabets decides 3-SAT within $c\cdot 2^{\delta n}$ steps. This is
weaker than the printed theorem, which counts. The counting sentence is not
stated on its own; it is the case $k = 3$ of the first half of Corollary 6
below, which has a proof of its own. Formulas are lists of clauses, each a list
of literals that may be empty or repeat a literal.

**The proof** cited here, `Given.threeSat_through_eStar` (the [index](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/PaperIndex.lean)'s main
entry), follows §6 through $e^* = 0$, reading clause (iii) of Definition 2 as
one condition on procedures that answer every question within $\tau$
operations. The project proves the same statement three more times
(`Printed.threeSat_through_eStar`, `Exits.threeSat_through_eStar`, and through
Algorithm 1).
-/

/-- **Theorem 2**, decision form: for every $\delta > 0$ one Turing machine
decides 3-SAT on $n$ variables within $c\cdot 2^{\delta n}$ steps. -/
theorem theorem2 : Sat3.ThmEveryDelta := by
  exact Given.threeSat_through_eStar

/-!
### ETH is false

Let $s_3$ be the infimum of the $\delta \ge 0$ for which some deterministic
algorithm decides 3-SAT on $n$ variables in time $O(2^{\delta n})$. The
Exponential Time Hypothesis of Impagliazzo and Paturi says $s_3 > 0$; the
paper shows $s_3 = 0$ (§2, p. 4, and Corollary 5; Appendix E, p. 40).

**Idea.** In the paper it is immediate: a 3-CNF is satisfiable exactly when its
count is positive, so Theorem 2 gives a decider in time $O(2^{\delta n})$ for
every $\delta$. Theorem 1 gives the same, since its bound is $2^{o(n)}$.

**In Lean** (`MainResults.ETH`, line 117, and `MainResults.ETHIsFalse`, line 122):
$s_3$ is defined with Mathlib's Turing machines with finite alphabets, a bound
of $\lfloor c\cdot 2^{\delta n}\rfloor$ steps for every $n$, and the input
$1^n 0$ followed by three slots per clause; `ETH` is $0 < s_3$ and
`ETHIsFalse` is its negation. The paper defines ETH as $s_k > 0$ for all
$k \ge 3$ and remarks that this is the same as $s_3 > 0$; the file's comment
explains why refuting this form refutes the usual one (a step that is not
part of the Lean proof).

**The proof does not follow the paper's route.** `MainResults.ethIsFalse`
([`Solution.lean`, line 40](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/Solution.lean#L40)) is drawn from the Main Theorem, not from
Theorem 2: `NamesInOrder.generalFormFollowsAsPropositions` allows any names of
the variables, and `Wrap.countingBoundImpliesFailureOfETH` wraps a counting
machine with that bound into one machine that decides 3-SAT within
$c\cdot 2^{\delta n}$ steps for every $\delta > 0$.
-/

/-- **ETH is false**: $s_3 = 0$ for $s_3$ defined with Mathlib's Turing machines. -/
theorem ethIsFalse : MainResults.ETHIsFalse := by
  exact MainResults.ethIsFalse

/-!
## Networks, cliques and grouping: Definitions 1 to 4 and Lemma 1 {fold}

Section 3 sets up the objects of the recursion: functions that factor through
$c$ bits, networks, $(K,\lambda)$-cliques, achievable exponents, and Lemma 1,
which evaluates any network on $3K^8$ nodes with an algorithm for $K$-cliques.
In Lean every definition adds a bound on memory or a model of operations.

### Definition 1: factoring through c bits

$F : X \times X' \to \mathbb{Z}$ "factors through $c$ bits" if
$F(z,z') = \sum_{\theta \in \{0,1\}^c} f(z,\theta)\, f'(z',\theta)$ for
integer functions $f, f'$ (§3, p. 14). As a matrix, $F$ is a product of two
integer matrices with inner dimension $2^c$, so its rank is at most $2^c$.
Products of factored functions add their bit counts, and an equality test of
two $c$-bit strings factors through $c$ bits.

**In Lean:** `Paper.FactorsThrough`
([`proof/networks/Paper/SecNetworks_DefFactor.lean`, line 40](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_DefFactor.lean#L40)). A $c$-bit string is a function `Fin c → Bool`, $F$ takes its two
arguments one after the other, and $X, X'$ need not be finite. It is a
definition, so it has no claim.

### Definition 2: networks

A network on a node set $J$ with parameters $P, B, \tau$ has, at each node
$a$, a set $S_a$ of settings (bit strings of a fixed length $P_a \le P$) and a
weight $W_a$; for each pair $\{a,b\}$, a function $\Psi_{a,b}$ with a
factorization through $c_{a,b}$ bits. It requires (i)
$\sum_b c_{a,b} \le P$, (ii) all values below $2^B$ in absolute value, and
(iii) that everything can be computed within $\tau$ operations. Its "value"
is $Z = \sum_z \prod_a W_a(z_a) \prod_{\{a,b\}} \Psi_{a,b}(z_a,z_b)$, and its
"total" $U = 2\sum_{\{a,b\}} c_{a,b}$ counts each shared bit from both ends
(§3, p. 14).

**In Lean:** `Given.IsGivenNetwork`
([`proof/statements/GivenStatement.lean`, line 75](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/GivenStatement.lean#L75)) states all clauses as one property of a network given by procedures
that may themselves query an oracle; an operation is a polynomial-time step or
one query, the procedures' states are bounded (the paper bounds no memory),
and the numbers are passed in unary. No claim.

### Definition 3: the (K, λ)-clique

The $(K,\lambda)$-clique with tables $W_1,\dots,W_K$ is the network on $[K]$
in which each node holds one $\lambda$-bit string for every other node, each
edge tests that its two copies agree, and the tables are not written out: a
query names $w$ and $z_w$ and costs one operation (§3, pp. 14–15). Its value
is the sum over one string per edge of $\prod_w W_w$.

**In Lean:** `Eight.SecNetworks.clique`
([`proof/networks/Eight/SecNetworks_Defs.lean`, line 139](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Defs.lean#L139)) numbers nodes from 0 and stores a setting as one list of
$(K-1)\lambda$ bits; query access is `Printed.tables`
([`proof/statements/PrintedStatement.lean`, line 57](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PrintedStatement.lean#L57)). No claim.

### Definition 4: achievable pairs and e*

$(K,e)$ is "achievable" if one algorithm and one constant $C$ compute the
value of every $(K,\lambda)$-clique with $|W_w| < 2^B$ within
$C\,2^{eK^2\lambda}(B+\lambda)^C$ operations, for all $\lambda, B \ge 1$.
$e^*$ is the infimum of the $e$ for which $(K,e)$ is achievable for infinitely
many $K$. Trying all $2^{\lambda K(K-1)/2}$ choices of edge strings shows
$e^* \le \tfrac12$ (§3, p. 15).

**In Lean:** `Printed.Achievable`
([`proof/statements/PrintedStatement.lean`, line 83](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PrintedStatement.lean#L83)) and `Printed.eStar` (line 90). An operation is a step that may be any
polynomial-time function of the whole state, or one table query; $\lambda$ and
$B$ are given in unary; and **every state must have size at most**
$C(B+\lambda)^C$, which the paper does not ask. The file explains why: in
this model a machine with unbounded memory could read all table entries and do
the rest in one step, making $e^* = 0$ trivial. So Lean's notion implies the
printed one (by an argument outside Lean), not conversely. No claim.

### Lemma 1: from cliques to networks by grouping

If $(K,e)$ is achievable and $g = 3K^8$, then the value of every network on
$[g]$ with parameters $P, B, \tau$ and total $U$ is computed within
$C_1\, 2^{e(U + gP/K) + 2gP/K}(P+B)^{C_1}\tau$ operations, for a constant
$C_1 = C_1(K,e)$ (§3, pp. 15–16).

**Idea.** A grouping sends each of the $g$ nodes to one of $K$ groups. It is
good if every group has at most $2g/K$ nodes and every two groups share at
most $(U + gP/K)/K^2$ bits. For a random grouping, each ordered pair lands in
two given groups with probability $1/K^2$; Chebyshev's inequality and union
bounds show that a good grouping exists, and the algorithm deterministically
tries all $K^g$ groupings, a constant number. Inside a group the settings are
summed out, which gives the tables of a $(K, L)$-clique with the same value;
evaluating one entry costs about $2^{2gP/K}$, which multiplies the clique
algorithm's time.

**In Lean:** `Printed.GroupingLemma`
([`proof/statements/PrintedStatement.lean`, line 157](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PrintedStatement.lean#L157)). The network is given by queries that cost $\tau$ operations each,
in place of clause (iii) of Definition 2; the hypothesis is Lean's
`Achievable`, with its memory bound, and the conclusion adds polynomial-time
steps and states of size at most $C_1(P+B)^{C_1}$. Because of these memory
bounds, the project's [index](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/PaperIndex.lean) says, neither this statement nor the printed lemma
implies the other.
-/

/-- **Lemma 1**: if $(K,e)$ is achievable, one machine computes the value of
every network on $[3K^8]$ within $C_1 2^{e(U+gP/K)+2gP/K}(P+B)^{C_1}\tau$
operations, with polynomial memory. -/
theorem lemma1 : Printed.GroupingLemma := by
  exact Printed.groupingLemma

/-!
## A cheaper crossing: the eight-square identity, Definition 5 and Lemma 2 {fold}

Two equality tests that cross between rows and columns cost 12 bits per block
of three, 6 each way. The eight-square identity rewrites them as a sum of
$\lceil\lambda/3\rceil + 1$ functions that together cost only 11 bits per
block. This is the factor $\rho = 11/12$ of the whole paper.

### The eight-square identity

For blocks $p, q \in \{0,1\}^3$ let $\sigma(p,q) = (-1)^{\phi(p,q)}$ with
$\phi(p,q) = \sum_{1\le i\le j\le 3} p_i q_j + q_1p_2p_3 + p_1q_2p_3 + p_1p_2q_3$.
Then $\sigma(p,q)\sigma(p',q') + \sigma(p,q')\sigma(p',q) = 0$ whenever
$p \oplus q = p' \oplus q'$ and $q \ne q'$ (§4, display (28), p. 16; also §2.4).
It is the classical identity of Degen (1818) and Graves (1843), which says
that the norm of the octonions is multiplicative.

**Why it matters.** With $\psi_k(p,q) = [p \oplus q = k]\,\sigma(p,q)$ put
$R(x,y,u,v) = \sum_k \psi_k(x,y)\psi_k(v,u)$ and
$C(x,y,u,v) = \sum_k \psi_k(x,u)\psi_k(v,y)$. Then
$R + C = 2\,[x = v]\,[y = u]$: twice the two diagonal tests of a rectangle.
$R$ factors through 3 bits between $(x,y)$ and $(u,v)$ (the rows), $C$
through 3 bits between $(x,u)$ and $(y,v)$ (the columns), while each crossing
test costs 6 bits either way.

![The table of signs σ(p, q) of the eight-square identity](assets/sigma.svg)

![A rectangle of the grid: two diagonals, the row choice and the column choice](assets/grid.svg)

**In Lean:** `Eight.Signs`
([`proof/statements/EightSquareStatement.lean`, line 53](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/EightSquareStatement.lean#L53)) is display (28) as printed, with $\oplus$ bit by bit (`Eight.bxor`).
-/

/-- **Eight-square identity**, display (28): for all blocks $p, q, p', q'$ of
three bits with $p \oplus q = p' \oplus q'$ and $q \ne q'$,
$\sigma(p,q)\sigma(p',q') + \sigma(p,q')\sigma(p',q) = 0$. -/
theorem eightSquare : Eight.Signs := by
  exact Eight.signs

/-!
### Definition 5: the functions A₀, …, Aₜ

Let $t = \lceil\lambda/3\rceil$, pad $x, y, u, v \in \{0,1\}^\lambda$ with zeros
to $3t$ bits and cut them into blocks $x_s, y_s, u_s, v_s$. Then $A_i$ is the
coefficient of $T^i$ in $\prod_{s=1}^{t}\bigl(R(x_s,y_s,u_s,v_s) + T\,C(x_s,y_s,u_s,v_s)\bigr)$:
the sum of the terms with exactly $i$ blocks taking the column choice. Set
$c^{row}_i = \min\{2\lambda, 4t + 3i\}$ and $c^{col}_i = \min\{2\lambda, 7t - 3i\}$
(§4, p. 17).

**Why group.** Expanding the product blockwise gives $2^t$ terms per rectangle,
exponentially many in $\lambda$; grouping by the number $i$ of column choices
leaves $t+1$, a polynomial number.

**In Lean:** `Eight.A` ([`proof/statements/EightSquareStatement.lean`, line 90](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/EightSquareStatement.lean#L90)),
`Eight.crow` and `Eight.ccol`, as printed with the blocks numbered from 0.
No claim.

### Lemma 2: the pieces cost 11 bits per block

For every $\lambda \ge 1$ and $i \in \{0,\dots,t\}$: (a)
$A_0 + \dots + A_t = 2^t [x = v][y = u]$ and $|A_i| \le 2^t$; (b) $A_i$ factors
through $c^{row}_i$ bits between $(x,y)$ and $(u,v)$ and through $c^{col}_i$
bits between $(x,u)$ and $(y,v)$, with factors bounded by $2^t$; (c)
$c^{row}_i, c^{col}_i \le 2\lambda$ and
$c^{row}_i + c^{col}_i \le 4\rho\lambda + 8$ with $\rho = 11/12$ (§4, p. 17).

**Idea.** Setting $T = 1$ and using $R + C = 2[x=v][y=u]$ blockwise gives (a). A
term of $A_i$ with column blocks $Q$ costs $3(t-i) + 6i$ bits by rows; naming
$Q$ costs $t$ more bits, so $A_i$ costs $4t + 3i$ by rows and, symmetrically,
$7t - 3i$ by columns. The two add up to $11t$, against $12t$ for the two
equality tests, whatever $i$ is.

![Bits per block: 12 for the two equality tests, 11 for the pieces](assets/block-bits.svg)

**In Lean:** `Eight.LemPieces`
([`proof/statements/EightSquareStatement.lean`, line 107](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/EightSquareStatement.lean#L107)). The claims that $A_i$ and its factorizations are computable in time
$\mathrm{poly}(\lambda)$ are left out, because that file has no model of
computation; the statement adds $c^{row}_i + c^{col}_i \le 11t$ from the
proof of (c).
-/

/-- **Lemma 2**: the $A_i$ add up to $2^t[x=v][y=u]$, are bounded by $2^t$,
factor through $c^{row}_i$ bits by rows and $c^{col}_i$ bits by columns, and
$c^{row}_i + c^{col}_i \le 4\rho\lambda + 8$. -/
theorem lemma2 : Eight.LemPieces := by
  exact Eight.lemPieces

/-!
## One level of the recursion: Proposition 3 {fold}

From an algorithm for cliques on $K$ nodes with exponent $e$, one level builds
an algorithm for cliques on $9K^{16}$ nodes with exponent
$(\rho + 2/K)e + 2/K$, so the best exponent $e^*$ satisfies $e^* \le \rho e^*$
and is $0$. In Lean this holds for the memory-bounded `Achievable`.

### Proposition 3

If $(K,e)$ is achievable and $g = 3K^8$, then $(g^2, e')$ is achievable for
$e' = (\rho + 2/K)e + 2/K$. Hence $e^* = 0$ (§5, pp. 18–19).

**Idea.** Take a $(g^2,\lambda)$-clique and put its nodes on a $g \times g$
grid. An edge whose ends differ in row and column is a diagonal of exactly one
rectangle; the others are straight. Multiply the value by $2^{t|R|}$ and
replace the two diagonal tests of every rectangle by $A_0 + \dots + A_t$
(Lemma 2), then expand: one term $Z_\iota$ for each choice
$\iota : R \to \{0,\dots,t\}$, $(t+1)^{|R|}$ terms, a polynomial in
$\lambda$ for fixed $K$. For each $\iota$ build two networks on $g$ nodes,
one by merging rows and one by merging columns; both have value $Z_\iota$.
Their totals add up to at most about $2(\rho + 1/g)N$ with $N = g^4\lambda$,
so the smaller one is at most about $(\rho + 1/g)N$. Lemma 1 applied to it
costs $2^{e'N}$ up to polynomial factors. The choice of rows or columns is
made once per $\iota$, for the whole grid.

**Why** $e^* = 0$. For $e > e^*$ and large $K$, $(9K^{16}, e'')$ is achievable
for every $e'' > \rho e$, so $e^* \le \rho e^*$; as $0 \le e^* \le \tfrac12$
and $\rho < 1$, $e^* = 0$.

**In Lean:** `Printed.LevelProposition`
([`proof/statements/PrintedStatement.lean`, line 164](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PrintedStatement.lean#L164)) is the first sentence for Lean's `Achievable`, which carries the
memory bound $C(B+\lambda)^C$ in the hypothesis and the conclusion, so it does
not give the printed statement; $\rho = 11/12$ is `Eight.rho`. The second
sentence is `Printed.EStarZero` (line 167), proved as `Printed.eStarZero` and
`Given.eStarZero`. Because Mathlib's infimum of the empty set of reals is 0,
$e^* = 0$ alone would also hold if nothing were achievable; it says what it
should together with `Printed.StHalf` ($(K,\tfrac12)$ is achievable for every
$K$) and `Printed.StEveryEta` (for every $\eta > 0$, $(K,\eta)$ is achievable
for infinitely many $K$), which the project states and proves separately.

**Which proof the claim cites.** The [index](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/PaperIndex.lean)'s main entry is
`Given.levelProposition`, but its file reaches the name `LevelProposition`
through `open Printed`, which the walkthrough cannot restate textually. It
proves the same proposition as `Printed.levelProposition`
([`proof/threesat/Printed/End.lean`, line 80](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/End.lean#L80)), which the claim below cites.
-/

/-- **Proposition 3**, first sentence: if $(K,e)$ is achievable then
$((3K^8)^2, (\rho + 2/K)e + 2/K)$ is achievable, for Lean's memory-bounded
notion of achievable. -/
theorem proposition3 : Printed.LevelProposition := by
  exact Printed.levelProposition

/-!
## From cliques to formulas: Lemma 4 and Algorithm 1 {fold}

The proof of Theorem 2 (§6) sparsifies the formula, turns each sparse formula
into a network of clause clusters, and evaluates it with Lemma 1 at a level
whose exponent is small; §8 writes this as Algorithm 1. Lean states Lemma 4
and Algorithm 1 only for deciding satisfiability.

### Lemma 4 (the Sparsification Lemma)

For every $\varepsilon > 0$ there is $M(\varepsilon) \ge 1$ such that any
3-CNF on $n$ variables can be turned, deterministically in time
$2^{\varepsilon n}\,\mathrm{poly}(n)$, into at most $2^{\varepsilon n}$ 3-CNFs
on the same variables, each with at most $M(\varepsilon)\,n$ clauses, such
that an assignment satisfies the input exactly when it satisfies one of them,
and no two of them share a satisfying assignment (§6, p. 19). The paper cites
it from Impagliazzo, Paturi and Zane, in the form of Dell et al.; Appendix C
sketches the change to Calabro's algorithm that makes the outputs disjoint.

**In Lean:** `SparsificationLemma.Mach.LemSparsification`
([`proof/sparsification/SparsificationLemma/Mach/Defs.lean`, line 114](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Defs.lean#L114)) is **the
deciding form only**: the input is satisfiable if and only if one of the
listed formulas is. One Turing machine serves every $\varepsilon$; it is
started on $1^s 0\,111\,0$ and the code of the formula, with $s$ depending on
$\varepsilon$. Lean proves it for a branching procedure like that of
Appendix C with thresholds of its own, not by citing the lemma. The printed
counting property (each satisfying assignment satisfies exactly one output,
other assignments none) is proved separately as
`SparsificationLemma.stExactlyOne` for the outputs of Lean's branching
procedure. According to the [index](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/PaperIndex.lean), no Lean proof of Theorem 2 uses the
statement below; they use other forms of the same procedure.
-/

/-- **Lemma 4** (Sparsification Lemma), deciding form: one Turing machine,
for every $\varepsilon > 0$, lists at most $2^{\varepsilon n}$ 3-CNFs with at
most $M(\varepsilon) n$ clauses each, within $2^{\varepsilon n}c(n+1)^c$
steps, one of which is satisfiable exactly when the input is. -/
theorem lemma4 : SparsificationLemma.Mach.LemSparsification := by
  exact SparsificationLemma.Mach.lemSparsification_holds

/-!
### The network of a formula (proof of Theorem 2, §6)

This step has no number in the paper and no claim here. Divide the $m$ clauses
into $g = 3K^8$ clusters. Give every occurrence of a variable its own bit, and
link the occurrences of each variable by a chain of equality tests between
consecutive occurrences, so fewer than $3m$ tests in all. A cluster's weight
checks its own clauses and the tests inside it; a pair of clusters checks the
tests between them. The value $Z$ of this network on $[g]$, with $P = 6\lceil m/g\rceil$
and $B = 1$, is the number of satisfying assignments of the variables that
occur. Lemma 1 at $e = \delta'/12$ with $K \ge 72/\delta'$ computes it within
an exponent below $\tfrac34\delta' m + \delta' g$, so in time $O(2^{\delta' m})$
plus a polynomial in $n$. Summing over the sparsified formulas, each count
multiplied by $2^{n'}$ for the $n'$ variables that do not occur, gives the
count in time $O(2^{\delta n})$.

### Algorithm 1

The proof of Theorem 2 as pseudocode, run from the top level down (§8,
pp. 22–23). The levels are $K_0 = 64$, $e_0 = \tfrac12$, $g_\ell = 3K_\ell^8$,
$K_{\ell+1} = 9K_\ell^{16}$ and $e_{\ell+1} = (\rho + 2/K_\ell)e_\ell + 2/K_\ell$;
by brute force and Proposition 3 each $(K_\ell, e_\ell)$ is achievable, and
$\tfrac12\rho^\ell \le e_\ell \le 0.56\rho^\ell$.

- **#Sat** sparsifies with $\varepsilon = \delta/3$ and adds up $2^{n'}\,\mathrm{Count}(\Phi)$.
- **Count** returns 1 for no clauses, otherwise chooses the first level with
  $K_\ell \ge 72/\delta'$ and $e_\ell \le \delta'/12$ and evaluates the network
  of $\Phi$ on $g_\ell$ clusters.
- **Network** tries groupings into $K_\ell$ groups until one is good (Lemma 1)
  and calls Clique on the summed-out tables, which are procedures evaluated
  when queried, never stored.
- **Clique** sums brute force at level 0; otherwise it puts the nodes on a
  $g \times g$ grid, forms the row and column networks for every choice
  $\iota$, calls Network one level down on the one with the smaller total, and
  divides the sum by $2^{t|R|}$ (Proposition 3).

![The exponents e_ℓ of the levels](assets/exponents.svg)

The first step raises the exponent slightly, $e_1 \approx 0.505$, because
$K_0 = 64$ is small; from then on it falls by about $\rho$ per level. The
depth is a constant for fixed $\delta$, but the numbers $K_\ell$ grow doubly
exponentially, which is why the result is purely asymptotic.

**In Lean:** `Exits.StAlgorithm`
([`proof/threesat/Exits/AlgDefs.lean`, line 135](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/AlgDefs.lean#L135)) runs Algorithm 1 line by line on "step machines" whose steps take
polynomial time, **in its deciding form**: procedure Sat stops at the first
formula with a positive count, where the paper's #Sat adds up the counts, and
the search of line 10 stops at the first good grouping. It assumes a list
of formulas as Lemma 4 gives for $\varepsilon = \delta/3$ (`Enumerates`), and
concludes, for $0 < \delta \le 1$ and the first level fixed by the header, that
Sat has polynomial-time steps and decides 3-SAT within $c\cdot 2^{\delta n}$
steps. That machine is turned into a Turing machine for Theorem 2 by
`Exits.threeSat_by_algorithm`.
-/

/-- **Algorithm 1**, deciding form, with the constants of its header: given a
list as Lemma 4 provides for $\varepsilon = \delta/3$, procedure Sat has
polynomial-time steps and decides 3-SAT within $c\cdot 2^{\delta n}$ steps. -/
theorem algorithm1 : Exits.StAlgorithm := by
  exact Exits.stAlgorithm

/-!
## Consequences: Definition 6 and Corollaries 5 and 6 {fold}

Section 7 draws the standard consequences: $s_k = 0$ for every $k \ge 3$, so
ETH and SETH fail (Corollary 5), and counting $k$-SAT is possible in time
$O(2^{\delta n})$, so #ETH fails (Corollary 6). Lean proves both for
Turing machines, by reductions of its own rather than the cited ones.

### Definition 6: sₖ, s∞, ETH and SETH

For $k \ge 1$, $s_k$ is the infimum of the $\delta \ge 0$ for which some
deterministic algorithm decides $k$-SAT on $n$ variables in time
$O(2^{\delta n})$, and $s_\infty = \sup_{k\ge 3} s_k$. ETH is the statement
$s_k > 0$ for all $k \ge 3$, the same as $s_3 > 0$ since $s_k \le s_{k+1}$
and the cited equivalence of Impagliazzo and Paturi; SETH is $s_\infty = 1$
(§7, p. 20).

**In Lean:** `SatK.sTM` ([`proof/statements/KSatStatement.lean`, line 118](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/KSatStatement.lean#L118)),
with Mathlib's Turing machines with finite alphabets, $\lfloor c\cdot 2^{\delta n}\rfloor$
steps for every $n$, formulas as lists with no clause written twice, $n$ in
unary and $k$ slots per clause, and the value $\infty$ when no $\delta$ works;
`PaperSentences.sInfty`, `PaperSentences.ETH` and `PaperSentences.SETH` in
[`proof/statements/PaperSentencesStatement.lean`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PaperSentencesStatement.lean). Note that `MainResults.ETH`
above is defined separately, in the [trusted file](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/MainResults.lean), with the same kind of
machine and code. No claim.

### Corollary 5

$s_k = 0$ for every $k \ge 3$; hence $s_\infty = 0$, and both ETH and SETH are
false (§7, pp. 20–21).

**Idea.** Theorem 2 gives $s_3 = 0$; for this the sparsification need not be
disjoint, since a positive sum still means satisfiable. A theorem of
Impagliazzo, Paturi and Zane (sparsify, then split long clauses into clauses
of three literals with new variables) carries $s_3 = 0$ to every $k \ge 3$.

**In Lean:** the statement is `PaperSentences.CorEth`:
$(\forall k \ge 3,\ s_k = 0) \wedge s_\infty = 0 \wedge \neg\mathrm{ETH} \wedge \neg\mathrm{SETH}$,
which `FromPrinted.SplitSat.ThreeSatStatement`
([`proof/consequences/FromPrinted/SatDefs.lean`, line 114](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SatDefs.lean#L114)) abbreviates. The
cited reduction is not used: for each $k > 3$ Lean builds a machine that
sparsifies, splits long clauses and calls the 3-SAT machine of the decision
form of Theorem 2, and $s_3 = 0$ comes from that deciding machine directly,
not from a positive count.
-/

/-- **Corollary 5**: $s_k = 0$ for every $k \ge 3$, $s_\infty = 0$, and ETH
and SETH are false, for $s_k$ defined with Mathlib's Turing machines. -/
theorem corollary5 : FromPrinted.SplitSat.ThreeSatStatement := by
  exact FromPrinted.SplitSat.eth_and_seth_false

/-!
### Corollary 6

For every $k \ge 3$ and $\delta > 0$ a deterministic algorithm counts the
satisfying assignments of a $k$-CNF on $n$ variables in time $O(2^{\delta n})$;
for $k = 3$, the counting hypothesis #ETH is false (§7, p. 21).

**Idea.** The counting form of sparsification at width $k$ gives few disjoint
formulas with $O(n)$ clauses; a width reduction that forces each new variable
to equal the disjunction it replaces keeps the count; Theorem 2 counts the
results.

**In Lean:** the statement is `PaperSentences.CorCounting`, both halves for
Turing machines on $n$ in unary and $k$ slots per clause, abbreviated by
`FromPrinted.SplitCount.ThreeSatStatement`
([`proof/consequences/FromPrinted/CountDefs.lean`, line 158](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/CountDefs.lean#L158)). At $k = 3$ its
first half is **Theorem 2 as printed**, the counting statement. The proof is
not the printed one: Lean does not pass through a counting Theorem 2; it runs
one search tree at width $k$, splits long clauses at every leaf, and counts
each leaf with procedure Count of Algorithm 1, taking the number of groups
from a level of Algorithm 1 rather than from $e^* = 0$. The cited results of
Dell et al. are replaced by proofs in Lean.
-/

/-- **Corollary 6**: for every $k \ge 3$ and $\delta > 0$ one Turing machine
counts the satisfying assignments of a $k$-CNF on $n$ variables within
$C\cdot 2^{\delta n}$ steps, and #ETH is false. -/
theorem corollary6 : FromPrinted.SplitCount.ThreeSatStatement := by
  exact FromPrinted.SplitCount.countingCorollary

/-!
## The stronger bounds: Appendices A to D {fold}

The appendices prove the Main Theorem. Each is one step here, summarized by its
main theorem. A lets the number of nodes grow with the input; B builds better
pieces with $\rho = 1/\sqrt2$; C makes the sparsification preserve counts; D
bounds the time in the number of variables; Corollary 11 combines A, B and D.
Lean's proof of the Main Theorem follows this route with recorded differences.

### Appendix A: the running time as a function of m and n

**Theorem A.** Abstract Lemma 2 into "pieces with parameters $(\rho, c)$"
(Definition 7): functions $A_i$ that add up to $d\,[x=v][y=u]$ with
$c^{row}_i + c^{col}_i \le 4\rho\lambda + c\log(2\lambda)$ and costs bounded
by $2^{c\lambda}$. From such pieces, with $\alpha' = \log(1/\rho)$ and levels
$K_{\ell+1} = g_\ell^2$, $g_\ell = 2^{3\ell+x_0}K_\ell$: (a)
$\log K_\ell = \Theta(2^\ell)$ and $\tfrac12\rho^\ell \le e_\ell \le 0.85\rho^\ell$;
(b) one algorithm evaluates the $(K_\ell,\lambda)$-cliques of all levels within
$2^{e_\ell K_\ell^2\lambda}(K_\ell(\lambda+B))^{C_0K_\ell^2}$ operations;
(c) $k$-CNFs are counted in time $2^{O(km/(\log m)^{\alpha'})}$, and for fixed
$k$ in time $2^{O(n\log\log n/(\log n)^{\alpha'})}$; (d) 3-SAT is decided in
time $2^{O(n/(\log n)^{\alpha'/10})}$ (pp. 26–29).

**Idea.** Redo Lemma 1 and Proposition 3 with every cost explicit, since $K$
now grows with the input; balance with Hoeffding's inequality (Lemma 8) so
that $g$ exceeds $K$ only by a polylogarithmic factor and one level roughly
squares $K$.

**In Lean:** `FixedWidth.RunningTimesFromPieces`
([`proof/statements/VariablesFixedWidthStatement.lean`, line 94](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/VariablesFixedWidthStatement.lean#L94)), in steps of a
Turing machine. Part (b) and the hypothesis on the pieces measure time by a
string of blank symbols given as a budget, with the tables written out; the
first sentence of (c) allows variables that do not occur but adds $C L^C$ for
the input length $L$; the printed proof of (d) is not formalized, and (d)
follows from a stronger bound (exponent $3/19$). The [index](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/PaperIndex.lean) notes that the
proof of the Main Theorem does not use this statement; it uses a counted form
of (b) (`ExplicitCost.recursionSolves`).
-/

/-- **Appendix A, Theorem A**: what pieces with parameters $(\rho, c)$ give:
the levels, one clique algorithm, the counting bounds of (c) and the decision
bound of (d), in Turing-machine steps. -/
theorem appendixA : FixedWidth.RunningTimesFromPieces := by
  exact FixedWidth.runningTimesFromPieces

/-!
### Appendix B: pieces with ρ = 1/√2

**Theorem B.** There are pieces with parameters $(1/\sqrt2, c)$ for an absolute
constant $c$ (pp. 30–33). With Theorem A this gives the exponent $\tfrac12$ of
$\log m$, the bound in $m$ of the Main Theorem.

**Idea.** The pieces are matrix entries of operators $a[r]$ and $Q_s(a,b)$ on the
polynomial ring $\mathbb{Q}[t_1, t_2, \dots]$, graded by weight (Lemmas 9
and 10). The bits a piece costs are logarithms of sums of partition numbers,
bounded by the Hardy–Ramanujan formula $\log p(E) \approx c\sqrt E$.

**In Lean:** `PiecesCounted.HalfPiecesExist`
([`proof/statements/PiecesCountedStatement.lean`, line 272](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PiecesCountedStatement.lean#L272)). The time clause of
Definition 7 becomes at most $2^{c\lambda}$ steps, each any polynomial-time
function of a state whose size may be exponential in $\lambda$; the pieces meet
it by writing $2^{c\lambda}$ symbols and doing all the work in one step, so on
a Turing machine only $2^{O(\lambda)}$ steps follow, with a larger constant.
The proof of the Main Theorem uses the form that names the functions,
`PiecesCounted.halfPieces`.
-/

/-- **Appendix B, Theorem B**: there are pieces with parameters
$(1/\sqrt 2, c)$ for some constant $c$. -/
theorem appendixB : PiecesCounted.HalfPiecesExist := by
  exact PiecesCounted.halfPiecesExist

/-!
### Appendix C: counting as a function of n (a proof sketch)

**Theorem C.** One deterministic algorithm counts the satisfying assignments of
a 3-CNF on $n \ge 2$ variables in time $2^{O(n/(\log n)^{\alpha/10})}$
(pp. 33–34). The paper gives only a proof sketch.

**Idea.** Calabro's sparsification branches on a set $H$ of literals; carry
along a side set of unit clauses that the algorithm never reads, adding the
negations of $H$ on one branch. The recursion tree is unchanged, so Calabro's
analysis still applies, and every satisfying assignment satisfies exactly one
output. Count each output with Theorem A (c) and add up.

**In Lean:** `PrintedOrder.CountRateFromBoundInN`
([`proof/consequences/PrintedOrder/Defs.lean`, line 140](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Defs.lean#L140)) is Theorem C with
$\alpha = \tfrac12$, so exponent $\tfrac1{20}$, for Turing machines. It is
derived from Theorem D (b) (`ThmCount.stTheorem`), **not along the sketch**.
Lean's own analysis of the changed procedure is used instead in Step 5 of
Appendix D, with thresholds the project takes to be Calabro's but did not
check against the dissertation.
-/

/-- **Appendix C, Theorem C** with $\alpha/10 = 1/20$: one Turing machine counts
the satisfying assignments of a 3-CNF on $n \ge 2$ variables within
$2^{C n/(\log n)^{1/20}}$ steps. -/
theorem appendixC : PrintedOrder.CountRateFromBoundInN := by
  exact PrintedOrder.countRateFromBoundInN

/-!
### Appendix D: the bound in n, and Corollary 11

**Theorem D.** (a) From one algorithm for the $(K_\ell,\lambda)$-cliques of all
levels, with exponents $e_\ell$, one algorithm counts the satisfying
assignments of a $k$-CNF on $n$ variables, for $3 \le k \le (\log n)^{1/4}$, in
time $2^{O(k^2 e n\log(k/e))}$. (b) With the levels of Appendices A and B,
for all $k \ge 1$ and $n \ge 4$, in time $2^{Ck^2 n\log\log n/\sqrt{\log n}}$.
**Corollary 11** runs the algorithms of Theorem A (c) and Theorem D (b) in
alternation and so attains
$\min\{2^{Ckm/\sqrt{\log m}}, 2^{Ck^2 n\log\log n/\sqrt{\log n}}\}$: the Main
Theorem with explicit ranges (pp. 34–40).

**Idea.** The network of §6 has a total that grows with the number of clauses.
Appendix D uses a network whose nodes hold variables: the condition that no
clause is violated is expanded by inclusion–exclusion over sets of violated
clauses, cut off at about $n/\log\Delta$ clauses (Lemma 12), with assignments
violating more removed by sparse parity checks (Lemma 13). Sparsification with
a vanishing $\varepsilon$ (Appendix C) keeps $\log\Delta = O(k\log(k/\varepsilon))$;
for large $k$, trying all assignments is within the bound.

**In Lean:** `CountedRoute.ThmVariablesBHolds`
([`proof/maintheorem/CountedRoute/Defs.lean`, line 152](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/CountedRoute/Defs.lean#L152)) is
`MainTheoremForms.ThmVariablesB`, the second sentence of (b), in steps of a
Turing machine, for formulas in which variables need not occur. It is read off
the chain on the machine of Theorem A (b) with operations counted, which also
gives Corollary 11 (`CountedRoute.corMinHolds`) and the Main Theorem. Step 5
uses Lean's own analysis of the procedure of Appendix C in place of Calabro's
cited results. Theorem D (a) is `ThmVariables.partA`; the [index](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/PaperIndex.lean) notes that the
proof of the Main Theorem does not use that statement, but a form of it for
machines given a padding string.
-/

/-- **Appendix D, Theorem D (b)**: one Turing machine and one constant $C$
count the satisfying assignments of every $k$-CNF on $n \ge 4$ variables,
$k \ge 1$, within $2^{Ck^2 n\log\log n/\sqrt{\log n}}$ steps. -/
theorem appendixD : CountedRoute.ThmVariablesBHolds := by
  exact CountedRoute.thmVariablesBHolds

end EthWalkthrough
