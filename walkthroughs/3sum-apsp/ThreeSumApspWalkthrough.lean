import ThreeSumApsp.Statements.EndStatement
import ThreeSumApsp.Statements.PaperStatements

/-!
# Truly subquadratic 3SUM and truly subcubic APSP: a guided walkthrough

This notebook walks through the paper *Truly Subquadratic 3SUM and Truly
Subcubic APSP via Triangles in Sparse Lopsided Graphs* by Josh Alman and
Virginia Vassilevska Williams (arXiv:2610.06783v1), and its Lean 4
formalization, the project `3sum-apsp` in the repository
[`anthropics/formal-math`](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp)
at commit `e1a4e65`. Its scope is the five headline claims of the project's
[`EndStatement.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean) and the numbered statements of Sections 1 to 3 of the paper
that they rest on: Theorem 2; Theorem 5, Lemmas 6 to 11 and equations (5) and
(6) of Section 2; and Definition 13, Corollaries 15 and 16 and Theorems 17, 19,
21 and 22 of Section 3. Two statements outside Sections 1 to 3 are needed to
close the argument and appear as one step each: Corollary 26 (Section 4, the
data structure) and Corollary 39 (Section 5, Zero-Weight $k$-Clique), which is
itself one of the five claims.

**What is proved.** The project proves five propositions, stated in the one
file a reader must trust for them, [`EndStatement.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean). That file imports
nothing, not even Mathlib, contains no proof, and defines a small word RAM, what
it means for a problem to be solved within a time bound on it, and five
problems. The five claims say that programs of that machine exist which solve

* Exact Triangle in $O(n^{3-0.0017})$ steps (Theorem 19),
* 3SUM in $O(n^{1.9992})$ steps (Theorem 22),
* the (min,+)-product of two $n \times n$ matrices in $O(n^{2.99942})$ steps (Theorem 22),
* APSP on directed graphs without negative cycles in $O(n^{2.99942})$ steps (Theorem 22),
* Zero-Weight $k$-Clique in $O(n^{k - 0.0017\lfloor k/3 \rfloor})$ steps for every $k \ge 3$ (Corollary 39),

each for integer inputs of absolute value at most $n^\kappa$, for every fixed
$\kappa$. The proofs are in the library folder [`ThreeSumApsp/`](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp) of the project.
The other statements below are propositions of the project's second trusted
file, [`PaperStatements.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean), which imports Mathlib and [`EndStatement.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean);
the project's index [`docs/INDEX.md`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/docs/INDEX.md) maps the paper to them, and its
[`docs/REMARKS.md`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/docs/REMARKS.md) records every difference, which this notebook repeats where
it matters.

**How to read the claims.** Each claim below restates the type of one of the
project's theorems, word for word, and is proved by that theorem with `exact`.
A claim adds nothing to the project: it shows where a statement of the paper
lives in Lean and what Lean actually says. Statements about running time other
than the five claims are explained in prose and cited by name (see the first
section for why).

**Status: unchecked.** The project pins Lean `v4.33.1` and Mathlib `v4.33.1`;
Glitnir supports only Lean `4.35.0`, so Glitnir cannot check this walkthrough,
and no claim below has a checking status. The project and Mathlib were not built
for this walkthrough, so this file has not been compiled either. Only a text
comparison of the claims and the outline with the project's source (the
walkthrough helper's `check`) has been run. The project's [README](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/README.md) describes its
own check: [`scripts/check.sh`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/scripts/check.sh) builds every library, and the tool Comparator
compares the statements with the proofs and their axioms; the [README](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/README.md) records
no run of Comparator.

**Attribution and licence.** The paper is by Josh Alman and Virginia
Vassilevska Williams; its "Acknowledgments and Methodology" says that Claude
found the algorithm of Section 2, that the authors simplified, strengthened and
extended it, and that after the paper was written Anthropic certified its main
results in Lean with an internal research model. The formalization
is Copyright 2026 Anthropic, PBC, released under the Apache License 2.0; see
[`LICENSE`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/LICENSE) and
[`NOTICE`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/NOTICE) in the project. This walkthrough
restates the paper in its own words and changes nothing in the project.

![How the proof fits together](assets/map.svg)

The map shows each statement above the statements its proof uses directly;
`map.html` beside this file is the clickable version, with each statement, its
Lean declarations and links to the paper's pages and the source lines.

## The strategy in one page

**The engine (Section 2).** Let $X$ be an $N \times D$ and $Y$ a $D \times N$
integer matrix with $D$ a small power of $N$ (a *thin* product), and let $W$ be
a set of at most $N^2/\sqrt{D}$ *wanted* positions. Computing each wanted entry
as an inner product costs $N^2\sqrt{D}$; computing all of $XY$ costs at least
$N^2$. Theorem 5 does better than both: $O(N^2 \log^2 D / D^{1/18})$ when
$N \ge D^{18}$. It runs Coppersmith's rectangular multiplication, built from
Schönhage's ten-term identity (Lemma 6) applied recursively at $L = 19m$
levels, but visits only the leaves of the recursion that some wanted entry needs
(Lemma 10), and shows there are few of them (Lemma 11).

**The stronger engine (Section 4).** Corollary 26 turns the same recursion into
a data structure: after $O(N^2/D^{0.063})$ preprocessing, one entry costs
$O(D^{0.437})$.

**From matrices to triangles (Section 3).** Read as a graph, the wanted entries
of a thin 0/1 product count triangles through prescribed pairs of a tripartite
graph whose middle part is small: Lopsided All-Edges Sparse Triangle
(Definition 13). Corollaries 15 and 16 solve it by Theorem 5 and by
Corollary 26.

**Exact Triangle.** Theorem 17 reduces Exact Triangle (is there a triangle of
total weight zero?) deterministically to instances of the lopsided problem, by
hashing the weights modulo a well-chosen small prime. Plugging in Corollary 16
gives Theorem 19: $O(n^{3-0.00175}\log n)$.

**3SUM, (min,+), APSP and $k$-Clique.** Known reductions to Exact Triangle
(Theorem 21, cited) give Theorem 22 for 3SUM, the (min,+)-product and APSP, and
a classical grouping of the parts gives Corollary 39 for Zero-Weight
$k$-Clique.

**Two routes.** The paper states each bound of Theorems 19 and 22 twice: once
by Theorem 5 and Corollary 15, once by Corollary 26 and Corollary 16. The five
claims take the second, smaller bounds, so in Lean they rest on Corollary 26 and
not on Theorem 5. The walkthrough covers both, because the paper's Theorem 19
does.
-/

namespace ThreeSumApspWalkthrough

/-!
## What is claimed: the machine and the five claims {fold}

The five claims say that word-RAM programs exist with the stated bounds; read
the machine first, since "solved in time" means exactly what
`EndStatement.Problem.SolvedInTime` says. Statements about running time other
than the five claims cannot be restated here and are cited by name.

### The machine and "solved in time"

The paper works on "a word RAM with $O(\log n)$-bit words" for inputs of
polynomially bounded integers (Theorem 2, and the start of Section 2).
[`EndStatement.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean) makes this precise in about sixty lines.

* **The machine** (`EndStatement.Instr`, `EndStatement.exec`). Memory cells are
  named by integers and hold words of $W$ bits. There are nine instructions: put
  the constant 1 into a cell; add, subtract or multiply two cells modulo $2^W$;
  load from or store to the cell whose name is the signed value of a word; jump
  if a word is negative; accept; reject. Every instruction is one step; running
  past the end rejects. There is no division, shift or bitwise operation, and no
  constant other than 1.
* **One run** (`EndStatement.Problem.SolvedBy`). The size $n$ stands in cell 0
  and the input numbers after it (`EndStatement.loadWords`); every other cell
  holds 0. The program must halt within $t$ steps, accept exactly on yes
  instances, and leave any required output in the cells right after the input.
* **Solved in time $O(n^r)$** (`EndStatement.Problem.SolvedInTime`). For every
  natural number $\kappa$ there are one program, one slope $b$ and one bound
  $T(n) = O(n^r)$ such that on every instance of every size $n$ (0 included)
  whose numbers have absolute value at most $n^\kappa$, and at every word size
  of at least $b(\lfloor\log_2 n\rfloor + 1)$ bits, the program solves the
  instance within $T(n)$ steps.
* **$O(n^r)$ without real powers** (`EndStatement.BigO`). Core Lean has no
  fractional powers, so for $r = p/q$ the bound reads $T(n)^q \le K n^p$ for
  $n \ge 2$; for example $r = 1.9992 = 2499/1250$.

**Where Lean differs from the paper.** The model is fixed in more detail than
the paper fixes it. The program, $b$ and $T$ are chosen after $\kappa$ and
before the instance, so they cannot depend on the input; the machine is weaker
than the usual word RAM (one constant, no division or shifts), and it is
generous on points that change no exponent: unused cells start at 0 and space is
not charged, the cells a program names in its text need not be addressable by a
word, and $b$ may depend on $\kappa$. The exponent $\kappa$ ranges over all
natural numbers, 0 included, where the paper has $\nu \ge 1$ in Theorem 19 and
Corollary 39. How each problem is written into memory is fixed by
[`EndStatement.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean), not by the paper ([`docs/MACHINE.md`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/docs/MACHINE.md), Part 1, has the
details and the table of layouts).

### Theorem 2

Theorem 2 of the introduction summarizes the results: on the word RAM, for
polynomially bounded integer inputs, deterministic algorithms solve Exact
Triangle in $O(n^{2.9983})$, APSP and the (min,+)-product in $O(n^{2.9995})$,
and 3SUM in $O(n^{1.9992})$; on real inputs, Las Vegas algorithms on a real RAM
reach $n^{1.998}$ and $n^{2.998}$.

In Lean, the four deterministic lines are the proposition
`ThreeSumApsp.WordRam.Items.Theorem_2` of [`PaperStatements.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean), proved by
`ThreeSumApsp.wordRam_theorem_2`; Exact Triangle is in tripartite form there
(`Items.Theorem_2_graphs` has $n$-vertex graphs). The lines on real inputs are
**not proved for any machine**: the machine has no random bits and no real
numbers, and they occur only as the conclusion of a conditional lemma of the
library, `conditional_theorem_35`. The integer half is the same as four of the
five claims below, with the coarser roundings $2.9983$ and $2.9995$.

`wordRam_theorem_2`, and every other `wordRam_` theorem, is not restated as a
claim: the project writes its type as `Items.Theorem_2`, a name it reaches
through `open ThreeSumApsp.WordRam`, and this notebook opens nothing, so the
exact text would not elaborate here. The same holds for Theorem 5, Corollaries
15, 16 and 26, and the `Items` forms of Theorems 19 and 22 and Corollary 39.

### The five claims

The five claims are propositions of [`EndStatement.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean). The project proves
each from the corresponding statement about programs in
[`ThreeSumApsp/Statements/EndStatement.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Statements/EndStatement.lean), by arithmetic on the form of the
bound: those statements have real exponents and logarithmic factors, which the
short form of [`EndStatement.lean`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean) cannot express, and the claims keep only the
rounded exponent. All five take the bounds of the route through Corollary 26.

**Exact Triangle** (`EndStatement.ExactTriangle`) is the complete tripartite
form of Section 3.2: three $n \times n$ integer matrices $w_{AB}$, $w_{BC}$,
$w_{AC}$, and the question whether $w_{AB}(a,b) + w_{BC}(b,c) + w_{AC}(a,c) = 0$
for some $a, b, c$. The claim has $\varepsilon_T = 0.0017$
(`EndStatement.ε_T`): the third bound of Theorem 19, which follows from its
second bound $O(n^{3-0.00175}\log n)$.
-/

/-- **Theorem 19** (first claim): Exact Triangle on three $n \times n$ weight
matrices with entries of absolute value at most $n^\kappa$ is solved in
$O(n^{3-0.0017})$ steps. -/
theorem theorem19 : EndStatement.Theorem_19 := by
  exact ThreeSumApsp.endStatement_theorem_19

/-!
**3SUM** (`EndStatement.ThreeSum`): given $n$ integers, are there three at
three *different positions* that sum to 0? The paper leaves open whether the
positions must differ; Lean requires it. Theorem 22 prints two exponents for
3SUM, $1.99923$ by the route through Theorem 5 and $1.9992$ by the route through
Corollary 26; the claim has the smaller.
-/

/-- **Theorem 22** (second claim): 3SUM on $n$ integers of absolute value at
most $n^\kappa$ is solved in $O(n^{1.9992})$ steps. -/
theorem theorem22ThreeSum : EndStatement.Theorem_22_3SUM := by
  exact ThreeSumApsp.endStatement_theorem_22_3SUM

/-!
**The (min,+)-product** (`EndStatement.MinPlusProduct`): the input is two
$n \times n$ integer matrices $A$, $B$, written row by row; the program must
accept and leave, in the $n^2$ cells after the input, the entries
$\min_k (A_{ik} + B_{kj})$. The claim has $2.99942$, the exponent of the route
through Corollary 26 (the other route gives $2.99949$; Theorem 2 prints
$2.9995$).
-/

/-- **Theorem 22** (third claim): the (min,+)-product of two $n \times n$
integer matrices with entries of absolute value at most $n^\kappa$ is computed
in $O(n^{2.99942})$ steps. -/
theorem theorem22MinPlus : EndStatement.Theorem_22_MinPlus := by
  exact ThreeSumApsp.endStatement_theorem_22_MinPlus

/-!
**APSP** (`EndStatement.APSP`, with walks `EndStatement.Path`): a directed graph
on $n$ vertices whose edges may be missing, given as a 0/1 edge matrix followed
by the weights; an instance carries the promise that no closed walk has negative
weight. For each pair $(i,j)$ the program writes a flag and a distance: flag 1
and the least weight of a walk from $i$ to $j$, or flag 0 if there is none, in
which case the distance cell is free.
-/

/-- **Theorem 22** (fourth claim): APSP on directed graphs with $n$ vertices,
integer weights of absolute value at most $n^\kappa$ and no negative cycle is
solved in $O(n^{2.99942})$ steps. -/
theorem theorem22APSP : EndStatement.Theorem_22_APSP := by
  exact ThreeSumApsp.endStatement_theorem_22_APSP

/-!
**Zero-Weight $k$-Clique** (`EndStatement.ZeroWeightKClique k`): a complete
$k$-partite graph with $n$ vertices per part, given as $k^2$ blocks of
$n \times n$ weights of which only the blocks $i < j$ count; is there one
vertex per part whose $\binom{k}{2}$ edge weights sum to 0? The paper's
Corollary 39 also covers minimum- and maximum-weight cliques; those cases are
stated about programs (`Items.Corollary_39_min_max`) but are not a headline
claim.
-/

/-- **Corollary 39** (fifth claim): for every $k \ge 3$, Zero-Weight
$k$-Clique on $k$ parts of $n$ vertices, with integer weights of absolute value
at most $n^\kappa$, is decided in $O(n^{k - 0.0017\lfloor k/3 \rfloor})$
steps. -/
theorem corollary39 : EndStatement.Corollary_39_ZeroWeight := by
  exact ThreeSumApsp.endStatement_corollary_39_zeroWeight

/-!
## The engine: wanted entries of a thin product (Section 2) {fold}

Theorem 5 computes $|W| \le N^2/\sqrt{D}$ wanted entries of an $N \times D$ by
$D \times N$ product in $O(N^2\log^2 D/D^{1/18})$ time when $N \ge D^{18}$.
Lemmas 6 to 9 set up the recursion and show that it multiplies matrices;
Lemmas 10 and 11, with equations (5) and (6), show that pruning it to the wanted
entries is cheap. In Lean the five claims do not use Theorem 5 itself, but
Section 4's Corollary 26, on which they rest, builds on the same recursion (the
library's Section 4 imports its Lemma 9, the leaf orders and the tiling).

### Theorem 5

**Statement.** Let $D \ge 4$ be a power of four and $N \ge D^{18}$. Given
$X \in \mathbb{Z}^{N \times D}$ and $Y \in \mathbb{Z}^{D \times N}$ with
entries of absolute value $N^{O(1)}$, and a set $W$ of at most $N^2/\sqrt{D}$
positions, the entries $(XY)[I,J]$ for $(I,J) \in W$ can be computed
deterministically in $O(N^2 \log^2 D / D^{1/18})$ time.

**Idea.** Write $D = 4^m$ and take $L = 19m$ levels of recursion. Cut the
product into *tiles*, each one run of the recursion that computes
$\binom{L}{m}$ block products at once (Lemma 9). Compute the *encoding* of each
row band and column band once, and share it among all tiles; equation (6) says
this costs little. In each tile, call only the branches of the recursion that
lead to a wanted entry (Lemma 10), and bound the number of leaves this touches
(Lemma 11): $O(M/D^{1/18})$ for a tile of $M$ entries at the density of $W$.
Each leaf costs $O(L^2) = O(\log^2 D)$ operations.

**In Lean.** `ThreeSumApsp.WordRam.Items.Theorem_5`, proved by
`ThreeSumApsp.wordRam_theorem_5`, is a statement that a program of the machine
exists; it cannot be restated here (see the first section). As a statement of
existence it also follows from Corollary 26, whose bound is smaller on these
inputs; that the algorithm of Section 2 reaches the bound is shown only by the
library's proofs. Of the tiling and the cost analysis nothing is stated beyond
equation (6): the statements below are about a single run of the recursion.

### Schönhage's identity: Lemma 6

**Statement.** Take seven *left* variables $x_1, x_2, x_3, p_{11}, p_{12},
p_{21}, p_{22}$, seven *right* variables $y_1, y_2, y_3, q_{11}, \dots,
q_{22}$, and ten *output* variables $z_{ij}$ ($1 \le i, j \le 3$) and $z_0$.
Let $G = \sum_{i,j\le 3} x_i y_j z_{ij} + \big(\sum_{i,j \le 2} p_{ij}
q_{ij}\big) z_0$: a $3\times 3$ outer product and a four-term inner product on
disjoint variables. Extend the $p$'s and $q$'s to $3 \times 3$ matrices
$\hat p$, $\hat q$ whose columns (of $\hat p$) and rows (of $\hat q$) sum to
zero. Then the ten products
$$\varphi_{P_{ij}}\psi_{P_{ij}}\chi_{P_{ij}} = (x_i + \hat p_{ij})(y_j +
\hat q_{ij})(z_{ij} + z_0), \qquad \varphi_{P_0}\psi_{P_0}\chi_{P_0} =
-(x_1+x_2+x_3)(y_1+y_2+y_3)\,z_0$$
sum to $G + E$, where every monomial of the error
$E = \sum_{i,j}(x_i\hat q_{ij} + \hat p_{ij} y_j + \hat p_{ij}\hat q_{ij})
z_{ij}$ pairs an outer output variable $z_{ij}$ with an inner input variable.

**Idea.** Compare coefficients. Only $P_{ij}$ contributes to $z_{ij}$. In the
coefficient of $z_0$, the products $x_i y_j$ cancel against $P_0$, and the cross
terms vanish because the columns of $\hat p$ and the rows of $\hat q$ sum to
zero. Two features drive everything that follows: $E$ never mixes with $G$
(Lemma 9), and each $z_{ij}$ gets exactly one term, which makes pruning
effective (Lemma 10).

**In Lean.** An identity of integer polynomials in the 24 variables; indices
count from 0 in Lean and from 1 in the paper.
-/

/-- **Lemma 6**: Schönhage's ten products sum to $G + E$. -/
theorem lemma6 : PaperStatements.Lemma_6 := by
  exact PaperStatements.lemma_6

/-!
### The recursion and what it computes: Lemmas 7, 8 and 9

**The recursion.** Index arrays by *strings* of $L$ variables: an array on left
strings has $7^L$ entries, one on output strings $10^L$. $\mathrm{Full}(a, b)$
cuts each array into slices by its first variable, forms for each of the ten
terms $\lambda$ the combinations $A_\lambda = \sum_s \varphi_\lambda(s) a_s$
and $B_\lambda = \sum_t \psi_\lambda(t) b_t$ (the *encoding*), recurses on each
pair, and assembles the ten output slices as the forms $\chi_\lambda$ say (the
*decoding*). Its recursion tree has $10^L$ leaves, one per string $\tau$ of
terms. A leaf $\tau$ *contributes* to an output string $w$ if it takes $P_{ij}$
at every level where $w$ has $z_{ij}$, and anything where $w$ has $z_0$.

**Lemma 7.** At the leaf $\tau$, $\mathrm{Full}$ multiplies two numbers
$\Phi_\tau(a)$ and $\Psi_\tau(b)$ that depend on $a$ alone and on $b$ alone, and
it returns $\mathrm{Mult}(a,b)$, whose entry at $w$ is the sum of these leaf
products over the leaves contributing to $w$ (equation (2)). The proof is
induction on $L$.
-/

/-- **Lemma 7**: at each leaf, `Full` multiplies $\Phi_\tau(a)$ by
$\Psi_\tau(b)$, and it returns $\mathrm{Mult}(a, b)$. -/
theorem lemma7 : PaperStatements.Lemma_7 := by
  exact PaperStatements.lemma_7

/-!
**Lemma 8.** $\mathrm{Mult}(a,b)[w] = \sum_{u,v}\prod_{\ell=1}^{L}
\gamma(u_\ell, v_\ell, w_\ell)\, a[u]\, b[v]$, where $\gamma(s,t,z)$ is the
coefficient of $stz$ in the identity (equation (3)). Contribution is decided
level by level, so a sum over contributing leaves of a product over levels
factors into a product of per-level sums.
-/

/-- **Lemma 8**: $\mathrm{Mult}(a,b)[w]$ is a sum of products of the
per-level coefficients $\gamma$. -/
theorem lemma8 : PaperStatements.Lemma_8 := by
  exact PaperStatements.lemma_8

/-!
**Lemma 9.** Fix $m$ and put $N_0 = 3^{L-m}$, $D = 4^m$. The *inner set* of a
string is the set of levels where it has an inner variable ($p$, $q$ or $z_0$).
Strings with inner set $Q$ of size $m$ index the entries of an
$N_0 \times D$ matrix $X_Q$, a $D \times N_0$ matrix $Y_Q$ and their product.
Lay all $\binom{L}{m}$ pairs $X_Q, Y_Q$ side by side in $a$ and $b$ (zero
elsewhere). Then $\mathrm{Mult}(a,b)[w] = (X_Q Y_Q)[w]$ for every output string
$w$ with inner set $Q$ of size $m$ (equation (4)): one run of $\mathrm{Full}$,
with $10^L$ multiplications, computes all $\binom{L}{m}$ products, and the
error $E$ does no harm.

**Idea.** By Lemma 8 only summands with nonzero $\gamma$ at every level survive.
At a level of $Q$, $w$ has $z_0$, and by Lemma 6 the only monomials with $z_0$
are $p_{ij}q_{ij}z_0$; outside $Q$, the only monomial with $z_{ij}$ and no
inner variable is $x_iy_jz_{ij}$. So exactly the terms of the matrix product
remain, each with coefficient 1.
-/

/-- **Lemma 9** (with equation (4)): one run of the recursion computes all the
products $X_Q Y_Q$. -/
theorem lemma9 : PaperStatements.Lemma_9 := by
  exact PaperStatements.lemma_9

/-!
### Pruning the recursion: Lemma 10

To use $\mathrm{Full}$ for one product $XY$, the paper tiles it: rows of $X$ in
blocks of $N_0$, columns of $Y$ likewise, and $\lfloor\sqrt K\rfloor^2 \le K =
\binom{L}{m}$ block products per tile, each with its own set $Q$. A tile has
$M = K N_0^2$ output entries. Because the leaf numbers $\Phi_\tau(a)$ depend on
$a$ alone (Lemma 7), each band's encoding is computed once and shared by all
tiles. What remains per tile is the decoding, and here the new idea enters:
$\mathrm{Pruned}$ passes to each call only the set $S$ of output strings that
are still wanted from it, and skips calls whose set is empty.

**Lemma 10.** Called at the root with a set $U$ of output strings,
$\mathrm{Pruned}$ returns $\mathrm{Mult}(a,b)$ restricted to $U$, visits
exactly the leaves $\mathrm{Leaves}(U)$ that contribute to some string of $U$,
and passes sets of total size at most $(L+1)\,|\mathrm{Leaves}(U)|$. So its
cost is governed by the size of the *union* of the leaf sets of the wanted
strings, not by the sum of their sizes.

**In Lean.** The second claim carries the hypothesis $0 < L$ or
$U \ne \emptyset$, which the paper omits; it excludes only $L = 0$,
$U = \emptyset$, where the root is a leaf that is visited although
$\mathrm{Leaves}(\emptyset)$ is empty. Lean also returns the zero array for a
skipped call, so that the sum in the decoding always has ten summands; this
changes nothing.
-/

/-- **Lemma 10**: the pruned recursion returns the wanted values, visits
exactly $\mathrm{Leaves}(U)$, and handles sets of total size at most
$(L+1)\,|\mathrm{Leaves}(U)|$. -/
theorem lemma10 : PaperStatements.Lemma_10 := by
  exact PaperStatements.lemma_10

/-!
### Few leaves are needed: equation (5) and Lemma 11

A single output string has $10^m \approx D^{1.66}$ contributing leaves, more
than the $D$ multiplications of an inner product, so the leaves must be shared.
The *private leaf* of $w$ takes $P_0$ at every level of its inner set; the
*order* of a leaf is $m$ minus the number of levels where it takes $P_0$.
Exactly $\alpha_d = \binom{m}{d}9^d$ leaves of order $d$ contribute to a given
string, while the whole tile has $\beta_d = \binom{L}{m-d}9^{L-m+d}$ leaves of
order $d$, and $\beta_0 = M$.

**Equation (5).** With $L = 19m$, $\beta_d/\beta_{d-1} = 9(m-d+1)/(L-m+d)
\le 9m/(18m+1) < 1/2$, so $\beta_d \le 2^{-d}M$. This is where $19$ comes
from: near $L = 10m$ the ratio would be close to 1 and the count would give no
saving.

**In Lean.** `PaperStatements.Eq_5` is the conclusion multiplied out,
$2^d\beta_d \le M$ for $d \le m$; the ratio (stated for every $L \ge m$) and the
two inequalities are the separate statements `PaperStatements.Eq_5_ratio` and
`PaperStatements.Eq_5_bound`.
-/

/-- **Equation (5)**: with $L = 19m$, $2^d\beta_d \le M$ for every
$d \le m$. -/
theorem equation5 : PaperStatements.Eq_5 := by
  exact PaperStatements.eq_5

/-!
**Lemma 11.** For a set $U$ of output strings with inner sets of size $m$,
$|\mathrm{Leaves}(U)| \le \sum_{d=0}^{m}\min\{|U|\alpha_d, \beta_d\}$, and if
$L = 19m$ then $|\mathrm{Leaves}(U)| \le 2^{-m/9}(2^m|U| + 2M)$.

**Idea.** For small orders $d \le m/9$, charge each wanted string its
$\alpha_d$ leaves; for large orders, take all $\beta_d$ leaves, which equation
(5) makes geometrically few. With $|U| = M/\sqrt{D} = M/2^m$ wanted strings the
bound is $3M/D^{1/18}$, a factor $D^{1/18}$ below the $M$ entries of the tile
and far below the $|U| D = M\sqrt{D}$ multiplications of computing the
wanted entries one by one. The bound is
linear in $|U|$, so it does not matter how $W$ spreads over the tiles.

![Lemma 11 for m = 36: the per-order bounds and their minimum](assets/leaf-orders.svg)

*The figure:* $m = 36$, $L = 684$, $|U| = M/2^{36}$. The red curve
$|U|\alpha_d$ rises with $d$, the blue $\beta_d$ falls; the leaves needed are at
most the shaded minimum, which sums to about $0.045\,M$ over all orders, under
the lemma's bound $2^{-4}\cdot 3M = 0.1875\,M$. The two curves cross between
$d = 4$ and $d = 5$; the proof splits at $d = m/9 = 4$, not necessarily at the
crossing.
-/

/-- **Lemma 11**: few leaves contribute to a sparse set of output strings. -/
theorem lemma11 : PaperStatements.Lemma_11 := by
  exact PaperStatements.lemma_11

/-!
### The encodings are affordable: equation (6)

**Equation (6).** If $N \ge D^{18}$ then $10^L \le 2^{-m/9} N N_0$ (with
$L = 19m$). The encodings cost $O(10^L)$ for each of $O(N/N_0)$ bands, so
equation (6) puts their total at $O(2^{-m/9}N^2) = O(N^2/D^{1/18})$, within the
budget. It holds because $10^{19}\cdot 2^{1/9}/3^{18} < 4^{18}$; this and the
padding of the tiling are why Theorem 5 asks for $N \ge D^{18}$.

With Lemmas 9 to 11 and equation (6), Theorem 5 follows: encodings
$O(N^2/D^{1/18})$, pruned recursions $O(L^2)$ per leaf of
$O(2^{-m/9}(2^m|W| + 2\cdot 4N^2))$ leaves, and $O(L)$ bookkeeping per tile,
subset and wanted position.
-/

/-- **Equation (6)**: if $N \ge D^{18}$, then $10^{19m} \le 2^{-m/9} N N_0$. -/
theorem equation6 : PaperStatements.Eq_6 := by
  exact PaperStatements.eq_6

/-!
## The stronger engine: Corollary 26 (Section 4, one step) {fold}

Corollary 26 is the one statement of Section 4 that the five claims use, and it
is summarized here as a single step: after $O(N^2/D^{0.063})$ preprocessing,
any entry of $XY$ costs $O(D^{0.437})$, for $N \ge D^{18}$. It is cited by name,
not restated.

**Statement.** Let $N \ge D^{18}$ and let $X \in \mathbb{Z}^{N\times D}$,
$Y \in \mathbb{Z}^{D \times N}$ have entries of absolute value $N^{O(1)}$. A
deterministic preprocessing in $O(N^2/D^{0.063})$ time and space lets any single
entry $(XY)[I,J]$ be computed in $O(D^{0.437})$ time; hence any set $W$ of
wanted entries costs $O(|W|D^{0.437} + N^2/D^{0.063})$, which is
$O(N^2/D^{0.063})$ when $|W| \le N^2/\sqrt{D}$.

**Idea.** Section 4 keeps the recursion, the tiling and the shared encodings of
Section 2 (Lemmas 7 and 9), with $L = 21m$ in place of $19m$ and a *switching
order* $t = m/9$. The $10^m$ leaves contributing to an output string form a
cube; a query adds up its few leaves of order below $t$ one by one, while the
preprocessing adds the leaves of higher order into partial sums over smaller
cubes (*boxes*), each shared by many output strings (Lemmas 27 to 29,
Theorem 30). The leaves are counted as in the proof of Lemma 11, with the
paper's equation (7), $\beta_d \le \rho^d M$, in place of (5). Corollary 26
is the entry $c = 21$, $q \approx 0.43$ of the paper's Table 2, with the
logarithms absorbed into the exponents. Section 4 has its own statements in the
project; this walkthrough does not go into them.

**In Lean.** `ThreeSumApsp.WordRam.Items.Corollary_26` (the data structure) and
`Items.Corollary_26_wanted` (the last sentence) are statements about programs,
proved by `ThreeSumApsp.wordRam_corollary_26` and
`ThreeSumApsp.wordRam_corollary_26_wanted`. They assume $D \ge 1$, which the
paper leaves out (for $D = 0$ the query bound would be 0 steps). "Space" is read
as the extent of the memory in which the preprocessing leaves the structure:
cells farther from the input are unchanged at its end.

## From matrices to triangles: Definition 13, Corollaries 15 and 16 {fold}

Wanted entries of a thin 0/1 product are the same as triangles through
prescribed pairs of a tripartite graph with a small middle part. Corollary 15
solves this lopsided triangle problem by Theorem 5, Corollary 16 by
Corollary 26; neither can be restated here.

**Definition 13 (Lop-AE-SparseTri$(n, D)$).** A tripartite graph has outer parts
$A$ and $B$ of $n$ vertices each, a middle part $M$ of at most $D$ vertices,
arbitrary edges between $M$ and $A$ and between $M$ and $B$, and a set
$W \subseteq A \times B$ of *query pairs*. For each $(a,b) \in W$, decide
whether $a$ and $b$ have a common neighbour in $M$. With the biadjacency matrices
$X \in \{0,1\}^{n \times D}$ and $Y \in \{0,1\}^{D \times n}$, $(XY)[a,b]$
counts the common neighbours, so the problem asks for the Boolean entries of a
thin product at the wanted positions $W$. Definition 14 is the counting version,
which asks for the integer entries; the five claims need only detection.

In Lean, the graph is `ThreeSumApsp.LopInstance`, the task
`ThreeSumApsp.LopInstance.IsDetectionAnswer`, and the problem as a machine sees
it is `ThreeSumApsp.WordRam.lopDetect`: the two 0/1 matrices and the query pairs
in memory, one output cell per pair.

**Corollary 15.** For $D \ge 4$ a power of four and $n \ge D^{18}$, the problem
and its counting version with $|W| \le n^2/\sqrt{D}$ are solved in
$O(n^2\log^2 D/D^{1/18})$ time (Theorem 5 with $N = n$), and with any $|W|$ in
$O((n^2 + |W|\sqrt{D})\log^2 D/D^{1/18})$ by splitting $W$.

**Corollary 16.** For $n \ge D^{18}$, they are solved in
$O(|W|D^{0.437} + n^2/D^{0.063})$ time (Corollary 26 with $N = n$).

**In Lean.** `ThreeSumApsp.WordRam.Items.Corollary_15` and
`ThreeSumApsp.WordRam.Items.Corollary_16`, proved by
`ThreeSumApsp.wordRam_corollary_15` and `ThreeSumApsp.wordRam_corollary_16`,
say that programs of the machine exist for both versions. Corollary 16 assumes
$D \ge 1$, which the paper omits. As a statement of existence, Corollary 15
also follows from Corollary 16, whose bound is smaller.

## Exact Triangle to lopsided triangles: Theorem 17 {fold}

Exact Triangle with $n$ vertices per part reduces deterministically and
non-adaptively to at most $4ng$ lopsided instances with middle parts of at most
$D$ vertices and at most $n^2/\sqrt{D}$ query pairs each, plus
$O(\nu n^3\log n/g + n^{\omega+o(1)}D^{3/2} + n^2Dg)$ further time. The Lean
statement has everything but the time.

**Exact Triangle.** An instance is a complete tripartite graph on parts $A$,
$B$, $C$ of $n$ vertices with integer edge weights $|w(e)| \le n^\nu$. With
$S(a,b,c) = w(a,b) + w(b,c) + w(a,c)$, a *zero triangle* has $S = 0$; decide
whether one exists.

**Statement.** Let $16 \le D \le n$ and let $g$ be an integer with
$1 \le g \le \sqrt{D}$. Exact Triangle reduces deterministically to at most
$4ng$ instances of Lop-AE-SparseTri$(n, D)$, each with at most $n^2/\sqrt{D}$
query pairs, plus the further time above. All instances are produced before any
oracle call.

**Idea.** Three steps.

1. *Hash modulo a prime.* For every prime $p \in [\sqrt{D}/2, \sqrt{D})$, count
   the triples with $S \equiv 0 \pmod p$ using matrix products over
   $\mathbb{Z}[x]/(x^p - 1)$; pick the prime with the smallest count. A triple
   with $S \ne 0$ is a *false positive* of the few primes dividing $S$, so by
   averaging the chosen prime has $F(p) = O(\nu n^3\log n/\sqrt{D})$ of them.
2. *Build the instances.* Split $C$ into pieces $C_k$ of about $\sqrt{D}/g$
   vertices. For each residue $\varrho$, cut the pairs $(a,b)$ with
   $w(a,b) \equiv \varrho$ into chunks of at most $n^2/\sqrt{D}$ query pairs.
   An instance has the middle part $C_k \times \mathbb{Z}_p$, with
   $a \sim (c,\sigma)$ iff $\sigma \equiv w(a,c) + \varrho$ and
   $(c,\sigma) \sim b$ iff $\sigma \equiv -w(b,c)$. A common neighbour is then
   exactly some $c \in C_k$ with $S(a,b,c) \equiv 0 \pmod p$.
3. *Find witnesses.* For each accepted pair, scan its piece for a $c$ with
   $S = 0$. Every failed scan contains its own false positive, so the scans cost
   $O((F(p)+1)\sqrt{D}/g) = O(\nu n^3\log n/g)$.

![Theorem 17: labels for p = 5](assets/theorem17.svg)

*The figure:* $p = 5$ and a query pair with $w(a,b) = 7$, so $\varrho = 2$.
For $c_1$ ($w(a,c_1) = 4$, $w(b,c_1) = -11$) both labels are 1 and
$S = 7 + 4 - 11 = 0$: a zero triangle. For $c_2$ ($3$ and $0$) both labels are 0
and $S = 10$: a false positive. For $c_3$ ($1$ and $1$) the labels are 3 and 4,
and $S = 9 \not\equiv 0$.

**In Lean.** `PaperStatements.Theorem_17` states the reduction step by step: a
selected prime exists, at most $4ng$ instances, middle parts of at most $D$
vertices, at most $n^2/\sqrt{D}$ query pairs, non-adaptivity (the instances do
not depend on the oracle's answers), and correctness of the search for every
oracle answer and every order of the scans, together with a count of the triples
the scans look at, behind the term $\nu n^3\log n/g$. The running time itself is
not stated: a program of the machine cannot simply be called as a subroutine, so
the time bound is proved only in the library, for programs that call an
arbitrary solver, with Strassen's exponent $\log_2 7$ in place of $\omega$.
$D$ is a natural number, which the bound on the number of chunks uses. The prime
number theorem is replaced by a counting form of Bertrand's postulate
(`exists_le_card_primesInRange`).
-/

/-- **Theorem 17**, everything but the running time: Exact Triangle reduces
deterministically and non-adaptively to at most $4ng$ lopsided instances. -/
theorem theorem17 : PaperStatements.Theorem_17 := by
  exact PaperStatements.theorem_17

/-!
## Exact Triangle in truly subcubic time: Theorem 19 {fold}

Theorem 17 with lopsided instances solved by Corollary 15 gives
$O(n^{3-1/648}\log^2 n)$; with Corollary 16 it gives
$O(n^{3-0.00175}\log n) \le O(n^{3-0.0017})$. The first claim, `theorem19` in
the first section, is the last bound.

**Statement.** For every constant $\nu \ge 1$, Exact Triangle on $n$ vertices
per part with integer weights of absolute value at most $n^\nu$ is solved
deterministically in $O(n^{3-1/648}\log^2 n)$ time using Theorem 5 (via
Corollary 15), and in $O(n^{3-\varepsilon'}\log n) \le O(n^{3-\varepsilon_T})$
time using Corollary 26 (via Corollary 16), where $\varepsilon' = 0.00175$ and
$\varepsilon_T = 0.0017$.

**Idea.** Small instances are solved by brute force. Otherwise apply Theorem 17
and solve every instance by a corollary of Section 3.1. With
$D = \lfloor n^{1/18}\rfloor$ and $g = \lceil D^{0.0315}\rceil$, the
$O(nD^{0.0315})$ instances cost $O(n^2/D^{0.063})$ each by Corollary 16, so
$O(n^3D^{-0.0315})$ together; the scans cost $O(n^3D^{-0.0315}\log n)$;
choosing the prime costs $O(n^{\log_2 7}D^{3/2}) = O(n^{2.9})$ with Strassen's
algorithm; and writing the instances costs $O(n^2D^{1.04})$. Since
$D \ge n^{1/18}/2$, $D^{-0.0315} \le 2n^{-0.00175}$. Remark 20 explains the
choice of $g = D^\eta$: instances cost $n^3D^{\eta-\gamma}$ and scans
$n^3D^{-\eta}$ for a saving $D^\gamma$ per instance, which balance at
$\eta = \gamma/2$. The route through Theorem 5 is the same with
$D$ the largest power of four below $n^{1/18}$, $g = \lceil D^{1/36}\rceil$ and
Corollary 15.

![From a saving per instance to the five exponents](assets/exponents.svg)

*The figure:* how the saving $D^{0.063}$ of Corollary 16 becomes
$\varepsilon' = 0.0315/18 = 0.00175$, and from there the exponents of the other
four claims: $2 - 0.00175/2 = 1.999125 \le 1.9992$ for 3SUM,
$3 - 0.00175/3 = 2.999416\ldots \le 2.99942$ for the (min,+)-product and APSP,
and $k - 0.0017\lfloor k/3\rfloor$ for Zero-Weight $k$-Clique.

**In Lean.** `ThreeSumApsp.WordRam.Items.Theorem_19`, proved by
`ThreeSumApsp.wordRam_theorem_19`, has all three bounds, the first two with their
logarithmic factors. As statements that programs exist, the first and third
follow from the second, so a statement of existence cannot tell the two routes
apart; the library proves each bound by its own route, with its own programs.
The claim `theorem19` is the third bound (by
`WordRam.Items.Theorem_19.rounded` and `SolvedInTime.endStatement`), so it rests
on Corollary 16 and Corollary 26, not on Theorem 5. "Assume $n$ is large" is
made concrete as $n \ge 16^{18}$ (`Theorem19.choice_corollary_26`).

## 3SUM, (min,+)-product and APSP: Theorems 21 and 22 {fold}

Known deterministic reductions from 3SUM, the (min,+)-product and APSP to Exact
Triangle (Theorem 21, cited without proof in the paper) turn Theorem 19 into
Theorem 22. The project proves the cited reductions as programs, and states
their combinatorial content; the second, third and fourth claims are
Theorem 22's bounds by the route through Corollary 26.

### Theorem 21(a): 3SUM to Exact Triangle

**Statement.** 3SUM on $n$ integers of absolute value at most $n^\nu$ reduces
deterministically, in $n^{3/2+o(1)}$ time, to $n^{1/2+o(1)}$ instances of Exact
Triangle with $n^{1/2+o(1)}$ vertices per part and weights of absolute value
$n^{O(1)}$. The paper cites Chan and He [CH20] (3SUM to Convolution-3SUM) and
Vassilevska Williams and Williams [VW13] (Convolution-3SUM to Exact Triangle).

**In Lean.** The project builds the composed reduction explicitly
(`ChanHe.instances`, then triangle templates) and states, in
`PaperStatements.Theorem_21a_threeSum_to_exact`: for $n \ge 2$ and natural
$\kappa$, at most $2t$ templates with $t \le \sqrt{N} + 1$ vertices per part
(where $N$ is the common length of the Convolution-3SUM arrays), a bound on
the number of arrays and on the weights, and that 3SUM has a solution exactly
when one of the triangle instances has a zero triangle. Not stated there: the
running time (it is about a machine), and the forms $n^{1/2+o(1)}$, which follow
from `PaperStatements.Theorem_21a_threeSum_to_convolution` and
`PaperStatements.Theorem_21a_compose` without being combined. The construction
for [CH20] follows that paper's proof with changes listed in [`docs/REMARKS.md`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/docs/REMARKS.md);
the programs for [VW13] are not compared with their source.
-/

/-- **Theorem 21(a)**, its combinatorial content: 3SUM reduces to few Exact
Triangle instances on about $\sqrt{N}$ vertices per part, with correctness. -/
theorem theorem21a : PaperStatements.Theorem_21a_threeSum_to_exact := by
  exact PaperStatements.theorem_21a_threeSum_to_exact

/-!
### Theorem 21(b): (min,+)-product and APSP to Exact Triangle

**Statement.** If a deterministic algorithm solves Exact Triangle on $s$
vertices per part with weights of absolute value at most $cU$ in time $T(s)$,
with $T(s)/s$ nondecreasing, then the (min,+)-product of two $n\times n$ integer
matrices with entries at most $U$ takes $O(n^2T(n^{1/3})\log^2 U)$ time, and
APSP on directed $n$-vertex graphs with weights at most $n^\nu$ and no negative
cycle takes $O(n^2T(n^{1/3})\log^3 n)$ time. The paper cites [VW10, VW18,
VW13]: Negative Triangle reduces to $O(\log U)$ Exact Triangle instances, the
(min,+)-product to Negative Triangle on $n^{1/3}$ vertices per part, and APSP to
$\lceil\log_2 n\rceil$ (min,+)-squarings.

**In Lean.** The implication between running times has no statement, for the
same reason as Theorem 17's time: it is proved in the library for programs over
an arbitrary solver (`minPlus_of_uniform_theorem_21b`). Stated are its
mathematical pieces: `PaperStatements.Theorem_21b_negative_to_exact`, restated
below, says that at most $2\lfloor\log_2 U\rfloor + 6$ re-weightings, with
weights at most $6U$, decide by zero triangles whether there is a negative
triangle; `PaperStatements.Theorem_21b_repeated_squaring`, proved by
`PaperStatements.theorem_21b_repeated_squaring` and not restated (a node has one
claim), says that $\lceil\log_2 n\rceil$ (min,+)-squarings give the distances
when no closed walk is negative; `PaperStatements.Theorem_21b_log_factors` has
the arithmetic of the logarithms, with $U = n^{\kappa+1}$ in both halves.
[VW18, Theorem 4.2] has no mathematical statement; it is a program with a proof.
-/

/-- **Theorem 21(b)**, the step from Negative Triangle to Exact Triangle: at
most $2\lfloor\log_2 U\rfloor + 6$ re-weighted instances decide whether there
is a negative triangle. -/
theorem theorem21b : PaperStatements.Theorem_21b_negative_to_exact := by
  exact PaperStatements.theorem_21b_negative_to_exact

/-!
### Theorem 22

**Statement.** For a constant $\nu$, using Corollary 26 through Theorem 19,
3SUM on $n$ integers of absolute value at most $n^\nu$ is solved
deterministically in $n^{2-\varepsilon'/2+o(1)} \le O(n^{1.9992})$ time, and
the (min,+)-product and APSP (no negative cycles) with entries or weights at
most $n^\nu$ in $\tilde O(n^{3-\varepsilon'/3}) \le O(n^{2.99942})$ time. Using
Theorem 5 instead, the bounds are $n^{2-1/1296+o(1)} \le O(n^{1.99923})$ and
$\tilde O(n^{3-1/1944}) \le O(n^{2.99949})$.

**Idea.** Plug Theorem 19 into Theorem 21. For 3SUM:
$n^{3/2+o(1)} + n^{1/2+o(1)}\cdot(n^{1/2+o(1)})^{3-\varepsilon'}\log n =
n^{2-\varepsilon'/2+o(1)}$, and $2 - 0.000875 = 1.999125$. For the
(min,+)-product and APSP, $T(s) = O(s^{3-\varepsilon'}\log s)$ has $T(s)/s$
nondecreasing, and $n^2(n^{1/3})^{3-\varepsilon'} = n^{3-\varepsilon'/3}$ with
$3 - 0.00175/3 = 2.99941\ldots < 2.99942$.

**In Lean.** `ThreeSumApsp.WordRam.Items.Theorem_22_second`, proved by
`ThreeSumApsp.wordRam_theorem_22_second`, has the bounds of the route through
Corollary 26 (and `Items.Theorem_22_first` those of the route through
Theorem 5); the claims `theorem22ThreeSum`, `theorem22MinPlus` and
`theorem22APSP` of the first section are its first and last two bounds. One
step is added to "plug Theorem 19 into Theorem 21": Theorem 21(b) needs a bound
for all sizes at one bound on the weights, while Theorem 19 bounds weights by a
power of the size. The library derives a uniform form of Theorem 19 for all
sizes and all weight bounds (`exactTriangleUniform_of_explicit`), from the
explicit bound, brute force for small sizes and two closure properties. The
programs give $(\log n)^{O(1)}$ factors where the paper writes $n^{o(1)}$
(`Theorem22.threeSum_polylog`).

## Zero-Weight $k$-Clique: Corollary 39 {fold}

For every $k \ge 3$, a classical grouping turns a $k$-partite instance into
$n^{k-3\lfloor k/3\rfloor}$ Exact Triangle instances on
$N = n^{\lfloor k/3\rfloor}$ vertices per part, and Theorem 19 solves them in
$O(n^{k-0.0017\lfloor k/3\rfloor})$ in all. This is the fifth claim,
`corollary39`.

**Statement.** Let $k \ge 3$ and $\nu \ge 1$ be constants. For a complete
$k$-partite graph with $n$ vertices per part and integer edge weights at most
$n^\nu$, deterministic algorithms decide in
$O(n^{k-\varepsilon_T\lfloor k/3\rfloor})$ time whether some $k$-clique with
one vertex per part has total weight zero (and, in the paper, find a clique of
minimum or maximum weight).

**Idea.** The reduction of Nešetřil and Poljak. Fix one vertex in each of the
$k - 3\lfloor k/3\rfloor$ leftover parts, in all possible ways. Split the
remaining parts into three groups of $\lfloor k/3\rfloor$; the vertices of part
$i$ of a tripartite graph $H$ are the choices of one vertex per part of group
$i$. Give each edge of $H$ the weight of the original edges it accounts for,
so that every original edge is counted on exactly one of the three edges of a
triangle; then the triangles of $H$ are the $k$-cliques through the fixed
vertices, with the same weight. Theorem 19 costs $O(N^{3-\varepsilon'}\log N)$
per graph, and $\varepsilon' > \varepsilon_T$ absorbs the logarithm:
$n^{k-3\lfloor k/3\rfloor}N^{3-\varepsilon_T} =
n^{k-\varepsilon_T\lfloor k/3\rfloor}$.

**In Lean.** `ThreeSumApsp.WordRam.Items.Corollary_39_zero`, proved by
`ThreeSumApsp.wordRam_corollary_39_zero`, applies the reduction, written as a
program that calls an arbitrary solver, to Theorem 19's bound by the route
through Corollary 26 (`zeroClique_of_theorem_19` is the deduction for an
arbitrary meaning of "solved in time $T$"). The minimum- and maximum-weight cases
are `Items.Corollary_39_min_max`, which also uses [VW13, Theorem 3.3] for
maximum-weight triangles; they are not among the five claims.

## What this walkthrough leaves out {fold}

Items of Sections 1 to 3 that the five claims do not rest on, and the
statements outside Sections 1 to 3 beyond the two steps above.

* **Section 1:** Theorems 1, 3 and 4 restate Section 4's matrix results and
  Section 5's hinted Online Matrix-Vector results; Figure 1 is a diagram.
* **Section 2:** equation (1) (Strassen's seven products, stated as
  `PaperStatements.Eq_1`) is recalled for intuition only; Figures 2 to 7 and
  Remark 12. Figures 3, 4 and 6 have statements of their own in the project.
* **Section 3:** Definition 14 (the counting version) is mentioned with
  Definition 13; Remarks 18 and 20 have statements (`Remark_18_block`,
  `Remark_20_balance`, `Remark_20_brute_force`); Remark 23 (3XOR) indicates a
  method without proof and has none.
* **Section 4:** everything but Corollary 26, among them Theorems 24, 25 and 30,
  Lemmas 27 to 29, Corollaries 31 and 32 and Table 2.
* **Section 5:** everything but the zero-weight case of Corollary 39. Of
  Theorems 34 and 35, Lemmas 36 and 37 and Corollary 38 only arithmetic and
  correctness are stated, and their running times are proved for no machine; the
  real-input half of Theorem 2 is among them.

[`docs/INDEX.md`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/docs/INDEX.md) in the project says, item by item, what is stated and where;
[`docs/REMARKS.md`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/docs/REMARKS.md) lists every departure from the printed text.
-/

end ThreeSumApspWalkthrough
