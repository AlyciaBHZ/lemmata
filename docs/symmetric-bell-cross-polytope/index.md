---
title: A three-party Bell polytope that is not a cross-polytope
---

```{include} ../_generated/provenance/symmetric-bell-cross-polytope.md
```

Section V of version 3 of @designolle2023symmetric conjectures that the symmetry projection
of a full-correlation local Bell polytope is a cross-polytope. The case of three
parties and seventeen inputs gives a counterexample. The obstruction is an
exact inequality: a mixed deterministic strategy lies outside the convex hull
of eighteen distinct exposed frequency points.

## The polytope and its symmetries

Inputs are indexed by $0,\ldots,16$. For sign vectors
$a,b,c\in\{-1,1\}^{17}$, write
$$
  d(a,b,c)_{ijk}=a_i b_j c_k,\qquad
  L=\operatorname{conv}\{d(a,b,c):a,b,c\in\{-1,1\}^{17}\}.
$$
Thus $L$ is the full local deterministic polytope.

Let $H$ be the common fixed subspace of the four signed permutation
generators in Eq. (23) of @designolle2023symmetric: exchanging parties,
cycling parties, shifting one input forward and another backward, and
reflecting all inputs simultaneously. Input reduction is antiperiodic:
$e_{x+17}=-e_x$. Let $\Gamma$ be orthogonal projection onto $H$, and set
$K=\Gamma(L)$. These are `symSub`, `Gamma` and `localPolytope` in Lean.

The generators are orthogonal and generate a finite group of signed
permutations. Its Reynolds average is self-adjoint, idempotent and has
range $H$, so it equals $\Gamma$. This relates the projection here to
the symmetry average in the paper; the Lean development defines orthogonal
projection directly.

```{prf:theorem} Nineteen distinct extreme points
:label: thm-symmetric-bell-cross-polytope-extreme

The polytope $K$ has at least nineteen distinct extreme points.
```

```{prf:theorem} A counterexample to the cross-polytope conjecture
:label: thm-symmetric-bell-cross-polytope

There is no affine map from the tensor space $\mathbb R^{17^3}$ to
$\mathbb R^9$ that is injective on $K$ and maps $K$ onto
$$
  C_9=\operatorname{conv}\{\pm e_0,\ldots,\pm e_8\}.
$$
In particular, $K$ is not affinely equivalent to a nine-dimensional
cross-polytope, and the universal conjecture in Section V is false.
```

## Exact projection coordinates

For $t=i+j+k=17q+s$, $0\le s<17$, put
$$
\begin{aligned}
 F_0(i,j,k)&=(-1)^q\mathbf 1_{s=0},\\
 F_r(i,j,k)&=(-1)^q(\mathbf 1_{s=r}-\mathbf 1_{s=17-r})
                  \quad(1\le r\le8).
\end{aligned}
$$
Opposite shifts force a fixed tensor to depend only on the antiperiodic
total input; reflection identifies residue $17-r$ with the negative of
residue $r$. Hence $F_0,\ldots,F_8$ form a basis of $H$.
Their supports are disjoint, and their squared norms are $289$ for $F_0$
and $578$ for every $F_r$ with $r>0$.

Define $C_s$ by the antiperiodic convolution
$$
 \left(\sum_i a_iX^i\right)\left(\sum_j b_jX^j\right)
 \left(\sum_k c_kX^k\right)
 \equiv \sum_{s=0}^{16} C_sX^s \pmod{X^{17}+1}.
$$
The scaled coordinates $Q_r=289(\Gamma d)_{r00}$ satisfy
$$
 Q_0=C_0,\qquad Q_r=\frac{C_r-C_{17-r}}2\ (1\le r\le8),
 \qquad \Gamma d=\frac1{289}\sum_{r=0}^8Q_rF_r .
$$
This coordinate map is injective on $H$.

## The eighteen exposed frequency points

Put $\zeta=\exp(i\pi/17)$ and $R=1/\sin(\pi/34)$.
For $h=1,3,\ldots,17$, let
$$
 A_h(x)=\operatorname{sign}\cos(\pi hx/17),\quad
 v_h=\Gamma d(A_h,A_h,A_h),\quad
 S_h(a)=\sum_{x=0}^{16}a_x\zeta^{hx}.
$$
None of these cosines vanishes.

The hull of $\sum_x a_x\zeta^x$ over all signs is a regular $34$-gon
of circumradius $R$. In a generic supporting direction the selected
signs have at most one change because the phases span less than $\pi$.
A threshold with initial sign $s\in\{-1,1\}$ and cut $k$ has sum
$2s\zeta^k/(\zeta-1)$. Identifying repeated endpoints gives $34$
equally spaced points of modulus $R$, each with a unique sign vector.
Strict convexity of the norm gives the bound and its equality cases.
The Lean support module proves the bound and the threshold equality
characterization directly.

For odd $h<17$, a signed permutation of the inputs gives
$|S_h(a)|\le R$, with equality precisely at the antiperiodic shifts of
$A_h$. For
$$
 (T_ta)_x=(-1)^{\lfloor(x+t)/17\rfloor}a_{(x+t)\bmod17},
$$
one has $S_h(T_tA_h)=R\zeta^{-ht}$.
The functional
$$
 E_h(p)=\sum_{i,j,k=0}^{16}
             \operatorname{Re}(\zeta^{h(i+j+k)})p_{ijk}
$$
is invariant under the four generators, and
$$
 E_h(\Gamma d(a,b,c))
    =\operatorname{Re}(S_h(a)S_h(b)S_h(c))\le R^3 .
$$
Equality forces three sign sums of modulus $R$, with product $R^3$.
Their shifts have total shift zero modulo $34$, so the projection formula
sends every equality strategy to $v_h$. Thus $E_h$ uniquely exposes
$v_h$ in the full polytope $K$.

For $h=17$, the alternating sum has modulus at most $17$, with equality
only for the two alternating sign vectors. The same product argument
exposes $v_{17}$. Negating one party's signs negates a deterministic
tensor, so $K=-K$ and the nine points $-v_h$ are exposed too.

## The mixed-strategy certificate

In input order $0,\ldots,16$, take
$$
\begin{aligned}
 a={}&(1,-1,1,-1,-1,1,-1,1,-1,1,-1,1,-1,-1,1,-1,1),\\
 b={}&(-1,1,-1,1,-1,1,-1,1,1,-1,1,-1,1,-1,1,1,-1),\\
 c={}&(1,-1,1,1,-1,1,-1,1,-1,1,-1,-1,1,-1,1,-1,1).
\end{aligned}
$$
The projection coordinates and a separating functional are
$$
 Q=(-141,133,-109,69,-13,-43,91,-123,139),\qquad
 w=(-15,27,-21,8,59,24,-5,-6,10).
$$
Writing $V_h=289((v_h)_{r00})_{r=0}^8$, exact arithmetic gives:

| $h$ | 1 | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $w\cdot V_h$ | 8295 | -8385 | -8313 | 8383 | 8271 | -8345 | -8169 | -8417 | -7225 |

Hence
$$
 w\cdot Q=8421>8417=\max_h|w\cdot V_h|.
$$
The eighteen signed frequency points are distinct: their first two scaled
coordinates are
$$
 \pm(145,x),\quad
 x\in\{143,127,95,47,-17,-73,-113,-137\},\qquad \pm(289,-289).
$$

```{prf:proof} of [](#thm-symmetric-bell-cross-polytope-extreme) and [](#thm-symmetric-bell-cross-polytope)
:nonumber:

The exposure argument gives eighteen distinct extreme points of $K$.
The mixed deterministic strategy belongs to $K$, while its value under
$w$ puts it outside their convex hull. A finite polytope is the convex
hull of its extreme points, so $K$ has another extreme point. This
proves the first theorem.

An affine map injective on a convex set preserves extreme points in
the image. Such a map would give at least nineteen distinct extreme
points of $C_9$, which has only eighteen. This proves the second theorem.
```

This does not assert that the mixed point itself is extreme or determine
the full vertex set. The paper's separate facet-lifting observation for
odd numbers of parties and even numbers of inputs is not addressed.

This integer-only program reproduces the certificate; the exposure
argument above is needed in addition to the computation.

```{literalinclude} certificate.py
:language: python
```

## Lean statement and provenance

The entry adapts the existing Trureturing
[proof at the published revision](https://github.com/the-omega-institute/trureturing/blob/1e631ab8fffbd5c0de0523af53fc3ecdea3d4a75/D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.lean)
and its
[sign-sum support module](https://github.com/the-omega-institute/trureturing/blob/1e631ab8fffbd5c0de0523af53fc3ecdea3d4a75/D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.lean).
`Statement.lean` defines the signed action, fixed subspace, projection,
local polytope and concrete proposition `Counterexample`.
`Foundation.lean` contains the small extracted helpers, `Support.lean`
the sign-sum and convexity arguments, and `Main.lean` the exposure
argument, integer identities, nineteen extreme points and refutation.
The finite decisions use ordinary `decide`.

```{literalinclude} ../../lean/Lemmata/SymmetricBellCrossPolytope/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/symmetric-bell-cross-polytope.md
```
