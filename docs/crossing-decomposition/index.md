---
title: Crossing Decomposition for Subquadratic Noncommutative Circuits
---

```{include} ../_generated/provenance/crossing-decomposition.md
```

Let $a_1,\ldots,a_n,b_1,\ldots,b_n$ be noncommuting variables, and consider the polynomial

$$
\mathrm{ID}_n=\sum_{i,j=1}^n a_i b_j a_i b_j.
$$

Direct evaluation uses $O(n^2)$ additions and multiplications.

## Previous bounds

@hrubes2011non connected the complexity of $\mathrm{ID}_n$ with composition of sums of squares. @hrubes2024subquadratic proved that $\mathrm{ID}_n$ can be computed with $O(n^{1.96})$ operations over fields of characteristic different from two. His result also covers symmetric quartics and the row-ordered $4\times n$ permanent (Theorem 3 and Remark 28). His Problem 3 asks whether $\mathrm{ID}_n$ admits subquadratic circuits in characteristic two.

We give circuits of size $O(n^{5/3})$ over every field, including characteristic two. The construction applies more generally to four independent groups of variables, as stated below.

The subexponential 3-SAT algorithms of @openai2026exponential and @anthropic2026algorithm use algebraic decompositions. We combine Anthropic's crossing construction with rectangular extensions of the $\omega\le9/4$ matrix-multiplication bound of @openai2026upper. @uznanski2026rectangular developed the rectangular analysis in characteristic zero, and @lu2026polynomial gave a characteristic-independent shared-leg separation construction. We use the arbitrary-field rectangular bounds stated by @amanov2026multiplying.

## Subquadratic circuits

A noncommutative arithmetic circuit uses addition and ordered multiplication, with intermediate results reused. We count addition and multiplication gates, including multiplication by scalar constants; scalar and variable inputs have zero cost. The constants in the circuit bounds may depend on the field but are uniform over polynomial coefficients.

::::{prf:theorem}
:label: thm-crossing-decomposition-quartics

The polynomial $\Phi_n(a,b,c,d)=\sum_{i,j=1}^n a_i b_j c_i d_j$ has an arithmetic circuit of size $O(n^{5/3})$ over an arbitrary field.

::::

Identifying $c_i=a_i$ and $d_j=b_j$ gives $\mathrm{ID}_n$.

The distinction between tensor rank and arithmetic circuit complexity in four or more modes is studied by @brand2026beyond. The ordinary coefficient tensor of $\Phi_n$ has rank $n^2$, since its flattening across $(a,b)\mid(c,d)$ is $I_{n^2}$. Our circuit construction uses two different cuts of this tensor and computes the resulting linear forms jointly.

A reverse circuit pass computes all left quotients $L_i(\Phi_n)=\sum_j b_jc_id_j$ with linear additional cost, as in the circuit differentiation argument of @chatterjee2023new, Section 4.2. Then $\sum_i a_iL_i(\Phi_n)e_i$ is the five-position crossing.

A polynomial is **symmetric** if every permutation of the variable names leaves it unchanged.

::::{prf:corollary}
:label: cor-crossing-decomposition-quintics

Over every field, every symmetric noncommutative polynomial in $n$ variables of degree at most five has an arithmetic circuit of size $O(n^{5/3})$.

::::

Keeping the variable groups separate gives a row-ordered permanent.

::::{prf:corollary}
:label: cor-crossing-decomposition-permanents

Over every field $F$, the row-ordered rectangular permanent

$$
\operatorname{perm}_{k,n}
=\sum_{\substack{j_1,\ldots,j_k\in[n]\\j_1,\ldots,j_k\text{ distinct}}}
x_{1,j_1}x_{2,j_2}\cdots x_{k,j_k}
$$

has an arithmetic circuit of size $O(n^{5/3})$, uniformly for $0\le k\le5$.

::::

## A finite fermionic Fock-space identity

The crossing construction in Appendix B of @anthropic2026algorithm uses bosonic Fock space, realized as a polynomial algebra with Heisenberg creation and annihilation operators. We use a finite fermionic model: the exterior algebra $\mathcal E_L=\Lambda_{\mathbb Z}(t_0,\ldots,t_{L-1})$, for an integer $L\ge1$. Its basis states $t_I=\prod_{i\in I}t_i$, with increasing indices, have each mode occupied at most once. Exterior multiplication and contraction are its creation and annihilation operators. The classical free-fermion model, including half-integer modes and normal ordering, is described by @kac1993vertex, Section 4.

Give a basis state energy $\mathrm e(I)=\sum_{i\in I}(i+1/2)$, and put $\epsilon_I=(-1)^{|I|(|I|-1)/2}$. Introduce a second colour $u_0,\ldots,u_{L-1}$, with all generators anticommuting. Coefficients $[t_Iu_J]$ place the $t$-generators before the $u$-generators and order each colour increasingly. Define

$$
\begin{aligned}
\theta_m(t,u)
&=\sum_{k=0}^{L-1}\left(\binom{k}{m}t_k+\binom{-k-1}{m}u_k\right),\\
K_\xi(t,u)
&=\xi(\theta_0,\ldots,\theta_{L-1})\prod_{k=0}^{L-1}(1+t_ku_k),\\
M(\xi)_{I,J}
&=\epsilon_J[t_Iu_J]K_\xi(t,u).
\end{aligned}
$$

Here $\binom{-k-1}{m}=(-1)^m\binom{k+m}{m}$, so all coefficients are integral. These are the normal-ordered creation–contraction matrices; normal ordering places creation operators before contractions. Let $M_r(\xi)$ retain exactly the entries with $\mathrm e(I)-\mathrm e(J)=r$, setting the others to zero. Write $\mathcal W_E$ for the span of basis states of energy at most $E$, and $[1]$ for the coefficient of the empty state.

For $h>0$ with $2h\in\mathbb Z$, let $\eta$ be homogeneous of energy $h$ and write $\xi=\sum_w\xi_w$, where $\xi_w$ has energy $0\le w\le h$ and $w-h\in\mathbb Z$. Put $\sigma_h=(-1)^{2h}$ and, for $r=1-h,2-h,\ldots,h$, define

$$
T_{h,r}(\xi)=\sigma_h\sum_w(-1)^{h+r}
\binom{h+w-1}{h+r-1}\xi_w.
$$

The binomial indices are nonnegative integers. Let $\lambda_h(\xi,\eta)=[1]M_{-h}(\xi)\eta$ be the vacuum pairing.

::::{prf:theorem}
:label: thm-crossing-decomposition-finite-identity

For every integer $E\ge0$ with $L\ge E+h$, the identity

$$
\sum_{r=1-h}^{h}\left(
M_{-r}(\eta)M_r(T_{h,r}(\xi))
-\sigma_h M_r(T_{h,r}(\xi))M_{-r}(\eta)
\right)
=\lambda_h(\xi,\eta)\operatorname{Id}
$$

holds on $\mathcal W_E$, with the sum advancing in steps of one.

::::

Integer $h$ gives a sum of commutators; strictly half-integer $h$ gives a sum of anticommutators. Both products pass through states of energy at most $E+h$. The identity is over $\mathbb Z$ and therefore specializes to every commutative coefficient ring.

## Crossing decomposition

Taking matrix entries of the signed identity gives a crossing decomposition across two cuts.

::::{prf:lemma}
:label: lem-crossing-decomposition-integral

Let $Q(T)=\#\{I\subset_{\mathrm{fin}}\mathbb N:\sum_{i\in I}(i+\tfrac12)\le T\}$. For integers $H\ge1$ and $E,n\ge0$ with $Q(H)>2Hn$, there are matrices $A_s,B_s,C_s,D_s\in\mathbb Z^{n\times Q(E)}$, $1\le s\le r$, satisfying

$$
\delta_{ik}\delta_{j\ell}
=\sum_{s=1}^{r}\left((A_s)_{ij}(B_s)_{k\ell}+(C_s)_{i\ell}(D_s)_{kj}\right),
$$

with $r\le2H Q(H+E)$.

::::

The two terms separate the variable groups across the cuts $(a,b)\mid(c,d)$ and $(a,d)\mid(b,c)$. This also fits the partial-transpose rank framework of @rossman2026multi, Section 3: with $(i,j)$ indexing rows and $(k,\ell)$ indexing columns, each first summand has rank at most one, and each second summand has rank at most one after interchanging $j$ and $\ell$. Every nonzero summand is therefore PT-basic, with blocks of sizes $n$ and $Q(E)$.

The capacity condition ensures that one of the $2H$ positive energy levels at most $H$ contains $n$ basis states. An inverse-Pascal substitution gives dual states with pairing $\delta_{ik}$ over $\mathbb Z$; Anthropic's Lemma 10 has normalization $h!\delta_{ik}$. This unit normalization specializes to every field. The action space uses all $Q(E)$ states of energy at most $E$, and intermediate states have energy at most $H+E$.

The four coefficient families of linear forms in $a_i$ and $c_i$ can be computed together in

$$
O\!\left((H+E+1)^3Q(H+E)Q(E)\right)
$$

arithmetic gates. This estimate counts the joint evaluation of linear forms in the inputs $a_i,c_i$. Anthropic's Appendix B constructs numerical coefficient tables; the bound here comes from sparse substitutions on aggregate states and the choice of truncation order. The same strategy has a bosonic version in characteristic zero. The exterior model gives an integral implementation over every field.

The construction also allows unequal alphabet sizes. For $n,N\ge1$ under the same capacity condition, write $\Phi_{n,N}=\sum_{i=1}^n\sum_{j=1}^N a_i b_j c_i d_j$, and put $\Lambda=H+E+1$, $R=Q(H+E)$, $m=Q(E)$, and $B_0=\lceil N/m\rceil$. Batch the second alphabet into $m\times B_0$ arrays. For each mode, four ordered matrix products have shapes $(R,m,B_0)$, $(B_0,m,R)$, $(B_0,R,m)$, and $(m,R,B_0)$. Over any commutative coefficient ring, if exact ordered algorithms for these shapes have total gate cost $G$, including their linear maps, the resulting circuit has size

$$
O\!\left(\Lambda^3(G+Rm+mB_0+1)\right).
$$

The implied constant is absolute. The order of multiplication keeps every resulting word in the order $abcd$. Surplus variables in the last batch are set to zero.

For $N=n$, the cumulative estimate $\log Q(T)=\kappa\sqrt T+o(\sqrt T)$, for a constant $\kappa>0$, allows $H$ and $E$ of order $\log^2n$. Choosing the cutoffs with a small positive capacity slack gives matrix exponents arbitrarily close to $\sqrt{1+\alpha^2}$, $\alpha$, and $1-\alpha$.

The classical algorithm of @strassen1969gaussian already gives a subquadratic bound over every field. Taking $\alpha=1/5$ and partitioning the four matrix products into square blocks gives circuits of size $O(n^{1.982})$.

The sharper rectangular bound

$$
\mathcal Q(A,B,C)=\frac{(AB+AC+BC)^2}{4ABC}
$$

gives $\mathcal Q(\sqrt{1+\alpha^2},\alpha,1-\alpha)=4/3+\sqrt7/8<5/3$ when $\alpha=(4-\sqrt7)/3$. Small positive slack in the energy cutoffs and matrix exponents absorbs the polynomial factors in $H+E$.

Finally, equality patterns of word positions connect the crossings to symmetric polynomials. Delete singleton blocks and merge adjacent occurrences of the same block; each step has an $O(n)$ reconstruction circuit. For at most five positions, the only remaining nonempty patterns are $ABAB$ and $ABABA$. Integer Möbius inversion on set partitions converts sums with permitted coincidences into sums with an exact equality pattern. Every symmetric polynomial in these degrees is a linear combination of finitely many such pattern polynomials. The row-ordered permanent is the pattern in which all position labels are distinct.

## Hurwitz's sum-of-squares problem

Hurwitz's sum-of-squares problem asks how many bilinear squares are needed to represent a product of two sums of squares. Over $\mathbb C$, @hrubes2024subquadratic obtained identities with $O(n^{1.62})$ such squares. The following corollary is a consequence of the crossing decomposition in Appendix B of @anthropic2026algorithm, equations (54)–(56). Choosing the shorter row or column factorization of each piece gives the exponent $\sqrt2$. The fermionic construction gives another derivation of this bound.

::::{prf:corollary}
:label: cor-crossing-decomposition-hurwitz

The product of two $n$-term sums of squares admits an identity

$$
\left(\sum_{i=1}^n a_i^2\right)
\left(\sum_{j=1}^n b_j^2\right)
=\sum_{\nu=1}^s f_\nu(a,b)^2,
$$

where $f_1,\ldots,f_s$ are complex bilinear forms and $s\le n^{\sqrt2+o(1)}$.

::::

The coefficient field matters even at fixed sizes: @zhang2026hurwitz construct an identity with two $12$-term sums and $18$ bilinear squares over $\mathbb Q(i)$, and prove that no such identity exists over any formally real field.

The finite fermionic construction suggests studying crossing decompositions for higher-degree noncommutative polynomials. Understanding patterns such as $ABCABC$, which first occur in degree six, could extend the circuit bounds beyond the cases considered here.

```{literalinclude} ../../lean/Lemmata/FockCircuits/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/crossing-decomposition.md
```
