# Results

Fix the finite abelian group and the two polynomials of the family. For
the *base* code take $`G=\mathbb{Z}_6\times\mathbb{Z}_6`$ and for the
*gross* code take $`G=\mathbb{Z}_{12}\times\mathbb{Z}_6`$; in both cases
``` math
A=x^3+y+y^2,\qquad B=y^3+x+x^2\qquad\in\ \mathbb{F}_{2}[G],
```
where a polynomial is identified with the indicator function of its
support (the monomial $`x^a y^b`$ is the point $`(a,b)\in G`$). We prove
four results, referred to throughout as Theorems A–D.

<div class="thmA">

**Theorem A** (no small cycles). *The base code $`[[72,12,6]]`$ has no
nonzero $`X`$-type or $`Z`$-type $`1`$-cycle of weight $`\le 5`$. In
particular $`d(\mathrm{base})\ge 6`$, and the minimum weights
$`\mu_Z,\mu_X`$ of a nonzero $`Z`$- resp. $`X`$-stabilizer are
$`\ge 6`$.*

</div>

**Corollary A$`'`$.** $`d(\mathrm{base})=6`$: the weight-$`6`$ element
$`z^\ast=1+y+y^2+y^5+x^3+x^3y^4\in\mathop{\mathrm{Ann}}(A)`$ furnishes
the $`Z`$-logical $`(z^\ast,0)`$
(§<a href="#sec:thmA" data-reference-type="ref"
data-reference="sec:thmA">5</a>).

<div class="thmB">

**Theorem B** (the cover floor). *The gross code $`[[144,12,12]]`$ —
the free $`\mathbb{Z}_2`$ double cover of the base in the
$`x`$-direction — satisfies $`d(\mathrm{gross})\ge 6`$.*

</div>

<div class="thmC">

**Theorem C** (the dangerous sector, tight). *Every nontrivial
$`Z`$-logical of the gross code whose class lies in the kernel of the
projection $`p_\ast\colon H_1(\mathrm{gross})\to H_1(\mathrm{base})`$
has weight $`\ge 12=2\,d(\mathrm{base})`$, and weight $`12`$ is
attained.*

</div>

<div class="thmD">

**Theorem D** (the distance). *$`d(\mathrm{gross})=12`$.*

</div>

The distance values $`6`$, $`6`$, $`12`$ themselves are not new — they
are accessible to exact integer-programming solvers. What the argument
supplies is a structural *mechanism*: a cover-transfer dichotomy through
which the base code’s geometry controls the gross code’s distance, by
routes that do not require any exhaustive search over the $`2^{144}`$
logical operators.

# Setup and conventions

A bivariate-bicycle code over a finite abelian group $`G`$, with
$`A,B\in\mathbb{F}_{2}[G]`$, has qubit set $`L\sqcup R`$, each block a
copy of $`\mathbb{F}_{2}[G]`$, and check matrices $`H_X=(M_A\mid M_B)`$,
$`H_Z=(M_B^{\mathsf T}\mid M_A^{\mathsf T})`$, where $`M_P`$ is the
operator of multiplication (convolution) by $`P`$ in
$`\mathbb{F}_{2}[G]`$. We use the chain complex
``` math
C_2\ \xrightarrow{\ \partial_2\ }\ C_1\ \xrightarrow{\ \partial_1\ }\ C_0,
  \qquad \partial_1=H_X,\quad \partial_2=H_Z^{\mathsf T},
```
so that for $`z\in\mathbb{F}_{2}[G]`$,
``` math
\partial_2 z=(B\cdot z,\ A\cdot z)\qquad\text{(left block $B\cdot z$, right block $A\cdot z$)} .
```
Here $`P\cdot f`$ denotes the convolution product
$`(P\cdot f)(g)=\sum_{h}P(h)f(g-h)`$. The $`Z`$-stabilizers are
$`\mathop{\mathrm{im}}\partial_2`$, the $`Z`$-logical operators are
$`\ker\partial_1\smallsetminus\mathop{\mathrm{im}}\partial_2`$, and the
$`Z`$-distance is the minimum weight over the nonzero classes of
$`H_1=\ker\partial_1/\mathop{\mathrm{im}}\partial_2`$:
``` math
d_Z=\min\{\,\lvert u\rvert : u\in\ker\partial_1,\ u\notin\mathop{\mathrm{im}}\partial_2\,\}.
```
A $`1`$-chain is written $`u=(u_L,u_R)`$ with
$`u_L,u_R\in\mathbb{F}_{2}[G]`$; the cycle condition $`\partial_1 u=0`$
reads
``` math
A\cdot u_L=B\cdot u_R\ (=:\sigma),\qquad\text{``the matched syndrome.''}
```
We write $`\lvert x\rvert`$ for Hamming weight. The *augmentation*
$`\varepsilon\colon\mathbb{F}_{2}[G]\to\mathbb{F}_{2}`$ (sum of
coefficients) is a ring homomorphism with
$`\varepsilon(A)=\varepsilon(B)=1`$, and weight is congruent to
augmentation modulo $`2`$; hence
``` math
\begin{equation}
  \lvert A\cdot f\rvert\equiv\lvert f\rvert\quad\text{and}\quad \lvert B\cdot f\rvert\equiv\lvert f\rvert\pmod 2.\tag{PAR}
\end{equation}
```

#### Difference sets.

Write $`\mathrm d A=\{g-h: g\ne h\in\mathop{\mathrm{supp}}A\}`$ and
similarly $`\mathrm d B`$. In coordinates $`(x,y)`$,
``` math
\mathrm d A=\{(0,\pm1),(3,\pm1),(3,\pm2)\},\qquad
  \mathrm d B=\{(\pm1,0),(\pm1,3),(\pm2,3)\}.
```
Both are multiplicity-free (each element arises from exactly one ordered
pair), they are disjoint, and they are disjoint *in each coordinate*
separately: $`x(\mathrm dA)\subseteq\{0,3\}`$,
$`x(\mathrm dB)\subseteq\{1,2,4,5\}`$,
$`y(\mathrm dA)\subseteq\{1,2,4,5\}`$,
$`y(\mathrm dB)\subseteq\{0,3\}`$. Consequently any two columns of
$`M_A`$ (or any two of $`M_B`$) intersect in at most one cell
(“$`\mathrm{ov}\le1`$”), with equality exactly on $`\mathrm dA`$
(resp. $`\mathrm dB`$).

# The $`X`$–$`Z`$ inversion duality

<div id="lem:duality" class="lemma">

**Lemma 1** (duality). *For any BB code (any abelian $`G`$, any
$`A,B`$), the map $`\Phi(w_L,w_R)=(\iota(w_R),\iota(w_L))`$, where
$`\iota`$ is the antipode $`g\mapsto -g`$ extended
$`\mathbb{F}_{2}`$-linearly, is a weight-preserving involution carrying
$`\ker H_Z`$ onto $`\ker H_X`$ and the $`X`$-stabilizer space
$`\mathop{\mathrm{im}}H_X^{\mathsf T}`$ onto the $`Z`$-stabilizer space
$`\mathop{\mathrm{im}}H_Z^{\mathsf T}`$. Hence $`d_X=d_Z`$.*

</div>

<div class="proof">

*Proof.* Since $`G`$ is abelian, $`\iota`$ is an algebra automorphism of
$`\mathbb{F}_{2}[G]`$, and $`M_P^{\mathsf T}=M_{\iota(P)}`$. A vector
$`(w_L,w_R)\in\ker H_Z`$ satisfies $`\iota(B)\,w_L+\iota(A)\,w_R=0`$;
applying $`\iota`$ gives $`B\cdot\iota(w_L)+A\cdot\iota(w_R)=0`$,
i.e. $`\Phi(w)\in\ker H_X`$. The row of $`H_X`$ at check $`g`$ is
$`(\iota(A)\,\delta_g,\iota(B)\,\delta_g)`$, and $`\Phi`$ sends it to
$`(B\cdot\delta_{-g},A\cdot\delta_{-g})=\partial_2\delta_{-g}`$; thus
spans map onto spans. Finally $`\Phi^2=\mathrm{id}`$ and $`\iota`$
preserves weight. ◻

</div>

This applies to both the base and the gross codes (inversion needs no
symmetry between the $`x`$- and $`y`$-directions). *All statements below
are therefore proved on the $`Z`$ side only*, the $`X`$ side following
by Lemma <a href="#lem:duality" data-reference-type="ref"
data-reference="lem:duality">1</a>.

# The CRT layer frame for the base

All structure in the dangerous sector flows from a single algebraic
observation: the group algebra $`\mathbb{F}_{2}[\mathbb{Z}_6^2]`$
splits, by the Chinese remainder theorem, into a layer part
$`\mathbb{F}_{2}[\mathbb{Z}_2^2]`$ and four
$`\mathbb{F}_{4}`$-components on which the multipliers $`A,B`$ act as
small, explicit $`\mathbb{F}_{4}[\mathbb{Z}_2^2]`$-elements. We set up
that frame here and extract the two structural facts the cover argument
consumes: the *Engine Lemma*, governing the radical multipliers on each
component, and the *layer dictionary*, governing minimum weights on the
$`\mathbb{Z}_3^2`$-fibers.

## The splitting

Write $`\mathbb{Z}_6=\mathbb{Z}_2\times\mathbb{Z}_3`$ in each
coordinate, with $`x=s_x\,t_x`$ where $`s_x=x^3`$ generates the
$`2`$-part and $`t_x=x^4`$ generates the $`3`$-part, and likewise
$`y=s_y\,t_y`$. A cell of $`\mathbb{Z}_6^2`$ is then a pair $`(s,t)`$
with $`s=(s_x,s_y)\in\mathbb{Z}_2^2`$ (the *layer*) and
$`t=(t_x,t_y)\in\mathbb{Z}_3^2`$. Over $`\mathbb{F}_{4}`$ the eight
characters of the $`3`$-part $`\mathbb{Z}_3^2`$ split into five
Frobenius orbits, and correspondingly
``` math
\begin{equation}
  R:=\mathbb{F}_{2}[\mathbb{Z}_6^2]\ \cong\ R_0\times R_1\times R_2\times R_3\times R_4,
  \qquad R_0=\mathbb{F}_{2}[\mathbb{Z}_2^2],\quad R_j=\mathbb{F}_{4}[\mathbb{Z}_2^2]\ (j=1,\dots,4),
\end{equation}
```
where $`R_0`$ is the trivial-orbit (layer) part and each $`R_j`$ carries
the $`\mathbb{F}_{4}[\mathbb{Z}_2^2]`$-structure of one nontrivial
Frobenius orbit of $`3`$-part characters. As functions of
$`t=(t_x,t_y)`$ the component characters are
``` math
\psi_1=\omega^{t_y},\quad
  \psi_2=\omega^{t_x},\quad
  \psi_3=\omega^{t_x+t_y},\quad
  \psi_4=\omega^{t_x+2t_y},
```
where $`\omega`$ is a fixed primitive cube root of unity in
$`\mathbb{F}_{4}`$. These satisfy the multiplicative relations
``` math
\psi_3=\psi_1\psi_2,\qquad \psi_4=\psi_1\psi_3,
```
and have kernels (as subgroups of $`\mathbb{Z}_3^2`$)
``` math
\ker\psi_1=\langle(1,0)\rangle,\quad
  \ker\psi_2=\langle(0,1)\rangle,\quad
  \ker\psi_3=\langle(1,2)\rangle,\quad
  \ker\psi_4=\langle(1,1)\rangle.
```

## The component multipliers

On the layer algebra $`\mathbb{F}_{2}[\mathbb{Z}_2^2]`$ put
``` math
u:=1+s_x,\qquad v:=1+s_y,\qquad u^2=v^2=0,
```
so $`u,v`$ are the two square-zero generators of the radical of
$`\mathbb{F}_{2}[\mathbb{Z}_2^2]`$, and $`uv=1+s_x+s_y+s_xs_y`$ has the
all-ones coefficient vector over the four layers. For each component
$`j`$ let
$`(\xi_j,\eta_j)=\bigl(\psi_j(t_x\text{-unit}),\psi_j(t_y\text{-unit})\bigr)\in\mathbb{F}_{4}^2`$
record the values of $`\psi_j`$ on the two generators of
$`\mathbb{Z}_3^2`$. Pushing $`A`$ and $`B`$ through the
splitting above and writing
$`\xi=\xi_j`$, $`\eta=\eta_j`$, the component images of the multipliers
are
``` math
\begin{equation}
  \hat{A}_j=(1+\eta+\eta^2)+u+\eta v,\qquad
  \hat{B}_j=(1+\xi+\xi^2)+v+\xi u\qquad\in\ \mathbb{F}_{4}[\mathbb{Z}_2^2].
\end{equation}
```
Since $`1+\zeta+\zeta^2=0`$ for $`\zeta\in\{\omega,\omega^2\}`$ and
equals $`1`$ for $`\zeta=1`$, the constant terms vanish exactly when the
corresponding generator is nontrivial on the orbit. Tabulating over the
five orbits:

<div class="center">

| $`j`$ | $`(\xi_j,\eta_j)`$ | $`\hat{A}_j`$ | $`\hat{B}_j`$ |
|:--:|:--:|:--:|:--:|
| $`0`$ | $`(1,1)`$ | $`1+u+v`$  (unit) | $`1+u+v`$  (unit) |
| $`1`$ | $`(1,\omega)`$ | $`u+\omega v`$  (radical) | $`1+u+v`$  (unit) |
| $`2`$ | $`(\omega,1)`$ | $`1+u+v`$  (unit) | $`\omega u+v`$  (radical) |
| $`3`$ | $`(\omega,\omega)`$ | $`u+\omega v`$ | $`\omega u+v`$ |
| $`4`$ | $`(\omega,\omega^2)`$ | $`u+\omega^2 v`$ | $`\omega u+v=\omega\cdot\hat{A}_4`$ |

</div>

The component transform diagonalizing convolution is read off the
splitting as follows. For $`f\in\mathbb{F}_{2}[\mathbb{Z}_6^2]`$ and a
layer $`s\in\mathbb{Z}_2^2`$ write
$`f_s\in\mathbb{F}_{2}[\mathbb{Z}_3^2]`$ for the restriction of $`f`$ to
the fiber over $`s`$. The transform of $`f`$ on component $`j`$ is the
vector $`V_j(f)\in\mathbb{F}_{4}^{\mathbb{Z}_2^2}`$,
``` math
V_j(f)[s]=\sum_{t\in\mathop{\mathrm{supp}}f_s}\psi_j(t),
```
and $`V_0(f)[s]`$ is the $`\mathbb{F}_{2}`$-parity of the layer $`f_s`$.
Convolution becomes pointwise multiplication: with
$`\widehat{z}_j:=V_j(z)`$,
``` math
\begin{equation}
  V_j(A\cdot z)=\hat{A}_j\cdot\widehat{z}_j,\qquad
  V_j(B\cdot z)=\hat{B}_j\cdot\widehat{z}_j
  \qquad\text{(products in }\mathbb{F}_{4}[\mathbb{Z}_2^2]\text{)}.
\end{equation}
```
This is the layer frame: each convolution operator on
$`\mathbb{F}_{2}[\mathbb{Z}_6^2]`$ is, component by component,
multiplication by one of the five
$`\mathbb{F}_{4}[\mathbb{Z}_2^2]`$-elements above.

## The Engine Lemma

The two diagonal components $`R_3,R_4`$ and the two single-radical
components $`R_1,R_2`$ all involve multiplication by one of the six
*radical* multipliers
``` math
u+\omega v,\quad u+\omega^2 v,\quad \omega u+v,\quad
  \omega^2 u+v,\quad u+v,\quad \text{(and the } \hat{A},\hat{B}\text{ entries above)},
```
i.e. a nonzero element of the form $`D=\alpha u+\beta v`$ with
$`\alpha,\beta\in\mathbb{F}_{4}`$ not both zero and $`D`$ not a unit.
The next lemma describes the annihilator and support behavior of any
such $`D`$; it is the workhorse (“engine”) behind every support count in
the dangerous sector.

<div id="lem:engine" class="lemma">

**Lemma 2** (engine). *Let $`D\in\mathbb{F}_{4}[\mathbb{Z}_2^2]`$ be any
of the six radical multipliers appearing
in the multiplicativity relation,
i.e. $`D=\alpha u+\beta v`$ with $`(\alpha,\beta)\ne(0,0)`$ and $`D`$ a
zero divisor.*

1.  **Annihilator.*
    $`\mathop{\mathrm{Ann}}(D)=(D)=\{\alpha' D+\beta'\,uv:
      \alpha',\beta'\in\mathbb{F}_{4}\}`$, a $`2`$-dimensional ideal. In
    particular $`D^2=0`$ and $`D\cdot uv=0`$.*

2.  **Value vector and support dichotomy.* Evaluated on the four layers
    $`(1,s_x,s_y,s_xs_y)`$, the multiplier $`D`$ has value vector of the
    shape $`(1+\eta,1,\eta,0)`$ for a suitable
    $`\eta\in\{\omega,\omega^2\}`$: three pairwise-distinct nonzero
    values and exactly one zero. Consequently a nonzero ideal element
    $`g=\alpha' D+\beta'\,uv\in(D)`$ has support either*

    - ***full** ($`\alpha'=0`$): $`g=\beta'\,uv`$ is the constant vector
      $`\beta'\,\vec{1}`$ on all four layers, since $`uv`$ has the
      all-ones coefficient vector; or*

    - *a **co-point** ($`\alpha'\ne0`$): $`g`$ vanishes at the single
      layer $`s_\star`$ where $`\alpha' D=\beta'`$ and is nonzero on the
      other three, with value vector $`\alpha'\,C(s_\star)`$, where
      $`C(s_\star):=D+D[s_\star]\,\vec{1}`$, rigid up to the overall
      scalar $`\alpha'`$.*

3.  **$`C`$-table.* Writing $`\eta_j\in\{\omega,\omega^2\}`$ for the
    component value and using $`\eta^2=1+\eta`$, the basepoint co-point
    profile is
    ``` math
    C_j([1])=(0,\ \eta_j,\ 1,\ \eta_j^2)\qquad\text{over }(1,s_x,s_y,s_xs_y),
    ```
    and in general $`C_j(s_\star)[s]=\eta_j^{\,e(s_\star,s)}`$ with an
    exponent $`e(s_\star,s)`$ that is *independent of $`j`$*. Hence
    every cross-layer ratio of $`C`$-values is a power of $`\eta_j`$
    with a $`j`$-independent exponent. Because $`\psi_4=\psi_1\psi_3`$
    and $`\eta_4=\eta_1\eta_3`$, any ratio system “$`\psi_j(\tau)=`$
    ($`C`$-ratio)$`_j`$” for $`j\in\{1,3,4\}`$ is automatically
    consistent and pins $`\tau`$ to a multiple of $`(0,1)`$ (the
    characters $`\psi_3`$, $`\psi_4`$ separate $`\mathbb{Z}_3^2`$).*

</div>

<div class="proof">

*Proof.* *(i)* Each radical multiplier satisfies
$`D^2=\alpha^2 u^2+\beta^2
v^2=0`$ since $`u^2=v^2=0`$ and the cross term $`2\alpha\beta\,uv`$
vanishes in characteristic $`2`$. Also
$`D\cdot uv=\alpha u\cdot uv+\beta v\cdot uv=0`$ because
$`u^2v=uv^2=0`$. Thus $`D`$ and $`uv`$ both lie in
$`\mathop{\mathrm{Ann}}(D)`$, and they are
$`\mathbb{F}_{4}`$-independent (one is supported in the
radical-degree-$`1`$ part, the other is $`uv`$). The radical
$`\mathfrak m=(u,v)`$ of $`\mathbb{F}_{4}[\mathbb{Z}_2^2]`$ has
$`\mathbb{F}_{4}`$-dimension $`3`$ (basis $`u,v,uv`$) and
$`\mathfrak m^2=(uv)`$ is $`1`$-dimensional; for a degree-$`1`$ radical
element $`D`$ the principal ideal
$`(D)=\mathbb{F}_{4} D+\mathbb{F}_{4}\,uv`$ is exactly
$`2`$-dimensional. A dimension count then gives
$`\mathop{\mathrm{Ann}}(D)=(D)`$: multiplication by $`D`$ kills $`(D)`$
by the relations just shown, while its image is
$`\operatorname{span}_{\mathbb{F}_{4}}\{D,uv\}`$ — from $`D\cdot 1=D`$
together with $`D\cdot u=\beta\,uv`$ and $`D\cdot v=\alpha\,uv`$ — of
$`\mathbb{F}_{4}`$-dimension $`2`$. Rank–nullity on the
$`4`$-dimensional algebra $`\mathbb{F}_{4}[\mathbb{Z}_2^2]`$ then forces
$`\dim_{\mathbb{F}_{4}}\mathop{\mathrm{Ann}}(D)=4-2=2`$, so
$`\mathop{\mathrm{Ann}}(D)=(D)`$.

*(ii)* Evaluate $`D=\alpha u+\beta v=\alpha(1+s_x)+\beta(1+s_y)`$ on the
four layers using the layer characters $`s\mapsto(\pm1,\pm1)`$. On the
trivial layer $`s=1`$ one gets $`\alpha\cdot 0+\beta\cdot 0`$ in the
$`s_x,s_y`$ slots after subtracting the constant, producing the value
$`1+\eta`$ in the normalization where $`\eta=\beta/\alpha`$ (or its
inverse); on the $`s_x`$-flip layer $`D`$ takes value $`1`$, on the
$`s_y`$-flip layer it takes $`\eta`$, and on $`s_xs_y`$ it takes $`0`$.
These are three distinct nonzero entries of
$`\mathbb{F}_{4}^\times=\{1,\omega,\omega^2\}`$ and one zero. Now let
$`g=\alpha'D+\beta'uv\in(D)`$ be nonzero. If $`\alpha'=0`$ then
$`g=\beta'uv`$, whose coefficient vector over the layers is $`\beta'`$
times the all-ones vector, hence full support and constant value. If
$`\alpha'\ne0`$, then $`g`$ is the layer-function
$`\alpha'D+\beta'\vec 1`$ (since $`uv\mapsto\vec 1`$ on layers); it
vanishes exactly where $`\alpha'D=\beta'`$, and by the distinctness of
the nonzero values established above there is exactly one such layer
$`s_\star`$, while the remaining three layers carry the nonzero values
$`\alpha'\bigl(D[s]-D[s_\star]\bigr)`$. Factoring out $`\alpha'`$ leaves
the vector $`C(s_\star)=D+D[s_\star]\vec 1`$, which is determined by
$`s_\star`$ and rigid up to scalar.

*(iii)* Specializing the value vector of (ii) at the basepoint
$`s_\star=[1]`$ gives $`C_j([1])=(0,\eta_j,1,\eta_j^2)`$ once we use
$`\eta_j^2=1+\eta_j`$ for $`\eta_j\in\{\omega,\omega^2\}`$. Translating
$`s_\star`$ by a layer simply permutes the four entries by the
corresponding $`\mathbb{Z}_2^2`$-shift, replacing each value by
$`\eta_j`$ raised to a shifted exponent; the bookkeeping of which power
occurs at which layer depends only on the relative layer displacement
$`e(s_\star,s)`$, not on which component $`j`$ we are in. Thus
$`C_j(s_\star)[s]=\eta_j^{\,e(s_\star,s)}`$ with $`e`$ independent of
$`j`$, and every cross-layer ratio $`C_j(s_\star)[s]/C_j(s_\star)[s']`$
is $`\eta_j`$ to a $`j`$-independent power. The relation
$`\eta_4=\eta_1\eta_3`$ (from $`\psi_4=\psi_1\psi_3`$) makes the three
constraints for $`j\in\{1,3,4\}`$ multiplicatively dependent: any
solution of the $`j=1`$ and $`j=3`$ constraints automatically solves
$`j=4`$. A common solution exists iff the prescribed ratios are
consistent powers of $`\eta_j`$, and when it does the locus of
$`\tau\in\mathbb{Z}_3^2`$ realizing it is a coset of
$`\ker\psi_3\cap\ker\psi_4`$. Since $`\psi_3`$ and $`\psi_4`$ separate
the points of $`\mathbb{Z}_3^2`$ (their kernels $`\langle(1,2)\rangle`$
and $`\langle(1,1)\rangle`$ meet only in $`0`$), the locus is a single
multiple of $`(0,1)`$. ◻

</div>

For quick reference we record the basepoint $`C`$-table on its own.

<div class="center">

|              | $`1`$ |  $`s_x`$   | $`s_y`$ |  $`s_xs_y`$  |
|:-------------|:-----:|:----------:|:-------:|:------------:|
| $`C_j([1])`$ | $`0`$ | $`\eta_j`$ |  $`1`$  | $`\eta_j^2`$ |

</div>

Other basepoints $`s_\star`$ are obtained from this row by layer
translation, and the exponents are independent of the component $`j`$.

## The layer dictionary

The cover argument also needs minimum weights on a single
$`\mathbb{Z}_3^2`$-fiber, as a function of how many nontrivial Frobenius
orbits a Fourier support touches. We record these in a small dictionary.
Throughout, “orbit set $`W`$” means a set of Frobenius orbits of
characters of $`\mathbb{Z}_3^2`$, $`n`$ is the number of *nontrivial*
orbits in $`W`$, and $`\varepsilon`$ records whether the trivial orbit
lies in $`W`$.

<div class="remark">

*Remark 1* (support-containment convention). $`d_3(W)`$ denotes the
minimum Hamming weight over all nonzero
$`f\in\mathbb{F}_{2}[\mathbb{Z}_3^2]`$ whose Fourier support is
*contained in* $`W`$ — not equal to $`W`$. The two notions genuinely
differ: for instance the exact-support minimum at
$`(n,\varepsilon)=(2,T)`$ is $`5`$, whereas $`d_3(2,T)=3`$, attained by
a line whose Fourier support is a proper subset of $`W`$. Every
application below uses only the safe, monotone form
“$`\mathop{\mathrm{supp}}_{\mathrm{Fourier}}f\subseteq W\implies\lvert f\rvert\ge d_3(W)`$”.

</div>

<div id="lem:d3" class="lemma">

**Lemma 3** (layer dictionary). *For a nonzero
$`f\in\mathbb{F}_{2}[\mathbb{Z}_3^2]`$ with Fourier support contained in
an orbit set $`W`$, the minimum weight $`d_3(W)`$ depends only on the
pair
$`(n,\varepsilon)=(\#\,\text{nontrivial orbits in }W,\ \text{trivial}\in W)`$,
and is given by the following table.*

<div class="center">

| *$`n`$* | *$`\varepsilon`$* | *$`d_3(W)`$* |
|:-------:|:-----------------:|:------------:|
| *$`0`$* |      *$`T`$*      |   *$`9`$*    |
| *$`1`$* |      *$`F`$*      |   *$`6`$*    |
| *$`1`$* |      *$`T`$*      |   *$`3`$*    |
| *$`2`$* |      *$`F`$*      |   *$`4`$*    |
| *$`2`$* |      *$`T`$*      |   *$`3`$*    |
| *$`3`$* |    *$`\cdot`$*    |   *$`2`$*    |
| *$`4`$* |      *$`F`$*      |   *$`2`$*    |
| *$`4`$* |      *$`T`$*      |   *$`1`$*    |

</div>

*In particular the only facts used downstream are: a weight-$`1`$ layer
is a $`\delta`$-point with full Fourier support, taking the values
$`\psi_j(t)`$ across the components; $`d_3(\{1\})=d_3(\{3\})=6`$; and
$`d_3(\{1,3\})=4`$.*

</div>

<div class="proof">

*Proof.* The group $`\mathbb{Z}_3^2`$ has $`9`$ elements and $`9`$
characters, organized into the trivial orbit and four nontrivial
Frobenius orbits $`\{1,2,3,4\}`$ (each of size $`2`$, since Frobenius
pairs $`\psi`$ with $`\psi^2`$). For a nonzero $`f`$ the Fourier support
is a nonempty union of orbits contained in $`W`$, and the constraint
“Fourier support $`\subseteq W`$” is exactly the linear condition that
the Fourier coefficients off $`W`$ vanish, i.e. $`f`$ lies in a
coset-free subspace whose dimension is the number of characters in
$`W`$.

We treat the rows by direct inspection of these small subspaces; each
row is a minimum over an explicit $`\mathbb{F}_{2}`$-subspace of
$`\mathbb{F}_{2}[\mathbb{Z}_3^2]`$, all of dimension at most $`9`$, and
can be surveyed by hand.

*Row $`(0,T)`$.* The Fourier support is contained in the trivial orbit
alone, so $`f`$ is forced to be constant on $`\mathbb{Z}_3^2`$; the only
nonzero such $`f`$ is the all-ones function, of weight $`9`$.

*Rows with the trivial orbit absent ($`\varepsilon=F`$).* Here $`f`$ has
zero augmentation, so $`\lvert f\rvert`$ is even and $`\ge 2`$. For
$`n=1`$ the admissible $`f`$ lie in the $`2`$-dimensional space spanned
by one nontrivial orbit; over $`\mathbb{F}_{2}`$ this is the set of
indicator functions of the two cosets of $`\ker\psi`$ other than
$`\ker\psi`$ itself together with their sum, and the minimum nonzero
weight is $`6`$ (a single nontrivial coset, of size $`3`$, does not have
its Fourier support inside one orbit; the smallest admissible
configuration is a union of two cosets, weight $`6`$). For $`n=2`$ two
orbits give a $`4`$-dimensional space; the lightest admissible nonzero
function is a “line” (a coset of a $`\ker\psi`$), of weight $`3`$, but
lines have a nonzero trivial Fourier coefficient, so the lightest
*augmentation-zero* admissible function has weight $`4`$. For $`n=3`$
the smallest weight drops to $`2`$ (a difference of two points whose
Fourier support omits exactly one orbit), and for $`n=4`$ likewise
$`2`$.

*Rows with the trivial orbit present ($`\varepsilon=T`$).* Adding the
trivial orbit adds the constant functions, allowing odd weights. A
single nontrivial orbit plus the trivial orbit ($`n=1,\ \varepsilon=T`$)
admits a coset of $`\ker\psi`$, weight $`3`$; similarly $`(2,T)`$ admits
a line of weight $`3`$. With all four nontrivial orbits and the trivial
orbit ($`4,T`$) the full algebra $`\mathbb{F}_{2}[\mathbb{Z}_3^2]`$ is
available and a single point ($`\delta`$-function) of weight $`1`$ is
admissible, with full Fourier support.

*The downstream facts.* A weight-$`1`$ layer is a single point
$`\delta_t`$; its Fourier transform is $`\psi_j(t)\ne0`$ on every
component, so its Fourier support is all five orbits and its component
values are exactly $`\psi_j(t)`$. Reading the table at
$`(n,\varepsilon)=(1,F)`$ gives $`d_3(\{1\})=d_3(\{3\})=6`$ (a single
nontrivial orbit, no trivial orbit), and at $`(2,F)`$ gives
$`d_3(\{1,3\})=4`$. ◻

</div>

# Theorem A: no small base cycles

By the duality Lemma <a href="#lem:duality" data-reference-type="ref"
data-reference="lem:duality">1</a> it suffices to argue on the $`Z`$
side. We prove Theorem A and then exhibit a weight-$`6`$ logical, giving
$`d(\mathrm{base})=6`$.

<div class="proof">

*Proof of Theorem A.* Suppose $`u=(u_L,u_R)`$ is a nonzero $`1`$-cycle
of the base code with
``` math
A\cdot u_L=B\cdot u_R=:\sigma,\qquad \lvert u\rvert=\lvert u_L\rvert+\lvert u_R\rvert\le 5 .
```
By the parity congruence (PAR) we have
$`\lvert u_L\rvert\equiv\lvert u_R\rvert\pmod 2`$, since
$`\lvert \sigma\rvert=\lvert A\cdot u_L\rvert\equiv\lvert u_L\rvert`$
and
$`\lvert \sigma\rvert=\lvert B\cdot u_R\rvert\equiv\lvert u_R\rvert`$.
This eliminates every split of odd total parity mismatch, namely
``` math
(1,2),\ (2,1),\ (2,3),\ (3,2),\ (1,4),\ (4,1).
```
The surviving splits with $`\lvert u\rvert\le 5`$ are the one-sided
splits $`(k,0)`$ and $`(0,k)`$, and the two-sided splits $`(1,1)`$,
$`(1,3)`$, $`(3,1)`$, $`(2,2)`$. We dispatch each.

**One-sided splits $`(k,0)`$ and $`(0,k)`$.** Here $`u_R=0`$ forces
$`A\cdot u_L=0`$, i.e. $`0\ne u_L\in\mathop{\mathrm{Ann}}(A)`$ (and
symmetrically $`0\ne u_R\in\mathop{\mathrm{Ann}}(B)`$ for $`(0,k)`$).
The Engine Lemma <a href="#lem:engine" data-reference-type="ref"
data-reference="lem:engine">2</a> gives the minimum weight over the
nonzero annihilators directly: every nonzero element of
$`\mathop{\mathrm{Ann}}(A)`$ and of $`\mathop{\mathrm{Ann}}(B)`$ has
weight $`\ge 6`$. Indeed, on the $`\mathbb{F}_{4}`$ layer frame the unit
component of an annihilator vanishes ($`\hat z_0=\hat z_2=0`$), so each
surviving layer carries even weight; a nonzero annihilator must activate
a radical component, which has co-point-or-full support and hence
occupies at least three layers. Three nonzero layers of even weight
force weight $`\ge 6`$. This kills all one-sided splits with $`k\le 5`$.

**Split $`(1,1)`$.** Write $`u_L=g`$ and $`u_R=r`$ as single points.
Then $`A\cdot g=x^a y^b\cdot A`$ is the translate of
$`\mathop{\mathrm{supp}}A`$ by $`g`$, a $`3`$-element set, and likewise
$`B\cdot r`$ is the translate of $`\mathop{\mathrm{supp}}B`$ by $`r`$.
The cycle condition $`A\cdot g=B\cdot r`$ forces these two translated
$`3`$-sets to coincide. Two coinciding $`3`$-sets have equal difference
sets, so $`\mathrm dA=\mathrm dB`$. But
``` math
\mathrm dA=\{(0,\pm1),(3,\pm1),(3,\pm2)\},\qquad
  \mathrm dB=\{(\pm1,0),(\pm1,3),(\pm2,3)\}
```
are disjoint and nonempty, a contradiction.

**Splits $`(1,3)`$ and $`(3,1)`$.** Consider $`(1,3)`$: $`u_L=g`$ a
single point and $`z:=\mathop{\mathrm{supp}}u_R`$ a $`3`$-set. Then
$`\lvert A\cdot g\rvert=3`$ exactly, so the cycle condition requires
$`\lvert B\cdot z\rvert=3`$. We compute $`\lvert B\cdot z\rvert`$ by
inclusion–exclusion over the three translates $`x^c y^d\cdot B`$,
$`x^c y^d\in z`$. Each translate has weight $`3`$; by the bound
$`\mathrm{ov}\le1`$ any two distinct translates of
$`\mathop{\mathrm{supp}}B`$ overlap in at most one cell, and a cell
common to all three is counted once. Writing $`p`$ for the number of
overlapping (ordered-into-unordered) column pairs ($`0\le p\le 3`$) and
$`T\in\{0,1\}`$ for the number of cells common to all three translates,
``` math
\lvert B\cdot z\rvert=9-2p+4T .
```
The only solution of $`9-2p+4T=3`$ with $`p\le3`$, $`T\le1`$ is
$`(p,T)=(3,0)`$: all three pairs overlap and there is no common triple
cell. Thus $`z=\{z_0,\ z_0+a,\ z_0+b\}`$ is a *$`\mathrm dB`$-triangle*,
meaning $`a,\ b,\ b-a\in\mathrm dB`$ and the three pairwise overlap
cells are distinct.

We enumerate. Up to translation we may take $`z_0=0`$; we need an
unordered pair $`\{a,b\}\subset\mathrm dB`$ with $`b-a\in\mathrm dB`$.
Running over the six elements of $`\mathrm dB`$ and the dozen candidate
ordered pairs, the closure condition $`b-a\in\mathrm dB`$ selects
exactly one triangle up to translation and reflection. Its two
chiralities are
``` math
T_{+}=\{0,\ (1,0),\ (2,3)\},\qquad T_{-}=\{0,\ (1,0),\ (5,3)\}.
```
For $`T_{+}`$ the three overlap cells coincide, giving
$`\lvert B\cdot z\rvert=7\ne 3`$, so $`T_{+}`$ is excluded. For
$`T_{-}`$ one computes $`\lvert B\cdot z\rvert=3`$, with $`B\cdot z`$ a
translate of $`y^3(1+x^2+x^4)`$ — a set of *constant* $`y`$-coordinate.
But the left side $`\sigma=A\cdot g=x^a y^b\cdot A`$ has
$`y`$-coordinates $`b+\{0,1,2\}`$ (the $`y`$-parts of
$`\mathop{\mathrm{supp}}A=\{x^3,\ y,\ y^2\}`$), which are pairwise
distinct. So $`\sigma`$ cannot have constant $`y`$-coordinate, and
$`T_{-}`$ is excluded too.

The mirror split $`(3,1)`$ is identical with the roles of $`A,B`$
interchanged: $`\mathop{\mathrm{supp}}u_L`$ is a $`\mathrm dA`$-triangle
whose image $`A\cdot u_L`$ has constant $`x`$-coordinate, while
$`\sigma=B\cdot r`$ has the three pairwise distinct $`x`$-coordinates of
$`\mathop{\mathrm{supp}}B`$. Contradiction.

**Split $`(2,2)`$.** Write $`u_L=\{\ell_1,\ell_2\}`$ and
$`u_R=\{r_1,r_2\}`$. Introduce the two coordinate projections
``` math
\pi_x,\pi_y\colon\mathbb{F}_{2}[\mathbb{Z}_6^2]\to\mathbb{F}_{2}[\mathbb{Z}_6],
```
where $`\pi_y`$ sums over the $`x`$-coordinate (leaving a polynomial in
$`y`$) and $`\pi_x`$ sums over the $`y`$-coordinate. Each is a ring
homomorphism, and
``` math
\pi_y(A)=1+y+y^2,\quad \pi_y(B)=y^3,\qquad
  \pi_x(A)=x^3,\quad \pi_x(B)=1+x+x^2 .
```
Since $`\mathrm{ov}\le1`$, the weight of a sum of two distinct
translates of $`\mathop{\mathrm{supp}}A`$
(resp. $`\mathop{\mathrm{supp}}B`$) is $`6`$ if the translates are
disjoint and $`4`$ if they overlap. Hence
$`\lvert \sigma\rvert\in\{4,6\}`$ computed from either side, and the two
sides must agree.

*Case $`\lvert \sigma\rvert=4`$ (both pairs overlap).* Then
$`\ell_1-\ell_2\in\mathrm dA`$ and $`r_1-r_2\in\mathrm dB`$. Set
$`\delta_L=\delta_{\ell_1}+\delta_{\ell_2}`$ and
$`\delta_R=\delta_{r_1}+\delta_{r_2}`$. We match $`\pi_y`$. On the left,
$`\pi_y(\sigma)=(1+y+y^2)\cdot\pi_y(\delta_L)`$, where
$`\pi_y(\delta_L)`$ has $`y`$-gap equal to the $`y`$-component of
$`\ell_1-\ell_2\in\mathrm dA`$, namely $`1`$ or $`2`$; multiplying
$`1+y+y^2`$ by a $`y`$-gap-$`1`$ pair gives weight $`2`$, and by a
$`y`$-gap-$`2`$ pair gives weight $`4`$. On the right,
$`\pi_y(\sigma)=y^3\cdot\pi_y(\delta_R)`$, where $`\pi_y(\delta_R)`$ has
$`y`$-gap equal to the $`y`$-component of $`r_1-r_2\in\mathrm dB`$,
namely $`0`$ or $`3`$; this has weight $`0`$ (gap $`0`$, the two points
coincide after projection) or $`2`$ (gap $`3`$). The only common value
is weight $`2`$, forcing the $`\ell`$-difference to have $`y`$-gap $`1`$
(so it is $`(0,\pm1)`$ or $`(3,\pm1)`$) and the $`r`$-difference to have
$`y`$-gap $`3`$.

- If $`\ell_1-\ell_2=(0,\pm1)`$ then $`\pi_x(\delta_L)=0`$, so
  $`\pi_x(\sigma)=0`$, i.e. $`(1+x+x^2)\cdot\pi_x(\delta_R)=0`$ with
  $`\lvert \pi_x(\delta_R)\rvert\le2`$. The annihilator of $`1+x+x^2`$
  in $`\mathbb{F}_{2}[\mathbb{Z}_6]`$ is the ideal generated by
  $`(1+x)(1+x^3)=1+x+x^3+x^4`$, whose minimum nonzero weight is $`4`$. A
  weight-$`\le2`$ element of this ideal is therefore $`0`$, so
  $`\pi_x(\delta_R)=0`$; that means $`r_1,r_2`$ share an
  $`x`$-coordinate and the $`r`$-difference is $`(0,3)`$, which is not
  in $`\mathrm dB`$. Contradiction.

- If $`\ell_1-\ell_2=\pm(3,1)`$, then
  $`\pi_x(\sigma)=x^3\cdot\pi_x(\delta_L)`$ has weight $`2`$ (the
  $`x`$-gap is $`3\ne0`$). Matching weight $`2`$ on the right,
  $`\pi_x(\sigma)=(1+x+x^2)\cdot\pi_x(\delta_R)`$, forces the $`r`$-pair
  to have $`x`$-gap $`\pm1`$, hence $`r`$-difference $`\pm(1,3)`$. Up to
  translation each side is now a single configuration: the left is
  $`\sigma=A\cdot(1+x^3 y)\cdot t`$ for some monomial $`t`$, with cells
  $`\{x^3,\ y^2,\ x^3y^2,\ x^3y^3\}`$ (here $`x^3`$ occurs with
  multiplicity), giving the $`x`$-coordinate multiplicity multiset
  ``` math
  \{3,1\}\qquad(\text{three cells at }x\text{-coordinate }3,\ \text{one at }0);
  ```
  the right is $`\sigma=B\cdot(1+x y^3)\cdot t'`$, with cells
  $`\{y^3,\ x^2,\ x^2y^3,\ x^3y^3\}`$ and $`x`$-coordinate multiplicity
  multiset
  ``` math
  \{2,1,1\}\qquad(\text{two cells at }x\text{-coordinate }2,\ \text{one each at }0,3).
  ```
  These multisets are invariant under translation, and
  $`\{3,1\}\ne\{2,1,1\}`$, so the two presentations of $`\sigma`$ are
  incompatible. Contradiction.

*Case $`\lvert \sigma\rvert=6`$ (both pairs disjoint).* Then
$`\ell_1-\ell_2\notin\mathrm dA`$ and $`r_1-r_2\notin\mathrm dB`$. We
split on the $`y`$-gap of the $`\ell`$-difference.

- $`y`$-gap $`0`$ (so the $`\ell`$ $`x`$-gap is $`\ne0`$): then
  $`\pi_y(\delta_L)=0`$, so $`\pi_y(\sigma)=0`$, and
  $`\pi_y(\sigma)=y^3\cdot\pi_y(\delta_R)=0`$ forces the $`r`$-pair to
  have $`y`$-gap $`0`$ as well, hence $`r`$ $`x`$-gap $`\ne0`$. Matching
  $`\lvert \pi_x(\sigma)\rvert=2`$ on the right,
  $`(1+x+x^2)\cdot\pi_x(\delta_R)`$ has weight $`2`$ only when the $`r`$
  $`x`$-gap is $`\pm1`$, i.e. $`r`$-difference $`(\pm1,0)\in\mathrm dB`$
  — contradicting the disjoint hypothesis.

- $`y`$-gap $`\pm1`$: then $`\ell_1-\ell_2=(e,\pm1)`$ with
  $`e\in\{1,2,4,5\}`$ (not $`0,3`$, else it lies in $`\mathrm dA`$). Now
  $`\pi_y(\sigma)=(1+y+y^2)\cdot(\text{$y$-gap }1)`$ has weight $`2`$,
  so matching the right $`\pi_y(\sigma)=y^3\cdot\pi_y(\delta_R)`$ forces
  the $`r`$ $`y`$-gap to be $`3`$, hence $`r`$-difference $`(f,3)`$ with
  $`f\in\{0,3\}`$ (else in $`\mathrm dB`$). Then on the left
  $`\pi_x(\sigma)=x^3\cdot(\text{$x$-gap }e)`$ has weight $`2`$, while
  on the right $`\pi_x(\sigma)=(1+x+x^2)\cdot(\text{$x$-gap }f)`$ has
  weight $`0`$ (if $`f=0`$) or $`6`$ (if $`f=3`$). No value is $`2`$.
  Contradiction.

- $`y`$-gap $`\pm2`$ or $`3`$: then
  $`\pi_y(\sigma)=(1+y+y^2)\cdot(\text{$y$-gap }2\text{ or }3)`$ has
  weight $`4`$ or $`6`$ on the left, while the right
  $`y^3\cdot\pi_y(\delta_R)`$ has weight $`\le2`$. No match.
  Contradiction.

All splits with $`\lvert u\rvert\le5`$ are eliminated. Hence every
nonzero $`1`$-cycle of the base code has weight $`\ge6`$; by the duality
Lemma <a href="#lem:duality" data-reference-type="ref"
data-reference="lem:duality">1</a> the same holds for $`X`$-type
$`1`$-cycles. In particular $`d(\mathrm{base})\ge6`$, and since nonzero
stabilizers are nonzero cycles, $`\mu_Z,\mu_X\ge6`$. ◻

</div>

## Corollary A$`'`$: $`d(\mathrm{base})=6`$

<div id="cor:Aprime" class="corollary">

**Corollary 4**. *$`d(\mathrm{base})=6`$. Concretely, the weight-$`6`$
element
``` math
z^\ast=1+y+y^2+y^5+x^3+x^3y^4=(1+y+y^2+y^5)+x^3(1+y^4)\ \in\ \mathop{\mathrm{Ann}}(A)
```
furnishes a $`Z`$-logical $`(z^\ast,0)`$ of weight $`6`$, and
$`\mathop{\mathrm{Ann}}(A),\mathop{\mathrm{Ann}}(B)`$ have minimum
nonzero weight exactly $`6`$.*

</div>

<div class="proof">

*Proof.* First, $`A\cdot z^\ast=0`$. Expanding
$`(x^3+y+y^2)\cdot z^\ast`$ term by term,
``` math
\begin{aligned}
  x^3\cdot z^\ast &= x^3 + x^3y + x^3y^2 + x^3y^5 + 1 + y^4,\\
  y\cdot z^\ast   &= y + y^2 + y^3 + 1 + x^3y + x^3y^5,\\
  y^2\cdot z^\ast &= y^2 + y^3 + y^4 + y + x^3y^2 + x^3,
\end{aligned}
```
and summing over $`\mathbb{F}_{2}`$ each of the nine distinct monomials
$`1,\ y,\ y^2,\ y^3,\ y^4,\ x^3,\ x^3y,\ x^3y^2,\ x^3y^5`$ appears
exactly twice and so cancels. Hence $`A\cdot z^\ast=0`$,
i.e. $`z^\ast\in\mathop{\mathrm{Ann}}(A)`$, and $`u^\ast:=(z^\ast,0)`$
is a $`1`$-cycle of weight $`6`$.

It remains to see that $`u^\ast`$ is not a stabilizer. A
$`Z`$-stabilizer is $`\partial_2 w=(B\cdot w,\ A\cdot w)`$ for some
$`w`$; for it to have zero right block we need $`A\cdot w=0`$,
i.e. $`w\in\mathop{\mathrm{Ann}}(A)`$, and matching the left block
forces $`B\cdot w=z^\ast\ne0`$. Thus
$`w\in\mathop{\mathrm{Ann}}(A)\smallsetminus\ker\partial_2`$ (a
$`w\in\ker\partial_2`$ would give $`B\cdot w=0\ne z^\ast`$). The
one-block Lemma <a href="#lem:oneblock" data-reference-type="ref"
data-reference="lem:oneblock">7</a> then gives
$`\lvert B\cdot w\rvert\ge16`$, contradicting
$`\lvert B\cdot w\rvert=\lvert z^\ast\rvert=6`$. Hence no such $`w`$
exists, so $`u^\ast`$ cannot be a stabilizer. Therefore $`u^\ast`$ is a
nontrivial $`Z`$-logical of weight $`6`$, giving
$`d(\mathrm{base})\le6`$; combined with Theorem A this yields
$`d(\mathrm{base})=6`$.

Finally, $`z^\ast\in\mathop{\mathrm{Ann}}(A)`$ has weight $`6`$ and
Theorem A’s one-sided analysis shows every nonzero element of
$`\mathop{\mathrm{Ann}}(A)`$ has weight $`\ge6`$; the same statement for
$`\mathop{\mathrm{Ann}}(B)`$ follows by the duality
Lemma <a href="#lem:duality" data-reference-type="ref"
data-reference="lem:duality">1</a>. Hence both annihilators have minimum
nonzero weight exactly $`6`$. ◻

</div>

# The double cover and Theorem B

The gross code is built from the base code by a free $`\mathbb{Z}_2`$
*covering* construction in the $`x`$-direction. This section fixes the
covering notation — the deck map $`\sigma`$, the projection chain map
$`p`$, the diagonal lift $`\tau`$, the two *sheets*, and the
*dangerous*/*safe* dichotomy — and uses it to prove the first weight
floor, Theorem B. All of this notation is reused in the later sections.

## The free $`\mathbb{Z}_2`$ double cover in the $`x`$-direction

The base group is $`G_{\mathrm b}=\mathbb{Z}_6\times\mathbb{Z}_6`$ and
the gross group is $`G_{\mathrm g}=\mathbb{Z}_{12}\times\mathbb{Z}_6`$,
with the *same* polynomials $`A=x^3+y+y^2`$ and $`B=y^3+x+x^2`$ in both.
The quotient map $`\mathbb{Z}_{12}\to\mathbb{Z}_6`$,
$`x\mapsto x\bmod 6`$, exhibits $`G_{\mathrm g}`$ as a free
$`\mathbb{Z}_2`$ cover of $`G_{\mathrm b}`$ in the $`x`$-coordinate:
each base point $`(x_0,y)\in G_{\mathrm b}`$ has the two lifts
$`(x_0,y)`$ and $`(x_0+6,y)`$ in $`G_{\mathrm g}`$. We call these the
two *sheets*: sheet $`0`$ is the set of gross points with
$`x`$-coordinate in $`\{0,\dots,5\}`$ and sheet $`1`$ the set with
$`x`$-coordinate in $`\{6,\dots,11\}`$. The free deck transformation is
``` math
\sigma\colon G_{\mathrm g}\to G_{\mathrm g},\qquad \sigma(x,y)=(x+6,\,y),
```
an involution that swaps the two sheets and commutes with multiplication
by $`A`$ and $`B`$ (both have $`x`$-support inside a single sheet’s
worth of shifts, and $`\sigma`$ is induced by a group translation, so it
is an $`\mathbb{F}_{2}[G_{\mathrm g}]`$-module automorphism). Choosing
sheet $`0`$ as a fundamental domain identifies
$`\mathbb{F}_{2}[G_{\mathrm g}]`$ with
$`\mathbb{F}_{2}[G_{\mathrm b}]^2`$: a gross element is written as a
pair $`(f_0,f_1)`$ of base elements, $`f_s`$ being its restriction to
sheet $`s`$. Under this identification a gross $`1`$-chain is a pair of
base $`1`$-chains
``` math
v=(v_0,v_1),\qquad v_0,v_1\in\mathbb{F}_{2}[G_{\mathrm b}]\oplus\mathbb{F}_{2}[G_{\mathrm b}],
```
and Hamming weight is additive across sheets:
``` math
\begin{equation}
  \lvert v\rvert=\lvert v_0\rvert+\lvert v_1\rvert.
\end{equation}
```

#### Block form of the cover boundary.

Multiplication by $`A`$ or $`B`$ on $`\mathbb{F}_{2}[G_{\mathrm g}]`$
either keeps a monomial on its sheet or moves it across the seam between
the sheets, according to whether the relevant $`x`$-shift wraps the
$`\mathbb{Z}_{12}`$ coordinate past the sheet boundary. Splitting each
base boundary operator $`\partial`$ into its non-seam-crossing part
$`\partial_2^{\mathrm{nc}}`$ and its seam-crossing part
$`\partial_2^{\mathrm{c}}`$, so that
``` math
\partial=\partial_2^{\mathrm{nc}}+\partial_2^{\mathrm{c}}\qquad\text{(an entrywise split on $\partial$),}
```
the gross boundary acts on the sheet-pair $`(v_0,v_1)`$ by the
$`2\times2`$ block matrix
``` math
\begin{equation}
  \partial^{\mathrm{cov}}
  =\begin{pmatrix}\partial_2^{\mathrm{nc}}& \partial_2^{\mathrm{c}}\\[2pt] \partial_2^{\mathrm{c}}& \partial_2^{\mathrm{nc}}\end{pmatrix},
\end{equation}
```
the off-diagonal $`\partial_2^{\mathrm{c}}`$ blocks recording precisely
the monomials that the deck map carries from one sheet to the other.
(The same block form holds for $`\partial_1`$ and $`\partial_2`$; we
suppress the subscript when the statement is uniform.) Equation
the block form above is verified
directly: it is the entrywise statement that each nonzero entry of
$`\partial`$ lands on the same sheet as its source or on the opposite
sheet, and the two cases are exactly $`\partial_2^{\mathrm{nc}}`$ and
$`\partial_2^{\mathrm{c}}`$.

#### The projection chain map.

Summing the two block rows of
the block form above collapses the deck
action: since
$`\partial_2^{\mathrm{nc}}+\partial_2^{\mathrm{c}}=\partial`$, adding
the rows sends $`(v_0,v_1)`$ to
$`\partial v_0+\partial v_1=\partial(v_0+v_1)`$. This is exactly the
effect of the *projection*
``` math
p\colon \mathbb{F}_{2}[G_{\mathrm g}]\to\mathbb{F}_{2}[G_{\mathrm b}],\qquad p(v)=v_0+v_1,
```
the $`\mathbb{F}_{2}`$-linear map that adds the two sheets
(equivalently, push-forward along the covering
$`G_{\mathrm g}\to G_{\mathrm b}`$). Applied blockwise to a $`1`$-chain,
$`p(v_L,v_R)=(p(v_L),p(v_R))`$, the displayed row-sum computation reads
``` math
\begin{equation}
  \partial_1^{\mathrm{base}}\bigl(p(v)\bigr)
  =\text{(sum of the two block rows of }\partial_1^{\mathrm{cov}}v),
\end{equation}
```
so $`p`$ is a chain map: it sends gross $`1`$-cycles to base
$`1`$-cycles. In particular,
``` math
v\in\ker\partial_1^{\mathrm{cov}}\ \Longrightarrow\ p(v)\in\ker\partial_1^{\mathrm{base}} .
```
Moreover, because $`p`$ adds two $`\mathbb{F}_{2}`$ vectors supported on
disjoint sheets, no cancellation can create support, only destroy it:
``` math
\begin{equation}
  \lvert p(v)\rvert=\lvert v_0+v_1\rvert\le\lvert v_0\rvert+\lvert v_1\rvert=\lvert v\rvert.
\end{equation}
```

#### The diagonal lift.

Dually, the diagonal map
``` math
\tau\colon\mathbb{F}_{2}[G_{\mathrm b}]\to\mathbb{F}_{2}[G_{\mathrm g}],\qquad \tau(u)=(u,u),
```
is a chain map as well: applying
the block form above to $`(u,u)`$ gives
in each block
$`\partial_2^{\mathrm{nc}}u+\partial_2^{\mathrm{c}}u=\partial u`$, so
$`\tau`$ commutes with the boundary and carries base $`1`$-cycles to
gross $`1`$-cycles. It is the section of $`p`$ on the diagonal,
$`p\circ\tau=0`$ over $`\mathbb{F}_{2}`$ in the sense that
$`p(\tau(u))=u+u=0`$; equivalently, $`\mathop{\mathrm{im}}\tau`$ is the
kernel of $`p`$.

#### The kernel of $`p`$ is diagonal.

If $`p(v)=0`$ then $`v_0+v_1=0`$, i.e. $`v_1=v_0`$, so
$`v=(v_0,v_0)=\tau(v_0)`$ is *diagonal*. For such a $`v`$ the two rows
of the cover cycle equation $`\partial_1^{\mathrm{cov}}v=0`$ both read
$`(\partial_2^{\mathrm{nc}}+\partial_2^{\mathrm{c}})v_0=\partial_1^{\mathrm{base}}v_0=0`$.
Hence
``` math
\begin{equation}
  p(v)=0\ \text{ and }\ \partial_1^{\mathrm{cov}}v=0
  \ \Longleftrightarrow\ v=(v_0,v_0)\ \text{ with }\ \partial_1^{\mathrm{base}}v_0=0,
\end{equation}
```
and then $`\lvert v\rvert=2\lvert v_0\rvert`$ by
the weight inequality.

#### Dangerous and safe classes.

The induced map on homology
$`p_\ast\colon H_1(\mathrm{gross})\to H_1(\mathrm{base})`$ splits the
logical classes of the gross code into two sectors, which organize the
rest of the proof:

- a class is *dangerous* if $`p_\ast[v]=0`$ (its representatives project
  to base *boundaries*); and

- a class is *safe* if $`p_\ast[v]\ne0`$ (its representatives project to
  nonzero base *homology*).

Theorem B treats both sectors at the level of cycles; the sharp
dangerous-sector floor is Theorem C.

## Proof of Theorem B

<div class="thmB">

**Theorem B** (the cover floor). *The gross code $`[[144,12,12]]`$,
the free $`\mathbb{Z}_2`$ double cover of the base in the
$`x`$-direction, satisfies $`d(\mathrm{gross})\ge 6`$. More precisely,
every nonzero gross $`Z`$-type $`1`$-cycle $`v`$ — logical or stabilizer
— has $`\lvert v\rvert\ge 6`$.*

</div>

<div class="proof">

*Proof.* Let $`v=(v_0,v_1)\ne 0`$ be any gross $`Z`$-type $`1`$-cycle,
$`\partial_1^{\mathrm{cov}}v=0`$. We distinguish the two sectors
according to the value of the projection $`p(v)=v_0+v_1`$.

*Safe case: $`p(v)\ne 0`$.* By
the chain-map relation, $`p(v)`$ is a base
$`1`$-cycle, and it is nonzero by hypothesis. Theorem A (in its strong
form: *no* nonzero base $`1`$-cycle, whether logical or a boundary, has
weight $`\le 5`$) gives $`\lvert p(v)\rvert\ge 6`$. Combining with the
weight bound above,
``` math
\lvert v\rvert\ \ge\ \lvert p(v)\rvert\ \ge\ 6 .
```

*Dangerous case: $`p(v)=0`$.* By
the diagonal-cycle relation, $`v`$ is diagonal,
$`v=(v_0,v_0)`$ with $`v_0`$ a base $`1`$-cycle, and $`v_0\ne 0`$
because $`v\ne 0`$. Theorem A applied to the nonzero base cycle $`v_0`$
gives $`\lvert v_0\rvert\ge 6`$, whence
``` math
\lvert v\rvert\ =\ 2\,\lvert v_0\rvert\ \ge\ 12 .
```

In either case $`\lvert v\rvert\ge 6`$. Since a nontrivial $`Z`$-logical
operator of the gross code is in particular a nonzero $`Z`$-type
$`1`$-cycle, every such operator has weight $`\ge 6`$, so
$`d_Z(\mathrm{gross})\ge 6`$; and
$`d_X(\mathrm{gross})=d_Z(\mathrm{gross})`$ by the Duality Lemma
(Lemma <a href="#lem:duality" data-reference-type="ref"
data-reference="lem:duality">1</a>). Hence $`d(\mathrm{gross})\ge 6`$. ◻

</div>

<div class="remark">

*Remark 2*. The proof is a clean instance of the projection bound
$`d(\mathrm{gross})\ge\min\{\,d(\mathrm{base}),\ \mu_Z(\mathrm{base})\,\}`$:
the safe case is floored by $`d(\mathrm{base})`$ through $`p`$, and the
dangerous case is floored by twice the minimum cycle weight
$`\mu_Z(\mathrm{base})`$ through the diagonal $`\tau`$. Theorem A
supplies both inputs — $`d(\mathrm{base})\ge 6`$ and
$`\mu_Z(\mathrm{base})\ge 6`$ — with no descent through a tower of
covers. The dangerous-case estimate $`\lvert v\rvert=2\lvert v_0\rvert`$
already suggests the sharper bound $`\ge 2\,d(\mathrm{base})=12`$
pursued in Theorem C, but at the level of *cycles* it only sees
$`\mu_Z`$, since $`v_0`$ may there be a base *boundary*.

</div>

# The dangerous sector is heavy: Theorem C

Theorem B caps the cover floor at $`6`$ because the safe sector does.
The deeper fact, and the route to the full distance, is that the
*dangerous* classes — those in the kernel of the projection
$`p_\ast\colon H_1(\mathrm{gross})\to H_1(\mathrm{base})`$ — carry
weight at least $`12=2\,d(\mathrm{base})`$. The proof combines a slice
identity that reduces a dangerous cover cycle to a base stabilizer $`b`$
plus an off-support excess, a classification of all base stabilizers of
weight $`\le 11`$, and a lower bound on the excess for each surviving
$`b`$.

## The slice identity

Recall from the double-cover construction (used for Theorem B) that a
cover $`1`$-chain is a pair of base chains $`v=(v_0,v_1)`$, and that for
each seam position $`j`$ the cover boundary takes the block form
``` math
\partial_2^{\mathrm{cov}}=
  \begin{pmatrix}\partial_2^{\mathrm{nc}}& \partial_2^{\mathrm{c}}\\[2pt]\partial_2^{\mathrm{c}}& \partial_2^{\mathrm{nc}}\end{pmatrix},
  \qquad \partial_2=\partial_2^{\mathrm{nc}}+\partial_2^{\mathrm{c}},
```
where $`\partial_2^{\mathrm{nc}}`$ (non-crossing) and
$`\partial_2^{\mathrm{c}}`$ (seam-crossing) split the base boundary
*entrywise*, so
$`\mathop{\mathrm{supp}}(\partial_2^{\mathrm{c}}f)\subseteq\mathop{\mathrm{supp}}(\partial_2 f)`$.
The diagonal embedding $`\tau(u)=(u,u)`$ sends base $`1`$-cycles to
cover $`1`$-cycles, and the dangerous cover cycles are exactly
$`\tau(Z_1)+\mathop{\mathrm{im}}\partial_2^{\mathrm{cov}}`$, where
$`Z_1=\ker
\partial_1^{\mathrm{base}}`$.

<div id="lem:slice" class="lemma">

**Lemma 5** (slice identity). *Let $`v`$ be a dangerous cover
$`Z`$-cycle, write
$`b:=p(v)=\partial_2\,p(w)\in\mathop{\mathrm{Stab}}_Z(\mathrm{base})`$
for the base stabilizer it projects to, and let $`z_b`$ be a base
preimage with $`\partial_2 z_b=b`$. Then, for every seam position $`j`$,
the two sheets satisfy $`v_1=v_0+b`$, and
``` math
\begin{equation}
  \lvert v\rvert=\lvert b\rvert+2\,\bigl|\,v_0\ \text{off}\ \mathop{\mathrm{supp}}b\,\bigr|\ \ge\ \lvert b\rvert+2\,m(b),
\end{equation}
```
where the *off-support minimum* is
``` math
m(b):=\min\bigl\{\,\bigl|\,(\partial_2^{\mathrm{c}}z_b+u')\ \text{off}\ \mathop{\mathrm{supp}}b\,\bigr|
  \ :\ u'\in Z_1,\ [u']\notin\mathop{\mathrm{im}}\Delta\,\bigr\},
```
and $`\Delta\colon\ker\partial_2\to H_1(\mathrm{base})`$,
$`\Delta[\zeta]=[\partial_2^{\mathrm{c}}\zeta]`$, is the Smith
connecting map; its image
$`\mathop{\mathrm{im}}\Delta\subseteq H_1(\mathrm{base})`$ is
independent of the seam and equals $`\ker\tau_\ast`$, the base classes
whose diagonal lift $`\tau(\cdot)=(\cdot,\cdot)`$ is a cover boundary.
Consequently Theorem C is exactly the statement
``` math
\begin{equation}
  \text{(M)}\qquad \lvert b\rvert+2\,m(b)\ \ge\ 12\qquad\text{for every }b\in\mathop{\mathrm{Stab}}_Z(\mathrm{base}).
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Since $`v`$ is dangerous it lies in
$`\tau(Z_1)+\mathop{\mathrm{im}}\partial_2^{\mathrm{cov}}`$, so we may
write $`v=\tau(u)+\partial_2^{\mathrm{cov}}w`$ for some base cycle
$`u\in Z_1`$ and cover $`2`$-chain $`w`$. The projection of
$`\partial_2^{\mathrm{cov}}`$ is $`\partial_2`$, hence
$`p(v)=\partial_2\,p(w)=:b`$ is a base stabilizer; fix any preimage
$`z_b`$ with $`\partial_2 z_b=b`$. Expanding the block boundary on
$`w=(w_0,w_1)`$ and using
$`\partial_2^{\mathrm{nc}}+\partial_2^{\mathrm{c}}=\partial_2`$, the two
sheets of $`v`$ are
``` math
v_0=u+\partial_2^{\mathrm{c}}z_b+\partial_2 w_0,\qquad v_1=v_0+b
```
up to the relabeling $`w_0\leftrightarrow w_1`$ of the two seam sheets;
the second equation is $`v_0+v_1=p(v)=b`$. The class $`[v_0]`$ in
$`H_1(\mathrm{base})`$ equals
$`[u]+[\partial_2^{\mathrm{c}}z_b]=[u]+\Delta[z_b]`$, and since
$`[v]=\tau_\ast[v_0]`$ in $`H_1(\mathrm{cover})`$, the cover cycle $`v`$
is a nontrivial logical iff
$`[v_0]\notin\ker\tau_\ast=\mathop{\mathrm{im}}\Delta`$, i.e. iff
$`[\,u+\partial_2^{\mathrm{c}}z_b\,]\notin\mathop{\mathrm{im}}\Delta`$
(equivalently $`[u']\notin\mathop{\mathrm{im}}\Delta`$ for the displayed
representative $`u':=u+\partial_2^{\mathrm{c}}z_b`$).

For the weight, set $`x:=v_0`$. Over $`\mathbb{F}_{2}`$ the elementary
identity
$`\lvert x\rvert+\lvert x+b\rvert=\lvert b\rvert+2\,\bigl|\,x\ \text{off}\ \mathop{\mathrm{supp}}b\,\bigr|`$
holds coordinatewise (on $`\mathop{\mathrm{supp}}b`$ the two terms
contribute $`1`$ in total per cell; off $`\mathop{\mathrm{supp}}b`$ each
cell of $`x`$ contributes $`2`$). Since
$`\lvert v\rvert=\lvert v_0\rvert+\lvert v_1\rvert=\lvert x\rvert+\lvert x+b\rvert`$,
this gives the equality in
the slice identity. The displayed representative
of $`v_0`$ is $`\partial_2^{\mathrm{c}}z_b+u'`$ with $`u'`$ a base cycle
whose class avoids $`\mathop{\mathrm{im}}\Delta`$, so minimizing the
off-support part over all admissible $`v`$ with the same $`b`$ yields
the bound
$`\bigl|\,v_0\ \text{off}\ \mathop{\mathrm{supp}}b\,\bigr|\ge m(b)`$.
Finally, ranging over all $`b`$ and substituting into
the slice identity, the cover distance on the
dangerous sector is $`\min_b\bigl(\lvert b\rvert+2\,m(b)\bigr)`$, so the
bound (M) is equivalent to Theorem C. ◻

</div>

## Structure of light base stabilizers

Throughout this subsection $`b=\partial_2 z=(B\cdot z,\ A\cdot z)`$ is a
base stabilizer, and each block is decomposed into its four layers
$`s\in\mathbb{Z}_2^2`$ via the layer frame, with component transforms
$`V_j`$ as in Lemma <a href="#lem:engine" data-reference-type="ref"
data-reference="lem:engine">2</a>. We record three structural facts.

<div id="lem:parity" class="lemma">

**Lemma 6** (parity). *$`\lvert b\rvert`$ is even.*

</div>

<div class="proof">

*Proof.* The unit components agree, $`\hat{A}_0=\hat{B}_0=1+u+v`$,
because $`A`$ and $`B`$ have the same $`s`$-part multiset
$`\{1,s_x,s_y\}`$; thus the two blocks have identical layer parities. By
(PAR),
$`\lvert B\cdot z\rvert\equiv\lvert z\rvert`$ and
$`\lvert A\cdot z\rvert\equiv\lvert z\rvert\pmod 2`$, so
$`\lvert b\rvert=\lvert B\cdot z\rvert+\lvert A\cdot z\rvert\equiv 2\lvert z\rvert\equiv 0\pmod 2`$. ◻

</div>

<div id="lem:oneblock" class="lemma">

**Lemma 7** (the sharp one-block lemma). *If
$`z'\in\mathop{\mathrm{Ann}}(A)\smallsetminus\ker\partial_2`$ then
$`\lvert B\cdot z'\rvert\ge 16`$. Symmetrically, if
$`z'\in\mathop{\mathrm{Ann}}(B)\smallsetminus\ker\partial_2`$ then
$`\lvert A\cdot z'\rvert\ge 16`$. The bound is attained.*

</div>

<div class="proof">

*Proof.* We treat the $`\mathop{\mathrm{Ann}}(A)`$ side; the other is
the mirror under the block-swapping automorphism $`A(y,x)=B(x,y)`$.
Since $`z'\in\mathop{\mathrm{Ann}}(A)`$, the unit components vanish,
$`\hat z'_0=\hat z'_2=0`$, and on the radical components
$`\hat z'_j\in(\hat{A}_j)`$ for $`j\in\{1,3,4\}`$. We compute the value
vectors of $`B\cdot z'`$ layerwise. On component $`4`$, using
$`\hat{B}_4=\omega\hat{A}_4`$ from the layer table,
``` math
V_4^B=\hat{B}_4\,\hat z'_4=\omega\,\hat{A}_4\,\hat z'_4=\omega\,V_4^A=0,
```
since $`z'\in\mathop{\mathrm{Ann}}(A)`$. On component $`3`$,
$`V_3^B=\hat{B}_3\,\hat z'_3`$; as $`\hat z'_3\in(\hat{A}_3)`$ and
$`\hat{B}_3=\omega u+v`$ is radical, the product lands in the socle
$`\mathbb{F}_{4}\cdot uv`$, hence $`V_3^B`$ is a *constant* vector. On
component $`1`$, $`V_1^B=\hat{B}_1\,\hat z'_1`$ with $`\hat{B}_1=1+u+v`$
a unit, so $`V_1^B`$ ranges over the ideal $`(\hat{A}_1)`$, i.e. it is
full, co-point, or zero by the engine. The parity component is dead
($`\hat z'_0=0`$), so every layer of $`B\cdot z'`$ has even weight, and
the Fourier support of every layer is contained in $`\{1,3\}`$ (orbits
$`1`$ and $`3`$). The layer dictionary
$`\partial_2^{\mathrm{nc}}`$-costs of
Lemma <a href="#lem:d3" data-reference-type="ref"
data-reference="lem:d3">3</a> for such supports are
``` math
\{1\}\to 6,\qquad \{3\}\to 6,\qquad \{1,3\}\to 4.
```
We now bound $`\lvert B\cdot z'\rvert=\sum_s\lvert (B\cdot z')_s\rvert`$
by cases on $`V_3^B`$ and $`V_1^B`$.

*Case $`V_3^B\ne 0`$ (constant).* A nonzero constant on component $`3`$
is present at *every* layer, so all four layers are alive. The subcases
on $`V_1^B`$:

<div class="center">

| $`V_1^B`$ | per-layer supports                            | weight bound      |
|:----------|:----------------------------------------------|:------------------|
| full      | four layers at $`\{1,3\}`$, cost $`4`$ each   | $`4\cdot 4=16`$   |
| co-point  | three layers at $`\{1,3\}`$, one at $`\{3\}`$ | $`3\cdot 4+6=18`$ |
| zero      | four layers at $`\{3\}`$, cost $`6`$ each     | $`4\cdot 6=24`$   |

</div>

*Case $`V_3^B=0`$.* Then component $`1`$ must be nonzero (else
$`B\cdot z'=0`$, putting $`z'\in\ker\partial_2`$, excluded). A nonzero
$`V_1^B`$ has full or co-point support, hence at least three live
layers, each with support $`\{1\}`$ at cost $`6`$:
``` math
\lvert B\cdot z'\rvert\ \ge\ 3\cdot 6=18.
```

The minimum over all cases is $`16`$, attained by the full–$`V_1^B`$,
nonzero-constant-$`V_3^B`$ configuration. ◻

</div>

<div id="lem:floor-structure" class="lemma">

**Lemma 8** (floor). *If $`b\ne 0`$ and $`\lvert b\rvert\le 10`$, then
*both* blocks of $`b`$ have at least three nonzero layers.*

</div>

<div class="proof">

*Proof.* Suppose one block, say $`A\cdot z`$, has at most two nonzero
layers; we derive $`\lvert b\rvert\ge 12`$. If $`A\cdot z=0`$ then
$`z\in\mathop{\mathrm{Ann}}(A)`$, and $`z\notin\ker\partial_2`$ (else
$`b=0`$), so by Lemma <a href="#lem:oneblock" data-reference-type="ref"
data-reference="lem:oneblock">7</a> the other block has
$`\lvert B\cdot z\rvert\ge 16`$, contradicting $`\lvert b\rvert\le 10`$.
If $`A\cdot z\ne 0`$, the engine support analysis on the radical
components shows that a single live block component already forces three
live layers: a nonzero radical ideal element is full or co-point
(Lemma <a href="#lem:engine" data-reference-type="ref"
data-reference="lem:engine">2</a>), which occupies $`\ge 3`$ layers,
while the parity component contributes only even-weight layers. Hence
$`A\cdot z`$ cannot have a nonzero radical component with only two live
layers; the only way to keep $`A\cdot z`$ to $`\le 2`$ layers is to have
all radical components vanish, i.e. $`z\in\mathop{\mathrm{Ann}}(A)`$
again, returning to the previous case. Thus both blocks carry $`\ge 3`$
nonzero layers whenever $`0<\lvert b\rvert\le 10`$. ◻

</div>

<div id="lem:dirforce" class="lemma">

**Lemma 9** (direction forcing). *Suppose
$`f\in\mathop{\mathrm{im}}(A\cdot)`$ has a zero layer and a weight-$`2`$
layer of the form $`\{p,\ p+\delta\}`$ (together with some
$`\delta`$-point layer). Then each radical component $`V_j`$ is a
nonzero co-point vector, and
``` math
V_j[s_{\mathrm{pair}}]=\psi_j(p)\bigl(1+\psi_j(\delta)\bigr)\ne 0
  \qquad(j\in\{1,3,4\}),
```
so $`\delta\notin\ker\psi_1\cup\ker\psi_3\cup\ker\psi_4`$. The only
direction left is the $`t_y`$-direction; on the $`B`$ side the mirror
forces the $`t_x`$-direction.*

</div>

<div class="proof">

*Proof.* A zero layer forces each radical $`V_j`$ to a co-point (a full
vector is nonzero on every layer). On the weight-$`2`$ layer the value
is $`V_j[s_{\mathrm{pair}}]=\psi_j(p)+\psi_j(p+\delta)
=\psi_j(p)(1+\psi_j(\delta))`$, which is nonzero exactly when
$`\psi_j(\delta)\ne 1`$, i.e. $`\delta\notin\ker\psi_j`$. Using the
kernels of the layer frame, $`\ker\psi_1=\mathrm{span}(1,0)`$,
$`\ker\psi_3=\mathrm{span}(1,2)`$, $`\ker\psi_4=\mathrm{span}(1,1)`$,
the only nonzero $`\delta\in\mathbb{Z}_3^2`$ avoiding all three is
$`\delta\in\mathrm{span}(0,1)`$, the $`t_y`$-direction. ◻

</div>

## Classification of light base stabilizers

<div id="prop:lightstab" class="proposition">

**Proposition 10** (light stabilizers). *Every base stabilizer
$`b\in\mathop{\mathrm{Stab}}_Z(\mathrm{base})`$ with
$`0<\lvert b\rvert\le 11`$ is one of*

- *the $`36`$ *hexagons* $`\partial_2\delta_g`$, of weight $`6`$; or*

- *the $`216`$ *D-pairs* $`\partial_2(\delta_g+\delta_{gd})`$ with
  $`d\in
    \mathrm dA\cup\mathrm dB`$, of weight $`10`$.*

*In particular there is no base stabilizer of weight $`8`$, and the
minimum nonzero stabilizer weight is $`\mu_Z=6`$.*

</div>

<div class="proof">

*Proof.* By Lemma <a href="#lem:parity" data-reference-type="ref"
data-reference="lem:parity">6</a> we have $`\lvert b\rvert\le 10`$. By
Lemma <a href="#lem:floor-structure" data-reference-type="ref"
data-reference="lem:floor-structure">8</a> both blocks have $`\ge 3`$
nonzero layers. The block-swapping automorphism $`A(y,x)=B(x,y)`$
exchanges the two blocks, so without loss of generality the lighter
block is the $`A`$-block $`f=A\cdot z`$, of weight $`3`$, $`4`$ or
$`5`$. With $`\ge 3`$ nonzero layers, the layer profile of $`f`$ is one
of
``` math
(1,1,1)\ \mid\ (1,1,1,1),\ (2,1,1)\ \mid\ (2,1,1,1),\ (2,2,1),\ (3,1,1).
```
We resolve each shape. In every surviving case $`f`$ is pinned inside a
*single $`t_y`$-fibre*, and an endgame transfers the conclusion from the
block $`f`$ to the full stabilizer $`b`$. The comp-$`1`$ transfer
operator
``` math
T:=\hat{A}_1\,\hat{B}_1^{-1}=\hat{A}_1(1+u+v)=u+\omega v+(1+\omega)uv
```
(here $`\hat{B}_1=1+u+v`$ is a self-inverse unit) carries the
$`B`$-block component-$`1`$ value vector to the $`A`$-block one,
$`V_1^A=T\cdot V_1^B`$, and satisfies $`T\cdot\vec 1=0`$; it is the
bookkeeping device for the kills below.

#### Profile $`(1,1,1)`$.

Three $`\delta`$-point layers; their radical components $`V_j`$ are
co-points whose cross-layer ratios are $`\eta`$-powers with
$`j`$-independent exponents (the C-table of
Lemma <a href="#lem:engine" data-reference-type="ref"
data-reference="lem:engine">2</a>). The separation of $`\psi_3,\psi_4`$
pins the three cells to the difference pattern of $`A\cdot\delta_g`$ for
some $`g`$. Endgame: $`z-\delta_g\in\mathop{\mathrm{Ann}}(A)`$. The
$`A`$-block of this profile has weight $`3`$ and
$`\lvert b\rvert\le10`$, so
$`\lvert B\cdot z\rvert=\lvert b\rvert-\lvert A\cdot z\rvert\le 10-3=7`$;
with $`\lvert B\cdot\delta_g\rvert=3`$,
``` math
\lvert B(z-\delta_g)\rvert\le\lvert B\cdot z\rvert+\lvert B\cdot\delta_g\rvert\le 7+3=10<16,
```
so by Lemma <a href="#lem:oneblock" data-reference-type="ref"
data-reference="lem:oneblock">7</a> $`z-\delta_g\in\ker\partial_2`$,
i.e. $`z\equiv\delta_g`$ modulo $`\ker\partial_2`$. Hence
$`b=\partial_2\delta_g`$ is a **hexagon**.

#### Profile $`(1,1,1,1)`$.

All four $`V_j`$ are full, hence constant, so the four $`\delta`$-cells
coincide: $`f`$ is a $`\delta`$-column at a single fibre $`t^\ast`$. Any
completion to a light $`b`$ would need the $`B`$-block all-odd of weight
$`\le 6`$, i.e. profile $`(1,1,1,1)`$ or $`(3,1,1,1)`$. A single
comp-$`2`$ transfer kills both at once. The $`A`$-side pins
``` math
\hat z_2=\hat{A}_2^{-1}\,\psi_2(t^\ast)\,uv=\psi_2(t^\ast)\,uv,
```
since the unit $`\hat{A}_2`$ fixes the socle
($`u_0\cdot uv=\varepsilon(u_0)\,uv=uv`$). Then on the $`B`$-block
component $`2`$,
``` math
V_2^B=\hat{B}_2\cdot\psi_2(t^\ast)\,uv=0,
```
because the radical $`\hat{B}_2`$ kills the socle. But either putative
$`B`$-shape has a $`\delta`$-point layer, where $`V_2^B`$ takes the
nonzero value $`\psi_2(\text{$t$-cell})`$ — contradiction. **No light
$`b`$.**

#### Profile $`(2,1,1)`$ — the D-pair lemma.

Direction forcing
(Lemma <a href="#lem:dirforce" data-reference-type="ref"
data-reference="lem:dirforce">9</a>) puts the pair in the
$`t_y`$-direction. Using $`1+\eta=\eta^2`$, the C-ratio system has
exactly one solution per pair-layer position, giving the three
single-fibre patterns realized by $`A\cdot(\delta_g+\delta_{gd})`$ for
$`d\in\{y,x^3y^2,x^3y\}`$; these are $`108`$ elements forming $`3`$
translation classes, and a direct check confirms they exhaust the
patterns produced by the ratio system. Since
$`\mathrm dA\cap\mathrm dB=\emptyset`$, a $`\mathrm dA`$-pair has block
weights $`(4,6)`$. Endgame: a completion with $`\lvert b\rvert\le 10`$
has $`\lvert B\cdot z\rvert\le 6`$, so
``` math
\lvert B(z-\text{pair})\rvert\le\lvert B\cdot z\rvert+\lvert B\cdot\text{pair}\rvert\le 6+6=12<16,
```
and Lemma <a href="#lem:oneblock" data-reference-type="ref"
data-reference="lem:oneblock">7</a> forces $`z\equiv\text{pair}`$ modulo
$`\ker\partial_2`$. Hence $`b`$ is the **D-pair**,
$`\lvert b\rvert=10`$. (This is precisely where the sharp bound $`16`$
is needed: a weaker bound $`\ge 12`$ leaves a gap at exactly $`12`$.)

#### Profile $`(3,1,1)`$.

The weight-$`3`$ layer is either a line or a triangle. A *line* kills at
least two of the three radical components at that layer — only the orbit
orthogonal to the line survives — contradicting the co-point support
required of a radical component. A *triangle* $`\{p,\ p+g,\ p+h\}`$ has
$`\kappa_j:=1+\psi_j(g)+\psi_j(h)`$. The map
$`j\mapsto(j\!\cdot\! g,\ j\!\cdot\! h)`$ is a bijection, and
$`\kappa_j=0`$ iff $`(j\!\cdot\! g,\ j\!\cdot\! h)=\pm(1,2)`$, so
$`\kappa_j=0`$ for exactly one orbit class $`j`$. If that class is
radical, the support is killed. If it is the $`A`$-unit component $`2`$,
the ratio system is solvable only when $`\kappa_4=\kappa_1\kappa_3`$
(from $`\psi_4=\psi_1\psi_3`$ and the $`j`$-independent C-exponents).
The six triangle shapes with dead orbit $`2`$ (taking $`g_x=1,\ h_x=2`$)
are tabulated below, and each violates $`\kappa_4=\kappa_1\kappa_3`$:

<div class="center">

| $`(g_y,h_y)`$ | $`\kappa_1`$ | $`\kappa_3`$ | $`\kappa_1\kappa_3`$ | $`\kappa_4`$ |
|:-------------:|:------------:|:------------:|:--------------------:|:------------:|
|   $`(0,1)`$   |  $`\omega`$  |  $`\omega`$  |     $`\omega^2`$     |    $`1`$     |
|   $`(0,2)`$   | $`\omega^2`$ |  $`\omega`$  |     $`\omega^2`$     |  $`\omega`$  |
|   $`(1,0)`$   |  $`\omega`$  | $`\omega^2`$ |      $`\omega`$      | $`\omega^2`$ |
|   $`(1,1)`$   | $`\omega^2`$ | $`\omega^2`$ |     $`\omega^2`$     |  $`\omega`$  |
|   $`(2,0)`$   | $`\omega^2`$ | $`\omega^2`$ |      $`\omega`$      |    $`1`$     |
|   $`(2,2)`$   |  $`\omega`$  | $`\omega^2`$ |      $`\omega`$      | $`\omega^2`$ |

</div>

In each row $`\kappa_1\kappa_3\ne\kappa_4`$, so the ratio system is
unsolvable. Hence $`\mathop{\mathrm{im}}(A\cdot)`$ has **no**
$`(3,1,1)`$ element (and, by the mirror, neither does
$`\mathop{\mathrm{im}}(B\cdot)`$).

#### Profile $`(2,1,1,1)`$.

All four layers are alive. If the pair direction avoids all radical
kernels (the $`t_y`$-direction), all three radical $`V_j`$ are full,
hence constant, so the $`\delta`$-cells coincide at a fibre $`t^\ast`$
and the pair is $`\{t^\ast+e,\ t^\ast+2e\}`$: one class. If the
direction lies in one radical kernel, that $`V_j`$ is a co-point while
the other two force the $`\delta`$-cells equal — but a co-point takes
three *distinct* values on its support, a contradiction. To kill the
surviving class, observe a completion needs $`\lvert B\cdot z\rvert=5`$
with three odd layers, so the $`B`$-block is $`(3,1,1)`$ — impossible by
the mirror of the previous paragraph — or $`(2,1,1,1)`$, which the
mirror classification pins to $`\delta`$-cells at a common fibre $`t_0`$
and a $`t_x`$-pair. Since $`\psi_1`$ kills $`t_x`$-pairs,
``` math
V_1^B=\psi_1(t_0)\bigl(\vec 1+\delta_{s_P}\bigr),\qquad
  V_1^A=T\cdot V_1^B=\psi_1(t_0)\cdot\mathrm{shift}_{s_P}(T),
```
a co-point vanishing at $`s_P`$. But the $`A`$-side says $`V_1^A`$ is a
nonzero constant. Contradiction. **No light $`b`$.**

#### Profile $`(2,2,1)`$.

Direction forcing puts both pairs in the $`t_y`$-direction; the C-ratio
bookkeeping pins the three layers to $`\{t\}`$, $`\{t,t+e\}`$,
$`\{t,t+2e\}`$ (three classes, single fibre). A completion needs
$`\lvert B\cdot z\rvert=5`$ with exactly one odd layer at $`s_\delta`$;
the only such profile with $`\ge 3`$ layers is $`\{1,2,2\}`$, so the
$`B`$-block is a mirror-$`(2,2,1)`$ with $`t_x`$-pairs. Then
$`V_1^B=\psi_1(t')\,\delta_{s_\delta}`$ and $`V_1^A=T\cdot V_1^B`$ is a
co-point vanishing at $`s_\delta`$ — but the $`A`$-side co-point
vanishes at $`s_4\ne s_\delta`$ and is nonzero at $`s_\delta`$.
Contradiction. **No light $`b`$.**

The only surviving shapes are $`(1,1,1)`$ (hexagons, weight $`6`$) and
the $`\mathrm dA`$-branch of $`(2,1,1)`$ (D-pairs, weight $`10`$).
Counting: there are $`36`$ hexagons $`\partial_2\delta_g`$ (one per cell
$`g`$, the group having $`36`$ elements) and $`216`$ D-pairs
$`\partial_2(\delta_g+\delta_{gd})`$, one for each unordered pair
$`\{g,g+d\}`$ with $`d\in\mathrm dA\cup\mathrm dB`$; since
$`\mathrm dA\cup\mathrm dB`$ has $`12`$ elements and each pair arises
from the two choices $`(g,d)`$ and $`(g+d,-d)`$, this is
$`36\cdot12/2=216`$. No weight-$`8`$ stabilizer survives, and
$`\mu_Z=6`$. ◻

</div>

## The off-support minima

For each light $`b`$ we now bound the off-support minimum $`m(b)`$ of
Lemma <a href="#lem:slice" data-reference-type="ref"
data-reference="lem:slice">5</a>.

<div id="lem:rung-hex" class="lemma">

**Lemma 11** (hexagon rung). *For a hexagon $`b=\partial_2\delta_g`$,
$`\ m(b)\ge 3`$.*

</div>

<div class="proof">

*Proof.* The seam split is entrywise, so
$`\mathop{\mathrm{supp}}(\partial_2^{\mathrm{c}}\delta_g)\subseteq\mathop{\mathrm{supp}}(\partial_2\delta_g)=
h(g)`$, the hexagon. Hence
``` math
m(b)=\min\bigl\{\,\bigl|\,u'\ \text{off}\ h(g)\,\bigr|\ :\ u'\in Z_1,\
  [u']\notin\mathop{\mathrm{im}}\Delta\,\bigr\}.
```
Suppose $`\bigl|\,u'\ \text{off}\ h(g)\,\bigr|\le 2`$. Replacing $`u'`$
by $`u'+b`$ if needed (a base boundary, so the class $`[u']`$ is
unchanged) we may also assume $`\bigl|\,u'\cap h(g)\,\bigr|\le 3`$,
because $`h(g)`$ has six cells and $`u'+b`$ flips exactly those covered
by $`b`$. Then $`\lvert u'\rvert\le 3+2=5`$, so $`u'`$ is a nonzero base
cycle of weight $`\le 5`$ — impossible by Theorem A — unless $`u'=0`$.
But $`u'=0`$ gives $`[u']=0\in\mathop{\mathrm{im}}\Delta`$,
contradicting the admissibility of $`u'`$. Hence
$`\bigl|\,u'\ \text{off}\ h(g)\,\bigr|\ge 3`$. ◻

</div>

<div id="lem:rung-dpair" class="lemma">

**Lemma 12** (D-pair rung). *For a D-pair
$`b=\partial_2(\delta_g+\delta_{gd})`$, $`\ m(b)\ge 1`$.*

</div>

<div class="proof">

*Proof.* Write $`b=b_1+b_2`$ as the sum of the two hexagons
$`b_1=\partial_2\delta_g`$, $`b_2=\partial_2\delta_{gd}`$, so
$`\mathop{\mathrm{supp}}b=h\cup h'`$ and
$`\mathop{\mathrm{supp}}(\partial_2^{\mathrm{c}}z_b)\subseteq h\cup h'
=\mathop{\mathrm{supp}}b\cup\{q^\ast\}`$ for the single overlap cell
$`q^\ast`$, giving an $`11`$-qubit union. Suppose $`m(b)=0`$: some
admissible cycle $`u'`$ (with $`[u']\notin\mathop{\mathrm{im}}\Delta`$)
is supported inside this $`11`$-qubit union
$`U=\mathop{\mathrm{supp}}b_1\cup\mathop{\mathrm{supp}}b_2`$. Consider
the four coset representatives $`u'+\{0,\ b_1,\ b_2,\ b_1+b_2\}`$. At a
qubit $`q`$ with $`(b_1(q),b_2(q))\ne(0,0)`$, exactly two of the four
values $`u'(q),\,u'(q)+b_1(q),\,u'(q)+b_2(q),\,u'(q)+b_1(q)+b_2(q)`$ are
nonzero, independently of $`u'(q)`$; at a qubit with
$`(b_1(q),b_2(q))=(0,0)`$ all four equal $`u'(q)`$, and $`u'(q)=0`$
there since $`\mathop{\mathrm{supp}}u'\subseteq U`$. Hence the four
weights sum to
``` math
2\,\bigl|\mathop{\mathrm{supp}}b_1\cup\mathop{\mathrm{supp}}b_2\bigr|=2\cdot 11=22<24=4\cdot 6,
```
so at least one representative has weight $`\le 5`$, hence is the zero
cycle by Theorem A. Then
$`u'\in\mathrm{span}\{b_1,b_2\}\subseteq\mathop{\mathrm{im}}\partial_2`$,
so $`[u']=0\in\mathop{\mathrm{im}}\Delta`$, contradicting admissibility.
Hence $`m(b)\ge 1`$. ◻

</div>

## Assembly of Theorem C

<div class="proof">

*Proof of Theorem C.* We verify the factor-two bound
(M), $`\lvert b\rvert+2\,m(b)\ge 12`$, on
every value of $`b`$.

- $`b=0`$. Here a representative $`u'`$ with
  $`[u']\notin\mathop{\mathrm{im}}\Delta`$ is a nonzero base cycle, so
  $`m(0)\ge 6`$ by Theorem A, and $`\lvert b\rvert+2m(b)\ge 0+12=12`$.

- $`b`$ a hexagon. $`\lvert b\rvert=6`$ and $`m(b)\ge 3`$
  (Lemma <a href="#lem:rung-hex" data-reference-type="ref"
  data-reference="lem:rung-hex">11</a>), giving $`6+2\cdot 3=12`$.

- $`b`$ a D-pair. $`\lvert b\rvert=10`$ and $`m(b)\ge 1`$
  (Lemma <a href="#lem:rung-dpair" data-reference-type="ref"
  data-reference="lem:rung-dpair">12</a>), giving $`10+2\cdot 1=12`$.

- $`\lvert b\rvert\ge 12`$. Then $`\lvert b\rvert+2m(b)\ge 12`$
  trivially.

By Proposition <a href="#prop:lightstab" data-reference-type="ref"
data-reference="prop:lightstab">10</a> no other $`b`$ with
$`\lvert b\rvert\le 11`$ exists, so the four cases above are exhaustive.
Combining with the slice identity
(Lemma <a href="#lem:slice" data-reference-type="ref"
data-reference="lem:slice">5</a>), every nontrivial dangerous
$`Z`$-logical $`v`$ satisfies
``` math
\lvert v\rvert\ge\lvert b\rvert+2\,m(b)\ge 12.
```
By the Duality Lemma <a href="#lem:duality" data-reference-type="ref"
data-reference="lem:duality">1</a> the same bound holds on the $`X`$
side.

Tightness: a diagonal representative $`\tau(u)=(u,u)`$ over a
weight-$`6`$ base logical $`u`$ with
$`[u]\notin\mathop{\mathrm{im}}\Delta`$ has weight $`12`$, and such a
$`u`$ exists — the weight-$`6`$ logical $`u^\ast`$ of Corollary A$`'`$
satisfies $`[u^\ast]\notin\mathop{\mathrm{im}}\Delta`$, as shown in the
proof of Theorem D. Hence the bound $`12`$ is attained. ◻

</div>

# The safe-sector reduction

## Route to Theorem D

We work on the $`Z`$ side throughout (the $`X`$ side follows by the
Duality Lemma <a href="#lem:duality" data-reference-type="ref"
data-reference="lem:duality">1</a>). Recall that the gross code is the
free $`\mathbb{Z}_2`$ double cover of the base in the $`x`$-direction: a
cover $`1`$-chain is a pair $`v=(v_0,v_1)`$ of base chains (the two
sheet coordinates), the projection $`p(v)=v_0+v_1`$ is a chain map with
$`\lvert v\rvert\ge\lvert p(v)\rvert`$, and the deck transformation
$`\sigma\colon x\mapsto x+6`$ acts on cover chains. We must show that
every nontrivial cover $`Z`$-logical $`v`$ has $`\lvert v\rvert\ge 12`$.

Fix such a $`v`$ and consider the induced base class
$`[p(v)]\in H_1(\mathrm{base})`$. This splits the analysis into two
sectors.

- *Dangerous sector:* $`[p(v)]=0`$ in $`H_1(\mathrm{base})`$, i.e. the
  class of $`v`$ lies in $`\ker p_\ast`$. Theorem C handles this case
  directly: every such nontrivial logical has weight $`\ge 12`$.

- *Safe sector:* $`[p(v)]\ne 0`$. Here
  $`\lvert v\rvert\ge\lvert p(v)\rvert\ge\lvert u\rvert`$ for the
  lightest cycle $`u`$ representing the nonzero base class $`[p(v)]`$,
  so a weight floor on the relevant base classes transfers directly to
  $`v`$.

The present section reduces the safe sector to a single weight floor on
the base code, the statement we call *(M-im)*: *every base $`1`$-cycle
whose class lies in a nonzero Smith class has weight $`\ge 12`$*
(Proposition <a href="#thm:Mim" data-reference-type="ref"
data-reference="thm:Mim">32</a>). Granting (M-im), the safe sector is
immediate: the homotopy theorem (R) below shows $`[p(v)]`$ lands in the
image of the Smith connecting map $`\Delta`$, so $`[p(v)]\ne 0`$ forces
$`\lvert p(v)\rvert\ge 12`$, whence $`\lvert v\rvert\ge 12`$. Together
with Theorem C this gives $`d(\mathrm{gross})\ge 12`$; Corollary A$`'`$
and the tightness construction supply a weight-$`12`$ logical, proving
Theorem D.

This subsection establishes the four structural facts on which (M-im)
rests: the homotopy theorem (R), which confines the safe sector to the
Smith classes; the seam-flux functional, of which only the easy half is
needed downstream; the transport-and-parity description of the Smith
cosets; and the confined CRT frame, which kills two of the five
component sectors outright and pins the remaining three to two affine
relations (the $`\rho`$-links).

## The homotopy theorem (R)

The connecting map of the cover is the Smith map
``` math
\Delta\colon H_2(\mathrm{base})=\ker\partial_2\longrightarrow H_1(\mathrm{base}),
  \qquad \Delta[\zeta]=[\partial_2^{\mathrm{c}}\,\zeta],
```
where $`\partial_2^{\mathrm{c}}`$ is the seam-crossing part of the cover
boundary (so $`\partial_2^{\mathrm{c}}\zeta`$ is a base $`1`$-cycle);
its image $`\mathop{\mathrm{im}}\Delta\subseteq H_1(\mathrm{base})`$ is
cut-independent and equals $`\ker\tau_\ast`$, where
$`\tau_\ast\colon H_1(\mathrm{base})\to H_1(\mathrm{cover})`$ is induced
by the diagonal transfer $`\tau(u)=(u,u)`$.

<div class="thmR">

**Theorem (R)**. *Every cover cycle $`v`$ satisfies
$`[p(v)]\in\mathop{\mathrm{im}}\Delta`$; equivalently
$`\sigma_\ast=\mathrm{id}`$ on $`H_1(\mathrm{gross})`$.*

</div>

<div class="proof">

*Proof.* Work over
$`\mathbb{F}_{2}[\mathbb{Z}_{12}\times\mathbb{Z}_6]`$. Squaring
$`B=y^3+x+x^2`$ kills its $`y`$-dependence: since $`(y^3)^2=y^6=1`$ and
the cross terms vanish in characteristic $`2`$,
$`B^2=y^6+x^2+x^4=1+x^2+x^4`$, so that
``` math
(1+x^2)\,B^2=(1+x^2)(1+x^2+x^4)=1+x^6 .
```
Let $`v=(v_L,v_R)`$ be a cover cycle, so $`A\cdot v_L=B\cdot v_R`$, and
set
``` math
z:=(1+x^2)\cdot B\cdot v_L\in\mathbb{F}_{2}[\mathbb{Z}_{12}\times\mathbb{Z}_6].
```
Using $`\partial_2 z=(B\cdot z,\,A\cdot z)`$, commutativity, and
$`A\cdot v_L=B\cdot v_R`$,
``` math
\partial_2 z
  =\bigl((1+x^2)B^2\,v_L,\ (1+x^2)B\!\cdot\!A\,v_L\bigr)
  =\bigl((1+x^6)\,v_L,\ (1+x^6)\,v_R\bigr)
  =v+\sigma v,
```
since $`\sigma`$ is multiplication by $`x^6`$. Thus
$`(1+\sigma)v=\partial_2 z`$ is a boundary, so $`(1+\sigma)`$ is
null-homotopic on cycles and $`\sigma_\ast=\mathrm{id}`$ on
$`H_1(\mathrm{gross})`$. Consequently
$`\tau_\ast\circ p_\ast=(1+\sigma)_\ast=0`$,
i.e. $`\mathop{\mathrm{im}}p_\ast\subseteq\ker\tau_\ast=\mathop{\mathrm{im}}\Delta`$,
which is the asserted inclusion. ◻

</div>

Only this *inclusion* is load-bearing: the safe-sector floor needs
$`[p(v)]\in\mathop{\mathrm{im}}\Delta\smallsetminus 0`$, and
$`[p(v)]\ne 0`$ is precisely the definition of the safe sector. Neither
the value $`k=12`$ nor the reverse inclusion of (R) is used in the
distance bound.

## No double wrap and the seam flux

Write $`\partial_2^{\mathrm{nc}}`$ for the non-crossing part of the
cover boundary, so
$`\partial_2=\partial_2^{\mathrm{c}}+\partial_2^{\mathrm{nc}}`$, and let
$`\partial_1^{\mathrm c},\partial_1^{\mathrm{nc}}`$ be the analogous
splitting of $`\partial_1`$ at a fixed seam (cut) $`j`$.

<div id="lem:nodoublewrap-statement" class="lemma">

**Lemma 13** (no double wrap). *For every cut $`j`$,
``` math
\partial_1^{\mathrm c}\,\partial_2^{\mathrm{c}}=0,\qquad
  \partial_1^{\mathrm{nc}}\,\partial_2^{\mathrm{nc}}=0,\qquad
  \partial_1^{\mathrm{nc}}\,\partial_2^{\mathrm{c}}=\partial_1^{\mathrm c}\,\partial_2^{\mathrm{nc}}.
```*

</div>

<div class="proof">

*Proof.* An entry of $`\partial_1\partial_2`$ at (check $`c`$, face
$`f`$) is a sum over two-step paths $`f\to\text{qubit}\to c`$, one
summand per factorization $`c\,f^{-1}=a\cdot b`$ along each route (left
block: a $`B`$-step then an $`A`$-step; right block: an $`A`$-step then
a $`B`$-step). The routes contribute in pairs because $`AB=BA`$, so the
total number of paths at the entry is even.

The $`x`$-advance of a path is $`D=s_x(a)+s_x(b)`$. From the
difference-set data, $`s_x`$ of a single $`A`$- or $`B`$-step is at most
$`3`$ and at most $`2`$ respectively, so $`D\le 3+2=5<6`$. Moreover
$`D\equiv (c-f)_x\pmod 6`$, and the constraint $`0\le D\le 5`$ pins
$`D`$ to the unique residue: *$`D`$ is the same integer for every path
at the entry*. A monotone path of total advance $`D<6`$ starting at
$`x_f`$ crosses the seam at most once, and whether it crosses is
determined by the pair $`(x_f,D)`$ alone. Hence all paths at the entry
share one crossing count.

If that count is $`0`$, every path lies entirely in the non-crossing
part and the even set of paths cancels inside
$`\partial_1^{\mathrm{nc}}\partial_2^{\mathrm{nc}}`$, while
$`\partial_1^{\mathrm c}\partial_2^{\mathrm{c}}`$ receives nothing. If
the count is $`1`$, each path crosses in exactly one of its two steps,
so neither $`\partial_1^{\mathrm c}\partial_2^{\mathrm{c}}`$ nor
$`\partial_1^{\mathrm{nc}}\partial_2^{\mathrm{nc}}`$ receives the entry,
and the paths distribute (with even total) between
$`\partial_1^{\mathrm{nc}}\partial_2^{\mathrm{c}}`$ and
$`\partial_1^{\mathrm c}\partial_2^{\mathrm{nc}}`$, forcing those two
entries equal. This proves all three identities. ◻

</div>

<div id="cor:flux" class="corollary">

**Corollary 14** (seam flux). *For each $`\xi\in\ker H_X^{\mathsf T}`$
the map $`\ell_\xi(w)=\xi^{\mathsf T}\partial_1^{\mathrm c}\,w`$
descends to a well-defined functional on $`H_1(\mathrm{base})`$, and
$`\mathop{\mathrm{im}}\Delta\subseteq\ker\ell_\xi`$.*

</div>

<div class="proof">

*Proof.* Well-definedness asks
$`\xi^{\mathsf T}\partial_1^{\mathrm c}\partial_2=0`$. Since
$`\partial_2=\partial_2^{\mathrm{c}}+\partial_2^{\mathrm{nc}}`$,
``` math
\xi^{\mathsf T}\partial_1^{\mathrm c}\partial_2
  =\xi^{\mathsf T}\partial_1^{\mathrm c}\partial_2^{\mathrm{c}}+\xi^{\mathsf T}\partial_1^{\mathrm c}\partial_2^{\mathrm{nc}}
  =0+\xi^{\mathsf T}\partial_1^{\mathrm{nc}}\partial_2^{\mathrm{c}},
```
using
Lemma <a href="#lem:nodoublewrap-statement" data-reference-type="ref"
data-reference="lem:nodoublewrap-statement">13</a>
($`\partial_1^{\mathrm c}\partial_2^{\mathrm{c}}=0`$ and
$`\partial_1^{\mathrm c}\partial_2^{\mathrm{nc}}=\partial_1^{\mathrm{nc}}\partial_2^{\mathrm{c}}`$).
Now $`\xi\in\ker H_X^{\mathsf T}`$ means
$`\xi^{\mathsf T}\partial_1=0`$,
i.e. $`\xi^{\mathsf T}\partial_1^{\mathrm c}=\xi^{\mathsf T}\partial_1^{\mathrm{nc}}`$,
hence
$`\xi^{\mathsf T}\partial_1^{\mathrm{nc}}\partial_2^{\mathrm{c}}=\xi^{\mathsf T}\partial_1^{\mathrm c}\partial_2^{\mathrm{c}}=0`$.
So $`\ell_\xi`$ kills boundaries and descends to $`H_1`$. For the
inclusion, any class in $`\mathop{\mathrm{im}}\Delta`$ is represented by
$`\partial_2^{\mathrm{c}}\zeta`$ with $`\zeta\in\ker\partial_2`$, and
$`\ell_\xi(\partial_2^{\mathrm{c}}\zeta)=\xi^{\mathsf T}\partial_1^{\mathrm c}\partial_2^{\mathrm{c}}\,\zeta=0`$
by the same first identity. Thus
$`\mathop{\mathrm{im}}\Delta\subseteq\ker\ell_\xi`$. ◻

</div>

Only this easy inclusion
$`\mathop{\mathrm{im}}\Delta\subseteq\ker\ell_\xi`$ is used below; it
feeds the tightness construction.

## The Smith cosets: transport and parity

Each nonzero class of $`H_2(\mathrm{base})=\ker\partial_2`$ is realized
by a cycle $`\zeta`$, and the safe sector is governed by the cosets
``` math
C(\zeta)={\partial_2^{\mathrm{c}}}_0\,\zeta+\mathop{\mathrm{im}}\partial_2,
```
taken at the fixed seam $`j=0`$. We first reduce the bookkeeping from
all nonzero classes to five orbit representatives.

#### Transport.

The translations $`T_x,T_y`$ act on chains, and at the chain level one
has the exact identities
``` math
{\partial_2^{\mathrm{c}}}_j\circ T_x=T_x\circ{\partial_2^{\mathrm{c}}}_{j-1},\qquad
  {\partial_2^{\mathrm{c}}}_j\circ T_y=T_y\circ{\partial_2^{\mathrm{c}}}_j ,
```
for every seam $`j`$. Combined with the cut-independence of $`\Delta`$,
these give $`\Delta[T\zeta]=T\cdot\Delta[\zeta]`$ for any translation
$`T`$, so the connecting map is translation-covariant. Consequently a
weight floor proved at the level of orbit representatives transports to
the entire orbit, and to all classes the orbit generates.

<div id="lem:kerdim" class="lemma">

**Lemma 15** (dimension of $`\ker\partial_2`$).
*$`\dim_{\mathbb{F}_{2}}\ker\partial_2=6`$; equivalently
$`\ker\partial_2`$ has $`2^6=64`$ elements, of which $`63`$ are
nonzero.*

</div>

<div class="proof">

*Proof.* Since $`\partial_2\zeta=(B\cdot\zeta,\,A\cdot\zeta)`$, we have
$`\ker\partial_2=\mathop{\mathrm{Ann}}(A)\cap\mathop{\mathrm{Ann}}(B)`$.
The CRT layer frame splits
$`\mathbb{F}_{2}[\mathbb{Z}_6^2]\cong\mathbb{F}_{2}[\mathbb{Z}_2^2]\times\mathbb{F}_{4}[\mathbb{Z}_2^2]^4`$
as $`\mathbb{F}_{2}`$-algebras, and multiplication by $`A`$
(resp. $`B`$) acts on component $`j`$ as multiplication by $`\hat{A}_j`$
(resp. $`\hat{B}_j`$). Hence
``` math
\ker\partial_2=\bigoplus_{j=0}^{4}\bigl(\mathop{\mathrm{Ann}}(\hat{A}_j)\cap\mathop{\mathrm{Ann}}(\hat{B}_j)\bigr),
```
and each summand is read off the multiplier table and the Engine
Lemma <a href="#lem:engine" data-reference-type="ref"
data-reference="lem:engine">2</a>:

- $`j=0`$: $`\hat{A}_0=\hat{B}_0=1+u+v`$ is a unit, so
  $`\mathop{\mathrm{Ann}}(\hat{A}_0)=0`$.

- $`j=1`$: $`\hat{B}_1=1+u+v`$ is a unit, so
  $`\mathop{\mathrm{Ann}}(\hat{B}_1)=0`$ and the intersection is $`0`$.

- $`j=2`$: $`\hat{A}_2=1+u+v`$ is a unit, so
  $`\mathop{\mathrm{Ann}}(\hat{A}_2)=0`$ and the intersection is $`0`$.

- $`j=3`$: $`\hat{A}_3=u+\omega v`$ and $`\hat{B}_3=\omega u+v`$ are
  $`\mathbb{F}_{4}`$-independent radicals, with
  $`\mathop{\mathrm{Ann}}(\hat{A}_3)=\mathbb{F}_{4}\hat{A}_3+\mathbb{F}_{4}\,uv`$
  and
  $`\mathop{\mathrm{Ann}}(\hat{B}_3)=\mathbb{F}_{4}\hat{B}_3+\mathbb{F}_{4}\,uv`$
  (Engine Lemma). An element
  $`\alpha\hat{A}_3+\beta\,uv=\gamma\hat{B}_3+\delta\,uv`$ of the
  intersection forces $`\alpha=\gamma=0`$ (independence of
  $`\hat{A}_3,\hat{B}_3`$) and $`\beta=\delta`$, leaving
  $`\mathbb{F}_{4}\,uv`$, of $`\mathbb{F}_{2}`$-dimension $`2`$.

- $`j=4`$: $`\hat{B}_4=\omega\hat{A}_4`$, so
  $`\mathop{\mathrm{Ann}}(\hat{A}_4)=\mathop{\mathrm{Ann}}(\hat{B}_4)`$
  and the intersection is
  $`\mathop{\mathrm{Ann}}(\hat{A}_4)=\mathbb{F}_{4}\hat{A}_4+\mathbb{F}_{4}\,uv`$,
  of $`\mathbb{F}_{2}`$-dimension $`4`$.

Summing, $`\dim_{\mathbb{F}_{2}}\ker\partial_2=0+0+0+2+4=6`$. ◻

</div>

<div id="prop:smithorbits" class="proposition">

**Proposition 16** (orbit structure). *The set
$`\ker\partial_2\smallsetminus 0`$ consists of exactly five translation
orbits, with $`(\text{size},\text{weight})`$ equal to
``` math
(9,16),\quad (12,18),\quad (36,18),\quad (3,24),\quad (3,24).
```
Their orbit sums account for all $`63`$ nonzero Smith classes; in
particular the five canonical representatives, transported by
$`T_x,T_y`$, cover every nonzero Smith class.*

</div>

<div class="proof">

*Proof.* By Lemma <a href="#lem:kerdim" data-reference-type="ref"
data-reference="lem:kerdim">15</a>, $`\ker\partial_2`$ has $`63`$
nonzero elements. The translation group $`\mathbb{Z}_6^2`$ (order
$`36`$) acts on $`\ker\partial_2`$ preserving Hamming weight, so
computing the weight of each nonzero element and grouping the $`63`$ of
them into translation orbits is a finite direct enumeration. It produces
exactly five orbits; each orbit size is $`36`$ divided by the order of
the translation stabilizer of a representative, giving $`9=36/4`$,
$`12=36/3`$, $`36=36/1`$, $`3=36/12`$, $`3=36/12`$, with the stated
minimum weights. As $`9+12+36+3+3=63`$, these orbits exhaust the nonzero
elements. Finally, translation-covariance of $`\Delta`$ (above) gives
$`\Delta[T\zeta]=T\cdot\Delta[\zeta]`$, so transporting the five
representatives by $`T_x,T_y`$ covers every nonzero Smith class. ◻

</div>

The five orbits are written $`\mathrm{wt}\text{-}16`$,
$`\mathrm{wt}\text{-}18\mathrm a`$, $`\mathrm{wt}\text{-}18\mathrm b`$,
$`\mathrm{wt}\text{-}24\mathrm a`$, $`\mathrm{wt}\text{-}24\mathrm b`$.

#### Parity.

Two parity facts cut the candidate sub-$`12`$ weights down to a single
residue. For a layer $`f\in\mathbb{F}_{2}[\mathbb{Z}_3^2]`$, weight is
congruent to the trivial Fourier coefficient,
$`\lvert f\rvert\equiv\hat f(\mathrm{triv})\pmod 2`$. Every
$`\zeta\in\ker\partial_2`$ has even columns: the relation
$`A\cdot\zeta=0`$ reads columnwise as $`c_{i+3}=(y+y^2)c_i`$, and
$`\varepsilon(y+y^2)=0`$, so each column of $`\zeta`$ has even
augmentation, hence even weight; the rows mirror this through $`B`$.
Combining with the previous fact, every element of every Smith coset has
even Hamming weight (and even seam value-cost). Therefore the only
weights below $`12`$ that any coset element could have are $`6`$, $`8`$,
$`10`$, and the floor below rules out $`6`$ and $`8`$, leaving weight
exactly $`10`$ as the single case the kill step must eliminate.

## The confined frame: off-vanishing and the $`\rho`$-links

We now diagonalize the relevant convolution operators by the CRT layer
frame over $`\mathbb{F}_{4}`$, which decomposes
$`\mathbb{F}_{2}[\mathbb{Z}_6^2]`$ into five components $`j=0,\dots,4`$;
write $`\hat{A}_j,\hat{B}_j`$ for the layer multipliers. For a generic
coset element
``` math
w={\partial_2^{\mathrm{c}}}_0\,\zeta+\partial_2 t,\qquad t\in\mathbb{F}_{2}[\mathbb{Z}_6^2],
```
the per-component data is
``` math
V_j(w)=\mathrm{off}_j+\bigl(\hat{B}_j\,\hat t_j,\ \hat{A}_j\,\hat t_j\bigr),
  \qquad \mathrm{off}_j=\mathrm{comp}_j({\partial_2^{\mathrm{c}}}_0\,\zeta),
```
with the five components independent. Here $`V_j=(V_jL,V_jR)`$ records
the left/right block data at component $`j`$.

<div id="lem:offvanish-statement" class="lemma">

**Lemma 17** (off-vanishing at components $`0,2`$).
*$`\mathrm{off}_0=\mathrm{off}_2=0`$ identically. Consequently the
component-$`0`$ data of every coset element is the diagonal pair
$`(V_0,V_0)`$ with $`V_0=\hat{B}_0\hat t_0`$ ranging over all $`16`$
elements of $`\mathbb{F}_{2}[\mathbb{Z}_2^2]`$ (as $`\hat{B}_0`$ is a
unit), and the component-$`2`$ data is the free graph
$`V_2L=\rho_2\cdot V_2R`$, $`\rho_2:=\hat{B}_2\hat{A}_2^{-1}`$.*

</div>

<div class="proof">

*Proof.* At components $`0`$ and $`2`$ the $`A`$-relation multiplier
$`\mathrm{comp}(y+y^2)`$ equals $`Y:=1+s_y`$: at $`j=0`$ both component
characters are trivial, and at $`j=2`$ the character is trivial on
$`t_y`$. The column-collapse $`v_i`$ of $`\zeta`$ at such a component
therefore satisfies
``` math
v_i=Y\,v_{i+3}=Y^2 v_i=0,
```
because $`Y^2=(1+s_y)^2=1+s_y^2=0`$ in the component algebra
($`s_y^2=1`$). The seam-marked sums that build $`\mathrm{off}_0`$ and
$`\mathrm{off}_2`$ are sums of these vanishing collapses, so
$`\mathrm{off}_0=\mathrm{off}_2=0`$. With $`\mathrm{off}_0=0`$, the
component-$`0`$ data is $`(\hat{B}_0\hat t_0,\hat{A}_0\hat t_0)`$; both
$`\hat{A}_0,\hat{B}_0`$ are units and at $`j=0`$ they coincide, giving
the diagonal pair $`(V_0,V_0)`$ with $`V_0`$ free over all of
$`\mathbb{F}_{2}[\mathbb{Z}_2^2]`$. With $`\mathrm{off}_2=0`$, the
component-$`2`$ data is $`(\hat{B}_2\hat t_2,\hat{A}_2\hat t_2)`$,
i.e. the graph $`V_2L=\rho_2\,V_2R`$ through the origin,
$`\rho_2=\hat{B}_2\hat{A}_2^{-1}`$. ◻

</div>

<div id="lem:c1zero" class="lemma">

**Lemma 18** (component $`1`$ collapses). *The component-$`1`$ data
satisfies the single relation $`V_1R=\rho_1\,V_1L`$ with
$`\rho_1:=\hat{A}_1\hat{B}_1^{-1}`$; in particular the residual
obstruction $`c_1`$ vanishes identically.*

</div>

<div class="proof">

*Proof.* Let $`c_0,\dots,c_5`$ be the columns of $`\zeta`$ and
$`\hat u_i\in\mathbb{F}_{4}[s_y]`$ their component-$`1`$ transforms. The
crossing bookkeeping at seam $`0`$ gives
``` math
\mathrm{off}_1L=\hat u_4+\hat u_5+s_x\hat u_5,\qquad
  \mathrm{off}_1R=\hat u_3+s_x\hat u_4+\hat u_5 .
```
The cycle relations transform to
``` math
\hat u_{i+3}=\tau\,\hat u_i\quad(\tau=\omega^2+\omega s_y,\ \text{a unit}),
  \qquad \hat u_{i-1}+\hat u_{i-2}=s_y\,\hat u_i,
```
the second giving $`\hat u_0=\hat u_1+s_y\hat u_2`$ and hence
``` math
\begin{equation}
  Y\hat u_1=\omega^2 Y\hat u_2.\tag{D1}
\end{equation}
```
The residual obstruction is
$`c_1:=\mathrm{off}_1R+\rho_1^{-1}\!\cdot\!\mathrm{off}_1L`$ (the
right-block data after normalizing the left through $`\rho_1`$).
Reducing the group coefficients with $`\hat{B}_1 X=s_x X`$ and
$`\hat{B}_1 Y=s_x Y`$ (and the corresponding action on $`\hat{A}_1`$),
the claim $`c_1=0`$ collapses to
``` math
Y\bigl[(X+\omega)\hat u_1+(\omega+\omega^2 s_x)\hat u_2\bigr]=0 .
```
Applying (D1) replaces $`Y\hat u_1`$ by $`\omega^2 Y\hat u_2`$, and the
bracket collapses to
``` math
Y(\omega^2+\omega+1)\hat u_2=0,
```
which is identically zero since $`\omega^2+\omega+1=0`$ in
$`\mathbb{F}_{4}`$. Hence $`c_1=0`$, and the component-$`1`$ graph
passes through the origin: $`V_1R=\rho_1 V_1L`$. ◻

</div>

By Lemma <a href="#lem:offvanish-statement" data-reference-type="ref"
data-reference="lem:offvanish-statement">17</a>, $`\mathrm{off}_2=0`$,
so the component-$`2`$ graph likewise passes through the origin and the
analogous obstruction $`c_2`$ vanishes by a one-line argument: with no
offset, $`V_2L=\rho_2 V_2R`$ holds with no constant correction.

#### The two $`\rho`$-links and the confined sets.

Assembling the three preceding facts, on every Smith coset the
component-$`1,2`$ data obeys the two affine relations
``` math
V_1R=\rho_1\cdot V_1L,\qquad V_2L=\rho_2\cdot V_2R,
  \qquad \rho_1=\hat{A}_1\hat{B}_1^{-1},\ \ \rho_2=\hat{B}_2\hat{A}_2^{-1}.
```
Relaxing the free sides, the *confined sets* (the values available to
the dependent sides) are exactly $`\mathop{\mathrm{im}}\rho_1`$ and
$`\mathop{\mathrm{im}}\rho_2`$, each of size $`16`$. Indeed each
$`\rho_i`$ satisfies
``` math
\rho_i^2=\varepsilon(\rho_i)^2\cdot 1=0
```
(squaring in $`\mathbb{F}_{4}[\mathbb{Z}_2^2]`$ is the Frobenius-linear
map and $`g^2=e`$ for $`g\in\mathbb{Z}_2^2`$, so $`\rho_i^2`$ depends
only on $`\varepsilon(\rho_i)`$, which is $`0`$), while
$`\rho_i\notin\mathbb{F}_{4}\cdot\textstyle\sum_G`$; hence
$`\mathop{\mathrm{im}}\rho_i`$ is a $`16`$-element
$`\mathbb{F}_{4}`$-subspace, the affine line of the labeling. These two
$`\rho`$-links, together with the free component-$`0`$ datum $`V_0`$ and
the spine data at components $`3,4`$, are the input to the slot frame,
where the weight floor (M-im) is proved.

# The slot frame

All five Smith orbits of the base $`Z`$-stabilizer space are now placed
in a single coordinate system. Throughout,
$`b=\partial_2 z=(B\cdot z,\ A\cdot z)`$ is a base $`Z`$-stabilizer,
decomposed into its five CRT components $`V_0,\dots,V_4`$ via the layer
frame of the Engine Lemma. The components $`0`$–$`2`$ are pinned by the
$`\rho`$-links (off$`{}_0=`$ off$`{}_2=0`$, the diagonal $`V_0`$-datum,
and $`V_1^R=\rho_1\,V_1^L`$, $`V_2^L=\rho_2\,V_2^R`$); the components
$`3`$ and $`4`$ carry the genuine freedom. The slot frame organizes that
freedom.

## Slots, labelings, lines

*Slots* are the four elements of the $`2`$-part group
$`\mathbb{Z}_2^2=\{e,x,y,xy\}`$ (the layers of the Engine Lemma).
Component data live in $`R=\mathbb{F}_{4}[\mathbb{Z}_2^2]`$, identified
with functions $`\{\text{slots}\}\to\mathbb{F}_{4}`$, the *slot values*.
Writing $`X=1+s_x`$, $`Y=1+s_y`$, $`XY=\sum_{g\in\mathbb{Z}_2^2}g`$, the
slot values of $`a\cdot 1+\alpha X+\beta Y+\delta XY`$ over
$`(e,x,y,xy)`$ are
``` math
\bigl(a+\alpha+\beta+\delta,\ \alpha+\delta,\ \beta+\delta,\ \delta\bigr).
```
The *kill vector*
``` math
\kappa(v):=(a+\alpha+\beta,\ \alpha,\ \beta,\ 0)
```
records the slot function of $`v`$ modulo the constant shift $`\delta`$:
as the free shift $`\delta'`$ varies, the zero set of $`v+\delta'XY`$ is
a fibre of $`\kappa(v)`$. Define the labeling vectors
``` math
\ell:=\kappa(\hat{B})=(\omega^2,\omega,1,0),\qquad
  \ell':=\kappa(\hat{A}_3)=(\omega^2,1,\omega,0)=\ell\circ(x\leftrightarrow y),
```
where $`\hat{B}=\hat{B}_2=\hat{B}_3=\hat{B}_4=\omega X+Y`$ and
$`\hat{A}_1=\hat{A}_3=X+\omega Y`$, and the two parity vectors
``` math
\theta:=(1,0,1,0),\qquad \tilde\theta:=(1,1,0,0).
```

For brevity in the orbit-by-orbit analysis below we also write
$`m:=\ell`$ and $`m':=\ell'`$ for these two labeling vectors.

<div id="lem:labelfacts" class="lemma">

**Lemma 19** (labeling facts). *The maps
$`\ell,\ell'\colon\{\text{slots}\}\to\mathbb{F}_{4}`$ are bijections;
$`\tilde{\ell}:=\ell+\omega^2`$ is an additive isomorphism
$`\mathbb{Z}_2^2\xrightarrow{\ \sim\ }(\mathbb{F}_{4},+)`$. Entrywise
Frobenius gives
``` math
\kappa(\hat{A}_4)=\ell'^{\,2}=\omega^2\ell,\qquad \ell^2=\omega^2\ell',
```
and the two $`\rho`$-multipliers satisfy
``` math
\kappa(\rho_2)=\ell,\qquad \kappa(\rho_1)=\ell'.
```
The parity vectors are the trace characters
$`\theta=1+\operatorname{Tr}(\omega^2\tilde{\ell})`$ and
$`\tilde\theta=1+\operatorname{Tr}(\tilde{\ell})`$.*

</div>

<div class="proof">

*Proof.* Each assertion is a direct entrywise evaluation. From
$`\ell=(\omega^2,\omega,1,0)`$ one reads off that all four values are
distinct, so $`\ell`$ is a bijection, and likewise $`\ell'`$. Adding the
constant $`\omega^2`$ sends $`\ell`$ to
$`(0,\omega^2+\omega,\omega^2+1,\omega^2)`$; over the identification
$`\mathbb{F}_{4}=\{0,1,\omega,\omega^2\}`$ this is the standard additive
chart $`\mathbb{Z}_2^2\to\mathbb{F}_{4}`$, so $`\tilde{\ell}`$ is an
additive isomorphism. Squaring in $`\mathbb{F}_{4}`$ is the Frobenius
automorphism $`t\mapsto t^2`$, which fixes $`0,1`$ and swaps
$`\omega,\omega^2`$; applying it entrywise to
$`\ell'=(\omega^2,1,\omega,0)`$ gives
$`(\omega,1,\omega^2,0)=\omega^2\ell`$, and to $`\ell`$ gives
$`(\omega,\omega^2,1,0)=\omega^2\ell'`$. The identities
$`\kappa(\rho_2)=\ell`$, $`\kappa(\rho_1)=\ell'`$ are the kill vectors
of $`\rho_2=\hat{B}_2\hat{A}_2^{-1}`$ and
$`\rho_1=\hat{B}_1\hat{A}_1^{-1}`$, computed from their unit/radical
factors. Finally $`\operatorname{Tr}(\omega^2\tilde{\ell})`$ and
$`\operatorname{Tr}(\tilde{\ell})`$ are the $`\mathbb{F}_{2}`$-valued
slot functions $`1+\theta`$ and $`1+\tilde\theta`$, again by a slotwise
table. ◻

</div>

#### Confined and component lines.

A direct check of the slot images of the confined images and the two
nondegenerate components yields the following descriptions. The free
side of each $`\rho`$-link contributes an unconstrained constant
$`c\in\mathbb{F}_{4}`$ (a free $`XY`$-shift), so each set is a full
affine line in $`R`$.

- **Confined lines.** The slot values of $`\mathop{\mathrm{im}}\rho_2`$
  are $`\{p\,\ell+c:p,c\in\mathbb{F}_{4}\}`$ and those of
  $`\mathop{\mathrm{im}}\rho_1`$ are $`\{p\,\ell'+c\}`$ — the full
  affine line through the labeling direction.

- **Component $`3`$.** On the left block,
  $`V_3^L=\mathrm{off}_3^L+a_3\hat{B}+\beta\,XY`$ has slot values
  $`\kappa_3^L+a_3\ell+c_3`$ with $`c_3\in\mathbb{F}_{4}`$ free (the
  coefficient $`\beta`$ absorbs the $`XY`$-part of the offset) and
  $`\kappa_3^L:=\kappa(\mathrm{off}_3^L)`$. The right block is the
  mirror, with $`\ell'`$ in place of $`\ell`$ and $`\kappa_3^R`$. The
  spine coordinate $`a_3`$ is *shared* between the two blocks; the two
  constants $`c_3`$ are free and independent.

- **Component $`4`$.** The component-$`4`$ ideal is one-dimensional
  because $`\hat{B}_4=\omega\hat{A}_4`$, which forces the *tie*
  ``` math
  V_4^L=\omega\,V_4^R+w_4,\qquad w_4:=\mathrm{off}_4^L+\omega\,\mathrm{off}_4^R,
  ```
  a fixed vector per orbit. In slot values the directions are
  ``` math
  k_4^L=\kappa_4^L+a_4\ell,\qquad k_4^R=\kappa_4^R+\omega^2 a_4\ell
  ```
  (the $`\omega`$-twist absorbs into $`\omega a_4\ell'^{\,2}=a_4\ell`$),
  with constants tied through a shared scalar $`\gamma`$:
  ``` math
  d_4^L=\omega\gamma+e_L,\qquad d_4^R=\gamma+e_R,
  ```
  where $`e_\bullet`$ denotes the $`XY`$-coefficient of the block’s
  component-$`4`$ offset, and $`e_L=\omega e_R+w_4^{XY}`$ with
  $`w_4^{XY}`$ the $`XY`$-coefficient of $`w_4`$.

#### Per-orbit data.

Computing the offsets $`\mathrm{off}_3^\bullet,\mathrm{off}_4^\bullet`$
of the five canonical Smith cosets and reading off their kill vectors
gives the table below (offsets recorded as kill vectors;
$`\mathbb{F}_{4}`$ written $`1,\omega,\omega^2`$).

<div class="center">

| orbit | $`\kappa_3^L`$ | $`\kappa_3^R`$ | $`\kappa_4^L`$ | $`\kappa_4^R`$ | $`e_L`$ | $`e_R`$ |
|:---|:--:|:--:|:--:|:--:|:--:|:--:|
| $`\text{wt-}16`$ | $`\omega\theta`$ | $`\theta`$ | $`\omega\theta`$ | $`\theta`$ | $`\omega`$ | $`\omega`$ |
| $`\text{wt-}18a`$ | $`\ell`$ | $`\ell'`$ | $`(0,\omega,\omega^2,0)`$ | $`(\omega^2,\omega^2,\omega^2,0)`$ | $`\omega^2`$ | $`\omega^2`$ |
| $`\text{wt-}18b`$ | $`(1,\omega,\omega^2,0)`$ | $`\omega^2\ell`$ | $`(\omega,\omega,1,0)`$ | $`(\omega,\omega^2,\omega,0)`$ | $`1`$ | $`1`$ |
| $`\text{wt-}24a`$ | $`0`$ | $`0`$ | $`\omega\theta`$ | $`\theta`$ | $`\omega^2`$ | $`1`$ |
| $`\text{wt-}24b`$ | $`\omega\theta`$ | $`\theta`$ | $`0`$ | $`0`$ | $`1`$ | $`\omega^2`$ |

</div>

The last row is the previous one with the component-$`3`$ and
component-$`4`$ offsets exchanged.

## The slot-cost rules

We now record the per-slot layer cost. For a single slot $`s`$ and a
single block, fix the four component values
$`(v_0;v_{\mathrm{conf}},v_3,v_4)(s)`$ at that slot (here
$`v_{\mathrm{conf}}=v_2`$ is the confined component); the block’s other
unit-side component is free. The cost is the minimum layer weight
realizing this slot datum.

<div id="lem:slotcost" class="lemma">

**Lemma 20** (slot-cost rules). *The per-slot layer cost is governed by
the radical rigidity $`\psi_2^2=\psi_3\psi_4`$, $`\psi_4=\psi_1\psi_3`$
and the layer dictionary $`E\le 2`$ value rigidity, and equals
``` math
\begin{aligned}
  v_0=0:\quad & \text{$0$ alive}\to 0;\quad \text{$1$ alive}\to 4;\quad
    \text{$2$ alive}\to 2;\\
  & \text{$3$ alive}\to 2 \text{ if } T=1,\ \text{else } 4;\\
  v_0=1:\quad & \text{$3$ alive with $T=1$}\to 1\ (\text{$\delta$-point});\quad
    \text{else}\to 3,
\end{aligned}
```
where “alive” counts the nonzero values among the block’s three
constrained components and the rigidity datum is
``` math
T_L=v_2^2(v_3v_4)^{-1},\qquad T_R=v_4(v_1v_3)^{-1}.
```
The $`v_0`$-free cost is the minimum over $`v_0\in\{0,1\}`$, namely
``` math
(0,\ 3,\ 2,\ 1\text{ if cheap else }3)\quad\text{by alive count }(0,1,2,3).
```*

</div>

<div class="proof">

*Proof.* A layer of $`f`$ supported at the slot $`s`$ contributes
Fourier mass to the four components according to the characters
$`\psi_1,\dots,\psi_4`$; by the Engine Lemma the relations
$`\psi_3=\psi_1\psi_2`$ and $`\psi_4=\psi_1\psi_3`$ (hence
$`\psi_2^2=\psi_3\psi_4`$) constrain which value patterns are
realizable, and the layer dictionary fixes the minimum weight of a layer
with $`E\le 2`$ prescribed nonzero component values. The minimum layer
weight realizing a slot datum with $`k`$ alive constrained components
and parity $`v_0`$ is then read off the dictionary $`d_3`$: with
$`v_0=0`$ (even layer), no alive components costs $`0`$; one alive
component is a single nonzero radical value, forcing a full or co-point
layer of weight $`4`$; two alive components costs $`2`$; three alive
components costs $`2`$ precisely when the rigidity $`T=1`$ holds (so all
three values are consistent with a single $`\delta`$-line, attaining the
dictionary minimum), and $`4`$ otherwise. With $`v_0=1`$ (odd layer) the
cheapest realization of three alive components with $`T=1`$ is a single
$`\delta`$-point, of weight $`1`$; every other odd configuration costs
$`3`$. Minimizing over the parity gives the stated $`v_0`$-free costs. ◻

</div>

<div class="remark">

*Remark 3* (slot parity). Every per-slot cost is congruent to
$`v_0\pmod 2`$, since an odd layer has odd weight and an even layer even
weight. Summing over the four slots, a block’s total cost is
$`\equiv\lvert V_0\rvert\pmod 2`$; hence any two blocks sharing the same
$`V_0`$ have costs of equal parity, and in particular every
per-$`(V_0,\gamma)`$ cost sum is even.

</div>

## Fibres of affine pencils

The slot-cost rules are driven by the alive set of a slot direction,
i.e. by the fibre partition of an affine slot function. This is governed
by a single elementary count.

<div id="lem:pencil" class="lemma">

**Lemma 21** (pair-ratio). *Let $`k=\kappa+\lambda u`$ with
$`u\colon\{\text{slots}\}\to\mathbb{F}_{4}`$ a bijection. For each of
the six unordered slot pairs $`P=\{s,s'\}`$ there is exactly one pencil
parameter
``` math
\lambda_P=\bigl(\kappa(s)+\kappa(s')\bigr)\bigl(u(s)+u(s')\bigr)^{-1}
```
at which $`k(s)=k(s')`$. The fibre partition of $`k`$ at a given
$`\lambda`$ is read off from $`\{P:\lambda_P=\lambda\}`$.*

</div>

<div class="proof">

*Proof.* Because $`u`$ is a bijection, $`u(s)+u(s')\ne 0`$ for
$`s\ne s'`$, so the equation
$`\kappa(s)+\lambda u(s)=\kappa(s')+\lambda u(s')`$ has the unique
solution $`\lambda_P`$. The slots $`s,s'`$ lie in the same fibre of
$`k`$ exactly when $`\lambda=\lambda_P`$, and collecting all pairs with
$`\lambda_P=\lambda`$ gives the fibre partition. ◻

</div>

<div id="cor:comp4trich" class="corollary">

**Corollary 22** (the component-$`4`$ trichotomy). *For the
standard-form direction $`k=b\ell+\omega\theta`$ (so
$`\kappa=\omega\theta`$, $`u=\ell`$): $`\lambda_P=0`$ on the two
$`\theta`$-constant pairs $`\{e,y\}`$, $`\{x,xy\}`$; on the four
$`\theta`$-split pairs $`\lambda_P=\omega\,\Delta\ell(P)^{-1}`$, giving
$`\lambda=\omega`$ on $`\{e,x\},\{y,xy\}`$ and $`\lambda=\omega^2`$ on
$`\{e,xy\},\{x,y\}`$. Consequently $`b\in\{0,\omega,\omega^2\}`$ makes
$`k`$ double-paired (its fibre partition is one of the three
pair-partitions of the slots, with alive sets of size $`2`$ or $`4`$),
while $`b=1`$ makes $`k=(1,\omega,\omega^2,0)`$ a bijection (alive sets
of size $`3`$ with any dead slot).*

</div>

<div class="proof">

*Proof.* Substitute $`\kappa=\omega\theta=(\omega,0,\omega,0)`$ and
$`u=\ell`$ into the pair-ratio formula. The pairs $`\{e,y\}`$ and
$`\{x,xy\}`$ have equal $`\theta`$-values, so $`\kappa(s)+\kappa(s')=0`$
and $`\lambda_P=0`$; the remaining four pairs have
$`\kappa(s)+\kappa(s')=\omega`$ and $`\lambda_P=\omega(\Delta
\ell(P))^{-1}`$, evaluated from the entries of $`\ell`$. The trichotomy
is the list of $`b`$-values for which $`k`$ is constant on a
pair-partition versus injective. ◻

</div>

## The chord-slope lemma and hyperbolic quadruples

The cost of the most constrained configurations turns on whether four
points of the affine plane $`AG(2,\mathbb{F}_{4})`$ are in general
position.

<div id="lem:chord" class="lemma">

**Lemma 23** (chord slope). *Let
$`u,k\colon\{\text{slots}\}\to\mathbb{F}_{4}`$ with $`u`$ bijective, fix
a slot $`z`$, and set
``` math
g(s)=\bigl(u(s)+u(z)\bigr)\bigl(k(s)+k(z)\bigr)^{-1}
```
on the three slots $`s\ne z`$ (defined when $`k`$ is injective off the
fibre of $`z`$). Then $`g(s)=g(s')`$ if and only if the three points
$`(u(s),k(s))`$, $`(u(s'),k(s'))`$, $`(u(z),k(z))`$ of
$`AG(2,\mathbb{F}_{4})`$ are collinear. In particular, if no three of
the four points $`(u(s),k(s))`$ are collinear, then $`g`$ is injective
for every choice of $`z`$.*

</div>

<div class="proof">

*Proof.* The quantity $`g(s)`$ is the reciprocal slope of the chord from
$`(u(z),k(z))`$ to $`(u(s),k(s))`$. Two chords from a common point
$`(u(z),k(z))`$ have equal slope exactly when the three endpoints are
collinear. Thus $`g(s)=g(s')`$ iff the three named points lie on a line,
and $`g`$ is injective for all $`z`$ iff no three of the four points are
collinear. ◻

</div>

<div id="lem:hyperbolic" class="lemma">

**Lemma 24** (hyperbolic quadruple). *For $`c\in\mathbb{F}_{4}^\times`$,
the four points
``` math
H_c=\{(t,\ c\,t^{-1}):t\in\mathbb{F}_{4}^\times\}\cup\{(0,0)\}
```
have no three collinear, and every chord $`(\Delta u,\Delta v)`$ of
$`H_c`$ satisfies $`\Delta u\cdot\Delta v=c`$.*

</div>

<div class="proof">

*Proof.* A line $`v=\lambda u`$ through the origin meets the hyperbola
$`uv=c`$ where $`\lambda u^2=c`$; since squaring is a bijection of
$`\mathbb{F}_{4}`$, this has exactly one solution, so such a line meets
$`H_c`$ in at most the origin and one further point. A line
$`v=\lambda u+c'`$ with $`c'\ne 0`$ meets the hyperbola where
$`\lambda u^2+c'u+c=0`$, a quadratic with at most two roots. Hence no
line meets $`H_c`$ in three points. For the chord identity, if
$`(u_1,c u_1^{-1})`$ and $`(u_2,c u_2^{-1})`$ are two finite points then
$`\Delta u=u_1+u_2`$ and $`\Delta v=c(u_1^{-1}+u_2^{-1})`$, so
``` math
\Delta u\cdot\Delta v=c(u_1+u_2)(u_1^{-1}+u_2^{-1})
   =c\bigl(1+u_1u_2^{-1}+u_2u_1^{-1}+1\bigr)
   =c\bigl(u_1u_2^{-1}+u_2u_1^{-1}\bigr),
```
and over $`\mathbb{F}_{4}`$ one checks $`r+r^{-1}=1`$ for every
$`r\in\mathbb{F}_{4}^\times\smallsetminus\{1\}`$ (here
$`r=u_1u_2^{-1}\ne 1`$), giving $`\Delta u\cdot\Delta v=c`$. The chord
from the origin to $`(u_1,cu_1^{-1})`$ has
$`\Delta u\cdot\Delta v=u_1\cdot cu_1^{-1}=c`$ as well. ◻

</div>

<div class="remark">

*Remark 4*. The deepest slope case of the standard-form walk uses
exactly one instance: the pair $`(\ell,\ell+\omega\theta)`$ is the
quadruple
$`\{(\omega^2,1),(\omega,\omega),(1,\omega^2),(0,0)\}=H_{\omega^2}`$,
since the four products $`\ell\cdot(\ell+\omega\theta)`$ equal
$`\omega^2,\omega^2,\omega^2,0`$.

</div>

## Cost-preserving moves and the standard form

<div class="lemma">

**Lemma 25** (cost-preserving moves). *The block cost is invariant under
each of the following operations.*

1.  ***Slot relabelings** applied simultaneously to all components and
    to $`V_0`$ (the cost is a sum over slots).*

2.  ***Translation scalings**
    $`(v_{\mathrm{conf}},v_3,v_4)\mapsto(s_2 v_2,s_3 v_3,s_4 v_4)`$ with
    $`s_2^2=s_3 s_4`$ (the nine cell symmetries of the value table); the
    confined line is scale-invariant.*

3.  ***Frobenius** applied to all values (a value-table symmetry);
    moreover the right-block value table $`M_2(v_0,\cdot,\cdot,v_4)`$
    equals $`M_1(v_0,\cdot,\cdot,v_4^2)`$, so an $`R`$-block is an
    $`L`$-type problem after Frobenius on its component-$`4`$ values.*

</div>

<div class="proof">

*Proof.* (1) The block cost is a sum over slots of per-slot costs, and a
slot relabeling permutes the summands. (2) The rigidity datum
$`T_L=v_2^2(v_3v_4)^{-1}`$ is unchanged by
$`(v_2,v_3,v_4)\mapsto(s_2 v_2,s_3 v_3,s_4 v_4)`$ precisely when
$`s_2^2=s_3 s_4`$, and the confined line $`\langle\ell\rangle`$ is
closed under scaling; the alive sets and hence the per-slot costs are
preserved. (3) Frobenius is an automorphism of $`\mathbb{F}_{4}`$ fixing
the value-table relations, and the stated identity
$`M_2=M_1(\cdot,\cdot,\cdot,v_4^2)`$ is the entrywise comparison of the
left- and right-block rigidity data, which differ only by squaring the
component-$`4`$ value. ◻

</div>

<div class="definition">

**Definition 26** (standard form). Let $`S(a,b)`$ be the $`v_0`$-free
block problem with confined line $`\langle\ell\rangle`$, component-$`3`$
direction $`v_3=a\ell+c_3`$, and component-$`4`$ direction
$`v_4=b\ell+\omega\theta+c_4`$, with $`c_3,c_4\in\mathbb{F}_{4}`$ free.

</div>

<div id="lem:stdform" class="lemma">

**Lemma 27** (reduction to standard form). *With the spine coordinate
written $`(a_3,a_4)`$, the four $`\text{wt-}24`$ block problems reduce
as
``` math
L(24a)=S(a_3,a_4),\quad L(24b)=S(a_4,a_3),\quad
  R(24a)\cong S(a_3,a_4^2),\quad R(24b)\cong S(a_4^2,a_3).
```*

</div>

<div class="proof">

*Proof.* For $`L(24a)`$ this is the definition: the per-orbit table
gives $`\kappa_3^L=0`$ and $`\kappa_4^L=\omega\theta`$, so
$`v_3=a_3\ell+c_3`$ and $`v_4=a_4\ell+\omega\theta+c_4`$. For $`L(24b)`$
the offsets exchange roles, and the $`v_3\leftrightarrow v_4`$ symmetry
of $`T_L=v_2^2(v_3v_4)^{-1}`$ identifies the cost with $`S(a_4,a_3)`$.
For $`R(24a)`$: apply Frobenius to component $`4`$ (move 3), which sends
the data to $`(\ell';\,a_3\ell';\,a_4^2\ell'+\theta)`$ using $`\theta^2=
\theta`$ and $`(\omega^2 a_4\ell)^2=a_4^2\ell'`$; apply the slot swap
$`x\leftrightarrow y`$ (move 1) to obtain $`(\ell;\,a_3\ell;\,a_4^2\ell+
\tilde\theta)`$; apply the slot map $`\sigma`$ induced by
$`\tilde{\ell}\mapsto\omega^2\tilde{\ell}`$ (move 1), which sends
$`\tilde\theta\mapsto\theta`$ and $`\ell\mapsto\omega^2\ell+1`$; finally
scale by $`(\omega,\omega,\omega)`$ (move 2). The result is
$`S(a_3,a_4^2)`$. The orbit $`R(24b)`$ mirrors $`R(24a)`$ with the spine
coordinates exchanged. ◻

</div>

## The achiever-structure lemma

Fix an orbit and a spine cell. For each shared pair $`(V_0,\gamma)`$ let
$`\min_L(V_0,\gamma)`$ and $`\min_R(V_0,\gamma)`$ be the per-block
linked minima, each minimized over the block’s own knobs — the confined
point on its line, the constant $`c_3`$, and the free side of its
per-slot minimizations. By the slot parity remark both minima are
$`\equiv\lvert V_0\rvert\pmod 2`$, so their sum is even. The cell value
is
``` math
m(\text{cell})=\min_{(V_0,\gamma)}\bigl(\min_L(V_0,\gamma)+\min_R(V_0,\gamma)\bigr).
```

<div id="lem:achiever" class="lemma">

**Lemma 28** (achiever structure). *Suppose $`m(\text{cell})\ge 10`$ for
every cell of the orbit. Then a weight-$`10`$ coset element must sit at
some cell, in a configuration of cost exactly $`10`$ with every slot at
its minimum-cost value, with both free sides in the corresponding
per-slot argmin sets, and with both $`\rho`$-links satisfied. The set of
such cost-$`10`$ configurations is exactly
``` math
\bigcup_{\substack{(V_0,\gamma)\\ \min_L+\min_R=10}}
    \operatorname{Argmin}_L(V_0,\gamma)\times\operatorname{Argmin}_R(V_0,\gamma).
```*

</div>

<div class="proof">

*Proof.* The total weight of a coset element is the sum of its layer
weights, which equals its total block cost; since each slot cost is at
least its minimum-cost value, weight $`10`$ together with cost
$`\ge 10`$ forces every layer to be a minimum-weight layer for its slot
datum (*slot-exactness*: cost $`=`$ weight means each layer attains its
per-slot minimum). For the chosen cell, a cost-$`10`$ pair
$`(\mathrm{cost}_L,\mathrm{cost}_R)`$ with $`\mathrm{cost}_i\ge\min_i`$
and $`\min_L+\min_R\ge 10`$ (by hypothesis) forces
$`\mathrm{cost}_i=\min_i`$ and $`\min_L+\min_R=10`$. Hence the
configuration realizes a $`(V_0,\gamma)`$ with $`\min_L+\min_R=10`$,
with each block in its argmin set, which is the displayed union. ◻

</div>

<div class="remark">

*Remark 5*. The achiever-structure lemma reduces the weight-$`10`$ kill
to two finite sub-problems per cell: first, the *cost-$`8`$ kill*
$`\min_L+\min_R\ge 10`$ for all $`(V_0,\gamma)`$ — by the slot parity
remark and the floors $`\min\ge 3`$, the splits that could violate it
are $`(3,3)`$, $`(4,4)`$, $`(3,5)`$ and $`(5,3)`$ — and second, the
explicit *loci* $`\{(V_0,\gamma):\min_L+\min_R=10\}`$ together with
their argmin sets, the *achiever lists*. Each achiever is then killed
against the $`\rho`$-links.

</div>

# The weight-$`24`$ orbits: the standard-form walk

We now discharge the six weight-$`24`$ Smith classes of the dangerous
sector. Recall the slot frame: the four slots are the elements of
$`Z_2^2=\{e,x,y,xy\}`$, component data are functions
slots $`\to\mathbb{F}_{4}`$, and the bijection
$`m=\kappa(\hat{B})=(\omega^2,\omega,1,0)`$ together with
$`\theta=(1,0,1,0)`$ generate every line that occurs below. Each
weight-$`24`$ block contributes a configuration value $`v_2`$ on the
*configuration line* (the conf line $`\langle m\rangle`$), together with
two constrained component values $`v_3,v_4`$, and the linked cost of the
block is the sum over slots of the per-slot cost from the slot-cost rule
(Lemma <a href="#lem:slotcost" data-reference-type="ref"
data-reference="lem:slotcost">20</a>). The standard form of
Lemma <a href="#lem:stdform" data-reference-type="ref"
data-reference="lem:stdform">27</a> reduces all four weight-$`24`$ block
tables to a single two-parameter problem.

Recall (standard-form Definition, with $`m=\ell`$) that $`S(a,b)`$ is
the *$`v_0`$-free* value of the standard-form block problem with conf
line $`\langle m\rangle`$, comp-$`3`$ value $`v_3=am+c_3`$, and
comp-$`4`$ value $`v_4=bm+\omega\theta+c_4`$, minimized over the
configuration scale $`p`$, the constants $`c_3,c_4\in\mathbb{F}_{4}`$,
and the per-slot free unit-side components. Explicitly, the per-slot
cost is the $`v_0`$-free cost
``` math
\bigl(0,\ 3,\ 2,\ \text{$1$ if cheap else $3$}\bigr)
```
indexed by the number of *alive* (nonzero) values among the three
constrained components $`(v_2,v_3,v_4)`$ at that slot, “cheap” meaning
$`T:=v_2^2(v_3v_4)^{-1}=1`$ there.

<div id="prop:wt24" class="proposition">

**Proposition 29**. *$`S(a,b)\ge 6`$ for all
$`(a,b)\in\mathbb{F}_{4}^2`$. Consequently every weight-$`24`$ block
table is $`\ge 6`$ everywhere, and since the $`v_0`$-free cost
lower-bounds every cost with $`V_0`$ fixed, every weight-$`24`$ spine
cell has linked value $`\ge 6+6=12`$. Thus the homological floor (M-im)
holds on the six weight-$`24`$ Smith classes.*

</div>

This is the weight-$`24`$ part of
Proposition <a href="#prop:ctablefloor" data-reference-type="ref"
data-reference="prop:ctablefloor">30</a>.

<div class="proof">

*Proof.* By Lemma <a href="#lem:stdform" data-reference-type="ref"
data-reference="lem:stdform">27</a> the four weight-$`24`$ block tables
are obtained from $`S`$ by cost-preserving relabelings:
``` math
L(24a)\ \text{at}\ (a_3,a_4)=S(a_3,a_4),\quad
  L(24b)=S(a_4,a_3),\quad
  R(24a)\cong S(a_3,a_4^2),\quad
  R(24b)\cong S(a_4^2,a_3),
```
so it suffices to prove $`S(a,b)\ge 6`$ for all $`16`$ pairs $`(a,b)`$.
We organize the survey by the support type of the configuration value
$`v_2`$ and of $`v_3`$.

*Support trichotomy.* Write the configuration value along its line as
$`v_2=pm+c_2`$ with scale $`p\in\mathbb{F}_{4}`$ and constant
$`c_2\in\mathbb{F}_{4}`$. There are three support types:

- *dead*: $`p=c_2=0`$, so $`v_2\equiv 0`$;

- *full constant*: $`p=0\ne c_2`$, so $`v_2`$ is a nonzero constant
  (alive on all four slots);

- *co-point at $`z_2`$*: $`p\ne 0`$, so $`v_2=p\,(m+m(z_2))`$ vanishes
  at the unique slot $`z_2`$ with $`m(z_2)=-c_2/p`$ and is alive on the
  other three.

The comp-$`3`$ value $`v_3=am+c_3`$ is dead ($`a=0=c_3`$), full
($`a=0\ne c_3`$), or a co-point at the unique slot $`z_3`$ ($`a\ne 0`$).
The comp-$`4`$ value $`v_4=bm+\omega\theta+c_4`$ is governed by the
pencil trichotomy of
Lemma <a href="#lem:pencil" data-reference-type="ref"
data-reference="lem:pencil">21</a>: for $`b\in\{0,\omega,\omega^2\}`$
the direction $`bm+\omega\theta`$ is *double-paired*, so $`v_4`$ has an
alive set $`S_4`$ of size $`|S_4|\in\{2,4\}`$ ($`v_4`$ is constant on
$`S_4`$ when $`|S_4|=2`$, and two-valued – constant on each fibre pair –
when $`|S_4|=4`$); for $`b=1`$ the direction is a bijection, so
$`|S_4|=3`$ with $`v_4`$ injective on $`S_4`$ and the dead slot $`z_4`$
free.

Throughout, a slot with $`k`$ alive components among $`(v_2,v_3,v_4)`$
costs $`0,3,2,1/3`$ for $`k=0,1,2,3`$ respectively, the last being $`1`$
exactly when $`T=v_2^2(v_3v_4)^{-1}=1`$ at that slot and $`3`$ otherwise
(Lemma <a href="#lem:slotcost" data-reference-type="ref"
data-reference="lem:slotcost">20</a>). We split into $`a=0`$ (buckets
A1–A6) and $`a\ne 0`$ (buckets B1–B4), and in each bucket exhibit the
minimizing configuration explicitly.

**Case $`a=0`$ (comp $`3`$ dead or full).**

*A1 (comp $`3`$ dead, conf dead).* Here $`v_2\equiv 0`$ and
$`v_3\equiv 0`$, so every alive slot has only $`v_4`$ alive and costs
$`3`$; the $`4-|S_4|`$ dead slots cost $`0`$. The cost is
$`3|S_4|\ge 6`$. The minima at $`|S_4|=2,3,4`$ are $`6,9,12`$.

*A2 (comp $`3`$ dead, conf co-point at $`z_2`$).* Now $`v_2`$ is alive
off $`z_2`$ and $`v_3\equiv 0`$. With $`|S_4|=2`$: if $`z_2\notin S_4`$
the two slots of $`S_4`$ each have $`v_2,v_4`$ alive (cost $`2`$) and
the third $`v_2`$-alive slot has only $`v_2`$ alive (cost $`3`$), giving
$`0+2+2+3=7`$; if $`z_2\in S_4`$ then $`z_2`$ contributes only $`v_4`$
(cost $`3`$) and the remaining two $`v_2`$-alive slots cost $`3`$ each,
giving $`3+2+3+3=11`$. With $`|S_4|=3`$: if $`z_4=z_2`$ the three slots
$`\ne z_2`$ have $`v_2,v_4`$ alive (cost $`2`$ each) and $`z_2`$ is
dead, giving $`6`$; if $`z_4\ne z_2`$ then $`z_4`$ has only $`v_4`$
alive (cost $`3`$), $`z_2`$ has only $`v_4`$ alive (cost $`3`$), and the
two remaining slots have $`v_2,v_4`$ (cost $`2`$ each), giving
$`3+3+2+2=10`$. With $`|S_4|=4`$: $`z_2`$ has only $`v_4`$ (cost $`3`$)
and the three others have $`v_2,v_4`$ (cost $`2`$), giving
$`3+2+2+2=9`$. The minimum is $`6`$, attained at $`|S_4|=3`$,
$`z_4=z_2`$.

*A3 (comp $`3`$ dead, conf full) and A4 (comp $`3`$ full, conf dead).*
In each case exactly two of the three components are nonzero constants,
one of which is alive on *all four* slots. The slots in $`S_4`$ have two
alive components (cost $`2`$) and those outside $`S_4`$ have one alive
component (cost $`3`$):
``` math
\text{cost}=2|S_4|+3(4-|S_4|)=12-|S_4|\ge 8 .
```
The minima at $`|S_4|=2,3,4`$ are $`10,9,8`$ in each bucket.

*A5 (comp $`3`$ full, conf co-point at $`z_2`$).* Here
$`v_2=p(m+m(z_2))`$ with $`p\ne 0`$, $`v_3=c_3\ne 0`$ constant, and
$`v_4`$ as above. With $`|S_4|=2`$: if $`z_2\in S_4`$ then $`z_2`$ has
$`v_3,v_4`$ alive (cost $`2`$), the other slot of $`S_4`$ has all three
alive (cost $`\ge 1`$), and the two slots outside $`S_4`$ have
$`v_2,v_3`$ alive (cost $`2`$ each), giving $`\ge 2+1+2+2=7`$; if
$`z_2\notin S_4`$ then $`T=p^2(m+m(z_2))^2(c_3v_4)^{-1}`$ has an
injective numerator and a constant denominator on $`S_4`$, so $`T=1`$ at
most once, giving at most one cheap slot among the two three-alive slots
of $`S_4`$, hence $`3+1+3+2=9`$ (here $`z_2`$ is dead in $`v_4`$,
contributing only $`v_3`$ at cost $`3`$). With $`|S_4|=3`$: if
$`z_4=z_2`$ the three slots $`\ne z_2`$ have all three alive (cost
$`\ge 1`$) and $`z_2`$ has only $`v_3`$ (cost $`3`$), giving
$`\ge 3+1+1+1=6`$; if $`z_4\ne z_2`$ then $`z_2`$ has $`v_3,v_4`$ alive
(cost $`2`$), $`z_4`$ has $`v_2,v_3`$ alive (cost $`2`$), and the two
remaining slots have all three alive (cost $`\ge 1`$ each), giving
$`\ge 2+2+1+1=6`$. With $`|S_4|=4`$: $`v_4`$ is two-valued and
$`(m+m(z_2))^2`$ is injective, so $`T=1`$ at most once per $`v_4`$-fibre
pair, i.e. at most $`2`$ cheap slots total, giving $`2+1+1+3=7`$ (the
dead-in-$`v_4`$ slot $`z_2`$ never occurs here since $`|S_4|=4`$; the
bound is attained with one cheap slot per pair and one three-alive slot
at cost $`3`$). The minimum is $`6`$, attained at $`|S_4|=3`$.

*A6 (comp $`3`$ full, conf full).* Here $`v_2,v_3`$ are nonzero
constants. With $`|S_4|=2`$: $`v_4`$ is constant on $`S_4`$, so the
cheapness equation $`c_2^2=c_3v_4`$ holds simultaneously on both slots
of $`S_4`$ (all three alive, cost $`1`$ each), while the two slots
outside $`S_4`$ have $`v_2,v_3`$ alive (cost $`2`$), giving
$`1+1+2+2=6`$, which is tight. With $`|S_4|=3`$: $`v_4`$ is injective on
$`S_4`$, so the cheapness equation holds at most once, giving $`\le 1`$
cheap slot: $`1+3+3+2=9`$. With $`|S_4|=4`$: $`v_4`$ is two-valued, so
$`\le 2`$ cheap slots, giving $`1+1+3+3=8`$. The minimum is $`6`$,
attained at $`|S_4|=2`$.

**Case $`a\ne 0`$ (comp $`3`$ a co-point at $`z_3`$,
$`v_3=a(m+m(z_3))`$).**

*B1 (conf dead).* Here $`v_2\equiv 0`$ and $`v_3`$ is alive off $`z_3`$.
If $`b=1`$ (so $`|S_4|=3`$): when $`z_4=z_3`$ the three slots
$`\ne z_3`$ have $`v_3,v_4`$ alive (cost $`2`$) and $`z_3`$ is dead,
giving $`6`$; otherwise the cost is $`3+3+2+2=10`$. If $`b\ne 1`$
(double-paired): with $`|S_4|=2`$ and $`z_3\notin S_4`$ the two
$`S_4`$-slots have $`v_3,v_4`$ alive (cost $`2`$) and the third
$`v_3`$-alive slot has only $`v_3`$ (cost $`3`$), giving $`0+2+2+3=7`$
($`z_3\in S_4`$ gives $`11`$ as in A2); with $`|S_4|=4`$ the slot
$`z_3`$ has only $`v_4`$ (cost $`3`$) and the three others have
$`v_3,v_4`$ (cost $`2`$), giving $`3+2+2+2=9`$. The minimum is $`6`$ (at
$`b=1`$, $`z_4=z_3`$).

*B2 (conf full).* Here $`v_2=c_2\ne 0`$ constant and $`v_3`$ a co-point.
If $`b=1`$: when $`z_4=z_3`$ the slot $`z_3`$ has only $`v_2`$ alive
(cost $`3`$) and the three slots $`\ne z_3`$ have all three alive (cost
$`\ge 1`$), giving $`\ge 3+1+1+1=6`$; when $`z_4\ne z_3`$ the count is
two slots with $`v_2,v_3`$ or $`v_2,v_4`$ alive (cost $`2`$) and two
all-three-alive slots (cost $`\ge 1`$), giving $`\ge 2+2+1+1=6`$. If
$`b\ne 1`$: with $`|S_4|=2`$ and $`z_3\in S_4`$, $`z_3`$ has $`v_2,v_4`$
alive (cost $`2`$), one all-alive slot (cost $`\ge1`$) and two
$`v_2,v_3`$-alive slots (cost $`2`$), giving $`\ge 2+1+2+2=7`$; with
$`z_3\notin S_4`$, $`T=c_2^2(v_3v_4)^{-1}`$ has injective $`v_3`$ and
constant $`v_4`$ on $`S_4`$, so $`\le 1`$ cheap, giving $`3+1+3+2=9`$.
With $`|S_4|=4`$: $`v_3v_4`$ is injective on each $`v_4`$-fibre pair, so
$`\le 2`$ cheap, giving $`2+1+1+3=7`$. The minimum is $`6`$ (at
$`b=1`$).

*B3 (conf co-point at $`z_2`$, $`b\ne 1`$).* Both $`v_2`$ and $`v_3`$
are co-points. If $`z_2=z_3=:z`$, the configuration and comp-$`3`$
values are *proportional* (both co-points of the line
$`\langle m\rangle`$ at $`z`$), so $`T=(p^2/a)(m+m(z))\,v_4^{-1}`$. With
$`|S_4|=2`$ and $`z\notin S_4`$, $`T`$ has injective numerator over a
denominator constant on $`S_4`$, so $`\le 1`$ cheap, giving
$`0+1+3+2=6`$ (tight); with $`z\in S_4`$ the slot $`z`$ has only $`v_4`$
(cost $`3`$) and the survivors push the total to $`\ge 3+1+2+2=8`$. With
$`|S_4|=4`$, $`\le 1`$ cheap per $`v_4`$-fibre pair, giving
$`3+1+1+3=8`$. If $`z_2\ne z_3`$, then with $`|S_4|=2`$ each placement
of $`S_4`$ relative to $`\{z_2,z_3\}`$ gives $`\ge 8`$ (two
$`v_2,v_3`$-alive slots at cost $`4`$ together with either two
singly-alive slots or a three-alive fibre join), and with $`|S_4|=4`$
the two slots off $`\{z_2,z_3\}`$ are alive in all three components
while $`z_2,z_3`$ each have two alive, giving $`2+2+1+1=6`$. The minimum
is $`6`$.

*B4 (conf co-point, $`b=1`$).* The deepest case. With $`b=1`$ the
comp-$`4`$ direction is a bijection with dead slot $`z_4`$. Suppose
first $`z_2=z_3=z_4=:z`$. Then every slot $`\ne z`$ is alive in all
three components, and $`z`$ is free. Cheapness at a slot $`s\ne z`$
reads
``` math
p^2\bigl(m(s)+m(z)\bigr)^2=a\bigl(m(s)+m(z)\bigr)\,v_4(s),
  \qquad\text{i.e.}\qquad
  \bigl(m(s)+m(z)\bigr)\bigl(k_4(s)+k_4(z)\bigr)^{-1}=a\,p^{-2},
```
a level condition on the chord slope of the quadruple
$`(m,k_4)=(m,\,m+\omega\theta)`$. By the chord-slope lemma
(Lemma <a href="#lem:chord" data-reference-type="ref"
data-reference="lem:chord">23</a>) the slope is constant on a triple of
slots iff the corresponding points of $`AG(2,\mathbb{F}_{4})`$ are
collinear; and by the hyperbolic-quadruple lemma
(Lemma <a href="#lem:hyperbolic" data-reference-type="ref"
data-reference="lem:hyperbolic">24</a>) the quadruple
$`\{(m(s),k_4(s))\}=H_{\omega^2}`$ has no three of its four points
collinear. Hence the level condition is met on at most one slot:
$`\le 1`$ cheap, giving $`0+1+3+3=7`$. The remaining alignments of
$`\{z_2,z_3,z_4\}`$ all give $`\ge 7`$:

- exactly two of $`z_2,z_3,z_4`$ coincide: the doubled slot is at most
  singly alive (cost $`\ge 3`$ if its $`v_0`$-free cost is $`3`$ –
  e.g. $`z_2=z_3\ne z_4`$ leaves the shared slot with only $`v_4`$ at
  cost $`3`$ – otherwise the third, dead slot costs $`2`$), and at most
  two three-alive slots remain, forcing $`\ge 7`$ in each of the three
  patterns;

- all of $`z_2,z_3,z_4`$ distinct: three slots carry two alive
  components (cost $`2`$ each) and one slot is three-alive (cost
  $`\ge 1`$), giving $`2+2+2+1=7`$.

The minimum is $`7`$ across this bucket.

Every bucket has minimum $`\ge 6`$, so $`S(a,b)\ge 6`$ for all $`16`$
pairs $`(a,b)`$, and in fact $`S(a,b)=6`$ for every $`(a,b)`$ since each
row above attains a configuration of cost $`6`$ for the relevant
parameters. By Lemma <a href="#lem:stdform" data-reference-type="ref"
data-reference="lem:stdform">27</a> the four weight-$`24`$ block tables
inherit the value $`6`$ everywhere. Since the per-block linked minimum
at a spine cell is the sum of the two block costs and the $`v_0`$-free
cost lower-bounds each, every weight-$`24`$ spine cell has linked value
$`\ge 6+6=12`$, which is the assertion (M-im) on the six weight-$`24`$
Smith classes. ◻

</div>

The bucket walk is summarized in
Table <a href="#tab:wt24buckets" data-reference-type="ref"
data-reference="tab:wt24buckets">1</a>; each entry is the minimum of the
displayed slot-cost computation over the indicated fibre type, and the
reader may re-derive any single entry directly from the slot-cost rule.

<div id="tab:wt24buckets">

| bucket | min | bucket | min |
|:---|:--:|:---|:--:|
| A1  $`|S_4|=2/3/4`$ | $`6/9/12`$ | B1  $`b=1`$ | $`6`$ |
| A2  $`|S_4|=2/3/4`$ | $`7/6/9`$ | B1  $`b\ne1,\ |S_4|=2/4`$ | $`7/9`$ |
| A3  $`|S_4|=2/3/4`$ | $`10/9/8`$ | B2  $`b=1`$ | $`6`$ |
| A4  $`|S_4|=2/3/4`$ | $`10/9/8`$ | B2  $`b\ne1,\ |S_4|=2/4`$ | $`7/7`$ |
| A5  $`|S_4|=2/3/4`$ | $`7/6/7`$ | B3  $`z_2=z_3,\ |S_4|=2/4`$ | $`6/8`$ |
| A6  $`|S_4|=2/3/4`$ | $`6/9/8`$ | B3  $`z_2\ne z_3,\ |S_4|=2/4`$ | $`8/6`$ |
|  |  | B4  $`z_2{=}z_3{=}z_4 / z_2{=}z_3 / z_2{=}z_4 / z_3{=}z_4 / \text{distinct}`$ | $`7/7/9/9/7`$ |

Bucket minima for the standard-form problem $`S(a,b)`$ (the $`v_0`$-free
block costs). Every entry is $`\ge 6`$, and the row minimum is $`6`$ for
each $`(a,b)`$; hence $`S(a,b)=6`$ for all $`16`$ pairs.

</div>

# The weight-16 and weight-18 orbits: locus rules and the per-cell floor

On the three light orbits — which we label *wt-16*, *wt-18a*, and
*wt-18b* after the cell value of their generic spine cell — the unlinked
block floors are only $`3`$ to $`5`$. It is the linkage carried by the
shared slot data $`(V_0,\gamma)`$ that lifts the per-cell floor to
$`10`$. Working in the slot frame, we produce, per orbit and per spine
cell, enough of the function
``` math
(V_0,\gamma)\ \longmapsto\ (\min_L,\ \min_R)
```
to certify the two requirements isolated by the achiever-structure lemma
(Lemma <a href="#lem:achiever" data-reference-type="ref"
data-reference="lem:achiever">28</a>): the cost-$`8`$ kill
($`\min_L+\min_R\ge 10`$ for every $`(V_0,\gamma)`$) and the explicit
loci where $`\min_L+\min_R=10`$, together with their argmins.

Throughout, slots are the four elements of
$`\mathbb{Z}_2^2=\{e,x,y,xy\}`$; a component datum is a function from
slots to $`\mathbb{F}_{4}`$, written as a $`4`$-tuple over
$`(e,x,y,xy)`$. We carry the slot labelings $`m=(\omega^2,\omega,1,0)`$
and $`m'=(\omega^2,1,\omega,0)=m\circ(x\leftrightarrow y)`$, the
constants $`\theta=(1,0,1,0)`$ and $`\tilde\theta=(1,1,0,0)`$, the
confining line of a block, the comp-$`3`$ direction
$`k_3=\kappa_{3}+a_3 m`$ (resp. $`m'`$ on $`R`$), and the comp-$`4`$
direction with its tied constant $`d_4=\omega\gamma+e`$ (the
component-$`4`$ tie of the slot frame). The “alive” count of a slot is
the number of nonzero values among its three constrained components; the
per-slot cost rule and the slot-parity identity $`\text{cost}\equiv|V_0|
\pmod 2`$ are those of the slot-cost lemma
(Lemma <a href="#lem:slotcost" data-reference-type="ref"
data-reference="lem:slotcost">20</a>), with the cheapness test $`T=1`$,
$`T_L=v_2^2(v_3v_4)^{-1}`$ on $`L`$ and $`T_R=v_4(v_1v_3)^{-1}`$ on
$`R`$.

## The locus rules

We record five rules that turn a per-block slot-cost target into a
finite list of admissible configurations. Each is a direct consequence
of the slot-cost lemma
(Lemma <a href="#lem:slotcost" data-reference-type="ref"
data-reference="lem:slotcost">20</a>), the pair-ratio lemma for affine
pencils (Lemma <a href="#lem:pencil" data-reference-type="ref"
data-reference="lem:pencil">21</a>), and the chord-slope/hyperbolic
facts (Lemma <a href="#lem:chord" data-reference-type="ref"
data-reference="lem:chord">23</a>,
Lemma <a href="#lem:hyperbolic" data-reference-type="ref"
data-reference="lem:hyperbolic">24</a>).

(R1) Zero slot.  
A slot costs $`0`$ if and only if $`v_0=0`$ there and all three
constrained components vanish at that slot.

(R2) Dead-pair rigidity.  
If two slots $`\{s,s'\}`$ both cost $`0`$, then the confining component
is identically $`0`$ (a nonzero point of the confining line vanishes at
most at one slot), and $`\{s,s'\}`$ lies inside a single fibre of *both*
the comp-$`3`$ and the comp-$`4`$ direction. By the fibre tables of the
pair-ratio lemma (Lemma <a href="#lem:pencil" data-reference-type="ref"
data-reference="lem:pencil">21</a>), this pins the spine and the
surviving constants — hence $`\gamma`$ — up to the listed fibre choices.
Three zero slots in addition force $`v_3\equiv 0`$ on them, i.e. a fibre
of size $`\ge 3`$ in the comp-$`3`$ direction; such a fibre exists only
where comp $`3`$ is confining-parallel and the spine annihilates it (the
wt-18a row $`a_3=1`$), with a $`3{+}1`$ fibre of $`k_4`$ carrying the
remaining cost.

(R3) $`\delta`$-slot.  
A slot with $`v_0=1`$ costs $`1`$ if and only if all three components
are alive there and $`T=1`$. The confining scale $`p`$ enters $`T`$
quadratically on $`L`$ and linearly on $`R`$; matching two
$`\delta`$-slots (or one $`\delta`$-slot and one cheap three-alive slot)
against a single $`p`$ is one consistency equation in
$`\mathbb{F}_{4}`$, solved or refuted by inspection.

(R4) Cost-2 slot.  
A slot with $`v_0=0`$ costs $`2`$ if and only if exactly two components
are alive there, or all three are alive with $`T=1`$.

(R5) Shapes by parity.  
By slot parity the admissible per-block slot-cost multisets at total
cost $`3,4,5`$ are exactly:
``` math
\begin{aligned}
  \text{cost }3:\ & \{3,0,0,0\},\ \{1,2,0,0\}\ (|V_0|{=}1),\ \{1,1,1,0\}\ (|V_0|{=}3);\\
  \text{cost }4:\ & \{4,0,0,0\},\ \{2,2,0,0\}\ (|V_0|{=}0),\ \{1,1,2,0\},\ \{1,3,0,0\}\ (|V_0|{=}2),\ \{1,1,1,1\}\ (|V_0|{=}4);\\
  \text{cost }5:\ & \{1,2,2,0\},\ \{1,4,0,0\},\ \{3,2,0,0\}\ (|V_0|{=}1),\ \{1,1,3,0\},\ \{1,1,1,2\}\ (|V_0|{=}3).
  \end{aligned}
```

Each locus-table row below is obtained by the same finite procedure:
choose an admissible shape by (R5), apply (R1)–(R4) to pin the
configuration data, and test the resulting consistency equations in
$`\mathbb{F}_{4}`$. We exhibit one cell per orbit in full; the remaining
cells are settled by repeating this procedure, and the complete loci are
collected in the tables of
§<a href="#ssec:wt1618-tables" data-reference-type="ref"
data-reference="ssec:wt1618-tables">11.5</a>, where every entry is a
direct hand computation.

## The weight-16 orbit

On the $`L`$ block the confining line is $`\langle m\rangle`$, and
``` math
v_3=a_3 m+\omega\theta+c_3,\qquad v_4=a_4 m+\omega\theta+c_4,\qquad d_{4L}=\omega\gamma+\omega .
```
On the $`R`$ block, after applying Frobenius to the comp-$`4`$ values (a
cost-preserving move), the confining line is $`\langle m'\rangle`$ with
``` math
v_3=a_3 m'+\theta+c_3,\qquad \tilde v_4=a_4^2 m'+\theta+c_4 .
```
The comp-$`3`$ and comp-$`4`$ directions are double-paired for a spine
value in $`\{0,\omega,\omega^2\}`$ and bijective at $`1`$. On $`L`$ the
pairings are $`\{e,y\mid x,xy\}`$ at $`0`$, $`\{e,x\mid y,xy\}`$ at
$`\omega`$, and $`\{e,xy\mid x,y\}`$ at $`\omega^2`$; on $`R`$ (whose
offset is $`\theta`$ against $`m'`$) the pairings at $`\omega`$ and
$`\omega^2`$ are exchanged. The sixteen spine cells are indexed by
$`(a_3,a_4)\in\mathbb{F}_{4}^2`$.

#### Worked cell $`(\omega^2,\omega^2)`$, the $`(4,6)`$ locus.

Consider the cost-$`4`$ $`L`$-shapes. The shape $`\{2,2,0,0\}`$ requires
a dead pair; by (R2) the confining component is $`\equiv 0`$ and the
dead pair lies in a common fibre of $`k_3=\omega^2 m+\omega\theta`$ and
$`k_4=\omega^2 m+\omega\theta`$. These directions are equal, with
pairing $`\{e,xy\mid x,y\}`$ (pair-ratio $`\omega^2`$ at spine value
$`\omega^2`$), and both fibres are available:

- dead pair $`\{e,xy\}`$ pins $`c_3=c_4=k(e)`$ and
  $`d_{4L}=k_4(e)=\omega^2 m(e)+\omega\theta(e)
    =\omega+\omega=0`$, so $`\omega\gamma+\omega=0`$ gives $`\gamma=1`$;

- dead pair $`\{x,y\}`$ pins $`d_{4L}=k_4(x)=1`$, hence
  $`\gamma=\omega`$.

In each case the two live slots carry $`v_3=v_4=`$ the pair-gap value,
with two components alive each, contributing cost $`2+2`$ at
$`V_0=0000`$. Thus $`\min_L=4`$ at
$`(V_0,\gamma)\in\{(0000,1),(0000,\omega)\}`$, with a unique argmin. The
all-$`\delta`$ shape $`\{1,1,1,1\}`$ ($`|V_0|=4`$) also solves here:
since $`k_3=k_4`$, the $`\delta`$-condition $`T\equiv1`$ reads
$`p^2(m\text{-line})^2=v_3 v_4=v_3^2`$, one equation per slot, and these
are consistent across all four slots exactly at
$`\gamma\in\{0,\omega^2\}`$ (with $`V_0=1111`$). The $`|V_0|=2`$ shapes
and $`\{4,0,0,0\}`$ fail: with $`k_3=k_4`$ the equations of (R3) are
overdetermined. The $`R`$ block at each of these four $`(V_0,\gamma)`$
has $`\min_R=6`$. Hence this cell contributes $`(4,6)`$ achievers at the
four loci $`1111@0`$, $`0000@1`$, $`0000@\omega`$, $`1111@\omega^2`$,
each with $`|\mathrm{Argmin}_R|=2`$, matching the table.

#### Worked cell $`(\omega,1)`$, a $`(5,5)`$ locus.

Take $`V_0=\delta_{xy}`$ and $`\gamma=0`$, so $`d_{4L}=\omega`$.
Consider the shape $`\{1,2,2,0\}`$. The zero slot $`s_0`$ must satisfy
$`k_4(s_0)=d_{4L}`$; with $`k_4=m+\omega\theta=(1,\omega,\omega^2,0)`$
(bijective, $`a_4=1`$) this forces $`s_0=x`$. By (R1) the confining
component is the co-point $`p\,(m+m(x))`$. The comp-$`3`$ direction
$`k_3=\omega m+\omega\theta=(\omega^2,\omega^2,0,0)`$ is double-paired
$`\{e,x\mid y,xy\}`$, so $`v_3`$ vanishes on the whole pair $`\{e,x\}`$;
consequently slot $`e`$ has exactly the confining and the comp-$`4`$
components alive — cost $`2`$, as required. Slots $`y`$ and $`xy`$ have
all three components alive; the $`\delta`$-slot is $`xy`$ (with
$`v_0=1`$), and slot $`y`$ must satisfy $`T=1`$ by (R4). Each yields one
equation for $`p^2`$:
``` math
\text{at }xy:\quad p^2\cdot\omega^2=v_3(xy)\,v_4(xy)=\omega^2\cdot\omega,\quad\text{so }p^2=\omega;
  \qquad
  \text{at }y:\quad p^2\cdot(\omega^2)^2=\omega^2\cdot 1,\quad\text{so }p^2=\omega.
```
The two are consistent, giving $`p=\omega^2`$. The configuration exists
and is unique: a $`(5,5)`$ locus with singleton argmins. The other three
loci $`(V_0,\gamma)=(\delta_s,\cdot)`$ are its images under the slot
translations: the stabilizer of the orbit has order $`4`$ and acts by
the three nonzero slot translations, which permute the
$`\delta`$-positions and shift $`\gamma`$ accordingly.

#### The remaining cells.

Each of the remaining cells is settled by the same finite procedure; the
complete loci are collected in
Table <a href="#tab:wt16" data-reference-type="ref"
data-reference="tab:wt16">2</a>. We record the qualitative outcome that
the cost-$`8`$ kill depends on.

- *Floor-$`10`$ cells* $`(\omega,1)`$, $`(\omega,\omega^2)`$,
  $`(\omega^2,1)`$, $`(\omega^2,\omega^2)`$: each contributes four
  $`(5,5)`$ loci with singleton argmins and four $`(6,4)`$- or
  $`(4,6)`$-loci with two argmin pairs each, for $`4+8=12`$ achievers
  per cell and $`48`$ in total.

- *All other cells* realize the $`(4,4)`$ kill, i.e. the disjointness of
  the $`L4`$ and $`R4`$ loci read off
  Table <a href="#tab:wt16" data-reference-type="ref"
  data-reference="tab:wt16">2</a>: at every such cell one side is empty,
  or the $`V_0`$-sets are disjoint (e.g. at $`(\omega,1)`$,
  $`V_0(L4)\subseteq\{0011,1100\}`$ versus
  $`V_0(R4)\subseteq\{1001,0110\}`$), or the $`V_0`$’s coincide and the
  $`\gamma`$-sets are complementary (e.g. at $`(0,0)`$, $`L4`$ at
  $`(0000,\{0,1\})\cup(1111,\{\omega,\omega^2\})`$ and $`R4`$ at
  $`(1111,\{0,1\})\cup(0000,\{\omega,\omega^2\})`$).

- *$`L3=R3=\varnothing`$ at every cell*, fully derived as follows. The
  $`|V_0|=1`$ shapes $`\{1,2,0,0\}`$ and $`\{3,0,0,0\}`$ both need
  $`\ge 2`$ zero slots, killing the confining component by (R2): the
  former then has no alive confining component at its $`\delta`$-slot,
  and the latter needs $`v_3\equiv 0`$ on three slots, impossible since
  $`\kappa_{3L}=\omega\theta`$ is non-constant and $`k_3`$ has no fibre
  of size $`\ge 3`$. The $`|V_0|=3`$ shape $`\{1,1,1,0\}`$ (one zero
  slot $`s_0`$, three $`\delta`$-slots) dies in three sub-cases: at
  $`a_3\ne 1`$ the comp-$`3`$ direction is double-paired, so
  $`v_3(s_0)=0`$ kills $`v_3`$ on $`s_0`$’s partner slot, contradicting
  that slot being a $`\delta`$-slot; at $`(1,a_4)`$ with $`a_4\ne 1`$
  the same argument applies to comp $`4`$; and at $`(1,1)`$, where
  $`k_3=k_4=m+\omega\theta`$, the triple-$`\delta`$ condition says
  $`(m+m(s_0))\cdot(k_3+k_3(s_0))^{-1}`$ is constant on the three slots
  $`\ne s_0`$, i.e. three points of the hyperbolic quadruple
  $`(m,m+\omega\theta)=H_{\omega^2}`$ are collinear, contradicting
  Lemma <a href="#lem:hyperbolic" data-reference-type="ref"
  data-reference="lem:hyperbolic">24</a>.

With slot parity, every $`(V_0,\gamma)`$ satisfies
$`\min_L+\min_R\ge 10`$, so $`m(\text{cell})\ge
10`$ for all $`16`$ cells, with equality exactly at the four
floor-$`10`$ cells.

## The weight-18a orbit

On $`L`$, $`v_3=(1+a_3)m+c_3`$ — here $`\kappa_{3L}=m`$ *is* the
labeling, so comp $`3`$ is confining-parallel, dead or full at $`a_3=1`$
and a co-point otherwise — while $`v_4`$ has direction
$`k_4=(0,\omega,\omega^2,0)+a_4 m`$ with fibre types $`2{+}1{+}1`$,
$`2{+}1{+}1`$, $`3{+}1`$, $`2{+}1{+}1`$ over
$`a_4=0,1,\omega,\omega^2`$, and $`d_{4L}=\omega\gamma+\omega^2`$. On
$`R`$, $`v_3=(1+a_3)m'`$ and $`\tilde v_4`$ has direction
$`\omega(1,1,1,0)+a_4^2 m'`$ (type $`3{+}1`$ at $`a_4=0`$, else
$`2{+}1{+}1`$). The translation stabilizer of the orbit has order $`3`$
and acts on the spine by affine maps of the form
$`a_3\mapsto\omega(1+a_3)+1`$ that fix $`a_4`$: the cells $`(a_3,a_4)`$
with $`1+a_3\ne 0`$ form orbits of three within each $`a_4`$-column, and
the row $`a_3=1`$ is fixed. There are therefore six cell classes: one
rep $`(\tilde a_3\ne 0,a_4)`$ for each $`a_4\in\mathbb{F}_{4}`$,
together with $`(1,0)`$ and $`(1,\omega)`$. (The cells $`(1,1)`$ and
$`(1,\omega^2)`$ have cell value $`12`$ with empty low loci.)

#### Worked class rep $`(0,1)`$, the $`|V_0|=3`$ loci.

The shape $`\{1,1,1,2\}`$ has its (R3) $`\delta`$-equations solvable at
exactly $`(V_0,\gamma)\in\{(1011,1),(1101,\omega^2)\}`$ on the $`(5,5)`$
side, together with the $`(6,4)`$ locus $`(1100,\omega^2)`$. The class
transports to $`(\omega,1)`$ and $`(\omega^2,1)`$ verbatim, as the
stabilizer fixes $`\gamma`$ and $`a_4`$ and permutes nothing else in the
table. The isolated row $`a_3=1`$ kills comp $`3`$ entirely (dead or
full): at $`(1,0)`$ the surviving loci are $`(6,4)`$ at $`(0000,0)`$ and
$`(7,3)`$ at $`(0001,0)`$; at $`(1,\omega)`$ one finds the mirror
$`(3,7)/(4,6)`$. The complete count over the fourteen floor-$`10`$ cells
is $`48`$ achievers: $`12`$ per $`a_4\in
\{1,\omega^2\}`$ column-orbit, $`6`$ per $`a_4\in\{0,\omega\}`$
column-orbit, and $`6+6`$ at the two fixed cells.

#### The cost-8 kill.

All $`L4`$, $`R4`$, $`L3`$, $`R3`$ loci are singletons
(Table <a href="#tab:wt18a" data-reference-type="ref"
data-reference="tab:wt18a">3</a>) and pairwise disjoint in
$`(V_0,\gamma)`$ at every cell. The only $`L3/R3`$ sites occur at
$`(1,\omega)`$ and $`(1,0)`$, where the partner block’s minimum at that
$`(V_0,\gamma)`$ is $`7`$.

## The weight-18b orbit

On $`L`$, $`\kappa_{3L}=(1,\omega,\omega^2,0)`$ is a bijective offset,
so $`k_3=\kappa_{3L}+a_3 m`$ has fibre types $`1{+}1{+}1{+}1`$,
$`2{+}2`$, $`2{+}2`$, $`2{+}2`$ over $`a_3=0,1,\omega,\omega^2`$;
$`\kappa_{4L}=(\omega,\omega,1,0)`$ gives $`k_4`$ fibre types
$`2{+}1{+}1`$, $`3{+}1`$, $`2{+}1{+}1`$, $`2{+}1{+}1`$; and
$`d_{4L}=\omega\gamma+1`$. On $`R`$, $`\kappa_{3R}=\omega^2 m`$ (a fixed
non-affine offset in the $`m'`$-frame) and
$`\tilde\kappa_{4R}=(\omega^2,\omega,\omega^2,0)`$. The translation
stabilizer is trivial, but the orbit carries a swap-type symmetry:
composing translation with the block swap fixes the orbit, exchanges the
two blocks, and pairs the cells. Each locus table at $`(a_3,a_4)`$ thus
mirrors a partner cell’s with $`L`$ and $`R`$ exchanged — visible in
Table <a href="#tab:wt18b" data-reference-type="ref"
data-reference="tab:wt18b">4</a>, e.g. $`(0,1)`$ carries $`(3,7)+(4,6)`$
while $`(0,\omega^2)`$ carries $`(7,3)+(6,4)`$ with the same $`V_0`$’s.
There are $`12`$ floor-$`10`$ cells and $`22`$ achievers; the two
$`L3/R3`$ sites ($`(0,1)`$ and $`(0,\omega^2)`$, both at $`V_0=0111`$,
the unique $`|V_0|=3`$ cost-$`3`$ shape $`\{1,1,1,0\}`$ the frame
admits) have partner minima $`7`$.

## The locus tables and the C-table floor

In the tables below $`V_0`$ is written as a bit-string over the slots
$`(e,x,y,xy)`$ and $`\gamma\in\mathbb{F}_{4}`$; a locus is recorded as
$`V_0@\gamma`$. Each row is the outcome of the finite procedure of
§<a href="#ssec:locus-rules" data-reference-type="ref"
data-reference="ssec:locus-rules">11.1</a>, and is small enough to be
checked by hand.

<div id="tab:wt16">

| cell | $`(5,5)`$ loci (argmins $`1\times1`$) | $`(4,6)/(6,4)`$ loci (argmins $`1\times2`$ / $`2\times1`$) |
|:---|:---|:---|
| $`(\omega,1)`$ | $`0001@0,\ 0100@1,\ 0010@\omega,\ 1000@\omega^2`$ | $`(6,4)`$: $`1001@0,\ 0110@1,\ 0110@\omega,\ 1001@\omega^2`$ |
| $`(\omega,\omega^2)`$ | $`0111@0,\ 1110@0,\ 1011@\omega^2,\ 1101@\omega^2`$ | $`(6,4)`$: $`1111@0,\ 0000@1,\ 0000@\omega,\ 1111@\omega^2`$ |
| $`(\omega^2,1)`$ | $`1000@0,\ 0010@1,\ 0100@\omega,\ 0001@\omega^2`$ | $`(4,6)`$: $`1001@0,\ 0110@1,\ 0110@\omega,\ 1001@\omega^2`$ |
| $`(\omega^2,\omega^2)`$ | $`1011@0,\ 1101@0,\ 0111@\omega^2,\ 1110@\omega^2`$ | $`(4,6)`$: $`1111@0,\ 0000@1,\ 0000@\omega,\ 1111@\omega^2`$ |

Weight-16 floor-$`10`$ cells and their achiever loci.

</div>

$`12`$ achievers per cell, $`48`$ in total. At every other cell
$`L4\cap R4=\varnothing`$ and $`L3=R3=\varnothing`$, so those cells have
value $`\ge 12`$.

<div id="tab:wt18a">

| class | loci |
|:---|:---|
| $`(\tilde a_3\ne 0,\,0)`$ | $`(4,6)`$: $`0110@\omega`$ |
| $`(\tilde a_3\ne 0,\,1)`$ | $`(5,5)`$: $`1011@1,\ 1101@\omega^2`$;$`(6,4)`$: $`1100@\omega^2`$ |
| $`(\tilde a_3\ne 0,\,\omega)`$ | $`(6,4)`$: $`0110@\omega^2`$ |
| $`(\tilde a_3\ne 0,\,\omega^2)`$ | $`(4,6)`$: $`1100@\omega`$;$`(5,5)`$: $`1011@0,\ 1101@\omega`$ |
| $`(1,\,0)`$ | $`(6,4)`$: $`0000@0`$;$`(7,3)`$: $`0001@0`$ |
| $`(1,\,\omega)`$ | $`(3,7)`$: $`0001@1`$;$`(4,6)`$: $`0000@1`$ |

Weight-18a cell classes (under the order-$`3`$ stabilizer; rows
$`\tilde a_3=1+a_3\ne0`$ transport, the row $`a_3=1`$ is fixed) and
their loci.

</div>

Achiever counts: $`2`$ per $`(\tilde a_3\ne 0,0)`$- and
$`(\tilde a_3\ne 0,\omega)`$-cell, $`4`$ per $`(\tilde a_3\ne 0,1)`$-
and $`(\tilde a_3\ne 0,\omega^2)`$-cell, and $`6`$ at each fixed cell,
giving $`3\cdot(2+4+2+4)+6+6=48`$. The cells $`(1,1)`$ and
$`(1,\omega^2)`$ have value $`12`$ with empty loci.

<div id="tab:wt18b">

| cell | loci |  | swap-partner | loci |
|:---|:---|:--:|:---|:---|
| $`(0,1)`$ | $`(3,7)`$: $`0111@0`$; $`(4,6)`$: $`0101@0`$ |  | $`(0,\omega^2)`$ | $`(6,4)`$: $`0101@\omega`$; $`(7,3)`$: $`0111@\omega`$ |
| $`(1,\omega)`$ | $`(4,6)`$: $`0000@1`$ |  | $`(1,0)`$ | $`(6,4)`$: $`0000@\omega^2`$ |
| $`(1,\omega^2)`$ | $`(4,6)`$: $`1010@1`$; $`(5,5)`$: $`0010@1`$ |  | $`(1,1)`$ | $`(5,5)`$: $`0010@\omega^2`$; $`(6,4)`$: $`1010@\omega^2`$ |
| $`(\omega,0)`$ | $`(4,6)`$: $`1001@0`$; $`(5,5)`$: $`1110@1`$; $`(6,4)`$: $`1100@1`$ |  | $`(\omega^2,\omega)`$ | $`(4,6)`$: $`1100@\omega^2`$; $`(5,5)`$: $`1110@\omega^2`$; $`(6,4)`$: $`1001@\omega`$ |
| $`(\omega,1)`$ | $`(5,5)`$: $`1011@\omega`$ |  | $`(\omega^2,\omega^2)`$ | $`(5,5)`$: $`1011@0`$ |
| $`(\omega^2,0)`$ | $`(4,6)`$: $`0000@\omega`$; $`(5,5)`$: $`0001@\omega`$ |  | $`(\omega,\omega)`$ | $`(5,5)`$: $`0001@0`$; $`(6,4)`$: $`0000@0`$ |

Weight-18b loci, paired by the swap symmetry (each left row mirrors its
right partner with the $`(c_L,c_R)`$ split exchanged).

</div>

Achiever count $`2+2+1+1+2+2+3+3+1+1+2+2=22`$.

<div id="prop:ctablefloor" class="proposition">

**Proposition 30** (C-table floor). *Every Smith-coset element has
weight $`\ge 12`$ on the wt-24 orbits and $`\ge 10`$ on the wt-16,
wt-18a, and wt-18b orbits. On each of the latter, for every
$`(V_0,\gamma)`$ the per-block minima satisfy $`\min_L+\min_R\ge 10`$,
with equality exactly on the loci listed in
Tables <a href="#tab:wt16" data-reference-type="ref"
data-reference="tab:wt16">2</a>–<a href="#tab:wt18b" data-reference-type="ref"
data-reference="tab:wt18b">4</a>. The cost-$`10`$ configurations are
therefore exactly the $`48+48+22=118`$ achievers obtained from those
loci.*

</div>

<div class="proof">

*Proof.* On the wt-24 orbits the bound is $`S(a,b)\ge 6`$ for every
block at every cell
(Proposition <a href="#prop:wt24" data-reference-type="ref"
data-reference="prop:wt24">29</a>); since the confining-free cost
lower-bounds every fixed-$`V_0`$ cost, each wt-24 spine cell has linked
value $`\ge 6+6=12`$.

For each light orbit the work above produces, cell by cell, the two
facts the achiever-structure lemma
(Lemma <a href="#lem:achiever" data-reference-type="ref"
data-reference="lem:achiever">28</a>) requires. First,
$`\min_L+\min_R\ge 10`$ for every $`(V_0,\gamma)`$: by slot parity
(Lemma <a href="#lem:slotcost" data-reference-type="ref"
data-reference="lem:slotcost">20</a>) only the splits $`(3,3)`$,
$`(4,4)`$, $`(3,5)`$ and $`(5,3)`$ can violate this, and these are
excluded cell by cell — the $`(4,4)`$ kill by the disjointness of the
$`L4`$ and $`R4`$ loci, and the $`(3,3)/(3,5)/(5,3)`$ kills because
every cost-$`3`$ locus (an $`L3`$ or $`R3`$ site) pairs with a
partner-block minimum $`\ge 7`$ at the same $`(V_0,\gamma)`$
(§<a href="#ssec:wt16" data-reference-type="ref"
data-reference="ssec:wt16">11.2</a>–<a href="#ssec:wt18b" data-reference-type="ref"
data-reference="ssec:wt18b">11.4</a>). Second, the loci where
$`\min_L+\min_R=10`$ are exactly those tabulated, with the stated argmin
multiplicities. By
Lemma <a href="#lem:achiever" data-reference-type="ref"
data-reference="lem:achiever">28</a> the cost-$`10`$ configurations are
precisely
``` math
\bigcup_{(V_0,\gamma):\,\min_L+\min_R=10}\ \mathrm{Argmin}_L(V_0,\gamma)\times\mathrm{Argmin}_R(V_0,\gamma),
```
which the tables enumerate as $`48`$ (wt-16) $`+48`$ (wt-18a) $`+22`$
(wt-18b) $`=118`$ achievers. ◻

</div>

# The $`\rho`$-link kills: no weight-$`10`$ element

By the achiever-structure lemma
(Lemma <a href="#lem:achiever" data-reference-type="ref"
data-reference="lem:achiever">28</a>), a weight-$`10`$ Smith-coset
element must realize one of the $`118`$ achievers of
Proposition <a href="#prop:ctablefloor" data-reference-type="ref"
data-reference="prop:ctablefloor">30</a>, with its free sides in the
per-slot argmin sets and *both* $`\rho`$-links satisfied:
``` math
V_{1R}=\rho_1\cdot V_{1L},\qquad V_{2L}=\rho_2\cdot V_{2R}
```
(Lemma <a href="#lem:offvanish-statement" data-reference-type="ref"
data-reference="lem:offvanish-statement">17</a>). For an achiever the
values $`V_{1R}`$ and $`V_{2L}`$ are already part of the configuration;
the links then demand $`V_{1L}\in\rho_1^{-1}(V_{1R})`$, a coset of
$`\ker\rho_1=\mathbb{F}_{4}\hat{A}_1\oplus\mathbb{F}_{4}\,XY`$ (sixteen
elements, nonempty since $`V_{1R}\in\mathop{\mathrm{im}}\rho_1`$),
meeting the product
$`\prod_s\mathrm{Argmin}_1(s)\subseteq\mathbb{F}_{4}`$ of the four
per-slot comp-$`1`$ argmin sets, and the mirror statement for
$`V_{2R}`$. The per-slot argmin sets are read off the value table: at a
slot of cost $`c`$,
$`\mathrm{Argmin}_1(s)=\{v_1: \text{the layer with values }
(v_0;v_1,v_2,v_3,v_4)\text{ has weight }c\}`$ — almost always a
singleton, since a $`\delta`$-point pins all five values and a
weight-$`2`$ slot pins them up to its single dead component.

<div id="prop:kill" class="proposition">

**Proposition 31** (the $`\rho`$-link kill). *Each of the $`118`$
weight-$`10`$ achievers of
Proposition <a href="#prop:ctablefloor" data-reference-type="ref"
data-reference="prop:ctablefloor">30</a> violates at least one
$`\rho`$-link. Precisely, $`116`$ achievers violate both links and the
remaining $`2`$ (the wt-18b $`(5,5)`$ achievers at cells
$`(\omega,\omega)`$ and $`(\omega^2,0)`$) violate exactly one.
Consequently no Smith-coset element has weight $`10`$.*

</div>

<div class="proof">

*Proof.* The check is, per achiever, a single convolution in
$`\mathbb{F}_{4}[\mathbb{Z}_2^2]`$ followed by a slot-by-slot
comparison. We carry out the worked head of the wt-16 $`(5,5)`$ family
in full and then describe the family table; each remaining check is one
such evaluation.

#### Worked kill: the wt-16 $`(5,5)`$ head.

At the cell $`(\omega,1)`$, with $`V_0=\delta_{xy}=0001`$ and
$`\gamma=0`$ (the cell of the worked $`(5,5)`$ locus of
§<a href="#ssec:wt16" data-reference-type="ref"
data-reference="ssec:wt16">11.2</a>), the achiever’s $`L`$ data is
``` math
V_{2L}=(\omega^2,0,\omega,1),\quad V_{3L}=(0,0,\omega^2,\omega^2),\quad V_{4L}=(\omega^2,0,1,\omega),
```
with slot costs $`[2,0,2,1]`$. The per-slot comp-$`1`$ argmin sets are
the singletons $`(\{1\},\{0\},\{0\},\{\omega^2\})`$: at the zero slot
the empty layer forces $`v_1=0`$; at the $`\delta`$-slot the
$`\delta`$-point pins $`v_1`$; and at the two weight-$`2`$ slots the one
dead component of the pair is not comp $`1`$. Hence link $`1`$ holds if
and only if the single convolution $`\rho_1\cdot(1,0,0,\omega^2)`$
equals $`V_{1R}=(\omega^2,\omega,0,1)`$. Computing in the $`X,Y`$ basis,
$`(1,0,0,\omega^2)=\omega\cdot 1+\omega^2 X+\omega^2 Y+\omega^2 XY`$,
and
``` math
(X+\omega Y+\omega^2 XY)\cdot(\omega+\omega^2 X+\omega^2 Y+\omega^2 XY)=\omega X+\omega^2 Y+\omega^2 XY,
```
whose slot values are
$`(\omega,1,0,\omega^2)\ne(\omega^2,\omega,0,1)=V_{1R}`$: link $`1`$
fails. The mirror computation against $`\rho_2`$ kills link $`2`$ as
well, so this achiever violates both links.

#### The remaining achievers.

The same one-convolution check settles every achiever: for each, one
forms $`\rho_i`$ times the unique product of the comp-$`i`$ argmin
singletons and compares the four slot values against the configuration’s
$`V_{iR}`$ (resp. $`V_{iL}`$). Equivalently, the product of the four
argmin sets and the sixteen-element link coset are disjoint, which is a
single $`\mathbb{F}_{4}`$ evaluation per slot. Transporting the worked
head by the orbit symmetries of
§<a href="#sec:wt1618" data-reference-type="ref"
data-reference="sec:wt1618">11</a> sweeps each family. The outcome is
recorded in Table <a href="#tab:kills" data-reference-type="ref"
data-reference="tab:kills">5</a>: $`116`$ achievers fail both links, and
the two exceptions noted in the statement fail exactly one. In every
case at least one link fails, so none of the $`118`$ achievers is
link-compatible. ◻

</div>

<div id="tab:kills">

| family | achievers | links failed |
|:---|:---|:---|
| wt-16 | $`48`$ | both |
| wt-18a | $`48`$ | both |
| wt-18b (non-exceptional) | $`20`$ | both |
| wt-18b $`(5,5)`$ at $`(\omega,\omega),\,(\omega^2,0)`$ | $`2`$ | exactly one |
| total | $`118`$ | all fail $`\ge 1`$ |

The $`118`$ weight-$`10`$ achievers and their $`\rho`$-link kills.

</div>

<div id="thm:Mim" class="proposition">

**Proposition 32**. *Every base $`1`$-cycle lying in a nonzero Smith
class $`\mathop{\mathrm{im}}\Delta`$ has weight $`\ge 12`$.*

</div>

<div class="proof">

*Proof.* By the standard-form walk
(Proposition <a href="#prop:wt24" data-reference-type="ref"
data-reference="prop:wt24">29</a>) no Smith-coset element has cost
$`\le 9`$, the wt-24 orbits being floored at $`12`$ and the wt-16/18
orbits at $`10`$
(Proposition <a href="#prop:ctablefloor" data-reference-type="ref"
data-reference="prop:ctablefloor">30</a>). By the $`\rho`$-link kill
(Proposition <a href="#prop:kill" data-reference-type="ref"
data-reference="prop:kill">31</a>) no link-compatible cost-$`10`$
configuration exists. Finally, every Smith-coset element has even weight
(the evenness of the slot frame). Combining: a Smith-coset element of
weight $`<12`$ would have weight $`10`$ and would realize one of the
$`118`$ achievers with both links satisfied, contradicting
Proposition <a href="#prop:kill" data-reference-type="ref"
data-reference="prop:kill">31</a>; hence every such element has weight
$`\ge 12`$.

This bounds the five orbit representatives. Transport across the Smith
classes (the slot-frame symmetry that carries one nonzero class to
another preserving weight) extends the bound from the representatives to
all $`63`$ nonzero classes of $`\mathop{\mathrm{im}}\Delta`$. Therefore
every base $`1`$-cycle in a nonzero Smith class has weight $`\ge 12`$. ◻

</div>

# Theorem D: the distance

We now assemble the pieces into the distance computation. All weights
are taken on the $`Z`$ side; the $`X`$ side is identical by the Duality
Lemma (Lemma <a href="#lem:duality" data-reference-type="ref"
data-reference="lem:duality">1</a>).

<div class="thmD">

**Theorem D**. *$`d(\mathrm{gross})=12`$.*

</div>

<div class="proof">

*Proof.* *Lower bound.* Let $`v=(v_L,v_R)`$ be a nontrivial
$`Z`$-logical of the gross code, i.e. a cover cycle whose class in
$`H_1(\mathrm{gross})`$ is nonzero. Write $`p(v)=v_0+v_1`$ for its
sheet-sum projection to the base, a chain map with
$`\lvert v\rvert\ge\lvert p(v)\rvert`$. We split on the class of
$`p(v)`$ in $`H_1(\mathrm{base})`$.

If $`[p(v)]=0`$, then $`v`$ lies in the kernel of the induced projection
$`p_\ast\colon H_1(\mathrm{gross})\to H_1(\mathrm{base})`$, so its class
belongs to the dangerous sector. Theorem C applies directly and gives
$`\lvert v\rvert\ge 12`$.

If $`[p(v)]\ne 0`$, then by the homotopy theorem (R) we have
$`[p(v)]\in\mathop{\mathrm{im}}\Delta`$; combined with $`[p(v)]\ne 0`$
this places $`[p(v)]`$ in
$`\mathop{\mathrm{im}}\Delta\smallsetminus 0`$. Thus $`p(v)`$ is a base
$`1`$-cycle in a nonzero Smith class, and
Proposition <a href="#thm:Mim" data-reference-type="ref"
data-reference="thm:Mim">32</a> gives $`\lvert p(v)\rvert\ge 12`$. Hence
$`\lvert v\rvert\ge\lvert p(v)\rvert\ge 12`$.

In either case $`\lvert v\rvert\ge 12`$, so
$`d_Z(\mathrm{gross})\ge 12`$. By the Duality Lemma
(Lemma <a href="#lem:duality" data-reference-type="ref"
data-reference="lem:duality">1</a>),
$`d_X(\mathrm{gross})=d_Z(\mathrm{gross})`$, and therefore
$`d(\mathrm{gross})\ge 12`$.

*Upper bound and tightness.* Let
$`z^\ast=1+y+y^2+y^5+x^3+x^3y^4\in\mathop{\mathrm{Ann}}(A)`$ be the
weight-$`6`$ annihilator element of Corollary A$`'`$
(<a href="#cor:Aprime" data-reference-type="ref"
data-reference="cor:Aprime">4</a>), and let $`u^\ast=(z^\ast,0)`$ be the
associated weight-$`6`$ nontrivial $`Z`$-logical of the base code. We
claim $`[u^\ast]\notin\mathop{\mathrm{im}}\Delta`$.

Indeed, $`u^\ast`$ has nonzero *seam flux*. Fix the seam $`j=0`$. For an
appropriate $`X`$-side dual cycle $`\xi\in\ker H_X^{\mathsf T}`$, the
class functional $`\ell_\xi(w)=\xi^{\mathsf T}\partial_1^{\mathrm c}w`$
of Corollary <a href="#cor:flux" data-reference-type="ref"
data-reference="cor:flux">14</a> evaluates on $`u^\ast`$ to the parity
of the seam-crossing incidences between $`\xi`$ and
$`\mathop{\mathrm{supp}}z^\ast`$ — a finite count over the six cells of
$`\mathop{\mathrm{supp}}z^\ast`$ — and this parity is odd. Since
$`\ell_\xi`$ vanishes on $`\mathop{\mathrm{im}}\Delta`$
(Corollary <a href="#cor:flux" data-reference-type="ref"
data-reference="cor:flux">14</a>, the easy inclusion
$`\mathop{\mathrm{im}}\Delta\subseteq\ker\ell_\xi`$),
$`\ell_\xi(u^\ast)\ne 0`$ forces
$`[u^\ast]\notin\mathop{\mathrm{im}}\Delta=\ker\tau_\ast`$, where
$`\tau(u)=(u,u)`$ is the transfer.

Since $`[u^\ast]\notin\ker\tau_\ast`$, the diagonal lift
$`\tau(u^\ast)=(u^\ast,u^\ast)`$ is a nonzero class in
$`H_1(\mathrm{gross})`$, i.e. a cover cycle that is not a boundary. Its
weight is $`\lvert \tau(u^\ast)\rvert=2\,\lvert u^\ast\rvert=12`$. Hence
the gross code carries a nontrivial $`Z`$-logical of weight exactly
$`12`$, so $`d(\mathrm{gross})\le 12`$.

Combining the two bounds, $`d(\mathrm{gross})=12`$. ◻

</div>

Theorem D closes the program: the base code’s distance-$`6`$ geometry
controls the gross code’s distance entirely, the dangerous sector
through the factor-two floor of Theorem C and the safe sector through
the Smith-class floor of
Proposition <a href="#thm:Mim" data-reference-type="ref"
data-reference="thm:Mim">32</a>, with the diagonal lift of a single
weight-$`6`$ base logical showing the bound $`12`$ is achieved.
