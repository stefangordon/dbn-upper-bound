# Computational estimates for the finite head and the source boxes

This appendix proves the two numerical inputs called P2 and P7 in the main
paper. The accompanying programs recompute their numerical enclosures. They
do not infer a theorem from a saved pass flag. The definitions of $H_t$, $S$
and $\Omega$ are those of the main paper. Write

$$
X=5999347341500,\quad X_e=5900000000000,\quad
N(x,t)=\left\lfloor\sqrt{x/(4\pi)+t/16}\right\rfloor.
$$

Both calculations use the repaired effective approximation H7, proved with
explicit constants in [analytic-estimates.md, Lemma A.1](analytic-estimates.md).
Its derivation includes a uniform vertical Stirling bound and the full Gaussian
and Riemann–Siegel remainders. This is the common analytic approximation input
for the finite head and the source boxes.

## 1. Normalization and finite sums

For $z=x+iY$, set

$$
w=\frac{1-iz}{2},\quad v=1-w,\qquad
\alpha(w)=\frac1{2w}+\frac1{w-1}+\frac12\Log\frac{w}{2\pi},
$$
$$
M_0(w)=\frac{w(w-1)}{16}\pi^{-w/2}\sqrt{2\pi}
 \exp\left[\left(\frac w2-\frac12\right)\Log\frac w2-\frac w2\right],
\quad M_t(w)=M_0(w)e^{t\alpha(w)^2/4}.
$$

All logarithms here have their principal branches; their arguments lie far
from zero and their cuts on every domain used below. Put

$$
\begin{aligned}
B_t(z)&=M_t(w),& \gamma&=\frac{M_t(v)}{M_t(w)},\\
s_B&=w+\frac t2\alpha(w),& s_A&=v+\frac t2\alpha(v),\\
P_N(s,t)&=\sum_{n\le N}e^{t\log^2n/4}n^{-s}.
\end{aligned}
$$

The source expression is the dimensionless quantity

$$ f_t(z)=P_N(s_B,t)+\gamma P_N(s_A,t). \tag{C1} $$

In particular, absolute error allowances for $H_t/B_t-f_t$ must be compared
with this expression including its prefactors. $B_t$ is nonzero throughout
the source domains.

## 2. A direct certificate for the full vertical boundary

**Proposition C.1.** For every $0\le t\le1/5$ and $0\le Y\le1$,
$H_t(X+iY)\ne0$.

### 2.1 A uniform H7 source error

Lemma A.1 gives, for $x\ge X_e$, $0\le t\le1/5$ and $0\le Y\le7$,

$$
|H_t(x+iY)/B_t(x+iY)-f_t(x+iY)|
\le E_{ab}(x)+E_c(x,t,Y),\qquad E_{ab}(x)<3\cdot10^{-9}, \tag{C2}
$$

where, with $q=x/(4\pi)$ and $L=\log q$,

$$
\begin{aligned}
E_c(x,t,Y)&=q^{-(1+Y)/4}
\exp\left[-\frac{tL^2}{16}
 +\frac{2(3^Y+3^{-Y})}{N(x,t)-1}+10^{-10}+V_7(x)\right],\\
V_7(x)&=\frac{20\sqrt{L^2+\pi^2/4}+200}{x-40}.
\end{aligned} \tag{C3}
$$

This includes $t=0$: Lemma A.1 proves the closed-time extension by dominated
convergence and right-constancy of the actual cutoff. We use the same repaired
lemma also on the smaller finite-head height interval $[0,1]$.

For an explicit whole-domain allowance, put $q_e=X_e/(4\pi)$ and
$N_e=685205$. The endpoint check $N_e^2<q_e$ gives $N(x,t)\ge N_e$.
Since $q\ge q_e>1$, $Y\ge0$, $t\ge0$ and $V_7$ decreases in $x$, the
power is at most $q_e^{-1/4}$ and the heat exponent is nonpositive.
The positive function $3^Y+3^{-Y}$ increases for $Y\ge0$, so its value
at $7$ bounds the whole H7 range. Consequently

$$
\begin{aligned}
E_{ab}(x)+E_c(x,t,Y)
&<3\cdot10^{-9}\\
&\quad+q_e^{-1/4}\exp\left[\frac{2(3^7+3^{-7})}{N_e-1}+10^{-10}+V_7(X_e)\right]\\
&<0.001215803<1/500.
\end{aligned} \tag{C4}
$$

The head evaluator `bounds.py` recomputes this endpoint expression at 256 bits;
`check_h7.py` independently checks the H7 derivation's scalar
gates at 512 bits. Taking different extremal heights in the positive inflation
and negative power enlarges the error bound, which is valid for all actual
points simultaneously. The full vertical-grid acceptance threshold remains
$1/500+10^{-12}$.

### 2.2 The matrix and its error

At $x=X$ the cutoff is exactly $N=690950$ throughout $[0,1/5]$; both strict
square-root endpoint inequalities are checked in `bounds.py`. Define

$$
n_0=345475,\quad X_m=X+\tfrac12=11998694683001/2,\quad
\ell_n=\log(n/n_0),\quad L_0=\log n_0,
$$
$$
M_{e,k}=\sum_{n=1}^{690950}n^{(-1+iX_m)/2}
       \frac{\ell_n^e}{e!}\frac{(\ell_n^2/4)^k}{k!},
\qquad 0\le e,k<62. \tag{C5}
$$

`support/head/generate-matrix.c` evaluates precisely these finite sums at
192-bit precision. It forms both factorial recurrences, their outer product,
and the complex power for each integer $n$. Arb retains the errors in the
large phase $X_m\log n/2$. No operation-count estimate or discarded-radius
argument is used. `regenerate.py` divides $1,\ldots,690950$ into consecutive
disjoint partitions, checks the exact partition endpoints, adds their balls
at 256 bits, and verifies enclosure under the final serialization. The
distributed `data/matrix.txt` is the result of this complete regeneration.

For $s=(1-Y+iX)/2$, put $w=1-s$, $s_c=\bar s$ and

$$
b_B=-Y/2-i/4,\quad b_A=Y/2-i/4,
\qquad v_B=b_B-\frac t2(\alpha(w)-L_0),\quad
v_A=b_A-\frac t2(\alpha(s_c)-L_0),
$$
$$
\begin{aligned}
p_B&=\exp\left[L_0\left(b_B-\frac t4(2\alpha(w)-L_0)\right)\right],\\
p_A&=\exp\left[L_0\left(b_A-\frac t4(2\alpha(s_c)-L_0)\right)\right],\\
F_e(t)&=\sum_{k<62}M_{e,k}t^k.
\end{aligned}
$$

The evaluated polynomial is

$$
F_M(t,Y)=p_B\sum_{e<62}F_e(t)v_B^e
       +\gamma\overline{p_A\sum_{e<62}F_e(t)v_A^e}. \tag{C6}
$$

Writing $\log n=L_0+\ell_n$ shows term by term that replacing both Taylor
polynomials in (C6) by their exponential series gives exactly (C1).
The imaginary constant $-1/4$ is $(X-X_m)/2$. The factorials occur in
(C5) once, and are not inserted again during Horner evaluation.
`matrix.py` evaluates $\log M_0$ directly, so the gamma ratio has the same
normalization as (C1).

The whole box $0\le t\le1/5$, $0\le Y\le1$ satisfies

$$
|v_A|,|v_B|<33/50,\qquad
\Re\alpha(w),\Re\alpha(s_c)>L_0.
$$

These inequalities are checked on one enclosing complex ball box. At actual
points, the last inequalities imply $|p_B|\le1$ and
$|p_A|\le n_0^{Y/2}\le\sqrt{n_0}<600$. The H7 gamma bound (A.3) gives
$|\gamma|\le\exp[Y(10^{-11}-\tfrac12\log(X/(4\pi)))]\le1$, including equality
when $Y=0$.

Set $U=L_0^2/20$ and $W=(33/50)L_0$. Since $U,W<63$, the elementary
geometric factorial-tail bound is

$$
R(a)=\frac{a^{62}}{62!\,(1-a/63)}\quad(0\le a<63).
$$

The error in a product of the two truncated exponentials is at most
$R(U)e^W+e^U R(W)$. Since $|\ell_n|\le L_0$ and
$\sum_{n\le N}n^{-1/2}\le2\sqrt N-1$, we obtain

$$
|f_t(X+iY)-F_M(t,Y)|
\le1200(2\sqrt N-1)\{R(U)e^W+e^UR(W)\}
<6.57\cdot10^{-19}<10^{-12}. \tag{C7}
$$

The coefficient balls already contain their generation and serialization
errors. Equation (C7) accounts only for the omitted analytic series.

### 2.3 Coverage and nonvanishing

The exact nominal cells are

$$
I_i=[i/2000,(i+1)/2000],\quad 0\le i<400,\qquad
J_j=[j/2000,(j+1)/2000],\quad 0\le j<2000.
$$

Their Cartesian products cover the entire closed parameter rectangle.
`support/head/verify.py` evaluates every pair $(i,j)$ at 192 bits and checks
that the evaluation ball for each parameter contains both nominal rational
endpoints. Enclosing parameter intervals can overlap or extend slightly
beyond the nominal domain; the error estimates are applied only to actual
points of the target rectangle. For a fixed time row the same interval
polynomials $F_e(I_i)$ are reused, which is an exact algebraic regrouping.
All $800000$ cells satisfy the certain inequality

$$ |F_M(I_i,J_j)|>1/500+10^{-12}. \tag{C8} $$

The smallest certified lower endpoint in the recorded replay is greater than
$1.2765849605$; this diagnostic minimum is not substituted for the individual
gates. Equations (C4), (C7) and (C8) show $H_t(X+iY)/B_t(X+iY)\ne0$.
This proves Proposition C.1.

### 2.4 The finite head remains real

**Proposition C.2 (P2).** Every zero $\rho$ of $H_t$ with
$|\Re\rho|\le X$ is real, for every $0\le t\le1/5$.

At $t=0$, [Platt–Trudgian, Theorem 1](https://arxiv.org/abs/2004.09765)
covers $0<x\le X$, since $X/2=2999673670750<3\cdot10^{12}$;
evenness covers $x<0$. At $x=0$, positivity of $\Phi(u)$ and
$\cosh(Yu)$ gives $H_0(iY)>0$. Thus the zero-height endpoint is covered too.
The finite-RH theorem is cited, not recomputed.

Proposition C.1, conjugation and evenness make both sides $\Re z=\pm X$
zero-free for $|\Im z|\le1$ throughout the time interval. At time zero the
horizontal sides of the rectangle
$K=\{|\Re z|\le X,\ |\Im z|\le1\}$ are zero-free by the finite-RH theorem.
For $t>0$, de Bruijn's strip contraction places all zeros strictly inside
$|\Im z|<1$. Thus the entire boundary of $K$ is zero-free for all these
times. By continuity and the argument principle, the number of enclosed zeros
with multiplicity is constant.

The times at which all enclosed zeros are real form a closed set: a nonreal
zero at a limiting time has a small disk away from the real axis with a
zero-free boundary, and Rouché's theorem would force a nonreal zero at nearby
times. The set is also open to the right. A simple real zero stays real by
conjugation and local uniqueness. At an $m$-fold real zero, the forward
Hermite splitting in [Polymath, Proposition 3.1(ii)](https://arxiv.org/html/1904.12438v2#S3)
gives $m$ zeros in disks of radius $O(\epsilon)$ around distinct real centres
separated by order $\sqrt\epsilon$, at time $t+\epsilon$. For sufficiently
small $\epsilon>0$ these disks are disjoint and invariant under conjugation;
each contains exactly one zero counting multiplicity, hence that zero is real.
There are finitely many clusters inside $K$, and no boundary entry is possible,
so one right-neighbourhood works for all of them. Starting at zero, closedness
and this extension property prove the assertion through $1/5$.
This conclusion concerns the finite strip $|\Re\rho|\le X$.

## 3. A uniform source recipe independent of the jet field

For each box $[t_-,t_+]\times[h_-,h_+]$ in
[support/source/boxes.json](../support/source/boxes.json), define
$Y_j=(j+2)h$, $j=1,2,3$, and

$$ V=\frac{15}{14}S(x,3h,t)-\frac{16}{21}S(x,4h,t)+\frac16S(x,5h,t). $$

**Proposition C.3 (P7).** At every point of each of these 26 closed boxes,
for every $x\ge X$, all three logarithmic derivatives are defined and
$V$ is strictly greater than the corresponding stated rational floor.

The proof uses only the H7 source and elementary zeta estimates below.
In particular it has no input from the old barrier, the jet field, or a
selected contour's actual zero height. Write

$$
\begin{gathered}
N_* =690950,\quad L_* =\log N_*,\quad r=1/20,\\
T_m=1/5,\quad \beta=1/2,\quad r_1=500001/1000000,
\quad \Omega_L=6722911/10^6.
\end{gathered}
$$

The 384-bit program `support/source/verify.py` evaluates the formulas below
for every box and rejects unless all the indicated inequalities hold.

### 3.1 Uniform domains and source constants

Every radius-$r$ disk about a source centre has real part at least
$X-r>X_e$ and height strictly between $0$ and $7$. The program verifies
$X-r>4\pi N_*^2$. Thus every actual cutoff on every disk is at least $N_*$.
The square root defining $N(x,t)$ has derivative at most $1/(8\pi N_*)$;
its variation on a disk is at most $r/(8\pi N_*)<1$. The disk and centre
cutoffs therefore differ by at most one.

At each centre, freeze its actual cutoff only for the local holomorphic germ

$$ E_{N_c}(z)=H_t(z)/B_t(z)-P_{N_c}(s_B,t)-\gamma P_{N_c}(s_A,t). $$

The centre cutoffs at different $x,t$ can differ. No floor function is
differentiated. H7 and the two changed-cutoff terms will bound $E_{N_c}$
on the whole disk. All Cauchy estimates below apply to this analytic
remainder, not to a quotient by $H_t$.

Set

$$
\begin{aligned}
\ell_{\rm cut}&=\log\left(1-\frac{T_m}{16N_*^2}\right),&
c_{\rm cap}&=-\frac{T_m\ell_{\rm cut}}4,\\
c_{\rm corr}&=\frac{T_m}{X_e^2},&
d_\gamma&=10^{-11}-\ell_{\rm cut}/2,\\
k&=\frac{T_m}{2(4\pi N_*^2-\pi T_m/4-6)}.
\end{aligned}
$$

Combining the H7 real-part, gamma and kappa bounds with the actual cutoff
relation gives, for $L=\log N$,

$$
\begin{aligned}
c(Y)&=(1+Y)/2-c_{\rm cap}-c_{\rm corr},\\
\Re s_B&\ge c(Y)+tL/2,\\
\Re s_A&\ge c(Y)-Y-kY+tL/2,\\
|\gamma|&\le e^{d_\gamma Y}N^{-Y}.
\end{aligned} \tag{C9}
$$

The cutoff relation is used before replacing $N$ by $N_*$; in particular
$\log(x/(4\pi))\ge2\log N+\log(1-T_m/(16N^2))$.
For $y_j^-=(j+2)h_-$, $y_j^+=(j+2)h_+$, put

$$ c_j=c(y_j^-),\qquad a_j=c_j+(t_-/2)L_*.
\quad\text{Then}\quad a_j=a_1+(j-1)h_-/2. \tag{C10} $$

Every actual $s_B(x+iY_j,t)$ and every ideal shifted argument
$s_B(x+3ih,t)+(j-1)h/2$ has real part at least $a_j$.
The program checks

$$ c_j>1,\quad c_j>5/\log1024,\quad a_j-r_1r>1,\quad a_j>3/L_*. \tag{C11} $$

Let $L_x=\log(x/(4\pi))$ and define

$$
d_a(x)=\frac8{x-20},\quad
A_0(x)=\tfrac12\sqrt{L_x^2+\pi^2/4}+d_a(x),\quad
A_1(x)=1/x+6/x^2,
$$
$$
b_B=d_a(X_e)/2+T_m A_0(X_e)A_1(X_e)/4,\qquad
\eta=t_+/[4(X_e-6)].
$$

The H7 archimedean estimates imply
$|B_t'/B_t+\pi/8+i\Omega(x)|\le b_B$ and
$|(s_B)_z+i/2|,|(s_A)_z-i/2|\le\eta$.
The products $A_0A_1$ and $A_1\log x$ decrease for $x\ge X_e$:
$A_0'\le1/(2x)$, $A_0>1/2$, and differentiation of the inverse powers
gives the signs. The code checks $b_B<10^{-10}$,
$1/2+\eta<r_1$, and the reflected phase allowance

$$
\frac1{N_*}+d_a(X_e)+\frac{t_+}{2}A_0(X_e)A_1(X_e)
 +\frac{t_+}{4}A_1(X_e)\log X_e<\beta. \tag{C12}
$$

Together with (C11), the spatial rate bound places the whole zeta reference
disk in $\Re s>1$.

### 3.2 The finite heat remainder and its infinite majorant

The identity at the actual cutoff is

$$
P_N(s_B,t)=\zeta(s_B)+\frac t4\zeta''(s_B)
 +R_{\rm heat}-T_N,
$$
$$
R_{\rm heat}=\sum_{n\le N}(e^{t\log^2n/4}-1-t\log^2n/4)n^{-s_B},\quad
T_N=\sum_{n>N}(1+t\log^2n/4)n^{-s_B}. \tag{C13}
$$

Only the finite sum is heated exponentially. No infinite positive-time
heated Dirichlet series is introduced. For $v=\log n$ and
$H(u)=1-(1+u)e^{-u}$, the included summands in $R_{\rm heat}$ are bounded by

$$
w_j(n)=n^{-c_j}
 \exp\{t_-[v^2/4-v\max(L_*,v)/2]\}\,H(t_+v^2/4). \tag{C14}
$$

Indeed $L\ge\max(L_*,v)$ for included $n$, the combined heat/source
exponent is nonpositive and uses $t_-$, while $H$ increases and uses $t_+$.
After this combination the positive majorant can be extended to all
$n\ge2$. Write $H_{j,k}=\sum_{n\ge2}(\log n)^k w_j(n)$ for $k=0,1$.

Since $H(u)=\int_0^u ve^{-v}dv\ge u^2e^{-u}/2$,
$H'/H\le2/u$ for $u>0$. The logarithmic derivatives of the summands
for $n\ge1024$ are at most $-c_j+(k+4)/\log n<0$ by (C11).
The head $2\le n\le1024$ is summed directly and the remainder is bounded
by the integral from $1024$ to infinity. In logarithmic coordinates its
decaying factor is

$$ D_j(v)=\exp\{-(c_j-1)v+t_-[v^2/4-v\max(L_*,v)/2]\}. $$

For each of the 1024 consecutive cells of width $1/16$ beginning at
$\log1024$, evaluate $D_j$ at the left endpoint and the increasing factor
$v^kH(t_+v^2/4)$ at the right. Above
$V_*=\log1024+64>L_*$, put
$q_j=c_j-1+t_-V_*/2>0$ and
$P_j=e^{-(c_j-1)V_*-t_-V_*^2/4}$. A tangent exponential bound gives the
remaining tails

$$ P_j/q_j,\qquad P_j(V_*/q_j+1/q_j^2). \tag{C15} $$

For the ordinary tail define the exact integral

$$
T_k(a)=N_*^{1-a}\sum_{\ell=0}^k
 \frac{k!}{(k-\ell)!}\frac{L_*^{k-\ell}}{(a-1)^{\ell+1}}
=\int_{N_*}^{\infty}(\log u)^ku^{-a}\,du.
$$

The decreasing-summand gates in (C11) show that the value and first
logarithmic-moment tails of $T_N$ are bounded by

$$ T_0(a_j)+(t_+/4)T_2(a_j),\qquad
T_1(a_j)+(t_+/4)T_3(a_j). \tag{C16} $$

The physical derivative of these terms and the heat remainder costs an
additional factor at most $r_1$ on their first logarithmic moments.

### 3.3 Reflected terms for every actual cutoff

For an actual included term, (C9) gives the reflected amplitude majorant

$$
e^{d_\gamma Y-YL}
n^{-c(Y)+Y+kY}\exp\{t(v^2/4-Lv/2)\}. \tag{C17}
$$

Its logarithmic derivative in $Y$ is bounded above by
$d_\gamma-(1/2-k)L_*<0$, an explicit checked gate. This gate also implies
$k<1/2$. The heat exponent is nonpositive. Thus the full expression is
bounded by its corner $Y=y_j^-$, $t=t_-$. Writing
$y=y_j^-$ and $b=c_j-y-ky$, the resulting envelope is
$e^{d_\gamma y-yL}n^{-b}e^{t_-(v^2/4-Lv/2)}$.

For the derivative, H7 gives the raw phase identity, with $g=\log\gamma$,

$$
|g_z-(s_A)_z\log n-i(L-\tfrac12\log n)|
\le1/N+d_a(x)+(t/2)A_0(x)A_1(x)+(t/4)A_1(x)\log x.
$$

By (C12), the derivative is bounded by $(L+\beta)$ times the amplitude
envelope. This retains the cancellation between the gamma and index phases.

Here is the all-$N$ reduction. The summand as a function of real $u\in[1,N]$
has at most one minimum, since its logarithmic derivative in $\log u$
increases. Its sum is consequently bounded by both endpoint terms plus
the integral. Set

$$
I(L)=\int_0^L e^{(1-b-t_-L/2)v+t_-v^2/4}\,dv,
\quad F(L)=e^{d_\gamma y-yL}
 [1+I(L)+e^{-bL-t_-L^2/4}].
$$

Let $a_0=1-b>0$, $e=b+y$, and
$K_0=(1-e^{-a_0L_*})/a_0$. The program checks

$$ (y-1/(L_*+\beta))K_0>1,\qquad e(L_*+\beta)>1. \tag{C18} $$

For $A(L)=e^{-yL}I(L)$ and
$E(L)=e^{(1-b-y)L-t_-L^2/4}$, differentiation gives
$A'\le E-yA$. Substitution $v=L-w$ gives
$A/E=\int_0^L e^{-a_0w+t_-w^2/4}dw\ge K_0$ for $L\ge L_*$.
Therefore $[(L+\beta)A]'$ is negative by (C18).
Both normalized endpoint terms, with the same factor $L+\beta$, also
decrease: the $n=N$ term uses the second gate of (C18), and the $n=1$
term uses the first. Hence $(L+\beta)F(L)$ and $F(L)$ decrease for every
real $L\ge L_*$.

At $L_*$ the additional gate $1-b-t_-L_*/2>0$ makes the integrand increasing.
The program bounds $I(L_*)$ by 1024 right-endpoint rectangles and obtains
upper bounds $\mathrm{Ref}_{j,0}=F^+(L_*)$ and
$\mathrm{Ref}_{j,1}=(L_*+\beta)F^+(L_*)$. The two endpoint terms are
included in both. This proves the cutoff reduction on the entire unbounded
range; it is not a sample at $N_*$.

### 3.4 Fixed-cutoff source disks and both cutoff changes

Let $y_d=y_j^--r$, $y_u=y_j^++r$, $L_e=\log(X_e/(4\pi))$ and

$$
I_+=\frac{2(3^{y_u}+3^{-y_u})}{685205-1}+10^{-10}
 +\frac{20\sqrt{L_e^2+\pi^2/4}+200}{X_e-40}.
$$

The H7 point-error contribution other than its $3\cdot10^{-9}$ allowance
is bounded at a centre and on its disk, respectively, by

$$
E_c=e^{-(1+y_j^-)L_e/4-t_-L_e^2/16+I_+},\qquad
E_d=e^{-(1+y_d)L_e/4-t_-L_e^2/16+I_+}. \tag{C19}
$$

All negative factors use lower endpoints; the positive height inflation uses
$y_u$. The unbounded-$x$ reduction uses the decreasing functions in H7.

At a disk point with actual cutoff $m\ge N_*$, a changed term has index
$n=m$ or $m+1$. Put $L=\log m$ and
$\delta=\log(n/m)\in[0,\log(1+1/m)]$. Its primary exponent is at most

$$
-a_d(L+\delta)-tL^2/4+t\delta^2/4,
\qquad a_d=(1+y_d)/2-c_{\rm cap}-c_{\rm corr}>0.
$$

Dropping $-a_d\delta$, bounding the positive correction by
$T_m\log(m+1)/(2m)$ and using decrease in $m$ gives

$$
\mathrm{Cut}_1=
\exp\left[-a_dL_*-t_-L_*^2/4
                 +\frac{T_m\log(N_*+1)}{2N_*}\right]. \tag{C20}
$$

The reflected changed term is at most $\mathrm{Cut}_1G_{\rm cut}$, where

$$
G_{\rm cut}=
\exp\{d_\gamma y_u+y_u\log(1+1/N_*)+ky_u\log(N_*+1)\}. \tag{C21}
$$

Here the gamma/index ratio is combined before taking endpoints. In particular
the positive product
$\log(m+1)T_m/[2(4\pi m^2-\pi T_m/4-6)]$ decreases for $m\ge N_*$,
as direct differentiation shows. An isolated unbounded $\log m$ is not
replaced by $\log N_*$.

The source error has no cutoff discrepancy at the centre. On the disk it
includes both changed terms. Cauchy's estimate on the fixed-$N_c$ germ gives

$$
\mathrm{Src}_{j,0}=3\cdot10^{-9}+E_c,\qquad
\mathrm{Src}_{j,1}=
\{3\cdot10^{-9}+E_d+\mathrm{Cut}_1(1+G_{\rm cut})\}/r. \tag{C22}
$$

Only the first derivative is needed. The source circle can cross $x=X$;
its validity comes from H7 on $x\ge X_e$, without a field assumption.

### 3.5 Nonvanishing and a single logarithmic-remainder bound

Let $\mathrm{Tail}_{j,k}$ denote (C16). At each actual point, (C13) and
(C1) yield

$$
G:=H_t/B_t=\zeta(s_B)(1+w+e),\quad
w=(t/4)Z(s_B),\quad Z=\zeta''/\zeta,\quad e=R/\zeta(s_B),
$$
$$
|R|\le R_0=H_{j,0}+\mathrm{Tail}_{j,0}+\mathrm{Ref}_{j,0}+\mathrm{Src}_{j,0},
$$
$$
|R_z|\le R_1=r_1(H_{j,1}+\mathrm{Tail}_{j,1})
                   +\mathrm{Ref}_{j,1}+\mathrm{Src}_{j,1}. \tag{C23}
$$

For real $a>1$, define
$$
W_k(a)=\sum_{n\ge2}\Lambda(n)(\log n)^kn^{-a},\qquad
m(a)=\zeta(2a)/\zeta(a)>0,
$$
where $\Lambda(n)$ is the von Mangoldt function. The Euler product implies
$|\zeta(s)|\ge m(a)$ for $\Re s\ge a$.
The real zeta Taylor coefficients at $a_j$ give certified enclosures of
$W_0,\ldots,W_3$. Put

$$
Z_0=W_1+W_0^2,\quad Z_1=W_2+2W_0W_1,\quad
Z_2=W_3+2W_1^2+2W_0W_2,
$$
$$
V_0^+(a)=W_0+(t_+/4)Z_1,\quad
V_1^+(a)=W_1+(t_+/4)Z_2,
$$
$$
\begin{gathered}
e_0=R_0/m(a_j),\quad e_1=(R_1+r_1W_0R_0)/m(a_j),\\
w_0=(t_+/4)Z_0,\quad w_1=(t_+/4)r_1Z_1,\quad \rho_0=w_0+e_0.
\end{gathered}
$$

Every one of the 78 bands passes the strict gate $\rho_0<1$. Consequently
$|1+w+e|\ge1-\rho_0>0$ at every centre, proving nonvanishing of $G$
and hence of $H_t$ there. This argument requires no prior zero-free region
for $H_t$ on the source disks.

For $\ell=\log\zeta$, the exact logarithmic-derivative remainder is

$$
\mathcal E=\frac{G_z}{G}-(s_B)_z[\ell'(s_B)+(t/4)Z'(s_B)]
=\frac{e_z-w_z(w+e)}{1+w+e}.
$$

Thus throughout the box

$$ |\mathcal E|\le E_j:=\frac{e_1+w_1\rho_0}{1-\rho_0}. \tag{C24} $$

This is the sole normalization route used by the publication checker.

### 3.6 The common-phase combination and the negative middle coefficient

At the actual time, the function

$$
\Phi_t(s)=-\ell'(s)-(t/4)Z'(s)
=\sum_{n\ge2}A_t(n)n^{-s}
$$

has nonnegative coefficients

$$ A_t(n)=\Lambda(n)+(t/4)
 [\Lambda(n)\log^2n+\log n\sum_{ab=n}\Lambda(a)\Lambda(b)]. $$

This ordinary Dirichlet series converges absolutely for $\Re s>1$.
Write $A=15/14$, $B=16/21$, $D=1/6$ and $\mu=A-B+D=10/21$.
For a shared argument $s_1$ and $v=n^{-h/2}$, the combined coefficient is
$P(v)=A-Bv+Dv^2>0$ on $[0,1]$. Moreover

$$
\frac{3A-4Bv+5Dv^2}{2}
=\frac{135-128v+35v^2}{84}\ge\frac12.
$$

Hence $n^{-3h/2}P(n^{-h/2})$ decreases in $h$.
First increase the positive coefficients from $t$ to $t_+$; then use
the lower real shift from $t_-$; finally combine the entire height factor
before taking $h=h_-$. This proves the coherent upper bound

$$
\Re\sum_{j=1}^3(A,-B,D)_j
\Phi_t(s_1+(j-1)h/2)
\le A V_0^+(a_1)-B V_0^+(a_2)+D V_0^+(a_3). \tag{C25}
$$

The three real zeta quantities on the right are values of one exact expression.
The program evaluates it by signed interval arithmetic, so the subtracted
term uses the correct enclosure direction. It does not subtract three
unrelated upper bounds. The factored common base exponent need not itself
exceed one; no zeta series at that incomplete exponent is used.

The actual arguments differ from the ideal ones by at most

$$ \epsilon_j=t_+(j-1)h_+/[4(X_e-6)]. $$

Both endpoints, and therefore their joining segment, have real part at least
$a_j$. The associated derivative allowance is $V_1^+(a_j)$.
The density identity from the definition of $\Phi_t$ is
$S_j=\Omega-\tfrac12\Re\Phi_t(s_j)+\text{error}$, with error modulus
at most $b_B+\eta V_0^+(a_j)+E_j$ by (C24).

Finally $\Omega(x)>\Omega_L$ for $x\ge X$; the program checks it at the
smaller $X-10^6$. Since $\mu>0$, only this lower bound on the unbounded
archimedean term is needed. We conclude

$$
\begin{aligned}
V\ge L_{\rm box}:={}&\mu\Omega_L
-\tfrac12[A V_0^+(a_1)-B V_0^+(a_2)+D V_0^+(a_3)]\\
&-\tfrac12[B\epsilon_2V_1^+(a_2)+D\epsilon_3V_1^+(a_3)]
-2b_B\\
&-\eta[A V_0^+(a_1)+B V_0^+(a_2)+D V_0^+(a_3)]
-[AE_1+BE_2+DE_3].
\end{aligned} \tag{C26}
$$

For each of the 26 boxes the computed ball for this exact lower expression
lies strictly above its published rational floor. For example, the A-box
lower expression exceeds $2.8911909440>289/100$, and the box-25 expression
exceeds $2.8271559938>565431/200000$. Every box, including all its edges and
corners, is checked separately. This proves Proposition C.3. The original
larger screening target on some boxes is irrelevant to this strict floor
comparison, and its failure was not interpreted as an upper bound for $V$.

## 4. Reproduction and trust boundary

From the publication root, using the pinned Python environment:

```sh
python support/head/verify.py
python support/head/spotcheck.py
python support/source/verify.py
```

The first run consumes the stored coefficient balls but computes every
boundary cell anew; the second computes every source enclosure from the
exact box parameters and the formulas above. Both refuse failed or ambiguous
inequalities. Optional `--output NEW.json` preserves a fresh replay record;
the default writes no files.

The additional `spotcheck.py` command independently evaluates both original
finite sums at $(t,Y)=(0,0)$ and $(1/5,1)$, at 256 bits. Its direct result
agrees with (C6) within $2.81\cdot10^{-33}$ at both points.
This checks the factorization and normalization through a different evaluation
path. Its scope is two points, and the full-domain proof remains (C7)–(C8).

To remove dependence on the stored matrix:

```sh
python support/head/regenerate.py --jobs 8 --output /tmp/dbn-matrix-new.txt
python support/head/verify.py --matrix /tmp/dbn-matrix-new.txt
```

The regeneration has no input numerical table. Exact matrix-centre and partition
metadata are checked. Runtime measurements are included in the replay records
and depend on the machine and execution profile.
The programs, rational input boxes, full matrix balls, component records and
environment details are distributed under `support/head/` and `support/source/`.

The analytic reductions in this appendix, H7, the published finite-RH theorem,
and the mathematical behavior of Arb/FLINT are the trust boundary. The C
regeneration also trusts its compiler and linked libraries. These are
computer-assisted mathematical proofs conditional on the stated literature
and software foundations; the numerical checkers do not constitute Lean
kernel verification of those foundations. The quoted intervals and error
bounds apply to their exact stated domains and cutoffs.
