# Appendix A. Analytic approximation, density, and jet bounds

This appendix proves the analytic estimates used as P3--P5 and supplies the
whole-row analytic interpretation of P8. The finite-head theorem P2 and the
three-probe source floors P7 are proved in Appendix C. The classical zero
identities and first-contact argument are stated in the main text. The only
non-elementary approximation input used here is the generic-real-part
Riemann--Siegel expansion of Arias de Reyna, in the explicit form recorded in
[Po19, Proposition 6.2 and equation (58)]. In particular, the restriction
$0\le y\le1$ in [Po19, Theorem 1.3] is respected: the larger range below is
derived from the generic-real-part expansion, with new error estimates.

Write $X_e=5900000000000$, $X_L=5999346341500$, $X=5999347341500$,
$t_m=1/5$, $N_e=685205$, and $N_0=690950$. All decimal constants in this
appendix denote exact rationals. The accompanying programs use exact rational
geometry and Arb ball arithmetic at 512 bits. Statements such as $a<b$ in a
program mean that the entire computed ball for $a$ lies strictly below the
entire ball for $b$.

## A.1. Normalization and the enlarged approximation

For $z=x+iy$, put $w=(1-iz)/2$, $v=1-w$, and define

$$
\begin{aligned}
M_0(s)&=\frac{s(s-1)}{16}\pi^{-s/2}\sqrt{2\pi}
 \exp\!\left[\left(\frac{s}{2}-\frac12\right)\Log\frac{s}{2}-\frac{s}{2}\right],\\
\alpha(s)&=\frac1{2s}+\frac1{s-1}+\frac12\Log\frac{s}{2\pi},
&M_t(s)&=M_0(s)e^{t\alpha(s)^2/4},\\
B_t(z)&=M_t(w),&s_B&=w+\frac t2\alpha(w),\\
s_A&=v+\frac t2\alpha(v),&\gamma&=M_t(v)/M_t(w),\\
b_t(n)&=e^{t\log^2n/4},&P_N(s,t)&=\sum_{n=1}^N b_t(n)n^{-s}.
\end{aligned}
$$

The principal logarithms are holomorphic throughout the large-$x$ regions
used below. In particular $B_t$ is nonzero there. Put
$\mathcal Q=x/(4\pi)$, $L=\log\mathcal Q$,
$Z=(L^2+\pi^2/4)^{1/2}$, and
$N=\lfloor\sqrt{\mathcal Q+t/16}\rfloor$. The holomorphic expression with
a *fixed* integer cutoff is
$f^{[N]}=P_N(s_B,t)+\gamma P_N(s_A,t)$.

**Lemma A.1 (enlarged approximation).** For every $x\ge X_e$,
$0\le t\le t_m$, and $0\le y\le7$,

$$
\left|\frac{H_t(z)}{B_t(z)}-f^{[N]}(z)\right|
 \le E_{ab}(x)+E_c(x,t,y),                                      \tag{A.1}
$$

where

$$
\begin{aligned}
d(x)&=\frac{t_m^2L^2/16+0.626}{x-6.66},\\
E_{ab}(x)&=2.01\frac{1000}{999}\frac{1.001^{0.501}}{0.501}
                 \mathcal Q^{0.2505}d(x),\\
V_7(x)&=\frac{20Z+200}{x-40},\\
E_c(x,t,y)&=\mathcal Q^{-(1+y)/4}
 \exp\!\left[-\frac{tL^2}{16}
       +\frac{2(3^y+3^{-y})}{N-1}+10^{-10}+V_7(x)\right].
\end{aligned}
$$

Here $E_{ab}(x)<3\cdot10^{-9}$ and the total error in (A.1) is less than
$1/500$. Both $E_{ab}(x)$ and $E_c(x,t,y)$ are nonincreasing in $x$, with
the latter interpreted across the upward jumps of $N$.

*Proof.* We give the details needed to enlarge the original parameter range.
Direct differentiation gives

$$
\alpha'=-\frac1{2s^2}-\frac1{(s-1)^2}+\frac1{2s}.
$$

For $s=\sigma+ix/2$, $|\sigma|\le4$, elementary bounds for the logarithm
and the two rational terms give

$$
\begin{aligned}
|\alpha(s)-L/2-i\pi/4|&\le7/x+16/x^2\le8/(x-20),\\
|\alpha'(s)|&\le1/x+6/x^2\le1/(x-6),\\
|\alpha''(s)|&\le2/x^2+24/x^3.
\end{aligned} \tag{A.2}
$$

The last two inequalities hold for every real $\sigma$. Conjugation gives
the signs appropriate to negative imaginary parts. Taking real parts of the
explicit formula also gives
$\Re\alpha((1+y-ix)/2)\ge L/2-2/x^2$ for $y\ge0$.
The possibly negative rational term occurs only when $y<1$ and has magnitude
at most $2/x^2$; when $y\ge1$ both rational real parts are nonnegative.

Let $\beta=\alpha+(t/2)\alpha\alpha'$. Since $Z\le L+\pi/2$, (A.2) gives

$$
|\Re\beta-L/2|\le\frac{tL/4+9}{x-20}<10^{-11}.
$$

Integrating horizontally between real parts $(1-y)/2$ and $(1+y)/2$,
both in $[-3,4]$, proves

$$
e^{-10^{-11}y}\mathcal Q^{-y/2}\le|\gamma|
 \le e^{10^{-11}y}\mathcal Q^{-y/2},\qquad
s_A=\overline{s_B}+\kappa-y,\quad
|\kappa|\le\frac{ty}{2(x-6)}.                         \tag{A.3}
$$

The heat-convolution identities [Po19, equations (39)--(41)] express $H_t$
as two sums of $r_{t,n}$ and two Riemann--Siegel remainders $R_{t,N}$.
The following estimate for $r_{t,n}(\sigma+iT)$ is valid for every real
$\sigma$, $T>10$, and $0<t\le1/2$:

$$
\left|\frac{r_{t,n}(\sigma+iT)}
 {M_t(\sigma+iT)b_t(n)n^{-\sigma-iT-t\alpha(\sigma+iT)/2}}-1\right|
\le \exp\!\left[
 \frac{t^2|\alpha(\sigma+iT)-\log n|^2/8+t/4+1/6}{T-3.33}
 \right]-1.                                                   \tag{A.4}
$$

For completeness, the uniform Stirling estimate that justifies the Gaussian
contour in (A.4) is proved in A.2. For every real $\sigma$,
$\Im\alpha(\sigma+iT)\ge-1/(2T)-1/T$, since the logarithm has positive
argument. The shift $+(t/2)(\alpha-\log n)$ therefore leaves imaginary
part at least $T-0.0375>T-0.08$. On that contour the gamma argument has
imaginary part at least $(T-0.08)/2$, giving the error
$1/[6(T-2.08)]\le1/[6(T-3.08)]$. Taylor's formula for $\log M_0$ and
$|\alpha'|\le1/[2(T-3.08)]$ then bound the remaining exponent by

$$
\frac{tv_0^2/2+t^2|\alpha-\log n|^2/8+1/6}{T-3.08}.
$$

Integration against $e^{-v_0^2}/\sqrt\pi$ yields (A.4): the Gaussian factor
$(1-t/[2(T-3.08)])^{-1/2}$ is at most $e^{t/[4(T-3.33)]}$.
Thus the proof of [Po19, Proposition 6.1] applies with this stated repair,
for arbitrary real $\sigma$.

For $n\le N$, (A.2) gives
$|\alpha-\log n|^2\le\frac14\log^2(\mathcal Q/n^2)+0.667$.
The remaining numerator is less than $0.313$ because
$t_m^2(0.667)/8+t_m/4+1/6<0.313$.
Also $|\log(\mathcal Q/n^2)|\le L$ on this domain. Hence the multiplier
in (A.4) is at most $e^{d(x)}-1\le1000d(x)/999$.
Combining the heat factors *before* bounding them gives
$|b_t(n)n^{-s_B}|\le n^{-0.499}$. By (A.3) and the cutoff relation the
reflected-to-first magnitude ratio at $n\le N$ is less than $1.01$.
Finally
$\sum_{n\le N}n^{-0.499}\le N^{0.501}/0.501$ and
$N\le1.001\sqrt{\mathcal Q}$. These inequalities give $E_{ab}$.

For the remainders, put $T=x/2$, $T'=T+\pi t/8$ and
$a=\sqrt{T'/(2\pi)}$. Section A.2 proves, uniformly for
$-3\le\sigma\le4$,

$$
R_{t,N}(\sigma+iT)=\omega_Ne^{i\pi\sigma/4}
 e^{t\pi^2/64}M_0(iT')\{C_0(p)+\varepsilon_\sigma\},
\quad |\omega_N|=1,\quad |C_0(p)|\le1/2,
$$

with

$$
|\varepsilon_{(1+y)/2}|+|\varepsilon_{(1-y)/2}|
 \le\frac{2(3^y+3^{-y})}{N-1}+10^{-10}.              \tag{A.5}
$$

In normalizing by $B_t$, the displacement from $iT'$ to
$(1+y)/2+iT$ has squared modulus less than $17$. The Taylor and linear
errors are bounded by
$3\sqrt{17}/x+17/[2(x-6)]<22/(x-20)$.
In $\log|M_0(iT')/M_0((1+y)/2+iT)|$ the displacement contributes
$-t\pi^2/32$. The other real leading terms are
$t\pi^2/64$ from the remainder contour, and
$-t\Re\alpha^2/4=-tL^2/16+t\pi^2/64+$ error from $M_t$.
The three $\pi^2$ terms cancel. The remaining positive error is at most

$$
\frac{22+2tZ}{x-20}+\frac{16t}{(x-20)^2}\le V_7(x).
$$

The two $C_0$ contributions have total modulus at most one; use
$1+r\le e^r$ on their combined error (A.5). This gives $E_c$.

All endpoint reductions are monotonic reductions. For $E_{ab}$ its
logarithmic derivative multiplied by $x$ is less than
$0.2505+2/L-1<0$. In $E_c$, the power and heat factors decrease, $N$ is
nondecreasing, and $V_7$ decreases since $xZ'(x)\le1$ and its numerator
is greater than $200$. The scalar program `check_h7.py` proves
$E_{ab}(X_e)<1.389336\cdot10^{-9}$ and the whole-domain envelope
$3\cdot10^{-9}+\mathcal Q_e^{-1/4}
 \exp(2(3^7+3^{-7})/(N_e-1)+10^{-10}+V_7(X_e))<0.001215803$.
The argument so far is for $t>0$. For each fixed $x,y$, the actual cutoff is
right-constant at $t=0$, including an integral square-root value. Dominated
convergence in the defining heat integral, using
$e^{t_m u^2+7u}|\Phi(u)|$, passes (A.1) to $t=0$. $\square$

## A.2. Uniform Stirling and the Gaussian Riemann--Siegel remainder

**Lemma A.2 (vertical Stirling bound).** On
$\mathbb C\setminus(-\infty,0]$, let
$\theta(z)=\log\Gamma(z)-[(z-1/2)\Log z-z+\frac12\log(2\pi)]$,
using the branch real on the positive axis. If $v_0=|\Im z|>1$, then

$$
|\theta(z)|<\frac1{12(v_0-1)}.                       \tag{A.6}
$$

*Proof.* Two-term Euler--Maclaurin, first for $\Re z>0$, gives

$$
\theta(z)=\frac1{12z}-\frac1{360z^3}
 -\frac14\int_0^\infty\frac{B_4(\{u\})}{(z+u)^4}\,du,
\quad B_4(r)=r^4-2r^3+r^2-\frac1{30}.
$$

The integral is locally uniformly convergent on the slit plane, so the
identity theorem extends the formula to that whole plane. This continuation
retains the contribution present near the negative real axis. Since
$|B_4(r)|\le1/30$ on $[0,1]$ and
$\int_{\mathbb R}(u^2+v_0^2)^{-2}\,du=\pi/(2v_0^3)$,

$$
|\theta(z)|\le\frac1{12v_0}
 +\frac{1/360+\pi/240}{v_0^3}<\frac1{12(v_0-1)}.
$$

The last inequality follows from
$12(1/360+\pi/240)(v_0-1)<v_0^2$. $\square$

This bound is used in place of the unrestricted $|z|$-dependent estimate
in [Po19, Lemma 5.1(v)]. A bound that decreases with $|\Re z|$ at fixed
nonzero $\Im z$ cannot discard the reflection contribution near the
negative real axis.

We now prove (A.5). In the contour for $R_{t,N}$, write
$U=\sigma+\sqrt t V$ with density $e^{-V^2}/\sqrt\pi$, and put
$A_g=T-3$, $D=1-t/A_g$. The gamma error from (A.6), the Taylor error for
$M_0(U+iT')$, and the linear error in $\alpha(iT')$ have combined modulus

$$
\frac{U^2+6|U|+2/3}{4A_g}\le\frac{U^2+1}{A_g}.       \tag{A.7}
$$

The $2/3$ in (A.7) is necessary: the gamma bound is $1/[6(T'-2)]$.
For $|\sigma|\le4$, Gaussian completion gives

$$
\begin{aligned}
\mathbb E e^{(U^2+1)/A_g}-1
 &\le D^{-1/2}e^{17/A_g+16t/(A_g^2D)}-1<6\cdot10^{-12},\\
0.2\,\mathbb E(9^Ue^{(U^2+1)/A_g})
 &\le0.2\,9^\sigma D^{-1/2}
       e^{17/A_g+t(\log3+4/A_g)^2/D}<0.26\,9^\sigma,\\
0.029\,\mathbb E(2^{-U}e^{(U^2+1)/A_g})
 &\le0.029\,2^{-\sigma}D^{-1/2}
       e^{17/A_g+t(\log2/2+4/A_g)^2/D}<0.030\,2^{-\sigma}.
\end{aligned} \tag{A.8}
$$

Every positive factor is largest at $x=X_e,t=t_m$; `check_h7.py`
verifies these endpoint inequalities. The coefficient $17$ replaces the
smaller-domain value $5$.

Here are the explicit coefficient and tail bounds used with (A.8).
The expansion in [Po19, Proposition 6.2] has coefficients $C_k(p,U)$ and
remainder $RS_K$ satisfying, with
$\kappa_0=((3-2\log2)\pi)^{-1/2}$ and $P_0=\sqrt2/(4\pi^2)$,

$$
\begin{array}{ll}
U\ge0:& |C_1|/a+|RS_1|
 \le0.2\,9^U/a+0.173\,2^{3U/2}/a^2
 \le0.2\,9^U/(a-0.865),\\
U<0:& |C_k|/a^k
 \le P_0\,2^{-U}\Gamma(k/2)(\kappa_0/a)^k.
\end{array}
$$

Choose the measurable truncation $K=1$ when $U\ge0$, and
$K=\max(100,\lfloor-U\rfloor+3)$ otherwise. Thus $K+U\ge2$
whenever the negative-real-part remainder requires it. Separating even and
odd indices shows

$$
a\sum_{k=1}^{100}P_0\Gamma(k/2)(\kappa_0/a)^k
 \le P_0\frac{\sqrt\pi\kappa_0+\kappa_0^2/a}
                  {1-50\kappa_0^2/a^2}<0.029.        \tag{A.9}
$$

For $K=100$, retain $RS_{100}$ separately. The elementary bound
$\Gamma(101/2)\le101^{101}$ and $1.1(101)/N_e<10^{-3}$,
together with (A.8) and $2^{-\sigma}\le8$, give a Gaussian expectation
less than $10^{-301}$.
All other indices beyond $100$, including $RS_K$ at its distinct index
$k=K+1$, are bounded by
$\frac12 2^{-U}1.1^k\Gamma(k/2)/a^k$ and satisfy $k\le-U+4$.
Tonelli's theorem applies to these positive majorants. With
$r=U-\sigma\le7-k$ and $U^2+1\le2r^2+33$, their total is at most

$$
8\sqrt{t/\pi}\,e^{33/A_g}
\sum_{k\ge100}\frac{1.1^k\Gamma(k/2)}{(k-8)a^k}
 \exp\!\left[-\frac{(k-7)^2}{2t}+(k-7)\log2\right].   \tag{A.10}
$$

The prefactor is less than $4$. Using
$\Gamma(k/2)\le k^k$, $\log k\le k/4$, $\log1.1<0.1$,
and $\log2<1$, the logarithm of each numerator in (A.10) is at most
$-3k^2/4+15.1k-49\le-k^2/2$ for $k\ge100$.
Thus (A.10) is less than $4e^{-5000}<10^{-100}$.
This accounts for the entire negative Gaussian tail, rather than a bounded
range of its real parts.

The two applied real parts are $(1+y)/2$ and $(1-y)/2$. Their
$0.26\,9^\sigma$ terms sum to $0.78(3^y+3^{-y})$, and
$2^{-1/2}(2^{y/2}+2^{-y/2})\le3^y+3^{-y}$.
The denominators $a-0.865$ and $a-0.353$ exceed $N-1$.
The remaining total $6\cdot10^{-12}+2\cdot10^{-100}+2\cdot10^{-301}$
is less than $10^{-10}$. Including the two factors $|C_0|\le1/2$
therefore gives (A.5).

## A.3. Full disks, the top boundary, and infinity

**Lemma A.3 (cutoff correction on a disk).** Fix a center $x_0+iY$,
a time $0\le t\le t_m$, and a disk of radius $0<r\le1/4$ lying inside
$x\ge X_e$, $0\le y\le7$. Suppose every actual cutoff in the disk
is at least $n_*\ge N_e$. If $0\le y_d\le y\le y_u\le7$ on the disk, let

$$
\begin{aligned}
\ell_*&=\log(1-t_m/(16n_*^2)),&c_*&=-t_m\ell_*/4,\\
k_*&=\frac{t_m}{2(4\pi n_*^2-\pi t_m/4-6)},\\
C_1&=\exp\!\left[
 (-(1+y_d)/2+t_m/X_e^2+c_*)\log n_*
 -t\log^2n_*/4+\frac{t_m\log(n_*+1)}{2n_*}\right],\\
C_2&=e^{10^{-11}y_u-y_u\ell_*/2}(1+1/n_*)^{y_u}
                       e^{k_*y_u\log(n_*+1)}.
\end{aligned}
$$

If $N_c$ is the center cutoff, the holomorphic remainder
$H_t/B_t-f^{[N_c]}$ is bounded on the entire disk by
$3\cdot10^{-9}+\sup E_c+C_1(1+C_2)$. Its $j$th derivative at the
center is bounded by $j!r^{-j}$ times this disk bound, for $j=1,2$.

*Proof.* Two points in the disk differ in $x$ by at most $1/2$, so their
cutoffs differ by at most one. At a point of actual cutoff $m$, the changed
index is $n=m$ or $m+1$. Then
$\mathcal Q\ge m^2e^{\ell_*}$,
$0\le\log n-\log m\le1/m$, and

$$
\log^2n-2\log m\log n
 \le-\log^2m+2\log(m+1)/m.
$$

Combining the negative coefficient of $\log n$ with $c_*$ before taking
endpoints gives $C_1$. Equation (A.3), $n/m\le1+1/m$, and the decreasing
function $\log(m+1)/(4\pi m^2-\pi t_m/4-6)$ give $C_2$ for the second
branch. The other combined factors decrease in $m$. Both branches are
included. Cauchy's theorem applies to the fixed-$N_c$ holomorphic remainder,
not to the discontinuous actual-cutoff formula. At $t=0$ (A.1) already
holds on the full disk, so the same Cauchy argument applies. $\square$

Replacing $10^{-11}$ by $1/50$ in $C_2$ is a permissible larger bound used
in the late-boundary evaluator. For time boxes, replace the negative $t$
exponent by the left time endpoint and the other positive quantities by
their upper endpoints. The source error itself uses the disk's smallest
$y$ in its negative power and its largest $y$ in $3^y+3^{-y}$.

**Lemma A.4 (top and head-center bounds).** For $x\ge X_L$ and
$0\le t\le1/5$, $H_t(x+5i)\ne0$ and $S(x,5,t)>6.59$. For
$X_e+1\le x\le X$, also $|H_t'/H_t(x+5i)|<10$. Finally, for
$x\ge X_L$ and $0\le t\le1/5$,

$$
J(x,5,t)<0.309518<8/25.                              \tag{A.11}
$$

*Proof.* Lemma A.3 with $Y=5,r=1/4,n_*=N_e$ gives a full disk error less
than $10^{-8}$ and a center derivative error less than $10^{-7}$.
At height $5$, combine the heat exponents to obtain ordinary weights
$n^{-\rho}$, $\rho=3-t_m/X_e^2>2$. The first sum differs from $1$ by at
most $\zeta(\rho)-1$, and its derivative has modulus at most
$r_1(-\zeta'(\rho))$, $r_1=500001/10^6$.
Retaining $(n/N)^y$ in the reflected sum bounds its value and derivative by
$1.01N_e^{1-\rho}<10^{-11}$ and
$1.01N_e^{1-\rho}(2\log(N_e+1)+1)<10^{-9}$.
The power-log expression decreases for $N\ge N_e$; no unbounded logarithm
has been replaced by a finite endpoint without its decaying factor.

For $F=H_t/B_t$ this proves

$$
\begin{aligned}
|F|&\ge m=2-\zeta(\rho)-10^{-11}-10^{-8}>0.79,\\
|F'/F|&\le K_3=
 \frac{r_1(-\zeta'(\rho))+10^{-9}+10^{-7}}m<0.124148480.
\end{aligned}
$$

The archimedean density loss is less than $10^{-10}$. Thus
$S(x,5,t)\ge\frac14\log(X_L/(4\pi))-10^{-10}-K_3
>6.598763368>6.59$.
Taking the modulus of $B'/B$ on the finite slab gives
$|u|<6.858519782<10$ there.

For (A.11), use the outer radius-one disk about $x+5i$, with heights in
$[4,6]$. At each point use an inner source disk of radius $1/4$, lying in
$[15/4,25/4]\subset[0,7]$. The same calculation with
$\rho=5/2-t_m/X_e^2$ bounds $|F'/F|$ on the outer disk by
$K_2<0.294104432$. This is a holomorphic function there: $H_t$ has no zeros
at these heights, and $B_t$ is nonzero. Cauchy gives
$|(F'/F)'(x+5i)|\le K_2$. Direct differentiation of $\beta$ gives
archimedean errors $e_1,e_2<10^{-10}$ for $u$ and $u_z$, respectively.
Consequently $J\le K_2+e_2+(K_3+e_1)^2<0.309518$.
All the stated numerical inequalities are reproduced by `check_h7.py` and
`check_fixed_c.py`. $\square$

Two distinct uniformity assertions are needed in the comparison proofs.
For a compact positive-time interval and a compact $y$-band in $(0,7)$,
combine the heat factors using
$\log N\le L/2+O(1/\mathcal Q)$. Each finite sum is bounded by an ordinary
power majorant whose exponent tends to infinity with $\log x$.
The first sum tends to $1$, the reflected contribution tends to $0$, and
the actual $x$-dependent error in (A.1) tends to $0$. On slightly larger
disks this proves $H_t/B_t\to1$, with two Cauchy derivatives, uniformly.
Thus

$$
S(x,y,t)\to\infty,\qquad J(x,y,t)\to0                 \tag{A.12}
$$

uniformly on these positive-time bands.

At the corner $t\downarrow0$, $x\to\infty$, use a compact band strictly
above $y=1$ instead. On slightly larger disks choose a fixed
$\sigma_*>1$ below all real parts of $w$. Combining the finite heat
exponents gives

$$
|P_N(s_B,t)-\zeta(s_B)|
 \le\frac t4\sum_{n\ge1}\log^2n\,n^{-\sigma_*}
       +\sum_{n>N}n^{-\sigma_*}.                     \tag{A.13}
$$

If necessary choose two fixed exponents between $1$ and the smallest
$\Re w$ to absorb the vanishing archimedean errors. The reflected term and
the remainder tend uniformly to zero. Both sides of the resulting
difference $H_t/B_t-\zeta(s_B)=O(t)+o(1)$ are holomorphic, so Cauchy twice
gives the same conclusion for their derivatives. The Euler product bounds
$\zeta(s_B)$ uniformly away from zero. Since
$s_{B,z}=-i/2+o(1)$ and $s_{B,zz}=o(1)$, it follows that

$$
S=\tfrac14\log(x/(4\pi))+O(1),\qquad
\limsup_{t\downarrow0,\ x\to\infty}J(x,y,t)
 \le\frac{\zeta''((1+y)/2)}{4\zeta((1+y)/2)}.          \tag{A.14}
$$

For the sharp constant in (A.14), put $q=\zeta'/\zeta$ and
$W(\sigma)=-q(\sigma)$. The Euler logarithm gives
$|q(s)|\le W(\sigma)$ and $|q'(s)|\le q'(\sigma)$ when $\Re s\ge\sigma>1$;
hence $(|q'(s)|+|q(s)|^2)/4\le\zeta''(\sigma)/(4\zeta(\sigma))$.
Use $\Re s_B\ge(1+y)/2-o(1)$ and continuity to obtain the displayed limsup.
It is uniform on the compact band. The argument allows
$t\log x$ to be unbounded; it does not replace $\zeta(s_B)$ by
$\zeta(w)$. For zero contacts themselves, independently of (A.12),
[Po19, Theorem 1.5(i)] supplies a uniform finite horizontal confinement on
each compact positive-time interval. An initial strict strip cushion will
keep this theorem from being used at $t=0$.

## A.4. The coupled density and strip comparison

Let $q_M$ be the continuous affine function defined by the 1620 exact rows
of `certificate/data/old-M3a-wall.json`. Its initial value is
$h_0^2$, $h_0=1000001/10^6$, its terminal value is $1/400$, and its horizon is

$$
T_M=\frac{10724023263453313712965415492196719802951}
          {66207211195936838001560220771250000000000}.
$$

Write $h_M(t)=\sqrt{q_M(t)}$, and define

$$
\begin{aligned}
U(Y,t)&=10^9+\sum_{j=1}^3a_je^{\lambda_j^2t}\cosh(\lambda_jY),\\
(a_1,a_2,a_3)&=(1758974,2464729,302096),\qquad
(\lambda_1,\lambda_2,\lambda_3)=(19/4,97/20,131/20),\\
f_0&=U_Y/U,\qquad \delta(t)=e^{90t}/10^{14},\qquad f=f_0-\delta.
\end{aligned} \tag{A.15}
$$

**Theorem A.5 (density and intermediate strip).** For every
$0\le t\le T_M$, all zeros of $H_t$ lie in $|\Im z|\le h_M(t)$.
For every $x\ge X$ and $h_M(t)<Y\le5$, $H_t(x+iY)\ne0$ and

$$
S(x,Y,t)\ge f(Y,t).                                  \tag{A.16}
$$

We prove these two assertions simultaneously. The finite-head theorem P2,
the initial critical strip, and the classical zero dynamics of the main
text are inputs. No later jet estimate or later reference barrier is used.

First, $U_t=U_{YY}$, so
$f_{0,t}=f_{0,YY}+2f_0f_{0,Y}$. Expanding the coshes into positive
exponentials makes $f_{0,Y}$ the variance of the slopes
$0,\pm\lambda_1,\pm\lambda_2,\pm\lambda_3$ under their normalized
positive weights. Consequently

$$
0<f_{0,Y}\le\lambda_{\max}^2=17161/400,\quad
0<f_0<\lambda_{\max}=131/20 \quad(Y>0),
$$

and

$$
f_{YY}+2ff_Y-f_t=(90-2f_{0,Y})\delta
 \ge(839/200)\delta>0.                              \tag{A.17}
$$

At fixed $Y>0$, group the positive cosh weights by their nonnegative
frequency, including a constant mode at frequency zero. Then
$f_0$ is the weighted mean of
$m(\lambda)=\lambda\tanh(\lambda Y)$ and

$$
\partial_t f_0=
\frac12\sum_{j,k}w_jw_k
 [m(\lambda_j)-m(\lambda_k)](\lambda_j^2-\lambda_k^2)\ge0.         \tag{A.18}
$$

Both functions in the covariance increase with $\lambda\ge0$.
It is $f_0$, rather than the subtracted function $f$, whose time
monotonicity is used in all row bounds. The scalar check gives
$\delta(T_M)<2.144\cdot10^{-8}<10^{-5}$.

For the initial density, (A.6), Cauchy on a unit $w$-disk, and the absolutely
convergent Euler series give, for $x\ge X_L$, $1<Y\le5$,

$$
S(x,Y,0)\ge\frac14\log\frac{x}{4\pi}
 +\frac{\zeta'((1+Y)/2)}{2\zeta((1+Y)/2)}
 -\frac1{x^2}-\frac1{6x-36}>E(Y),                    \tag{A.19}
$$

where
$E(Y)=\frac14\log(X_L/(4\pi))-10^{-6}
       +\zeta'((1+Y)/2)/(2\zeta((1+Y)/2))$.
The last two errors in (A.19) are less than $2.779\cdot10^{-14}$.
The function $E$ increases, since its derivative is
$\frac14\sum_{n\ge1}\Lambda(n)\log n\,n^{-(1+Y)/2}>0$.

An additional kernel comparison is useful close to $Y=1$. For $1<u<v$
and $0\le b\le1$, clearing denominators in
$K_u(d,b)/u-K_v(d,b)/v$ leaves a positive factor times

$$
(v^2-u^2)\{D^2+(u^2+v^2-6b^2)D+(u^2-b^2)(v^2-b^2)\},
\quad D=d^2.
$$

The expression in braces decreases with $b^2\in[0,1]$. At $b=1$ it is
nonnegative for all $D\ge0$ precisely when

$$
u^2+v^2-6\ge0\quad\hbox{or}\quad
4(u^2-1)(v^2-1)\ge(u^2+v^2-6)^2.                    \tag{A.20}
$$

If (A.20) holds and $E(v)>0$, summing the absolutely convergent paired
zero kernels gives $S(x,u,0)>(u/v)E(v)$. Admissibility persists as $u$
increases toward $v$, because the brace has positive derivative with respect
to $u^2$.

`check_m3a.py` reconstructs the 855 dyadic leaves of $[h_0,5]$ in
`support/fields/data/m3a-initial.json`, and checks their exact adjacency.
On 851 leaves $[l,r]$ it verifies $E(l)-f_0(r,0)>10^{-7}$.
On the other four, it verifies (A.20) at $u=l$, $v\ge r$, $E(v)>0$,
and $(l/v)E(v)-f_0(r,0)>10^{-7}$.
Their reference heights are $447/200$, $179/100$, $1601/1000$, and $193/125$.
Monotonicity then proves the strict initial bound on every point of every
leaf. The smallest computed gap is greater than $4.7661468\cdot10^{-7}$.

The moving bottom has a separate, exact nonlocal inequality. Put
$A_j=a_je^{\lambda_j^2t}$, $r_j=\sinh(\lambda_jh)/(\lambda_jh)$ and

$$
V=\sum_jA_j\cosh(\lambda_jh),\quad
W=\sum_jA_j\lambda_j^2r_j,\quad
D=\sum_jA_j\lambda_j^4r_j^3,\quad
E_*=\sum_jA_j\lambda_j^2\cosh(\lambda_jh)r_j^2.
$$

Triple-angle identities give

$$
\frac{f_0(3h,t)}3-f_0(h,t)
 =\frac{4h^3[D(10^9+V)-3WE_*]}{3U(3h,t)U(h,t)}.       \tag{A.21}
$$

Each of $D,V,W,E_*$ increases with both $t$ and $h>0$.
For $r_j$ this follows from
$v\cosh v-\sinh v>0$, whose derivative is $v\sinh v$.
On a decreasing row $[t_l,t_r]$ with endpoint squares $q_l>q_r$, a lower
bound for the numerator factor in (A.21) is therefore

$$
D(t_l,\sqrt{q_r})[10^9+V(t_l,\sqrt{q_r})]
 -3W(t_r,\sqrt{q_l})E_*(t_r,\sqrt{q_l}).               \tag{A.22}
$$

The checker verifies positivity on all 1620 rows, with minimum greater than
$3.4851\cdot10^{19}$, and verifies $3h_M\le5$.
This rectangle estimate does not require the difference in (A.21) itself
to be monotone. Subtracting $\delta$ adds $2\delta/3$ to (A.21), giving
$f(3h_M,t)/3>f(h_M,t)$.

The spatial boundary is supplied by the finite-head theorem. If
$|x|\le X-1$ and $Y>0$, every nonreal zero has horizontal distance at least
$1$ from $x$. Its paired kernel is

$$
K_Y(d,b)=\frac{2Y(d^2+Y^2-b^2)}
 {[d^2+(Y-b)^2][d^2+(Y+b)^2]}>0
$$

because $|b|\le1$. Real-root contributions are positive as well.
Thus $p=iH'/H$ is holomorphic with positive real part in the radius-five
disk centered at $x+5i$ when $X_e+6\le x\le X-6$.
The Cayley transform and Schwarz's lemma give

$$
|\Re u(x+iY)|\le|\Re u(x+5i)|+(10/Y-1)S(x,5,t)<2000
\quad(1/20\le Y\le5),                               \tag{A.23}
$$

using Lemma A.4. We use the looser constant $M=20000$.
Choose a smooth nondecreasing $\chi$, zero on $(-\infty,0]$ and one on
$[1,\infty)$, and set

$$
g(x,t)=10e^{86t}\chi\!\left(\frac{X-100000+40000t-x}{900000}\right),
\qquad F=f-g.                                       \tag{A.24}
$$

Then $g=0$ for $x\ge X$ and $g\ge10$ at $x=X_L$.
The transition lies in $[X_L,X-92000]\subset[X_e+6,X-6]$ for
$t\le1/5$. There $g_x\le0$ and $g_t=86g+40000|g_x|$.

On a zero-free region write $u=A-iS$. The heat equation and the
Cauchy--Riemann equations give the exact vertical equation

$$
S_t=S_{YY}-2A S_x+2S S_Y.                            \tag{A.25}
$$

Equations (A.17), (A.23), and $86-2\lambda_{\max}^2=39/200$ imply

$$
F_{YY}-2AF_x+2FF_Y-F_t
 \ge(839/200)\delta+(39/200)g+(40000-2M)|g_x|>0.       \tag{A.26}
$$

Where $g_x=0$ no bound on $A$ is needed. At the left boundary $F<0<S$;
at the top $F<f_0<6.55<6.59<S$. The initial comparison follows from
(A.19)--(A.20). At the bottom,
$F(3h_M,t)/3-F(h_M,t)>0$ by (A.21) and $2g/3\ge0$.

Suppose a first failure of the strip or the density bound occurs.
Initially $h_0>1$, and by continuity $h_M>1+\eta$ for some positive
initial time interval. The first formula in (A.14) excludes density
contacts escaping to infinity on that interval; its compact complement is
handled by the strict initial margin. Equation (A.12) excludes later
density escape. The initial strip cushion and [Po19, Theorem 1.5(i)]
exclude height contacts escaping to infinity. Thus any first contact occurs
at a finite point and a positive time.

Until that time all roots stay in the closed $h_M$ strip. For
$h_M<Y\le3h_M/\sqrt5$, the unsigned kernel inequality in the main text
gives
$S(x,Y,t)\ge(Y/(3h_M))S(x,3h_M,t)$.
Taking a lower limit, also as $x,t$ vary, gives

$$
\liminf_{Y\downarrow h_M}(S-F)
 \ge F(x,3h_M,t)/3-F(x,h_M,t)>0.                     \tag{A.27}
$$

The reference $3h_M$ stays outside the root strip. Thus (A.27) excludes
bottom contacts even at a possible pole, without asserting an infinite
liminf along every approach to that pole. At an interior density contact,
$S_x=F_x$, $S_Y=F_Y$, and $S_{YY}\ge F_{YY}$.
Equations (A.25)--(A.26) give $(S-F)_t>0$, contradicting first contact
from positive values. No horizontal diffusion term is assumed.

A first height contact is outside $|x|\le X$ by P2; symmetry puts it at
$x>X$, where $g=0$. For every exact row the checker verifies

$$
\begin{gathered}
0<t_r-t_l\le10^{-4},\quad 1/400\le q_r<q_l,\quad
0<p\le5,\quad p^2\ge5q_l,\\
s<f_0(p,t_l)-10^{-5},\qquad
k=4s/p-8/(p^2-q_l)>0,\qquad
\frac{q_l-q_r}{t_r-t_l}\le2+kq_r.                    \tag{A.28}
\end{gathered}
$$

By (A.18), $S(x,p,t)\ge f_0(p,t)-\delta(t)>s$ throughout the closed row.
At a simple highest zero the unsigned force law in the main text therefore
gives
$(h^2)'<-2-kq_M(t)\le-2-kq_r\le q_M'$.
This contradicts first contact. A multiple contact is excluded by backward
Hermite splitting: an earlier zero has imaginary part greater by a positive
multiple of $\sqrt\varepsilon$, while $h_M$ changes by $O(\varepsilon)$.
At a time knot use the preceding row and the left derivative.
Simultaneous contacts need only the non-strict other bound at the first time,
so both strict contradictions remain valid. In fact the argument proves
$S(x,Y,t)\ge f(Y,t)-g(x,t)$ on the larger domain
$x\ge X_L$, $h_M(t)<Y\le5$, at every time in $[0,T_M]$.
Its restriction to $x\ge X$, where $g=0$, is Theorem A.5. This larger
intermediate density field is the spatial estimate used in A.5.

## A.5. The fixed jet supersolution

Define

$$
\Omega(x)=\frac14\log\frac{x}{4\pi},\quad c=-\pi/8,\quad
J=|u_z|+|u-c+i\Omega|^2,\quad
b(t)=h_M(t)+3/5,
$$

and

$$
C(Y,t)=e^{\kappa t}\left[\frac8{25}+\frac{A_*}{U(Y,t)}\right],
\qquad \kappa=10^{-5},\quad A_*=1130000000000.         \tag{A.29}
$$

**Theorem A.6 (jet bound).** For every $x\ge X$, $0\le t\le T_M$,
and $b(t)\le Y\le5$,

$$
J(x,Y,t)\le C(Y,t).                                  \tag{A.30}
$$

The band is separated by $3/5$ from every zero, by Theorem A.5.
Its lower-boundary input is the estimate

$$
J(x,b(t),t)<C(b(t),t)\quad(x\ge X_L, 0\le t\le T_M), \tag{A.31}
$$

which is proved directly in A.6--A.7 below. We first prove that this input
implies (A.30), keeping every other boundary and the unbounded-domain issue.

Put $u=A-iS$, $V=-u_z=R+iP$, and
$\mathcal L=\partial_t-\partial_{YY}+2A\partial_x-2S\partial_Y$.
Direct differentiation of the heat equation gives
$\mathcal Lu=0$, $\mathcal LV=2V^2$.
With $a=A-c$, $d=S-\Omega$, define the smooth symmetric matrix

$$
\mathcal M=(a^2+d^2)I+
 \begin{pmatrix}R&P\\P&-R\end{pmatrix}.
$$

Its largest eigenvalue is $J$. The product rule, including
$\Omega'=1/(4x)$, gives

$$
\mathcal L(a^2+d^2)=-2(R^2+P^2)-Ad/x,\qquad
\mathcal L\mathcal M
 =-4\begin{pmatrix}P\\-R\end{pmatrix}
      \begin{pmatrix}P&-R\end{pmatrix}-(Ad/x)I.        \tag{A.32}
$$

At a prospective upper contact $J=D>0$, take a unit eigenvector at that
point and then hold it constant locally. The smooth scalar
$\varphi=v^T\mathcal Mv$ is everywhere at most $J$, equals $J$ at contact,
and satisfies

$$
\mathcal L\varphi\le-Ad/x
 \le E(D):=\frac{\sqrt D(\pi/8+\sqrt D)}{X_L}.        \tag{A.33}
$$

The inequalities $|A-c|\le\sqrt D$ and $|d|\le\sqrt D$ justify the last
step. This argument also covers $u_z=0$ and a repeated eigenvalue. It does
not differentiate an eigenvector or the nonsmooth function $|u_z|$.

Since $A_*/U$ satisfies
$v_t=v_{YY}+2f_0v_Y$, (A.29) gives

$$
C_t-C_{YY}-2fC_Y=\kappa C+2\delta C_Y,\qquad
C_Y\le0,\quad |C_Y|\le\lambda_{\max}C,\quad C\ge8/25.
$$

Thus its relative supersolution margin over (A.33) is at least

$$
\kappa-2\lambda_{\max}\delta(T_M)
 -\frac{1+\pi/(8\sqrt{8/25})}{X_L}>9.7192\cdot10^{-6}.
                                                               \tag{A.34}
$$

The exact source term in (A.32) is retained; the center $c-i\Omega(x)$
is not a constant holomorphic function.

At $t=0$ and $1<Y\le7$, write $G=\zeta'/\zeta(w)$.
Use (A.6) on a $w$-disk of radius $x/4$; its gamma argument has imaginary
part at least $x/8$. Define

$$
R_\Gamma(x)=\frac1{12(x/8-1)},\quad
e_u=\frac4{x-20}+\frac{2R_\Gamma(x)}x,\quad
e_V=\frac{1/x+6/x^2}{4}+\frac{8R_\Gamma(x)}{x^2}.
$$

Equations (A.2), (A.6), and Cauchy give
$|u-(c-i\Omega)|\le|G|/2+e_u$ and
$|u_z|\le|G'|/4+e_V$. For real $\sigma=(1+Y)/2>1$, put
$W=-\zeta'(\sigma)/\zeta(\sigma)$.
The absolutely convergent Euler logarithm yields

$$
J(x,Y,0)\le C_{\rm in}(Y)
 :=\frac{\zeta''(\sigma)}{4\zeta(\sigma)}
       +e_V+We_u+e_u^2,                              \tag{A.35}
$$

using the decreasing error terms at $x=X_L$.
Indeed $|G|\le W$, $|G'|\le(\log\zeta)''(\sigma)$ and
$(\log\zeta)''+W^2=\zeta''/\zeta$.
Both $W$ and $\zeta''/\zeta$ decrease with $\sigma$; for the latter,
differentiate the expectation of $\log^2n$ under weights
$n^{-\sigma}/\zeta(\sigma)$ to get
$-\operatorname{Cov}(\log^2n,\log n)\le0$.

The fixed-C checker divides $[b(0),3]$ into 400 equal exact rational cells
$[l,r]$ and verifies
$[C_{\rm in}(l)-8/25]_+U(r,0)<A_*$ on each.
The maximum is less than $1128379860282.031<A_*$.
For $3\le Y\le5$, $C_{\rm in}(Y)\le C_{\rm in}(3)<0.302335<8/25$.
This proves a uniform strict initial margin on the entire required band.
Only the finite range $1<Y\le7$ is asserted in (A.35).
Lemma A.4 gives the strict top margin.

For the left boundary, Schwarz--Pick in the same positive-real-part disk
used for (A.23) gives

$$
|u(x+iY)|<100/Y,\qquad
|u_z(x+iY)|\le\frac{10S(x,Y,t)}{Y(10-Y)}
             <100/Y^2.
$$

Since $Y\ge b(t)\ge13/20$ and $|c-i\Omega(X_L)|<7$,
$J(X_L,Y,t)<4412281/169<30000$.
Let $G_*=10^6g$, with $g$ from (A.24), and use the full spatial
supersolution $D=C+G_*$. Then $D=C$ for $x\ge X$ and
$G_*(X_L,t)\ge10^7$.
Throughout the transition $\mathcal LG_*\ge86\cdot10^6g$.
The actual density estimate there is $S\ge f-g$, so

$$
\mathcal LC\ge C_t-C_{YY}-2fC_Y-2g|C_Y|.
$$

The checker bounds $C<103.119<10^6$ on the entire band, using the
opposite time/height corners of every $q_M$ row. Also
$E(C+G_*)-E(C)\le L_EG_*$, where
$L_E=[1+\pi/(16\sqrt{8/25})]/X_L$.
The strict inequality
$(86-L_E)10^6>2\lambda_{\max}10^6$ therefore proves
$\mathcal LD>E(D)$, with the positive margin from (A.34).
All spatial derivative terms are included. Outside the transition $g_x=0$,
so no bound on $\Re u$ is needed there.

Finally, (A.14) and the strict initial margin (A.35) exclude a first upper
contact escaping through $t=0,x=\infty$. By continuity the margin persists
on a small neighborhood below $b(0)>1$, which contains the short-time
moving band. Compact $x$ is handled by ordinary joint continuity.
For times bounded away from zero, (A.12) and $D\ge8/25$ exclude escape
to infinity. Hence a first contact, if present, is finite and at positive
time. Initial, left, top, and bottom contacts are excluded by the strict
bounds already established, including (A.31).
At an interior contact the fixed-eigenvector scalar from (A.32) satisfies
$\varphi-D\le0$, equals zero, has vanishing spatial first derivatives,
and has nonpositive $Y$ second derivative. First contact from below gives
its time derivative a nonnegative left limit. Thus
$\mathcal L(\varphi-D)\ge0$, contrary to (A.33) and
$\mathcal LD>E(D)$. At a knot of $b$ use the preceding closed interval;
$C$ itself is smooth. This proves Theorem A.6 once (A.31) is supplied.

## A.6. The early boundary: a relative Euler expansion

The 162 exact boundary rectangles are defined by $t_i=i/1000$ for
$0\le i\le161$, $t_{162}=T_M$, and

$$
y_i^-=\frac35+10^{-6}\lfloor10^6h_M(t_{i+1})\rfloor,\qquad
y_i^+=\frac35+10^{-6}\lceil10^6h_M(t_i)\rceil.          \tag{A.36}
$$

Then $b(t)\in[y_i^-,y_i^+]$ on $[t_i,t_{i+1}]$. The fixed-C checker
reconstructs these square inequalities, their rounding intervals, every
$q_M$ interpolation, and the exact time cover from the local geometry
file. It also checks that all physical radius-$1/4$ disks and source
radius-$3/20$ disks stay in $x>X_e$, $0<y<5/2$, with cutoff at least $N_0$.

For boxes $0,\ldots,44$, the center heights lie in
$[1353931/10^6,1600001/10^6]$, so every radius-$3/20$ source disk centered
in the center rectangle stays above $y=1$.
This direct method does not use source disks centered on an additional
radius-$1/4$ circle. The resulting closed time interval
includes $t=0$ and $t=9/200$.
For one box $[t_l,t_r]\times[y_l,y_r]$, put

$$
\begin{aligned}
\ell_0&=\log N_0,& e_0&=\log(1-t_m/(16N_0^2)),\\
c_*&=-t_me_0/4,& d_*&=t_m/X_e^2,\\
c_y&=(1+y)/2-c_*-d_*,&
c_0&=c_{y_l},\qquad a=c_0+t_l\ell_0/2 .
\end{aligned}
$$

The cutoff relation and (A.2) give

$$
\Re s_B\ge c_y+(t/2)\log N\ge a>1.                    \tag{A.37}
$$

The small errors remain inside exponents when $\log N$ is unbounded.
Let

$$
\begin{aligned}
A_0&=\tfrac12\sqrt{\log^2(X_e/(4\pi))+\pi^2/4}+8/(X_e-20),\\
A_1&=1/(X_e-6),\quad A_2=2/X_e^2+24/X_e^3,\\
r_1&=500001/10^6,\quad r_2=t_mA_2/8,\\
D_\beta&=8/(X_e-20)+(t_m/2)A_0A_1,\\
B_\beta&=A_1+(t_m/2)(A_1^2+A_0A_2),\quad
\epsilon_1=D_\beta/2,\quad\epsilon_2=B_\beta/4 .
\end{aligned}
$$

These bound $|s_{B,z}|$, $|s_{B,zz}|$, $|B'/B+\pi/8+i\Omega|$,
and $|(\log B)''|$ by $r_1,r_2,\epsilon_1,\epsilon_2$, respectively.
Every product containing $A_0(x)$ decreases after combination with its
inverse powers: $xZ'(x)\le1$, $Z(x)>1$, so $Z(x)/(x-d)^k$ decreases for
$d=6,20,40$ and $k\ge1$. The same argument controls
$\frac12\log(x/(4\pi)+t_m/16)$ times these inverse powers.
The growing logarithm by itself is never bounded at $X_e$.

For a locally fixed actual cutoff, the identity

$$
\begin{aligned}
P_N(s_B,t)&=\zeta(s_B)+(t/4)\zeta''(s_B)+R_H-T_N,\\
R_H&=\sum_{n\le N}[e^{t\log^2n/4}-1-t\log^2n/4]n^{-s_B},\\
T_N&=\sum_{n>N}[1+(t/4)\log^2n]n^{-s_B}
\end{aligned}                                                   \tag{A.38}
$$

is exact. The heated sums are finite; the infinite sum is ordinary and
absolutely convergent. Write

$$
H_t/B_t=\zeta(s_B)(1+\rho),\qquad
\rho=\frac t4\frac{\zeta''}{\zeta}(s_B)
 +\frac{R_H-T_N+\gamma P_N(s_A,t)+E_N}{\zeta(s_B)},     \tag{A.39}
$$

where $E_N=H_t/B_t-f^{[N]}$ is holomorphic for this fixed cutoff.
We now bound the three raw jets of the remainder numerator.

For $j=0,1,2$, let $H_j$ bound the positive sum

$$
\sum_{n\ge2}\log^jn\,n^{-c_0}
 \exp\!\left[t_l\left(\frac{\log^2n}{4}
       -\frac{\log n\,\max(\ell_0,\log n)}2\right)\right]
 h(t_r\log^2n/4),\quad h(v)=1-(1+v)e^{-v}.            \tag{A.40}
$$

Here $h\ge0$ increases and $h'/h\le2/v$, since
$h(v)=\int_0^v r e^{-r}\,dr\ge v^2e^{-v}/2$.
For $n\le N$, combine the heat factors with (A.37) and use
$\log N\ge\max(\ell_0,\log n)$ before extending the majorant to all $n$.
The combined heat exponent is nonpositive, so its time is lowered to
$t_l$; the increasing $h$ is bounded at $t_r$.
The logarithmic derivative of the resulting summand is at most
$-c_0+(j+4)/\log n$.
The gate $c_0>6/\log1024$ makes it decreasing beyond $1024$.

The checker sums $2\le n\le1024$ and bounds the rest by an integral.
In log coordinates,
$\mathcal E(v)=\exp[-(c_0-1)v+t_l(v^2/4-v\max(\ell_0,v)/2)]$
decreases, while $v^jh(t_rv^2/4)$ increases.
On 1024 intervals with exact symbolic endpoints
$v_k=\log1024+k/16$ use their left exponential and right polynomial/$h$
factors. The remaining tail from $V=\log1024+64>\ell_0$ is at most

$$
\mathcal E(V)\sum_{k=0}^j
 \binom jk\frac{V^{j-k}k!}{(c_0-1+t_lV/2)^{k+1}}.      \tag{A.41}
$$

This follows from
$\mathcal E(V+w)\le\mathcal E(V)e^{-(c_0-1+t_lV/2)w}$
and $h\le1$. Every rate is checked positive, including the $t_l=0$ box.

The ordinary tails use

$$
I_j=N_0^{1-a}\sum_{k=0}^j
 \frac{j!}{(j-k)!}\frac{\ell_0^{j-k}}{(a-1)^{k+1}},
\qquad T_j=I_j+(t_r/4)I_{j+2}\quad(j=0,1,2).          \tag{A.42}
$$

Here $I_j=\int_{N_0}^\infty u^{-a}\log^ju\,du$.
The gate $a>4/\ell_0$ proves the decreasing sum-integral comparison for
every moment through degree four and every actual $N\ge N_0$.

For the reflected term put

$$
K=\frac{t_m}{2(4\pi N_0^2-\pi t_m/4-6)},\quad
\Delta=10^{-11}-e_0/2,\quad
b=c_0-y_l-Ky_l,\quad e=b+y_l,\quad a_0=1-b.
$$

After combining gamma and polynomial factors, the coefficient of $y$ is
$\Delta-\log N+(1/2+K)\log n<0$, by a gate at $N_0$.
Its maximum therefore occurs at $y_l$.
For $L_N=\log N$, the remaining summand
$g(u)=\exp[-(b+t_lL_N/2)\log u+t_l\log^2u/4]$ has a single valley.
Thus $\sum_{n\le N}g(n)\le1+\int_1^Ng(u)\,du+g(N)$.
After multiplication by $e^{-y_lL_N}$, its integral is

$$
\mathcal A(L_N)=e^{-y_lL_N}
 \int_0^{L_N}e^{(a_0-t_lL_N/2)v+t_lv^2/4}\,dv,        \tag{A.43}
$$

and its endpoints are $e^{-y_lL_N}$ and $e^{-eL_N-t_lL_N^2/4}$.
The first and second raw phase multipliers are bounded by
$L_N+\beta_0$ and $\tau_2$, where $\beta_0=1/1000$, $\tau_2=10^{-10}$.
Differentiate $\log\gamma-s_A\log n$ directly; the leading opposite
imaginary phases in $\alpha(v)+\alpha(w)$ cancel. The residual bounds are

$$
1/N_0+D_\beta+\frac{t_m\ell_0}{4(X_e-6)}<\beta_0,\qquad
B_\beta/2+r_2\ell_0<\tau_2.                          \tag{A.44}
$$

The inverse-power/logarithm monotonicities already stated extend these
to every $x,N$. This calculation is for the raw reflected sum.

The square phase weight also has an all-$N$ reduction. Set
$K_0=(1-e^{-a_0\ell_0})/a_0$. The checker verifies

$$
a_0>0,\qquad(y_l-2/(\ell_0+\beta_0))K_0>1,\qquad
e(\ell_0+\beta_0)>2.                                 \tag{A.45}
$$

If $\mathcal B$ is the upper-endpoint integrand in (A.43), then
$\mathcal A'\le-y_l\mathcal A+\mathcal B$ and
$\mathcal A/\mathcal B\ge\int_0^{L_N}e^{-a_0w}\,dw\ge K_0$.
The latter follows from the exact exponent difference
$-a_0w+t_lw^2/4$ at $v=L_N-w$.
Thus $(L_N+\beta_0)^2\mathcal A(L_N)$ decreases for $L_N\ge\ell_0$.
The two endpoint terms with this weight decrease by (A.45) too.
At $L_N=\ell_0$, the integrand increases because
$1-b-t_l\ell_0/2>0$, another checked gate. Use 1024 right-endpoint
rectangles there. If $A_R$ is this full reflected magnitude bound,
including both endpoints and $e^{\Delta y_l}$, its first two derivatives
are bounded by $(\ell_0+\beta_0)A_R$ and
$[(\ell_0+\beta_0)^2+\tau_2]A_R$.

Lemma A.3 on the full radius $r=3/20$ disk gives $E_0,E_1,E_2$,
where $E_0$ is the point error, $E_1=E_D/r$ and $E_2=2E_D/r^2$.
The second derivative factorial is retained.
Positive source factors may use $N_e$ in place of $N_0$; the cutoff
corrections themselves use $N_0$.
The raw remainder jets in (A.39) are therefore bounded by

$$
\begin{aligned}
R_0&=H_0+T_0+A_R+E_0,\\
R_1&=r_1(H_1+T_1)+(\ell_0+\beta_0)A_R+E_1,\\
R_2&=r_1^2(H_2+T_2)+r_2(H_1+T_1)
       +[(\ell_0+\beta_0)^2+\tau_2]A_R+E_2.
\end{aligned} \tag{A.46}
$$

Here $H_j$ is the moment (A.40), not the heat-flow function.
For $W_j(a)=\sum_{n\ge1}\Lambda(n)\log^jn\,n^{-a}$, put

$$
Z_0=W_1+W_0^2,\quad Z_1=W_2+2W_0W_1,\quad
Z_2=W_3+2W_1^2+2W_0W_2,\quad m_\zeta=\zeta(2a)/\zeta(a).
$$

The Euler product gives $|\zeta(s)|\ge m_\zeta$ for $\Re s\ge a$;
the $Z_j$ bound the first three $s$-jets of $\zeta''/\zeta$.
Product and quotient differentiation in (A.39) give

$$
\begin{aligned}
p_0&=t_rZ_0/4+R_0/m_\zeta,\\
p_1&=t_rr_1Z_1/4+(R_1+r_1W_0R_0)/m_\zeta,\\
p_2&=t_r(r_1^2Z_2+r_2Z_1)/4\\
&\quad+[R_2+2r_1W_0R_1+
       \{r_1^2(W_0^2+W_1)+r_2W_0\}R_0]/m_\zeta .
\end{aligned}                                                   \tag{A.47}
$$

Thus $|\rho^{(j)}|\le p_j$. With $d=1-p_0>0$, put
$g_1=r_1W_0+p_1/d$ and
$g_2=r_1^2W_1+r_2W_0+p_2/d+(p_1/d)^2$.
Then $H_t\ne0$ and

$$
J\le\epsilon_2+g_2+(\epsilon_1+g_1)^2.                \tag{A.48}
$$

The checker computes the $W_j$ from the Taylor series of $\log\zeta(a+u)$
with the exact coefficient factorials. For every box it verifies $d>0$
and compares (A.48) with

$$
C_i^-=e^{t_i/100000}
 \left[8/25+A_*/U(y_i^+,t_{i+1})\right].              \tag{A.49}
$$

Monotonicity of $U$ in time and positive height gives $C(Y,t)\ge C_i^-$
on the whole rectangle. The program check_early_boundary.py verifies all
45 strict gates, with minimum margin greater than $17.07745$.
This proves (A.31) on $[0,9/200]$ for every $x\ge X_L$ and actual cutoff.

## A.7. The late boundary: mollified derivative bounds

For boxes $45,\ldots,161$ define the cutoff-independent holomorphic function

$$
\mathcal E_t(s)=\prod_{p\in\{2,3,5,7,11\}}(1-b_t(p)p^{-s}),\qquad
\mathcal F(z)=\mathcal E_t(s_B(z))H_t(z)/B_t(z).        \tag{A.50}
$$

For each time interval evaluate the center-height rectangle and its
enlargement by $1/4$ on either side. Their horizontal lower bounds are
$X_L$ and $X_L-1/4$. Every source disk has radius $3/20$.
$\mathcal F$ and $\mathcal F'$ are holomorphic on these disks even where
an estimate of $|\mathcal F|$ from below is unavailable.

The actual cutoffs are partitioned into eight finite bands $[n,m]$,
starting at $n=N_0$, with $m=\lfloor11n/10\rfloor$ and then $n\gets m+1$,
followed by $[1481120,\infty)$. They are exact adjacent integer intervals.
For a band starting at $n$,
$x\ge x_b=\max(x_{\min},4\pi n^2-\pi t_m/4)$.
Write $y=y_l$, $t_0=t_l$, $L_n=\log n$, and put

$$
\begin{aligned}
c_A&=(1+y)/2-c_*-d_*,\quad c_B=c_A-y-Ky,\quad c_E=c_B+y,\\
\sigma_0&=c_A+t_0L_n/2,\quad
\Delta=1/50-e_0/2,\quad \beta_1=1.
\end{aligned} \tag{A.51}
$$

The constants $e_0,c_*,d_*,K$ are those of A.6.
Equations (A.2)--(A.3), with the permissible larger gamma allowance
$1/50$, imply

$$
\Re s_B\ge c_A(Y)+(t/2)\log N,\quad
\Re s_A\ge c_B(Y)+(t/2)\log N,\quad
|\gamma|\le e^{\Delta Y}N^{-Y}.                       \tag{A.52}
$$

The formulas below specify the all-cutoff calculation in late_core.py.
Let $\mathcal D$ be the 32 squarefree divisors of $2310$ and
$\ell_d^{(2)}=\sum_{p\mid d}\log^2p$. With $R=100000<N_0$, the exact
coefficient of $r^{-s_B}$ in the mollified first polynomial for $r\le R$ is

$$
B_r(t)=\sum_{\substack{d\in\mathcal D\\d\mid r}}
 \mu(d)\exp\!\left[\frac t4
       \{\ell_d^{(2)}+\log^2(r/d)\}\right].            \tag{A.53}
$$

All these terms occur for every actual $N$ and $B_1=1$.
The program encloses this signed sum on the whole time interval before
taking absolute values. Define

$$
S_B=\sum_{r=2}^R|B_r|r^{-\sigma_0},\qquad
D_B=\sum_{r=2}^R\log r\,|B_r|r^{-\sigma_0}.            \tag{A.54}
$$

Every omitted divisor term has $u>\lfloor R/d\rfloor$ and $u\le N$.
For a finite band take $M=m$, $H=\log M$; for the unbounded band use
$M=n$, $H=L_n$ on its finite prefix.
The program checks, for every divisor,

$$
H<2L_n,\quad
c_A-\frac{t_0}{2}(H-L_n)>
 \frac1{\log d+\log\lfloor R/d\rfloor},\quad
\ell_d^{(2)}-2L_n\log d\le0.                         \tag{A.55}
$$

The combined heat exponent is nonincreasing in time, so the left endpoint
is valid. The middle gate makes both the summand and its
$\log(du)$-weighted version decreasing on the finite interval.
Put $I_j(a,t;l,M)=\int_l^M u^{-a}e^{t\log^2u/4}\log^ju\,du$ for
$j=0,1$. The finite tails are bounded by

$$
\begin{aligned}
T_B&=\sum_{d\in\mathcal D}
 e^{t_0\ell_d^{(2)}/4-\sigma_0\log d}
 I_0(\sigma_0,t_0;\lfloor R/d\rfloor,M),\\
D_T&=\sum_{d\in\mathcal D}
 e^{t_0\ell_d^{(2)}/4-\sigma_0\log d}
 [\log d\,I_0+I_1](\sigma_0,t_0;\lfloor R/d\rfloor,M).
\end{aligned}                                                   \tag{A.56}
$$

The upper endpoint is $M$, rather than $M/d$, retaining every original
polynomial term after multiplication by a divisor.
On the unbounded band replace $\log N$ by $\max(L_n,\log u)$ only after
combining its nonpositive coefficient. For $u>n$ this gives a negative
Gaussian in $\log u$. In (A.56) add, to each $I_j$,

$$
J_j(c_A,t_0;n)=\int_n^\infty
 u^{-c_A}e^{-t_0\log^2u/4}\log^ju\,du.                \tag{A.57}
$$

The gates $a+t_0L_n/2>1/L_n$ for both $a=c_A$ and $a=c_E$ prove the
decreasing tail comparisons here and for the reflected tail below.
Thus all $N\ge n$ are covered.
All integrals are computed by exact antiderivatives and ball arithmetic.
For $k=1-a$, $l_0=\log l$, $h_0=\log M$, and $t>0$,

$$
\begin{aligned}
I_0&=\sqrt{\pi/t}\,e^{-k^2/t}
 [\operatorname{erfi}(\sqrt t\,h_0/2+k/\sqrt t)
 -\operatorname{erfi}(\sqrt t\,l_0/2+k/\sqrt t)],\\
I_1&=\frac2t[e^{th_0^2/4+kh_0}-e^{tl_0^2/4+kl_0}-kI_0],\\
J_0&=\sqrt{\pi/t}\,e^{k^2/t}
 \operatorname{erfc}(\sqrt t\,L_n/2-k/\sqrt t),\\
J_1&=\frac2t[e^{kL_n-tL_n^2/4}+kJ_0].
\end{aligned}                                                   \tag{A.58}
$$

Every computed integral is checked positive; cancellation is enclosed by
Arb. Every late box has $t_l>0$.

For the reflected term, the combined coefficient of $Y$ is
$\Delta-L_n+(1/2+K)\log u$. The checked gates

$$
\Delta-L_n+(1/2+K)H<0,\qquad
\Delta-(1/2-K)L_n<0                                 \tag{A.59}
$$

justify its height endpoint on the finite and unbounded parts, respectively,
even when $c_B$ is negative.
Before differentiating the Euler factor, the exact phase multiplier is

$$
\frac{\gamma'}\gamma-s_A'\log u
=\frac i2\left[\alpha(v)+\alpha(w)-\log u+
\frac t2\{\alpha'(v)(\alpha(v)-\log u)+\alpha'(w)\alpha(w)\}\right].
$$

Here the entire source geometry has $|\Re w|,|\Re v|<2$.
The sharper elementary bound

$$
|\alpha-L/2\mp i\pi/4|
\le5/x+4/x^2\le5/(x-6)                              \tag{A.60}
$$

follows by adding the logarithm error $|\sigma|/x+\sigma^2/x^2$ and
the rational error $3/x$ for $|\sigma|\le2$.
The opposite leading imaginary phases cancel. The phase multiplier is
therefore at most
$\frac12\log(x/(4\pi))-\frac12\log u+
 [5+t_m(\log(x/(4\pi))+1)/2]/(x-6)$.
As before, decaying factors are kept with their logarithms in each endpoint
reduction.

For $Z_p=e^{t_0\log^2p/4-\sigma_0\log p}$ set

$$
M_E=\prod_p(1+Z_p),\quad
L_E=\frac{C_1}{2}\sum_p\frac{\log p\,Z_p}{1-Z_p},
\qquad C_1=1+\frac{t_m}{2(x_b-6)}.
$$

The program checks $Z_p<1$ before division and

$$
L_E+\frac1n+\frac{5+t_m(\log(x_b/(4\pi))+1)/2}{x_b-6}
 <\beta_1.                                          \tag{A.61}
$$

Thus the full phase weight, including the Euler derivative, is at most
$W_N(u)=\log N+\beta_1-\frac12\log u$.
Its product with the magnitude decreases in $\log N$ when
$y_l(L_n+\beta_1-H/2)>1$ on the finite prefix, or
$y_l(L_n/2+\beta_1)>1$ on the unbounded part.
Both inequalities are checked. They justify the same all-$N$ reduction
for the weighted derivative while retaining its negative half-log term.

Explicitly, let $a=c_B+t_0L_n/2$, $g(u)=u^{-a}e^{t_0\log^2u/4}$,
$I_j=I_j(a,t_0;1,M)$, and
$W_I=(L_n+\beta_1)I_0-I_1/2>0$.
If $a-t_0H/2>0$, set $V_0=1+I_0$ and $V_1=L_n+\beta_1+W_I$.
Otherwise use

$$
V_0=1+I_0+g(M),\qquad
V_1=L_n+\beta_1+W_I+
 (L_n+\beta_1)\max(1,g(M)).                          \tag{A.62}
$$

To justify these discrete-sum estimates, $g$ has a single valley.
The derivative of $(L_n+\beta_1-\frac12\log u)g(u)$ has a concave quadratic
sign polynomial in $\log u$. Its positive variation occupies at most one
interval, and is bounded by its supremum, at most
$(L_n+\beta_1)\max(1,g(M))$.
The unit-interval sum-integral identity gives (A.62).
In the decreasing case this variation is zero.
Maxima are enclosed by $(a+b+|a-b|)/2$, retaining overlapping balls.

Set $J_j=0$ on a finite band and $J_j=J_j(c_E,t_0;n)$ on the unbounded
band. The reflected magnitude and its mollified derivative are bounded by

$$
\begin{aligned}
A_R&=e^{y(\Delta-L_n)}V_0+e^{y\Delta}J_0,\\
D_2&=M_E\{e^{y(\Delta-L_n)}V_1+
             e^{y\Delta}(\beta_1J_0+J_1/2)\}.
\end{aligned} \tag{A.63}
$$

The first-polynomial derivative is bounded by $D_1=C_1(D_B+D_T)/2$.
Lemma A.3, multiplied by the modulus bound for all five Euler factors on
its complete source disk, gives
$D_{\rm rem}=M_D E_D/(3/20)$.
If $E_0$ denotes the point source error, this proves

$$
|\mathcal F'|\le D_1+D_2+D_{\rm rem}=:D_{\rm raw},\qquad
|\mathcal F-1|\le S_B+T_B+M_E(A_R+E_0)=:r_{\rm point}. \tag{A.64}
$$

The first inequality does not require $r_{\rm point}<1$.
For each time box, take $D_{\rm outer}$ to be the maximum of the outward
upper endpoints of all nine wide-rectangle $D_{\rm raw}$ balls.
These endpoints are exact dyadic numbers, so their maximum bounds every
ball, including overlapping candidates. Cauchy applied to $\mathcal F'$
on the physical radius-$1/4$ disk gives

$$
|\mathcal F''(z_0)|\le4D_{\rm outer}.                 \tag{A.65}
$$

Every center band separately has the checked denominator
$m=1-r_{\rm point}>0$. Put $D_{\rm center}=D_{\rm raw}$ there.
Let $\epsilon_1,\epsilon_2$ be the archimedean first and second jet errors
at $x_b$, using (A.60).
With $s_1=(1+t_m/[2(x_b-6)])/2$ and
$s_2=t_m(2/x_b^2+24/x_b^3)/8$, direct differentiation gives

$$
\left|\left(\frac{\mathcal E'}{\mathcal E}\right)'\right|
\le E_2=s_2\sum_p\frac{\log p\,Z_p}{1-Z_p}
       +s_1^2\sum_p\frac{\log^2p\,Z_p}{(1-Z_p)^2}.
$$

The identities
$u=B'/B-\mathcal E'/\mathcal E+\mathcal F'/\mathcal F$ and its derivative
therefore yield

$$
J\le\epsilon_2+E_2+\frac{4D_{\rm outer}}m+
\left(\frac{D_{\rm center}}m\right)^2+
\left(L_E+\frac{D_{\rm center}}m+\epsilon_1\right)^2.  \tag{A.66}
$$

Both square terms are required: they come from differentiating
$\mathcal F'/\mathcal F$ and from $|u+\pi/8+i\Omega|^2$.
No wide-circle quotient or center-error/radius substitution occurs.

The program check_late_boundary.py recomputes (A.53)--(A.66) for all 117
boxes and all nine center and wide cutoff bands, importing no stored
numerical bounds. It uses the common H7 error
$E_{ab}<3\cdot10^{-9}$ and $V_7$ even on the smaller domain.
All 1053 center denominators, all 1053 wide derivative evaluations, and all
1053 final comparisons with (A.49) pass at 512 bits. The smallest final
margin is greater than $1.47132047$.
This proves (A.31) for $9/200\le t\le T_M$.
The early and late intervals share the closed endpoint $9/200$.
Together they establish (A.31) at every time, discharging the sole
remaining boundary premise of Theorem A.6.

## A.8. Domains, whole-row use, and reproduction

The dependency order is acyclic. The enlarged approximation supplies the
top and infinity estimates and the finite source errors.
P2 and Theorem A.5 give the density field and $q_M$ strip simultaneously,
using only unsigned force rows.
The early and late calculations prove the physical jet boundary directly.
Theorem A.6 then propagates it through the band above $b(t)$.
Only after these steps are the signed field rows of the reference and
final barriers used.

For a row $[t_l,t_r]$ and fixed probe $p$, the gates $p^2>q_M(t_l)$,
and, where needed, $p\ge3/5$ and $(p-3/5)^2\ge q_M(t_l)$ imply
$p>h_M(t)$ and $p\ge b(t)$ throughout the closed row.
The gates $p\le5$ and $t_r\le T_M$ preserve the stated domains.
Equation (A.18) and $\delta<10^{-5}$ turn
$s<f_0(p,t_l)-10^{-5}$ into the strict field bound $S>s$.
Also

$$
C(p,t)\le e^{t_r/100000}[8/25+A_*/U(p,t_l)]
 \le c_{\rm row}.                                   \tag{A.67}
$$

This uses separate monotonic factors and does not assert that $C$ itself
decreases in time. These are the whole-row bounds consumed by P8.
The uncut density field is used only for $x\ge X$, $h_M(t)<Y\le5$,
and the uncut jet field only for $x\ge X$, $b(t)\le Y\le5$.
No continuation below a pole, to all heights, or left of $X$ is used.

The finite verifications for this appendix are:

| Program in support/fields/ | Mathematical checks |
|---|---|
| check_h7.py | Enlarged source, Gaussian/Arias scalars, top and head-center bounds |
| check_m3a.py | 855 initial leaves, 1620 unsigned rows, 1620 nonlocal bottom inequalities |
| check_fixed_c.py | 400 initial cells, supersolution/head constants, nested top disks, 162 boundary rectangles |
| check_early_boundary.py | 45 early boxes, relative Euler jets and complete tails |
| check_late_boundary.py | 117 late boxes, 1053 center and 1053 wide cutoff-band evaluations |

Programs write only to an explicitly supplied --output path and reject
optimized Python, which would disable their assertions.
Late calculations may be divided into adjacent index ranges, but a full
verification must cover exactly $45,\ldots,161$; the early calculation
covers exactly $0,\ldots,44$.
The unified command in the main text checks that coverage.
The output balls are arithmetic evidence; the reductions in A.1--A.7
give them their continuum and all-cutoff meaning.
These are paper proofs with ball-arithmetic verification, and are not
asserted to be formalized in Lean.
