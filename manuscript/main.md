# A computer-assisted upper bound for the de Bruijn–Newman constant

**Abstract.** We construct an explicit piecewise-affine barrier for the squared imaginary parts of the zeros of the heat deformation of Riemann's xi function. The resulting upper bound for the de Bruijn–Newman constant is
$$
 B=\frac{3885632262767861213460393068710302759}
         {24646172707879668706230182733520000000}
   =0.157656619095490606768\ldots<0.158.
$$
The argument combines classical zero dynamics with a three-probe source estimate, a density lower bound, and a bound for a logarithmic-derivative jet. Its finite barrier certificate contains 12,666 rational rows. Supporting computations use rigorous ball arithmetic; a second arithmetic library checks the elementary profile inequalities. A Lean 4 companion verifies the barrier comparison and zero dynamics, conditional on explicitly stated analytic inputs. The finite verification of RH used in the argument is the published theorem of Platt and Trudgian.

## 1. Introduction

For real $t$, let
$$
 \begin{aligned}
 H_t(z)&=\int_0^\infty e^{tu^2}\Phi(u)\cos(zu)\,du,\\
 \Phi(u)&=\sum_{n\ge1}(2\pi^2n^4e^{9u}-3\pi n^2e^{5u})e^{-\pi n^2e^{4u}}.
 \end{aligned}
$$
This is the normalization of Polymath [Po19], in which
$$
 H_0(z)=\frac18\,\xi\!\left(\frac{1+iz}{2}\right),\qquad
 \partial_tH_t=-\partial_z^2H_t.
$$
Here $\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$, continued to an entire function. The de Bruijn–Newman constant is
$$
 \Lambda=\inf\{t\in\mathbb R:H_t\text{ has only real zeros}\}.
$$
De Bruijn proved $\Lambda\le1/2$ [dB50]; Newman proved finiteness from below and conjectured $\Lambda\ge0$ [Ne76]. Rodgers and Tao proved this conjecture [RT20]. Thus RH is equivalent to $\Lambda=0$.

Polymath obtained $\Lambda\le0.22$ [Po19]. Platt and Trudgian's rigorous verification of RH to height $3\cdot10^{12}$ gives $\Lambda\le0.2$ [PT21, Corollary 2]. Gomila has made public a computer-assisted argument for $\Lambda\le0.1787854$, described by its author as not yet peer reviewed [Go26]. That argument instantiates Polymath's upper-bound criterion. The present argument uses the same classical heat-flow framework and finite-RH input, with density and jet estimates providing additional contraction of a moving barrier. No claim of priority over concurrent work is needed for the proof.

**Theorem 1.1.** In this normalization,
$$
 \Lambda\le B
 =\frac{3885632262767861213460393068710302759}
        {24646172707879668706230182733520000000}.
$$

The mathematical argument is given below and in the two analytic supplements. The distinction between its conventional proof and the scope of its Lean formalization is recorded in §8. The theorem is a positive upper bound; it does not prove RH.

## 2. Notation and classical inputs

Write $z=x+iy$. The corresponding zeta coordinate is $s=(1-y)/2+ix/2$. Set
$$
 \begin{aligned}
 u(z,t)&=\frac{H_t'(z)}{H_t(z)},&
 S(x,Y,t)&=-\operatorname{Im}u(x+iY,t),\\
 \Omega(x)&=\frac14\log\frac{x}{4\pi},&
 J(x,Y,t)&=|u_z|+(\operatorname{Re}u+\pi/8)^2+(S-\Omega)^2,
 \end{aligned}
$$
where the quantities in $J$ are evaluated at $x+iY$. Also $S_Y=-\operatorname{Re}u_z$. The fixed spatial cutoffs are
$$
 X=5999347341500,\quad X_L=X-10^6,\quad X_e=5900000000000,
 \qquad \Omega_L=\frac{6722911}{10^6}.
$$
In particular, $\Omega(x)>\Omega_L$ for $x\ge X$. This elementary inequality is proved in Lean and checked independently by interval arithmetic.

For $Y>b\ge0$, define the conjugate-pair kernel
$$
 K_Y(d,b)=\frac{Y-b}{d^2+(Y-b)^2}+\frac{Y+b}{d^2+(Y+b)^2}.
$$
When $Y$ lies above all zeros, pairing conjugate zeros gives
$S(x,Y,t)=\sum_{\mathrm{pairs}}K_Y(x-\operatorname{Re}\rho,|\operatorname{Im}\rho|)$.
Multiplicities are retained; real zeros have half-pair weight.

We use the following classical facts [Po19, §§1, 3]. Each $H_t$ is real, even, entire, and not identically zero. For $t\ge0$, its zeros lie in $|\operatorname{Im}z|\le1$. Zeros persist locally under small changes of time, with multiplicity counted. A simple zero has a differentiable branch with velocity
$$
 \rho'(t)=\frac{H_t''(\rho(t))}{H_t'(\rho(t))}.
$$
The regularized Hadamard identity at a simple zero is
$$
 \frac{H_t''(\rho)}{H_t'(\rho)}
 =2\left\{\frac1\rho+
       \sum_{\zeta\ne\rho}
       \left(\frac1{\rho-\zeta}+\frac1\zeta\right)\right\}.
 \tag{2.1}
$$
The regularized sum is absolutely convergent. Equivalently, one may use a symmetrically paired reciprocal-zero sum. Absolute convergence of the unpaired complex series is not asserted. The imaginary parts and pair-kernel sums used below are absolutely summable.

At a zero $z_0$ of multiplicity $m\ge2$ at time $t_0$, backward evolution gives zeros
$$
 z_0+i\sqrt{2\epsilon}\,\lambda_j+O(\epsilon)
 \quad\text{of }H_{t_0-\epsilon},
 \tag{2.2}
$$
where the $\lambda_j$ are the real roots of the probabilists' Hermite polynomial $\operatorname{He}_m$. One such zero has imaginary part
$\operatorname{Im}z_0+c\sqrt\epsilon+O(\epsilon)$ with $c>0$.
The formal proof establishes the needed height increase directly.

De Bruijn's strip theorem states that a zero strip of half-width $h$ at time $t$ becomes a real spectrum at time $t+h^2/2$ [dB50; Po19, Theorem 3.2].

## 3. The two barriers

An affine row is $(t_L,t_R,q_L,q_R)$ with $t_L<t_R$ and $q_R<q_L$. Its value and positive speed are
$$
 q(t)=q_L+\frac{q_R-q_L}{t_R-t_L}(t-t_L),\qquad
 w=\frac{q_L-q_R}{t_R-t_L}.
$$
Adjacent rows join exactly in time and squared height. We use a reference barrier $q_{\rm ref}$ on $[0,T_*]$ and a main barrier $Q$ on $[3/50,T]$. Their exact rational data are in the compact barrier certificate. A third trace $q_M$ specifies the domain of the density and jet estimates.

| Trace | Interval | Rows | Purpose |
|---|---|---:|---|
| $q_M$ | $[0,T_M]$ | 1,620 | Density and jet domain |
| $q_{\rm ref}$ | $[0,T_*]$ | 7,849 | Strict entry for $Q$ |
| $Q$ | $[3/50,T]$ | 4,817 | Final bound |

The horizons are
$$
 \begin{aligned}
 T_M&=\frac{10724023263453313712965415492196719802951}
            {66207211195936838001560220771250000000000},\\
 T_*&=\frac{3727212594484883717859635359632643731427893093}
            {23745856366798857962956857522257275000000000000},\\
 T&=\frac{3854824546883011627577605340293402759}
           {24646172707879668706230182733520000000}.
 \end{aligned}
$$
They satisfy $3/50<T<T_*<T_M<1/5$. The endpoint and entry identities are
$$
 \begin{aligned}
 q_{\rm ref}(0)&=(1000001/1000000)^2>1,& q_{\rm ref}(T_*)&=1/400,\\
 Q(3/50)&=\frac{84648870770133}{200000000000000}
           =q_{\rm ref}(3/50)+10^{-9},& Q(T)&=1/400.
 \end{aligned}
 \tag{3.1}
$$
Both barriers are continuous, piecewise affine, strictly decreasing, and at least $1/400$.

**Theorem 3.1 (reference comparison).** For $0\le t\le T_*$, every zero $\rho$ of $H_t$ satisfies $(\operatorname{Im}\rho)^2<q_{\rm ref}(t)$.

**Theorem 3.2 (main comparison).** For $3/50\le t\le T$, every zero $\rho$ of $H_t$ satisfies $(\operatorname{Im}\rho)^2<Q(t)$.

**Deduction of Theorem 1.1.** At time $T$, all zeros lie in the strip of half-width $1/20$. De Bruijn's theorem gives a real spectrum at
$$
 T+\frac{(1/20)^2}{2}=T+\frac1{800}=B.
 \tag{3.2}
$$
These are exact rational identities. The comparisons are proved in §7.

## 4. Supporting estimates

The following statements specify every analytic input beyond §2. The accompanying analytic and computational supplements provide their proofs and executable enclosures. Labels P2–P8 are retained to connect the paper to the formal interfaces.

**P2 (finite head).** For $t\in[0,1/5]$, every zero of $H_t$ with $|\operatorname{Re}z|\le X$ is real. The finite-RH input is [PT21, Theorem 1], since $X/2<3\cdot10^{12}$. Boundary non-vanishing is established by a direct 800,000-cell interval computation on $(t,y)\in[0,1/5]\times[0,1]$ at $x=X$. A zero-counting homotopy and forward Hermite splitting give the finite-rectangle conclusion. This computation does not reverify the published finite-RH theorem.

**P3a (confinement).** For every $0<\tau\le T'\le1/5$, nonreal zeros of $H_t$ have uniformly bounded real part for $t\in[\tau,T']$. Indeed, [Po19, Theorem 1.5(i)] gives an absolute $C>0$ such that zeros with $x\ge\exp(C/t)$ are real. Taking $R=\exp(C/\tau)$ and using evenness proves the assertion. No numerical value of $R$ is required.

**P3b (effective approximation).** The normalized approximation $H_t/B_t=f_N+E$ is used on $x\ge X_e$, $t\in[0,1/5]$, $0\le y\le7$.
The analytic supplement defines every term and proves the extended domain and errors, including the vertical Stirling remainder, Gaussian tails, and cutoff changes. This domain is not an unqualified application of the narrower numerical domain in [Po19, Theorem 1.3]. Its consequences include
$$
 S(x,5,t)>6.59\quad(x\ge X_L),\qquad
 |u(x+5i,t)|<10\quad(X_e+1\le x\le X).
$$

**P4 (density).** Define
$$
 \begin{aligned}
 U(Y,t)&=10^9+\sum_{j=1}^3a_j e^{\lambda_j^2t}\cosh(\lambda_jY),\\
 (a_1,a_2,a_3)&=(1758974,2464729,302096),\\
 (\lambda_1,\lambda_2,\lambda_3)&=(19/4,97/20,131/20),\\
 f_0(Y,t)&=U_Y/U,\qquad \delta(t)=e^{90t}/10^{14},\qquad f_M=f_0-\delta.
 \end{aligned}
$$
For $x\ge X$, $0\le t\le T_M$, and $\sqrt{q_M(t)}<Y\le5$,
$H_t(x+iY)\ne0$ and $S(x,Y,t)\ge f_M(Y,t)$.
The proof couples the vertical Burgers comparison with the wall $q_M$ and checks initial, lower, side, top, and infinity boundaries. At fixed $Y>0$, $f_0$ is nondecreasing in $t$ by a covariance identity; also $\delta(T_M)<10^{-5}$. Monotonicity of $f_M$ is not needed.

**P5 (jet).** Set
$$
 C(Y,t)=e^{t/10^5}\left(\frac8{25}+\frac{1130000000000}{U(Y,t)}\right),
 \qquad b(t)=\sqrt{q_M(t)}+\frac35.
$$
For $x\ge X$, $0\le t\le T_M$, and $b(t)\le Y\le5$, one has $J(x,Y,t)\le C(Y,t)$.
The proof supplies the differential inequality for $J$, the initial and exterior boundary estimates, and all 162 boxes of the lower moving boundary. The statement is confined to this finite height band.

**P7 (three-probe source).** Set
$$
 V(x,h,t)=\frac{15}{14}S(x,3h,t)-\frac{16}{21}S(x,4h,t)+\frac16S(x,5h,t).
$$
For each of the 26 source boxes, $V(x,h,t)>L$ throughout its closed $(t,h)$ rectangle and for every $x\ge X$. The exact boxes and floors are tabulated in the source-box supplement. The computation establishes all required non-vanishing directly and uses neither $q_M$ nor the jet bound. The uniform reduction, infinite tails, and integer-cutoff changes are part of the proof.

**P8 (profile values).** Every reference row has a probe $p$ and floor $s$ with
$$
 s<f_0(p,t_L)-10^{-5}.
 \tag{4.1}
$$
Signed rows also carry $c$ with
$$
 c\ge e^{t_R/10^5}\left(\frac8{25}+\frac{1130000000000}{U(p,t_L)}\right).
 \tag{4.2}
$$
These inequalities are checked on all 7,849 reference rows with Arb at 512 bits and independently with mpmath intervals at 80 decimal digits. For $t\in[t_L,t_R]$, P4 gives
$$
 S(x,p,t)\ge f_0(p,t)-\delta(t)>f_0(p,t_L)-10^{-5}>s.
 \tag{4.3}
$$
Monotonicity of $U$ and P5 similarly give $J(x,p,t)\le c$ on a signed row. The main barrier uses exactly these field records on contained time cells.

## 5. Kernel inequalities and velocity bounds

Let $\rho=x+ih$, $h>0$, be a simple zero of maximal imaginary part and write $q=h^2$. Separating its conjugate from (2.1) gives
$$
 h'=-\frac1h-2\sum_{\text{other pairs}}K_h(d_j,b_j),\qquad q'=2hh'.
 \tag{5.1}
$$
All other pair heights satisfy $0\le b_j\le h$. At the lower height $h$, the singular point $(d,b)=(0,h)$ is excluded; it would represent the distinguished zero itself.

Three rational-function inequalities hold on this domain:

1. If $p^2\ge5h^2$ and $p>0$, then $K_h\ge(h/p)K_p$.
2. With $(c_1,c_2,c_3)=(15/14,-16/21,1/6)$,
   $K_h\ge c_1K_{3h}+c_2K_{4h}+c_3K_{5h}$.
3. If $p^2\ge9h^2$ and $p>0$, put
   $$
   \alpha=\frac{h(3p^2-h^2)}{2p^3},\qquad
   a=\frac{p(p^2-h^2)}{3p^2-h^2}.
   $$
   Then $K_h\ge\alpha(K_p-a\,\partial_pK_p)$.

These are proved by clearing positive denominators; the three-probe case also has an interpolation proof. Their exact polynomial proofs are formalized in the companion kernel module.

### 5.1. Source rows

The distinguished conjugate pair contributes
$\sum_jc_jK_{(j+2)h}(0,h)=7/(15h)$.
The second kernel inequality and (5.1) therefore give
$$
 q'\le-\frac2{15}-4\sqrt q\,V.
 \tag{5.2}
$$
Suppose a row lies in a source box:
$$
 t_a\le t_L<t_R\le t_b,\qquad
 h_{\rm lo}^2\le q_R<q_L\le h_{\rm hi}^2,\qquad L>0.
 \tag{5.3}
$$
Its speed is strictly beaten whenever
$$
 w\le\frac2{15}\quad\text{or}\quad
 \left(w>\frac2{15}\ \text{and}\ (w-\tfrac2{15})^2<16L^2q_R\right).
 \tag{5.4}
$$
Indeed, at contact $q\ge q_R$, so
$q'\le-2/15-4L\sqrt{q_R}<-w$.
The sign conditions in (5.4) are necessary when squaring.

### 5.2. Unsigned field rows

The first kernel inequality, with the distinguished pair separated, yields
$$
 q'\le-2-\frac{4qS}{p}+\frac{8q}{p^2-q}<-2-qK_u(q),\qquad
 K_u(q)=\frac{4s}{p}-\frac8{p^2-q}.
 \tag{5.5}
$$
Here $S>s$ is supplied by (4.3). The function $K_u$ is decreasing for $q<p^2$.

### 5.3. Signed field rows

Set $D=S-aS_Y$, where $a=p(p^2-q)/(3p^2-q)$. The third kernel inequality gives
$$
 q'\le-2-4h\alpha D+\frac{16q}{p^2-q}.
 \tag{5.6}
$$
From $J\le c$ and $S_Y=-\operatorname{Re}u_z$,
$D\ge S-ac+a(S-\Omega)^2$.
If $s<\Omega_L<\Omega$ and $2a(\Omega_L-s)\le1$, then
$$
 S-ac+a(S-\Omega)^2>s-aL_0,\qquad L_0=c-(\Omega_L-s)^2.
 \tag{5.7}
$$
To see this, write $u_0=S-s\ge0$, $v=\Omega-\Omega_L>0$, and $d=\Omega_L-s>0$.
The difference is $u_0(1-2ad)+a(u_0-v)^2+2adv>0$.

Substitution in (5.6) gives
$$
 \begin{aligned}
 q'&<-2-qK_s(q),\\
 K_s(q)&=\frac{6s}{p}-2L_0+
 q\left(\frac{2L_0}{p^2}-\frac{2s}{p^3}\right)-\frac{16}{p^2-q}.
 \end{aligned}
 \tag{5.8}
$$
If $pL_0\le s$, then $K_s'(q)<0$. The coefficient $a(q)$ is decreasing, so its branch condition need only be checked at $q_R$.

For either field mode let $k=K(q_L)>0$. If
$$
 w\le2+kq_R,
 \tag{5.9}
$$
then at contact $q\in[q_R,q_L]$,
$q'<-2-qK(q)\le-2-kq_R\le-w$.
Equality in the rational speed gate is harmless because the analytic inequality is strict.

## 6. Exact certificate conditions

The compact certificate stores rational values, source-box indices, and references to field records. The exact checker verifies:

- proper rows, exact joins, prescribed endpoints, and $q_R\ge1/400$;
- closed source-box containment and the strict speed condition (5.4);
- containment in each field record's time cell, of length at most $1/50000$;
- exact interpolation of the density wall at the row's left endpoint;
- $0<p\le5$, $p^2>q_M(t_L)$, and $p^2>q_L$;
- in unsigned mode, $5q_L\le p^2$;
- in signed mode, $p\ge3/5$, $(p-3/5)^2\ge q_M(t_L)$,
  $9q_L\le p^2$, $c>0$, $\Omega_L>s$, $pL_0\le s$, and $2a(q_R)(\Omega_L-s)\le1$;
- positivity of the recomputed $k$ and the speed condition (5.9).

The decreasing wall makes the left-endpoint domain checks valid throughout the row. The main barrier has 541 source, 2,772 signed field, and 1,504 unsigned field rows. The reference barrier has 6,317 signed and 1,532 unsigned field rows. Every source box is used.

The Python checker uses exact rational arithmetic and explicit failure checks. In Lean, equivalence between the executable row check and its propositional specification is proved. Kernel evaluation verifies every row, the chains, source catalog, and wall. A deterministic generator checks the correspondence between the compact JSON and generated Lean declarations.

The certificate is a witness. Its validity does not depend on how it was optimized, unused candidate rows, rejected numerical targets, or producer acceptance flags.

## 7. First-contact proof

We give a common argument for both barriers. For $Q$, the starting time is $t_0=3/50$. Theorem 3.1 and (3.1) give strict entry. For the reference barrier, the global strip gives strict entry at zero. Exact arithmetic shows that
$$
 \tau_0=\frac{20000010}{238529173356019}>0,\qquad
 q_{\rm ref}(t)>1\quad(0\le t\le\tau_0).
$$
Its first possible contact is therefore after $\tau_0$, where confinement is uniform.

Let $q_b$ be the barrier under consideration. Suppose a zero reaches or exceeds it, and define
$$
 \mathcal F=\{t:\exists z,\ H_t(z)=0,\ (\operatorname{Im}z)^2\ge q_b(t)\}.
$$
Every such zero has $|\operatorname{Im}z|\ge1/20>1/40$. P3a bounds its real part uniformly on the positive-time interval. Joint continuity of $H$ and continuity of the barrier make the relevant zero set closed in a compact box. Thus $\mathcal F$ has a first time $t_1>t_0$.

Local persistence excludes a strict overshoot: a zero strictly above the barrier would persist above it at earlier nearby times. Hence a highest zero $\rho_1=x_1+ih_1$ satisfies $h_1^2=q_b(t_1)$, and all zeros lie at or below this height. P2 gives $|x_1|>X$. Evenness and conjugation allow $x_1>X$ and $h_1>0$.

A multiple contact is impossible. By (2.2), backward evolution produces a zero at height $h_1+c\sqrt\epsilon+O(\epsilon)$. The function $\sqrt{q_b}$ is Lipschitz because $q_b\ge1/400$ and has finitely many affine pieces. Its earlier height is only $h_1+O(\epsilon)$, contradicting first contact.

The contact zero is simple. Choose the row ending at $t_1$ if $t_1$ is a knot, so its slope is the left derivative. P7 and §5.1, or P4–P5–P8 and §§5.2–5.3, give
$$
 \frac{d}{dt}(\operatorname{Im}\rho(t))^2\bigg|_{t=t_1}<q_b'(t_1^-).
$$
But $(\operatorname{Im}\rho(t))^2-q_b(t)$ is negative just before $t_1$ and zero at $t_1$, so its left derivative is nonnegative. This contradiction proves both comparisons.

The argument includes terminal times, changes of row type, and multiple zeros. It never differentiates an unattained supremum or evaluates a logarithmic derivative at a zero. Equation (3.2) completes Theorem 1.1.

## 8. Verification scope and reproducibility

The manuscript, source code, exact certificates, and reproduction instructions are maintained at [github.com/stefangordon/dbn-upper-bound](https://github.com/stefangordon/dbn-upper-bound).

The classical inputs are cited published theorems. The new analytic estimates are conventional proofs in the supplements, with rigorous finite computations furnishing their explicit inequalities. The Lean companion verifies the deduction from stated analytic inputs, including the concrete heat integral, zero dynamics, kernel inequalities, barrier calculus, and first-contact argument. Its main theorem remains conditional on those inputs.

Every P8 endpoint gate is kernel-checked using a proved rational evaluator. Finite-head propagation is proved from the time-zero finite-RH input and vertical boundary non-vanishing; neither input is thereby proved.

An alternative interface assumes the residual estimate and nonzero normalizer of Lemma A.1, finite RH at time zero, the continuous lower bound $|f^{[N]}(X+iy)|>1/500$, source floors, and density/jet comparisons. Lean derives the required confinement and finite head from these inputs. The continuous bound is not a Lean-checked grid: the polynomial computation and its Taylor-error bridge remain unformalized. Auxiliary zeta and finite heat-sum identities are proved, but the remaining analytic inputs are not. The published positive-time tail statement provides an alternative confinement input.

For the main theorem, Lean reports only its standard foundational axioms: propositional extensionality, classical choice, and quotient soundness. This report does not prove the theorem's explicit hypotheses.

The standalone numerical entry point is:

~~~bash
python3.12 -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python verify.py --regenerate
~~~

The supplied Dockerfile provides CPython 3.12, a C compiler, and FLINT headers. This command regenerates the boundary matrix and runs all numerical checks, including every boundary cell, source box, field estimate, and both P8 arithmetic backends. Late boundary boxes run in separate processes. The explicit quick mode omits the supporting computations.

To check the formal companion:

~~~bash
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
~~~

Python packages and Lean dependencies are version-pinned; native tool versions are recorded by the runs. The release manifest identifies the published bytes; it is an integrity mechanism, not a proof of the mathematics.

The research and initial drafts were produced with AI assistance. Subsequent automated reviews independently reconstructed mathematical arguments and numerical evaluations. Such reviews are not external peer review. Responsibility for the submitted statements and their verification remains with the human authors.
