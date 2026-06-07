The exact-rank version is not enough. The correct ITER core is:


$$\text{windowed minorization}+\text{deterministic matched/unmatched recursion}.$$


And yes: route 4 works, but not with only a scalar $\rho_m$. You must also track an unmatched pair measure $U_m(x,y)$, because future overlap depends on whether the unmatched pair is in the rank window.

0. First obstruction: the stated far-rank theorem is false
From (A)+(B′) alone, the desired statement


$$\operatorname{ov}(\widetilde P^m(i,\cdot),\widetilde P^m(j,\cdot))
\ge 1-(1-\delta_*)^m-\varepsilon$$


for fixed $m$ and arbitrary far-apart ranks cannot hold.
Counterexample: let every state of rank $R$ jump deterministically to a canonical state of rank $R-1$. Then same-rank rows are identical, so (B′) holds with $\delta_*=1$. No big jumps holds perfectly. But if


$$\operatorname{rnk}(i)-\operatorname{rnk}(j)>m,$$


then after $m$ steps the two laws are still supported on different ranks, so overlap is $0$.
Thus exact-rank encounters are not guaranteed. The rank difference is not automatically a martingale with useful hitting estimates, and jumps can skip exact levels. You need a window relation.

1. Replace exact-rank minorization by windowed minorization
Use:


$$G_W(x,y) :\Longleftrightarrow
|\operatorname{rnk}x-\operatorname{rnk}y|\le W.$$


The correct minorization hypothesis is:


$$\tag{B\(_W\)}
G_W(x,y)
\Longrightarrow
\sum_z \min(P(x,z),P(y,z))\ge \delta .$$


In Lean form, for a finite state space α:
leandef overlap (μ ν : α → ℝ) : ℝ :=  ∑ z, min (μ z) (ν z)def Good (W : ℕ) (x y : α) : Prop :=  Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ)) ≤ W
Then assume:
leanhminor :  ∀ x y, Good W x y →    δ ≤ ∑ z, min (P x z) (P y z)
This is the actual replacement for (B′). Exact equality of rank is too brittle.
If you have exact-rank minorization plus local TV regularity of one-step laws, prove $B_W$ by:


$$\operatorname{ov}(\mu,\nu')
\ge
\operatorname{ov}(\mu,\nu)-\sum_z |\nu'(z)-\nu(z)|.$$


So if exact-rank overlap is $\delta_0$, and moving within a rank window changes the row law by at most $\eta$, then


$$\operatorname{ov}(P(x,\cdot),P(y,\cdot))
\ge \delta_0-\eta.$$


Choose $\eta\le \delta_0/2$, giving $\delta=\delta_0/2$.

2. Deterministic ITER construction
First prove the stochastic finite-state version. For the substochastic killed kernel, add a cemetery state and subtract the final cemetery overlap as a killing error.
Assume finite α, stochastic kernel:
leanhPnonneg : ∀ x y, 0 ≤ P x yhPmass   : ∀ x, ∑ y, P x y = 1
Define the common part at a pair:


$$C_{x,y}(z)
:=
\begin{cases}
\min(P(x,z),P(y,z)), & G_W(x,y),\\
0, & \text{otherwise}.
\end{cases}$$


Lean:
leandef C (x y z : α) : ℝ :=  if Good W x y then min (P x z) (P y z) else 0def cmass (x y : α) : ℝ :=  ∑ z, C W P x y z
Then define residuals:


$$L_{x,y}(z)=P(x,z)-C_{x,y}(z),$$




$$R_{x,y}(z)=P(y,z)-C_{x,y}(z).$$


Since rows are stochastic,


$$\sum_z L_{x,y}(z)=1-\operatorname{cmass}(x,y),$$




$$\sum_z R_{x,y}(z)=1-\operatorname{cmass}(x,y).$$


Define a residual product coupling:


$$K_{x,y}(a,b)
=
\begin{cases}
\dfrac{L_{x,y}(a)R_{x,y}(b)}
      {1-\operatorname{cmass}(x,y)},
& \operatorname{cmass}(x,y)<1,\\[1.2ex]
0, & \operatorname{cmass}(x,y)=1.
\end{cases}$$


Lean:
leandef Lres (x y z : α) : ℝ :=  P x z - C W P x y zdef Rres (x y z : α) : ℝ :=  P y z - C W P x y zdef Kres (x y a b : α) : ℝ :=  if h : cmass W P x y < 1 then    Lres W P x y a * Rres W P x y b / (1 - cmass W P x y)  else    0
The key finite-sum lemmas are:
leanlemma C_le_left :  C W P x y z ≤ P x zlemma C_le_right :  C W P x y z ≤ P y zlemma C_nonneg :  0 ≤ C W P x y zlemma cmass_le_one :  cmass W P x y ≤ 1lemma Kres_left_marginal :  ∑ b, Kres W P x y a b = Lres W P x y alemma Kres_right_marginal :  ∑ a, Kres W P x y a b = Rres W P x y blemma Kres_mass :  ∑ a, ∑ b, Kres W P x y a b =    1 - cmass W P x y
These are all finite-sum algebra.

3. Matched/unmatched recursion
Track two objects:


$$\rho_t(z)
=
\text{mass already coalesced at state }z,$$




$$U_t(x,y)
=
\text{unmatched pair mass at pair }(x,y).$$


Initialize:


$$\rho_0(z)=0,$$




$$U_0(x,y)=1_{\{x=i,y=j\}}.$$


Recursion:


$$\rho_{t+1}(z)
=
\sum_a \rho_t(a)P(a,z)
+
\sum_{x,y} U_t(x,y)C_{x,y}(z).$$


And


$$U_{t+1}(a,b)
=
\sum_{x,y} U_t(x,y)K_{x,y}(a,b).$$


Lean skeleton:
leandef rho : ℕ → α → ℝ| 0, z => 0| t+1, z =>    (∑ a, rho t a * P a z)    +    (∑ x, ∑ y, U t x y * C W P x y z)def U : ℕ → α → α → ℝ| 0, x, y =>    if x = i ∧ y = j then 1 else 0| t+1, a, b =>    ∑ x, ∑ y, U t x y * Kres W P x y a b
This is the hand-built coupling, but expressed purely as finite-sum recursion.

4. Marginal invariant
Let


$$\mu_t(z)=P^t(i,z),
\qquad
\nu_t(z)=P^t(j,z).$$


Then prove:


$$\rho_t(z)+\sum_y U_t(z,y)=\mu_t(z),$$




$$\rho_t(z)+\sum_x U_t(x,z)=\nu_t(z).$$


Lean lemmas:
leanlemma left_marginal :  rho W P i j t z + ∑ y, U W P i j t z y =    Ppow P t i zlemma right_marginal :  rho W P i j t z + ∑ x, U W P i j t x z =    Ppow P t j z
Therefore $\rho_t$ is a common minorant:


$$\rho_t(z)\le \mu_t(z),
\qquad
\rho_t(z)\le \nu_t(z).$$


Hence:


$$\sum_z \rho_t(z)
\le
\operatorname{ov}(\mu_t,\nu_t).$$


Lean:
leanlemma rho_le_left :  rho W P i j t z ≤ Ppow P t i zlemma rho_le_right :  rho W P i j t z ≤ Ppow P t j zlemma rho_mass_le_overlap :  ∑ z, rho W P i j t z ≤    overlap (Ppow P t i) (Ppow P t j)
This is the deterministic substitute for “probability of coalescence is at most overlap.”

5. Unmatched-mass recurrence
Define:


$$u_t=\sum_{x,y}U_t(x,y),$$




$$g_t=\sum_{G_W(x,y)} U_t(x,y),$$




$$b_t=u_t-g_t.$$


Here $b_t$ is unmatched mass outside the rank window.
Lean:
leandef umass (t : ℕ) : ℝ :=  ∑ x, ∑ y, U W P i j t x ydef goodMass (t : ℕ) : ℝ :=  ∑ x, ∑ y, if Good W x y then U W P i j t x y else 0def badMass (t : ℕ) : ℝ :=  umass W P i j t - goodMass W P i j t
Since


$$u_{t+1}
=
\sum_{x,y}U_t(x,y)(1-\operatorname{cmass}(x,y)),$$


and on good pairs


$$\operatorname{cmass}(x,y)\ge\delta,$$


we get


$$u_{t+1}
\le
u_t-\delta g_t.$$


Equivalently,


$$u_{t+1}
\le
(1-\delta)u_t+\delta b_t.$$


Lean:
leanlemma umass_step_exact :  umass W P i j (t+1)    =  ∑ x, ∑ y,    U W P i j t x y * (1 - cmass W P x y)lemma umass_step_le :  umass W P i j (t+1)    ≤  umass W P i j t - δ * goodMass W P i j tlemma umass_step_bad :  umass W P i j (t+1)    ≤  (1 - δ) * umass W P i j t    + δ * badMass W P i j t
This is the core ITER inequality.

6. Scalar recursion solver
Assume an analytic/window lemma gives


$$b_t\le e_t
\qquad
\text{for }t<m.$$


Then:


$$u_{t+1}
\le
(1-\delta)u_t+\delta e_t.$$


With $u_0=1$, solve:


$$u_m
\le
(1-\delta)^m
+
\delta\sum_{t=0}^{m-1}
(1-\delta)^{m-(t+1)}e_t.$$


Lean-friendly statement:
leanlemma scalar_rec_solve  {u e : ℕ → ℝ} {q δ : ℝ} {m : ℕ}  (hq_nonneg : 0 ≤ q)  (hrec : ∀ t < m, u (t+1) ≤ q * u t + δ * e t) :  u m ≤ q^m * u 0    + δ * ∑ t in Finset.range m, q^(m - (t+1)) * e t
Apply with $q=1-\delta$.
Since overlap is at least matched mass and matched mass is $1-u_m$, we get:


$$\operatorname{ov}(P^m(i,\cdot),P^m(j,\cdot))
\ge
1-(1-\delta)^m
-
\delta\sum_{t=0}^{m-1}
(1-\delta)^{m-(t+1)}e_t.$$


So the final deterministic theorem is:
leantheorem iter_window_overlap  (hδpos : 0 < δ)  (hδle : δ ≤ 1)  (hminor :    ∀ x y, Good W x y →      δ ≤ ∑ z, min (P x z) (P y z))  (hbad :    ∀ t < m,      badMass W P i j t ≤ e t) :  overlap (Ppow P m i) (Ppow P m j)    ≥  1 - (1 - δ)^m    - δ * ∑ t in Finset.range m,        (1 - δ)^(m - (t+1)) * e t
That is the ITER lemma.

7. What (A) is actually used for
(A) does not prove the ITER algebra. It is only used to prove the analytic side condition


$$b_t=\text{unmatched mass outside the rank window}\le e_t.$$


So the architecture should be:
(A) + rank-decrement asymptotics        ⟹ window-visit / bad-mass bound(B_W)        ⟹ one-step coalescence inside windowfinite-sum ITER        ⟹ m-step overlap
Do not mix these layers.
The analytic lemma should look like:
leantheorem badMass_small  :  ∀ t < m,    badMass W P i j t ≤ e t
or the weaker aggregate version:


$$\sum_{t<m} b_t\le E.$$


Then the scalar estimate gives


$$u_m\le (1-\delta)^m+\delta E,$$


hence


$$\operatorname{ov}(P^m(i,\cdot),P^m(j,\cdot))
\ge
1-(1-\delta)^m-\delta E.$$


This aggregate version is often easier.

8. Answer to the four concrete questions
1. Equal-rank coalescence recursion?
The right recursion is not “attempt every step if equal rank.” It is:


$$u_{t+1}\le u_t-\delta g_t,$$


where $g_t$ is unmatched mass inside the rank window. Equivalently,


$$u_{t+1}\le (1-\delta)u_t+\delta b_t.$$


There is no general lower bound on the number of exact-rank encounters from (A)+(B′).
2. Do chains visit equal ranks?
Not reliably. Jumps skip ranks. Exact equality is a lattice hitting event. You need either a local CLT / aperiodicity input or, better, avoid exact equality and use a window.
The deterministic replacement is not “both chains visit every rank.” That is false. The replacement is a window bad-mass estimate:


$$b_t\le e_t.$$


3. Should (B′) be windowed?
Yes. The correct hypothesis is $B_W$:


$$|\operatorname{rnk}x-\operatorname{rnk}y|\le W
\Longrightarrow
\sum_z\min(P(x,z),P(y,z))\ge\delta.$$


This is both sufficient and formalization-friendly.
4. Does deterministic common-minorant induction work?
Yes, but not with $\rho_m$ alone. Use the pair:


$$(\rho_t,U_t).$$


rho_t is the common minorant. U_t tracks unmatched pair mass. The entire proof is finite-sum algebra; no probabilistic coupling library is needed.
The one-line core is:


$$u_{t+1}
=
\sum_{x,y}U_t(x,y)(1-\operatorname{cmass}(x,y))
\le
(1-\delta)u_t+\delta b_t.$$


Everything else is scalar recursion.