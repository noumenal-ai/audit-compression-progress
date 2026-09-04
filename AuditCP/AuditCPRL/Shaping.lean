import AuditCPRL.L0
import AuditCP.FiniteExperts
import RLTheory.MarkovDecisionProcess.MarkovRewardProcess

/-!
# Target 1 — approximate potential-based shaping, with a horizon-decaying ordering error

`AuditCP.cumCP` is unweighted, so a discount cannot enter through the potential (ng1999pbrs).  It enters
through the **index type**: audit `ℕ × S` with `E (t, s) := γ ^ t * Φ s`.  Under that lift
`AuditCP.cumCP_telescope` returns `Φ (s 0) − γ ^ T * Φ (s T)`, which is minus the discounted
potential-based shaping return of Ng–Harada–Russell.

Five consequences, and the last two are where the content is.

* **Single trajectory.**  The measured and true discounted shaping returns differ by at most
  `(1 + γ ^ T) * Δ`, hence by `2Δ` uniformly in `T` and in `γ`.  The `2Δ` half is exactly
  `AuditCP.finite_audit_goodhart` applied through the lift; the `γ ^ T` refinement is not, since
  that theorem charges the same radius at both endpoints (see `AuditCPRL.L0`).
* **Two trajectories from a common start state.**  The start-state estimation error cancels
  identically, leaving `2 * γ ^ T * Δ`, which tends to `0`.  Approximate shaping is therefore
  asymptotically exactly ordering-preserving for **any** finite `Δ`.
* **The gauge.**  Under discount a constant offset of the potential moves the ledger by
  `(1 - γ ^ T) * c`, which is zero exactly at `γ = 1`.  The absolute level of a learned potential is
  therefore measured, and that is why the hypothesis below is the pointwise `AuditCP.UniformDev`
  rather than equality up to a constant.
* **Ranking and Best-of-N.**  A true margin above `2 * γ ^ T * Δ` survives estimation, so `Φ̂`
  returns the true best of a family of candidate trajectories and agrees with `Φ` on every
  consecutive pair a margin covers.  The family index carries no `Fintype`: `Δ` prices the declared
  class and never the candidate family, so no union bound over `N` appears and `N` may be infinite.
* **Where `Δ` comes from.**  `Φ` is a population value and `Φ̂` its Monte-Carlo estimate on one
  shared i.i.d. panel of `n` rollouts per state — common random numbers, which is the native form of
  `AuditCP.finite_experts_iid_badEvent_le` rather than an extra assumption.  At
  `candidates := states` that route makes `AuditCP.UniformDev` a theorem with probability `1 - δ` at
  `Δ = (b - a) * √(log (2 |F| / δ) / (2 n))`, and both shaping bounds become probability statements
  over the panel law.  Nothing about the accuracy of the learned potential is assumed.

## Which RLTheory hypotheses bit

`ReinforcementLearning.FiniteMRP` carries `hγ : 0 ≤ γ ∧ γ < 1`.  All three parts of that field are
consumed and none is assumed:

* `MRP.hγ.1 : 0 ≤ γ` and `MRP.hγ.2.le : γ ≤ 1` discharge the `AuditCP.UniformDev` transfer to the
  lifted class (`shapePot_uniformDev`), so the audit hypothesis is a *theorem* about the MRP;
* `MRP.hγ.1` again gives `0 ≤ γ ^ T`, which is what makes the terminal radius `γ ^ T * Δ` a radius;
* `MRP.hγ.2 : γ < 1` is load-bearing in `approx_shaping_slack_tendsto` and in `abs_mrpReturn_le`,
  where it is what makes the return range finite and horizon-free, and nowhere else.

`MRP.M.init : ProbabilityMeasure S` discharges `Nonempty S` in the two panel theorems, so the
candidate type of the finite-experts route is inhabited by the binder rather than by a hypothesis.

Deleting the `MRP` binder from any theorem below forces re-adding `0 ≤ γ` (and, for the last one,
`γ < 1`) as hypotheses.  The binder discharges hypotheses; it is not decoration.

`ReinforcementLearning.FiniteMRP.r : S → ℝ` admits no successor-state argument, so no shaping term
is ever installed into the reward field.  For a fixed trajectory the base-reward discounted return
is the same real number under `Φ̂` and `Φ`, so it cancels in every difference below and the
statements are about total shaped returns.  The `r` field is never written — deliberately.  It is
*read* in exactly one place, `mrpReturn`, where it supplies the audited loss whose range prices the
panel; RLTheory carries no return functional, so that definition is made here.

-/

namespace AuditCPRL

open AuditCP ReinforcementLearning

universe u

/-! ### The lift.  No RL and no audit yet: this is the bridge definition alone.

These four carry no `S` instance: the lift, the telescope and the two transfer lemmas are
instance-free, and only the crossovers below need `ReinforcementLearning.FiniteMRP`'s carrier
instances. -/

section Lift
variable {S : Type u}

/-- The time-augmented potential on `ℕ × S`, `fun (t, s) => γ ^ t * Φ s` (ng1999pbrs). -/
noncomputable def shapePot (γ : ℝ) (Φ : S → ℝ) : ℕ × S → ℝ := fun ts => γ ^ ts.1 * Φ ts.2

/-- `cumCP (shapePot γ Φ) (fun t => (t, traj t)) T + ∑_{t<T} γ^t · (γ · Φ (traj (t+1)) -
Φ (traj t)) = 0`. -/
theorem cumCP_shapePot_add_shapingReturn (γ : ℝ) (Φ : S → ℝ) (traj : ℕ → S) (T : ℕ) :
    cumCP (shapePot γ Φ) (fun t => (t, traj t)) T
      + ∑ t ∈ Finset.range T, γ ^ t * (γ * Φ (traj (t + 1)) - Φ (traj t)) = 0 := by
  simp only [cumCP, shapePot, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun t _ => by rw [pow_succ]; ring

/-- `cumCP (shapePot γ Φ) (fun t => (t, traj t)) T = Φ (traj 0) - γ^T * Φ (traj T)`. -/
theorem cumCP_shapePot_endpoints (γ : ℝ) (Φ : S → ℝ) (traj : ℕ → S) (T : ℕ) :
    cumCP (shapePot γ Φ) (fun t => (t, traj t)) T = Φ (traj 0) - γ ^ T * Φ (traj T) := by
  rw [cumCP_telescope]; simp [shapePot]

/-- `cumCP (shapePot γ (fun s => Φ s + c)) (fun t => (t, traj t)) T =
cumCP (shapePot γ Φ) (fun t => (t, traj t)) T + (1 - γ^T) * c` (ng1999pbrs). -/
theorem cumCP_shapePot_const_shift (γ : ℝ) (Φ : S → ℝ) (c : ℝ) (traj : ℕ → S) (T : ℕ) :
    cumCP (shapePot γ (fun s => Φ s + c)) (fun t => (t, traj t)) T
      = cumCP (shapePot γ Φ) (fun t => (t, traj t)) T + (1 - γ ^ T) * c := by
  rw [cumCP_shapePot_endpoints, cumCP_shapePot_endpoints]; ring

/-- `cumCP (shapePot 1 (fun s => Φ s + c)) (fun t => (t, traj t)) T =
cumCP (shapePot 1 Φ) (fun t => (t, traj t)) T`. -/
theorem cumCP_shapePot_const_shift_one (Φ : S → ℝ) (c : ℝ) (traj : ℕ → S) (T : ℕ) :
    cumCP (shapePot 1 (fun s => Φ s + c)) (fun t => (t, traj t)) T
      = cumCP (shapePot 1 Φ) (fun t => (t, traj t)) T := by
  simpa using cumCP_shapePot_const_shift 1 Φ c traj T

/-- If `0 ≤ γ ≤ 1` and `UniformDev F Φhat Φ Δ`, then
`UniformDev {ts | ts.2 ∈ F} (shapePot γ Φhat) (shapePot γ Φ) Δ`. -/
theorem shapePot_uniformDev {F : Set S} {Φ Φhat : S → ℝ} {Δ γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hUD : UniformDev F Φhat Φ Δ) :
    UniformDev {ts : ℕ × S | ts.2 ∈ F} (shapePot γ Φhat) (shapePot γ Φ) Δ := by
  rintro ⟨t, s⟩ hs
  have hp : |γ ^ t| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hγ0 t)]; exact pow_le_one₀ hγ0 hγ1
  have hre : shapePot γ Φhat (t, s) - shapePot γ Φ (t, s) = γ ^ t * (Φhat s - Φ s) := by
    simp only [shapePot]; ring
  rw [hre, abs_mul]
  calc |γ ^ t| * |Φhat s - Φ s| ≤ 1 * Δ :=
        mul_le_mul hp (hUD s hs) (abs_nonneg _) zero_le_one
    _ = Δ := one_mul Δ

/-- If `Admissible traj F`, then `Admissible (fun t => (t, traj t)) {ts | ts.2 ∈ F}`. -/
theorem shapePot_admissible {F : Set S} {traj : ℕ → S} (hadm : Admissible traj F) :
    Admissible (fun t => (t, traj t)) {ts : ℕ × S | ts.2 ∈ F} :=
  fun t => hadm t

end Lift

/-! ### The crossovers.  `ReinforcementLearning.FiniteMRP` enters here and discharges hypotheses. -/

section Crossover
variable {S : Type u} [Fintype S] [DecidableEq S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- If `UniformDev F Φhat Φ Δ` and `Admissible traj F`, then
`cumCP (shapePot MRP.γ Φhat) (fun t => (t, traj t)) T ≤
cumCP (shapePot MRP.γ Φ) (fun t => (t, traj t)) T + 2Δ` (ng1999pbrs). -/
theorem approx_shaping_goodhart (MRP : FiniteMRP (S := S))
    {F : Set S} {Φ Φhat : S → ℝ} {Δ : ℝ} (hUD : UniformDev F Φhat Φ Δ)
    {traj : ℕ → S} (hadm : Admissible traj F) (T : ℕ) :
    cumCP (shapePot MRP.γ Φhat) (fun t => (t, traj t)) T
      ≤ cumCP (shapePot MRP.γ Φ) (fun t => (t, traj t)) T + 2 * Δ :=
  finite_audit_goodhart (shapePot_uniformDev MRP.hγ.1 MRP.hγ.2.le hUD)
    (shapePot_admissible hadm) T

/-- If `UniformDev F Φhat Φ Δ` and `Admissible traj F`, then
`|cumCP (shapePot MRP.γ Φhat) (fun t => (t, traj t)) T -
cumCP (shapePot MRP.γ Φ) (fun t => (t, traj t)) T| ≤ (1 + MRP.γ^T) * Δ`. -/
theorem approx_shaping_single (MRP : FiniteMRP (S := S))
    {F : Set S} {Φ Φhat : S → ℝ} {Δ : ℝ} (hUD : UniformDev F Φhat Φ Δ)
    {traj : ℕ → S} (hadm : Admissible traj F) (T : ℕ) :
    |cumCP (shapePot MRP.γ Φhat) (fun t => (t, traj t)) T
       - cumCP (shapePot MRP.γ Φ) (fun t => (t, traj t)) T| ≤ (1 + MRP.γ ^ T) * Δ := by
  have hp : (0 : ℝ) ≤ MRP.γ ^ T := pow_nonneg MRP.hγ.1 T
  have h0 : |shapePot MRP.γ Φhat (0, traj 0) - shapePot MRP.γ Φ (0, traj 0)| ≤ Δ := by
    have hre : shapePot MRP.γ Φhat (0, traj 0) - shapePot MRP.γ Φ (0, traj 0)
        = Φhat (traj 0) - Φ (traj 0) := by simp only [shapePot]; ring
    rw [hre]; exact hUD (traj 0) (hadm 0)
  have hT : |shapePot MRP.γ Φhat (T, traj T) - shapePot MRP.γ Φ (T, traj T)| ≤ MRP.γ ^ T * Δ := by
    have hre : shapePot MRP.γ Φhat (T, traj T) - shapePot MRP.γ Φ (T, traj T)
        = MRP.γ ^ T * (Φhat (traj T) - Φ (traj T)) := by simp only [shapePot]; ring
    rw [hre, abs_mul, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left (hUD (traj T) (hadm T)) hp
  have hkey := abs_cumCP_sub_cumCP_le_of_endpoints
    (Ehat := shapePot MRP.γ Φhat) (E := shapePot MRP.γ Φ)
    (g := fun t => (t, traj t)) (T := T) h0 hT
  calc |cumCP (shapePot MRP.γ Φhat) (fun t => (t, traj t)) T
         - cumCP (shapePot MRP.γ Φ) (fun t => (t, traj t)) T| ≤ Δ + MRP.γ ^ T * Δ := hkey
    _ = (1 + MRP.γ ^ T) * Δ := by ring

/-- If `UniformDev F Φhat Φ Δ`, `Admissible traj F`, `Admissible traj' F`, and `traj 0 = traj' 0`,
then the measured and true shaped-return gaps between `traj` and `traj'` at horizon `T` agree to
within `2 · MRP.γ^T · Δ` (ng1999pbrs). -/
theorem approx_shaping_pairwise (MRP : FiniteMRP (S := S))
    {F : Set S} {Φ Φhat : S → ℝ} {Δ : ℝ} (hUD : UniformDev F Φhat Φ Δ)
    {traj traj' : ℕ → S} (hadm : Admissible traj F) (hadm' : Admissible traj' F)
    (hstart : traj 0 = traj' 0) (T : ℕ) :
    |(cumCP (shapePot MRP.γ Φhat) (fun t => (t, traj t)) T
        - cumCP (shapePot MRP.γ Φhat) (fun t => (t, traj' t)) T)
      - (cumCP (shapePot MRP.γ Φ) (fun t => (t, traj t)) T
        - cumCP (shapePot MRP.γ Φ) (fun t => (t, traj' t)) T)|
      ≤ 2 * MRP.γ ^ T * Δ := by
  have hp : (0 : ℝ) ≤ MRP.γ ^ T := pow_nonneg MRP.hγ.1 T
  rw [cumCP_shapePot_endpoints, cumCP_shapePot_endpoints,
      cumCP_shapePot_endpoints, cumCP_shapePot_endpoints, hstart]
  have hkey :
      ((Φhat (traj' 0) - MRP.γ ^ T * Φhat (traj T))
          - (Φhat (traj' 0) - MRP.γ ^ T * Φhat (traj' T)))
        - ((Φ (traj' 0) - MRP.γ ^ T * Φ (traj T))
          - (Φ (traj' 0) - MRP.γ ^ T * Φ (traj' T)))
        = MRP.γ ^ T * ((Φ (traj T) - Φhat (traj T)) - (Φ (traj' T) - Φhat (traj' T))) := by
    ring
  have hsplit : 2 * MRP.γ ^ T * Δ = MRP.γ ^ T * (2 * Δ) := by ring
  rw [hkey, abs_mul, abs_of_nonneg hp, hsplit]
  refine mul_le_mul_of_nonneg_left ?_ hp
  have h1 := abs_le.1 (hUD (traj T) (hadm T))
  have h2 := abs_le.1 (hUD (traj' T) (hadm' T))
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- If `UniformDev F Φhat Φ Δ`, `Admissible traj F`, `Admissible traj' F`, `traj 0 = traj' 0`, and
the true shaped-return gap between `traj` and `traj'` exceeds `2 · MRP.γ^T · Δ`, then the measured
shaped-return gap between them is positive. -/
theorem approx_shaping_order_preserved (MRP : FiniteMRP (S := S))
    {F : Set S} {Φ Φhat : S → ℝ} {Δ : ℝ} (hUD : UniformDev F Φhat Φ Δ)
    {traj traj' : ℕ → S} (hadm : Admissible traj F) (hadm' : Admissible traj' F)
    (hstart : traj 0 = traj' 0) (T : ℕ)
    (htrue : cumCP (shapePot MRP.γ Φ) (fun t => (t, traj t)) T
        - cumCP (shapePot MRP.γ Φ) (fun t => (t, traj' t)) T > 2 * MRP.γ ^ T * Δ) :
    cumCP (shapePot MRP.γ Φhat) (fun t => (t, traj t)) T
      - cumCP (shapePot MRP.γ Φhat) (fun t => (t, traj' t)) T > 0 := by
  have h := abs_le.1 (approx_shaping_pairwise MRP hUD hadm hadm' hstart T)
  linarith [h.1]

/-- If `UniformDev F Φhat Φ Δ`, every candidate `cand k` is admissible for `F` and shares a common
start state, and `cand k₀`'s true shaped return beats every other candidate's by more than
`2 · MRP.γ^T · Δ` (`hmargin`), then `cand k₀` maximizes the measured shaped return:
`cumCP (shapePot MRP.γ Φhat) (fun t => (t, cand k t)) T ≤
cumCP (shapePot MRP.γ Φhat) (fun t => (t, cand k₀ t)) T` for every `k` (ng1999pbrs). -/
theorem approx_shaping_argmax_preserved (MRP : FiniteMRP (S := S))
    {F : Set S} {Φ Φhat : S → ℝ} {Δ : ℝ} (hUD : UniformDev F Φhat Φ Δ)
    {K : Type*} {cand : K → ℕ → S} (hadm : ∀ k, Admissible (cand k) F)
    (hstart : ∀ k k', cand k 0 = cand k' 0) (T : ℕ) {k₀ : K}
    (hmargin : ∀ k, k ≠ k₀ →
      cumCP (shapePot MRP.γ Φ) (fun t => (t, cand k₀ t)) T
        - cumCP (shapePot MRP.γ Φ) (fun t => (t, cand k t)) T > 2 * MRP.γ ^ T * Δ) (k : K) :
    cumCP (shapePot MRP.γ Φhat) (fun t => (t, cand k t)) T
      ≤ cumCP (shapePot MRP.γ Φhat) (fun t => (t, cand k₀ t)) T := by
  by_cases hk : k = k₀
  · exact le_of_eq (by rw [hk])
  · have h := approx_shaping_order_preserved MRP hUD (hadm k₀) (hadm k)
      (hstart k₀ k) T (hmargin k hk)
    linarith

/-- If `UniformDev F Φhat Φ Δ`, every candidate `cand k` is admissible for `F` and shares a common
start state, and consecutive true shaped returns along `rank` decrease by more than
`2 · MRP.γ^T · Δ` at every step (`hgap`), then the measured shaped returns along `rank` are also
strictly decreasing. -/
theorem approx_shaping_ranking_preserved (MRP : FiniteMRP (S := S))
    {F : Set S} {Φ Φhat : S → ℝ} {Δ : ℝ} (hUD : UniformDev F Φhat Φ Δ)
    {K : Type*} {cand : K → ℕ → S} (hadm : ∀ k, Admissible (cand k) F)
    (hstart : ∀ k k', cand k 0 = cand k' 0) (T : ℕ) (rank : ℕ → K)
    (hgap : ∀ i, cumCP (shapePot MRP.γ Φ) (fun t => (t, cand (rank i) t)) T
        - cumCP (shapePot MRP.γ Φ) (fun t => (t, cand (rank (i + 1)) t)) T
          > 2 * MRP.γ ^ T * Δ) (i : ℕ) :
    cumCP (shapePot MRP.γ Φhat) (fun t => (t, cand (rank (i + 1)) t)) T
      < cumCP (shapePot MRP.γ Φhat) (fun t => (t, cand (rank i) t)) T := by
  have h := approx_shaping_order_preserved MRP hUD (hadm (rank i)) (hadm (rank (i + 1)))
    (hstart (rank i) (rank (i + 1))) T (hgap i)
  linarith

/-- `Tendsto (fun T => 2 * MRP.γ^T * Δ) atTop (nhds 0)`. -/
theorem approx_shaping_slack_tendsto (MRP : FiniteMRP (S := S)) (Δ : ℝ) :
    Filter.Tendsto (fun T : ℕ => 2 * MRP.γ ^ T * Δ) Filter.atTop (nhds 0) := by
  simpa using
    (((tendsto_pow_atTop_nhds_zero_of_lt_one MRP.hγ.1 MRP.hγ.2).const_mul (2 : ℝ)).mul_const Δ)

end Crossover

/-! ### The panel.  `Δ` stops being a hypothesis: the potential is a value estimate trained on a
shared i.i.d. rollout panel, and its uniform deviation is priced by the state count. -/

section Panel
variable {S : Type u} [Fintype S] [DecidableEq S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

open MeasureTheory

/-- The `H`-step discounted return of the rollout `roll s z` from state `s`,
`∑_{t<H} MRP.γ^t · MRP.r (roll s z t)`. -/
noncomputable def mrpReturn (MRP : FiniteMRP (S := S)) {Z : Type*}
    (roll : S → Z → ℕ → S) (H : ℕ) (s : S) (z : Z) : ℝ :=
  ∑ t ∈ Finset.range H, MRP.γ ^ t * MRP.r (roll s z t)

/-- `∃ Rmax, 0 ≤ Rmax ∧ ∀ s, |MRP.r s| ≤ Rmax`. -/
theorem exists_rewardBound (MRP : FiniteMRP (S := S)) :
    ∃ Rmax : ℝ, 0 ≤ Rmax ∧ ∀ s, |MRP.r s| ≤ Rmax :=
  ⟨∑ s, |MRP.r s|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun s => Finset.single_le_sum (f := fun s => |MRP.r s|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)⟩

/-- If `|MRP.r s| ≤ Rmax` for every `s`, then `|mrpReturn MRP roll H s z| ≤ Rmax / (1 - MRP.γ)`. -/
theorem abs_mrpReturn_le (MRP : FiniteMRP (S := S)) {Z : Type*}
    (roll : S → Z → ℕ → S) (H : ℕ) (s : S) (z : Z) {Rmax : ℝ}
    (hR : ∀ s, |MRP.r s| ≤ Rmax) :
    |mrpReturn MRP roll H s z| ≤ Rmax / (1 - MRP.γ) := by
  have hγ0 : (0 : ℝ) ≤ MRP.γ := MRP.hγ.1
  have hone : (0 : ℝ) < 1 - MRP.γ := by have := MRP.hγ.2; linarith
  have hR0 : (0 : ℝ) ≤ Rmax := le_trans (abs_nonneg _) (hR s)
  have hsum : ∑ t ∈ Finset.range H, MRP.γ ^ t ≤ 1 / (1 - MRP.γ) := by
    rw [le_div_iff₀ hone, geom_sum_mul_neg]
    have : (0 : ℝ) ≤ MRP.γ ^ H := pow_nonneg hγ0 H
    linarith
  simp only [mrpReturn]
  calc |∑ t ∈ Finset.range H, MRP.γ ^ t * MRP.r (roll s z t)|
      ≤ ∑ t ∈ Finset.range H, |MRP.γ ^ t * MRP.r (roll s z t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range H, MRP.γ ^ t * Rmax := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
        exact mul_le_mul_of_nonneg_left (hR _) (pow_nonneg hγ0 t)
    _ = (∑ t ∈ Finset.range H, MRP.γ ^ t) * Rmax := by rw [Finset.sum_mul]
    _ ≤ (1 / (1 - MRP.γ)) * Rmax := mul_le_mul_of_nonneg_right hsum hR0
    _ = Rmax / (1 - MRP.γ) := by ring

/-- If `roll s · t` is measurable for every `s` and `t`, then `mrpReturn MRP roll H s` is
measurable. -/
theorem measurable_mrpReturn (MRP : FiniteMRP (S := S)) {Z : Type*} [MeasurableSpace Z]
    (roll : S → Z → ℕ → S) (hroll : ∀ s t, Measurable fun z => roll s z t) (H : ℕ) (s : S) :
    Measurable (mrpReturn MRP roll H s) := by
  show Measurable fun z => ∑ t ∈ Finset.range H, MRP.γ ^ t * MRP.r (roll s z t)
  exact Finset.measurable_sum _ fun t _ =>
    measurable_const.mul ((measurable_of_countable MRP.r).comp (hroll s t))

/-- If `ret` is measurable and a.e. valued in `[a, b]` at every state, then on an i.i.d. panel of
size `n`, with probability at least `1 - δ` the measured and true discounted shaped returns of
`traj` under the panel-trained potential agree to within
`2 · deltaFiniteExperts (card S) n (b - a) δ` at every horizon `T` (ng1999pbrs). -/
theorem shaping_from_panel_trained_potential (MRP : FiniteMRP (S := S))
    {Z : Type*} [MeasurableSpace Z] (Q : Measure Z) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 0 < n) {a b : ℝ} (hab : a < b) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ret : S → Z → ℝ) (hmeas : ∀ s, Measurable (ret s))
    (hbdd : ∀ s, ∀ᵐ z ∂Q, ret s z ∈ Set.Icc a b)
    (traj : ℕ → S) (T : ℕ) :
    Measure.pi (fun _ : Fin n => Q)
        {panel | ¬ |cumCP (shapePot MRP.γ fun s => empiricalLoss ret s panel)
                        (fun t => (t, traj t)) T
                      - cumCP (shapePot MRP.γ (populationLoss Q ret)) (fun t => (t, traj t)) T|
                  ≤ 2 * deltaFiniteExperts (Fintype.card S) n (b - a) δ}
      ≤ ENNReal.ofReal δ := by
  haveI : Nonempty S := MRP.M.init.nonempty
  have hΔ : (0 : ℝ) ≤ deltaFiniteExperts (Fintype.card S) n (b - a) δ := by
    simp only [deltaFiniteExperts]
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hstep : (1 + MRP.γ ^ T) * deltaFiniteExperts (Fintype.card S) n (b - a) δ
      ≤ 2 * deltaFiniteExperts (Fintype.card S) n (b - a) δ :=
    mul_le_mul_of_nonneg_right
      (by have := pow_le_one₀ MRP.hγ.1 MRP.hγ.2.le (n := T); linarith) hΔ
  refine le_trans (measure_mono ?_)
    (finite_experts_iid_badEvent_le (ι := S) Q n hn a b hab δ hδ0 hδ1 ret hmeas hbdd)
  intro panel hpanel
  simp only [Set.mem_setOf_eq] at hpanel ⊢
  intro hUD
  exact hpanel (le_trans
    (approx_shaping_single MRP hUD (fun t => Set.mem_univ (traj t)) T) hstep)

/-- If `ret` is measurable and a.e. valued in `[a, b]` at every state and `traj 0 = traj' 0`, then
on an i.i.d. panel of size `n`, with probability at least `1 - δ` the measured and true
shaped-return gaps between `traj` and `traj'` under the panel-trained potential agree to within
`2 · MRP.γ^T · deltaFiniteExperts (card S) n (b - a) δ` at every horizon `T`. -/
theorem shaping_pairwise_from_panel_trained_potential (MRP : FiniteMRP (S := S))
    {Z : Type*} [MeasurableSpace Z] (Q : Measure Z) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 0 < n) {a b : ℝ} (hab : a < b) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ret : S → Z → ℝ) (hmeas : ∀ s, Measurable (ret s))
    (hbdd : ∀ s, ∀ᵐ z ∂Q, ret s z ∈ Set.Icc a b)
    (traj traj' : ℕ → S) (hstart : traj 0 = traj' 0) (T : ℕ) :
    Measure.pi (fun _ : Fin n => Q)
        {panel | ¬ |(cumCP (shapePot MRP.γ fun s => empiricalLoss ret s panel)
                          (fun t => (t, traj t)) T
                        - cumCP (shapePot MRP.γ fun s => empiricalLoss ret s panel)
                          (fun t => (t, traj' t)) T)
                      - (cumCP (shapePot MRP.γ (populationLoss Q ret)) (fun t => (t, traj t)) T
                        - cumCP (shapePot MRP.γ (populationLoss Q ret))
                          (fun t => (t, traj' t)) T)|
                  ≤ 2 * MRP.γ ^ T * deltaFiniteExperts (Fintype.card S) n (b - a) δ}
      ≤ ENNReal.ofReal δ := by
  haveI : Nonempty S := MRP.M.init.nonempty
  refine le_trans (measure_mono ?_)
    (finite_experts_iid_badEvent_le (ι := S) Q n hn a b hab δ hδ0 hδ1 ret hmeas hbdd)
  intro panel hpanel
  simp only [Set.mem_setOf_eq] at hpanel ⊢
  intro hUD
  exact hpanel (approx_shaping_pairwise MRP hUD (fun t => Set.mem_univ (traj t))
    (fun t => Set.mem_univ (traj' t)) hstart T)

end Panel

end AuditCPRL
