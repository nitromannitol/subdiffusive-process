module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedExteriorL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedSource

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.Frozen.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-! ## 1. A point at exact distance -/

/-- In the project supremum metric on `Vec d` every nonnegative radius is
attained. -/
theorem exists_dist_eq_of_nonneg (x0 : Vec d) {R : ℝ}
    (hR : 0 ≤ R) : ∃ z : Vec d, dist z x0 = R := by
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  refine ⟨fun i ↦ x0 i + R, ?_⟩
  have hcoord : ∀ i : Fin d, dist ((fun i ↦ x0 i + R) i) (x0 i) = R := by
    intro i
    simp [abs_of_nonneg hR]
  have hle : dist (fun i ↦ x0 i + R) x0 ≤ R :=
    (dist_pi_le_iff hR).mpr (fun i ↦ le_of_eq (hcoord i))
  have hge : R ≤ dist (fun i ↦ x0 i + R) x0 := by
    have h := dist_le_pi_dist (fun i ↦ x0 i + R) x0 (Classical.arbitrary (Fin d))
    rwa [hcoord] at h
  linarith

/-! ## 2. The refutation at bracket zero -/

/-- **The every-bracket short-crossing certificate is false.**

For the canonical source family a short crossing always exists at `k = 0`: take
a point `z` at distance exactly `R` from `x0`.  It lies outside
`Metric.ball x0 (3 ^ 0 * R)` and inside `Metric.closedBall x0 R`, so any refined
cell containing it both meets the exterior and belongs to the source, whence its
graph distance is `0 < ⌈epsilon⌉₊`.

Consequently no theorem may assume
`∀ k, ¬ RepairedStoppingShortCrossing (repairedStoppingSourceCells …) … k`; the
usable form is the bracket-restricted one of §4. -/
theorem repairedStoppingShortCrossing_zero
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) {R epsilon : ℝ} (hR : 0 < R) (heps : 0 < epsilon) :
    RepairedStoppingShortCrossing
      (repairedStoppingSourceCells hinitial hrepair x0 R)
      (repairedStoppingSourceCells_nonempty hinitial hrepair x0 hR.le)
      x0 R epsilon 0 := by
  classical
  obtain ⟨z, hz⟩ := exists_dist_eq_of_nonneg (d := d) x0 hR.le
  have hcover := iUnion_refinedStoppingCell_eq_univ failure omega hinitial hrepair
  have hzmem : z ∈ ⋃ q : RefinedStoppingCell failure omega base,
      translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) := by
    rw [hcover]; trivial
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hzmem
  have hzEnlarged : z ∈ translatedCube d (refinedStoppingScale q + 1)
      (refinedStoppingCenter q) :=
    translatedCube_subset_translatedCube_sameCenter (by omega)
      (refinedStoppingCenter q) hq
  have hsourceMem : q ∈ repairedStoppingSourceCells hinitial hrepair x0 R := by
    refine (mem_repairedStoppingSourceCells_iff hinitial hrepair x0 R q).mpr ?_
    exact ⟨z, hzEnlarged, Metric.mem_closedBall.mpr hz.le⟩
  have hradius : ((3 : ℝ) ^ (0 : ℕ)) * R = R := by norm_num
  have hzout : z ∈ (Metric.ball x0 ((3 : ℝ) ^ (0 : ℕ) * R))ᶜ := by
    rw [Set.mem_compl_iff, Metric.mem_ball, hradius, hz]
    exact lt_irrefl R
  refine ⟨q, ⟨z, hq, hzout⟩, ?_⟩
  rw [stoppingGraphDistance_eq_zero_of_mem _ _ hsourceMem]
  refine Nat.ceil_pos.mpr ?_
  simpa using heps

/-! ## 3. Triadic brackets above a fixed height -/

private theorem exists_three_pow_bracket_aux {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    ∃ k : ℕ, (3 : ℝ) ^ k * R ≤ r ∧ r < (3 : ℝ) ^ (k + 1) * R := by
  classical
  have hP : ∃ n : ℕ, r < (3 : ℝ) ^ (n + 1) * R := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (r / R) (by norm_num : (1 : ℝ) < 3)
    refine ⟨n, ?_⟩
    have h1 : r < (3 : ℝ) ^ n * R := by
      rw [div_lt_iff₀ hR] at hn
      exact hn
    have h3 : (0 : ℝ) < (3 : ℝ) ^ n := pow_pos (by norm_num) n
    have h2 : (3 : ℝ) ^ n * R < (3 : ℝ) ^ (n + 1) * R := by
      have hlt : (3 : ℝ) ^ n < (3 : ℝ) ^ (n + 1) := by
        rw [pow_succ]
        nlinarith
      exact mul_lt_mul_of_pos_right hlt hR
    linarith
  refine ⟨Nat.find hP, ?_, Nat.find_spec hP⟩
  rcases Nat.eq_zero_or_pos (Nat.find hP) with hk0 | hkpos
  · rw [hk0]
    simpa using hr
  · have hmin := Nat.find_min hP (m := Nat.find hP - 1) (by omega)
    have hk : Nat.find hP - 1 + 1 = Nat.find hP := by omega
    rw [hk] at hmin
    exact not_lt.mp hmin

/-- Every radius at least `3 ^ K R` lies in a triadic bracket of height at
least `K`. -/
theorem exists_three_pow_bracket_ge {R r : ℝ} {K : ℕ} (hR : 0 < R)
    (hr : (3 : ℝ) ^ K * R ≤ r) :
    ∃ k : ℕ, K ≤ k ∧ (3 : ℝ) ^ k * R ≤ r ∧ r < (3 : ℝ) ^ (k + 1) * R := by
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hRr : R ≤ r := le_trans (by nlinarith) hr
  obtain ⟨k, hk1, hk2⟩ := exists_three_pow_bracket_aux hR hRr
  refine ⟨k, ?_, hk1, hk2⟩
  by_contra hlt
  push_neg at hlt
  have hkK : k + 1 ≤ K := hlt
  have hpow : (3 : ℝ) ^ (k + 1) ≤ (3 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkK
  have hle : (3 : ℝ) ^ (k + 1) * R ≤ (3 : ℝ) ^ K * R := by nlinarith
  linarith

/-! ## 4. The exterior row from the bracket-restricted certificate -/

/-- **The exterior conjunct of `WholeSpaceRows` from the bracket-restricted
short-crossing certificate.**

This is `wholeSpaceSolution_exterior_row_of_repaired_stopping_cells_of_constants`
with the every-bracket hypothesis — refuted by
`repairedStoppingShortCrossing_zero` — replaced by the certificate at the
brackets `k ≥ K`, and the conclusion correspondingly quantified over
`r ≥ 3 ^ K R` instead of `r ≥ R`.  Since `WholeSpaceRows` quantifies its
exterior bound over `r ≥ Rstar omega` for a *random* `Rstar` with
`R ≤ Rstar omega`, the witness `Rstar omega := 3 ^ K omega * R` is admissible;
`ogammaLE_log_wholeSpaceDecayRadius` converts a geometric tail on `K` into the
required `O_{Γ₁}` control of `log (Rstar / R)`. -/
theorem wholeSpaceSolution_exterior_row_of_repaired_stopping_cells_of_bracket
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsourceNonempty : source.Nonempty) (x0 : Vec d)
    {R epsilon c C : ℝ} {K : ℕ}
    (hR : 0 < R) (heps : 0 < epsilon)
    (hc : c ≤ epsilon * Real.log 2 / 3)
    (hC : 2 * ((stoppingGraphLevelCells repairedStoppingGraph source
      hsourceNonempty 0).card : ℝ) ≤ C)
    (hgood : ∀ k : ℕ, K ≤ k → ¬ RepairedStoppingShortCrossing source
      hsourceNonempty x0 R epsilon k)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
        ∫ x in translatedCube d (refinedStoppingScale q)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
        repairedStoppingContractionFactor d *
          ∫ x in translatedCube d (refinedStoppingScale q + 1)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume) :
    ∀ r, (3 : ℝ) ^ K * R ≤ r →
      ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
        C * Real.exp (-c * r / R) * ∫ x, f x ^ 2 ∂volume := by
  classical
  intro r hr
  obtain ⟨k, hkK, hk1, hk2⟩ := exists_three_pow_bracket_ge hR hr
  set N : ℝ := ((stoppingGraphLevelCells repairedStoppingGraph source
    hsourceNonempty 0).card : ℝ) with hNdef
  set F : ℝ := ∫ x, f x ^ 2 ∂volume with hFdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ F := integral_nonneg fun x ↦ sq_nonneg _
  have hbase := wholeSpaceSolution_exterior_decay_of_repaired_stopping_cells_of_l2
    u hL2 hinitial hrepair source hsourceNonempty x0 R epsilon k (hgood k hkK)
    hcell
  have hsub : (Metric.ball x0 r)ᶜ ⊆ (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ :=
    Set.compl_subset_compl.mpr (Metric.ball_subset_ball hk1)
  have hmono : (∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume) ≤
      ∫ x in (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_mono_set u.memL2_toFun.integrable_sq.restrict ?_
      (HasSubset.Subset.eventuallyLE hsub)
    exact Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := pow_pos (by norm_num) k
  have hrRpos : (0 : ℝ) ≤ r / R := by
    have : (0 : ℝ) ≤ r := le_trans (by positivity) hr
    exact div_nonneg this hR.le
  have hrR : r / R < 3 * (3 : ℝ) ^ k := by
    rw [div_lt_iff₀ hR]
    have hpow : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by
      rw [pow_succ]; ring
    rw [hpow] at hk2
    exact hk2
  have hexpArg : Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k) ≤
      -c * r / R := by
    have hlogval : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    have hcoef : (0 : ℝ) ≤ epsilon * Real.log 2 / 3 :=
      div_nonneg (mul_nonneg heps.le hlog2.le) (by norm_num)
    have hstep1 : c * (r / R) ≤ epsilon * Real.log 2 / 3 * (r / R) :=
      mul_le_mul_of_nonneg_right hc hrRpos
    have hstep2 : epsilon * Real.log 2 / 3 * (r / R) ≤
        epsilon * Real.log 2 / 3 * (3 * (3 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left hrR.le hcoef
    have hdiv : -c * r / R = -(c * (r / R)) := by field_simp
    rw [hlogval, hdiv]
    nlinarith [hstep1, hstep2]
  have hexp : Real.exp (Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k)) ≤
      Real.exp (-c * r / R) := Real.exp_le_exp.mpr hexpArg
  have hprod : N * F * (1 - (1 / 2 : ℝ))⁻¹ *
        Real.exp (Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k)) ≤
      C * Real.exp (-c * r / R) * F := by
    have hhalf : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    rw [hhalf]
    have hfront : (0 : ℝ) ≤ N * F * 2 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hexp hfront
    have hC0 : (0 : ℝ) ≤ C := le_trans (by positivity) hC
    have hE0 : (0 : ℝ) ≤ Real.exp (-c * r / R) := (Real.exp_pos _).le
    have hlast : N * F * 2 * Real.exp (-c * r / R) ≤
        C * Real.exp (-c * r / R) * F := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC hE0) hF0
      nlinarith [this]
    exact hstep.trans hlast
  exact hmono.trans (hbase.trans hprod)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
