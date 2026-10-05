
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCarrierLegs

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## 1. The triadic bracket of a radius -/

/-- Every radius at least `R` lies in a triadic bracket above `R`. -/
theorem exists_three_pow_bracket {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
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

/-! ## 2. The exterior row -/

/-- **The exterior row of `WholeSpaceRows`, from the repaired stopping
partition.**

`wholeSpaceSolution_exterior_decay_of_repaired_stopping_cells_of_l2` bounds the
exterior mass at the radii `3^k R`; the mass outside a ball only decreases with
the radius, so an arbitrary `r ≥ R` is handled by the largest bracket below it,
at the cost of a factor `3` in the exponential rate.  The conclusion is verbatim
the first conjunct of the almost-sure clause of `WholeSpaceRows`, at
`Rstar = R`. -/
theorem wholeSpaceSolution_exterior_row_of_repaired_stopping_cells
    [NeZero d] {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsourceNonempty : source.Nonempty) (x0 : Vec d) {R epsilon : ℝ}
    (hR : 0 < R) (heps : 0 < epsilon)
    (hgood : ∀ k : ℕ, ¬ RepairedStoppingShortCrossing source hsourceNonempty
      x0 R epsilon k)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
        ∫ x in translatedCube d (refinedStoppingScale q)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
        repairedStoppingContractionFactor d *
          ∫ x in translatedCube d (refinedStoppingScale q + 1)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume) :
    ∀ r, R ≤ r →
      ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
        (2 * ((stoppingGraphLevelCells repairedStoppingGraph source
            hsourceNonempty 0).card : ℝ)) *
          Real.exp (-(epsilon * Real.log 2 / 3) * r / R) *
          ∫ x, f x ^ 2 ∂volume := by
  classical
  intro r hr
  obtain ⟨k, hk1, hk2⟩ := exists_three_pow_bracket hR hr
  set N : ℝ := ((stoppingGraphLevelCells repairedStoppingGraph source
    hsourceNonempty 0).card : ℝ) with hNdef
  set F : ℝ := ∫ x, f x ^ 2 ∂volume with hFdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ F := integral_nonneg fun x ↦ sq_nonneg _
  have hbase := wholeSpaceSolution_exterior_decay_of_repaired_stopping_cells_of_l2
    u hL2 hinitial hrepair source hsourceNonempty x0 R epsilon k (hgood k) hcell
  -- the exterior mass only decreases with the radius
  have hsub : (Metric.ball x0 r)ᶜ ⊆ (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ :=
    Set.compl_subset_compl.mpr (Metric.ball_subset_ball hk1)
  have hmono : (∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume) ≤
      ∫ x in (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_mono_set u.memL2_toFun.integrable_sq.restrict ?_
      (LE.le.eventuallySubset hsub)
    exact Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  -- the exponential comparison
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := pow_pos (by norm_num) k
  have hrR : r / R < 3 * (3 : ℝ) ^ k := by
    rw [div_lt_iff₀ hR]
    have hpow : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by
      rw [pow_succ]; ring
    rw [hpow] at hk2
    exact hk2
  have hcoef : (0 : ℝ) ≤ epsilon * Real.log 2 / 3 :=
    div_nonneg (mul_nonneg heps.le hlog2.le) (by norm_num)
  have hexpArg : Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k) ≤
      -(epsilon * Real.log 2 / 3) * r / R := by
    have hlogval : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    have hstep : epsilon * Real.log 2 / 3 * (r / R) ≤
        epsilon * Real.log 2 / 3 * (3 * (3 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left hrR.le hcoef
    have heq : epsilon * Real.log 2 / 3 * (3 * (3 : ℝ) ^ k) =
        Real.log 2 * (epsilon * (3 : ℝ) ^ k) := by ring
    have hdiv : -(epsilon * Real.log 2 / 3) * r / R =
        -(epsilon * Real.log 2 / 3 * (r / R)) := by
      field_simp
    rw [hlogval, hdiv]
    linarith
  have hexp : Real.exp (Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k)) ≤
      Real.exp (-(epsilon * Real.log 2 / 3) * r / R) := Real.exp_le_exp.mpr hexpArg
  have hE0 : (0 : ℝ) ≤ Real.exp (Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k)) :=
    (Real.exp_pos _).le
  have hprod : N * F * (1 - (1 / 2 : ℝ))⁻¹ *
        Real.exp (Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k)) ≤
      2 * N * Real.exp (-(epsilon * Real.log 2 / 3) * r / R) * F := by
    have hhalf : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    rw [hhalf]
    have hfront : (0 : ℝ) ≤ N * F * 2 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hexp hfront
    calc N * F * 2 *
          Real.exp (Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k))
        ≤ N * F * 2 * Real.exp (-(epsilon * Real.log 2 / 3) * r / R) := hstep
      _ = 2 * N * Real.exp (-(epsilon * Real.log 2 / 3) * r / R) * F := by ring
  exact hmono.trans (hbase.trans hprod)

/-- **The exterior row with free constants.**

`WholeSpaceRows` fixes one pair `(c, C)` for the whole model, so the row must be
available for any `C` above `2 · #(level 0)` and any rate `c` below
`ε log 2 / 3`.  Both directions are monotone. -/
theorem wholeSpaceSolution_exterior_row_of_repaired_stopping_cells_of_constants
    [NeZero d] {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsourceNonempty : source.Nonempty) (x0 : Vec d) {R epsilon c C : ℝ}
    (hR : 0 < R) (heps : 0 < epsilon)
    (hc : c ≤ epsilon * Real.log 2 / 3)
    (hC : 2 * ((stoppingGraphLevelCells repairedStoppingGraph source
      hsourceNonempty 0).card : ℝ) ≤ C)
    (hgood : ∀ k : ℕ, ¬ RepairedStoppingShortCrossing source hsourceNonempty
      x0 R epsilon k)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
        ∫ x in translatedCube d (refinedStoppingScale q)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
        repairedStoppingContractionFactor d *
          ∫ x in translatedCube d (refinedStoppingScale q + 1)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume) :
    ∀ r, R ≤ r →
      ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
        C * Real.exp (-c * r / R) * ∫ x, f x ^ 2 ∂volume := by
  classical
  intro r hr
  set N : ℝ := ((stoppingGraphLevelCells repairedStoppingGraph source
    hsourceNonempty 0).card : ℝ) with hNdef
  set F : ℝ := ∫ x, f x ^ 2 ∂volume with hFdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ F := integral_nonneg fun x ↦ sq_nonneg _
  have hbase := wholeSpaceSolution_exterior_row_of_repaired_stopping_cells u hL2
    hinitial hrepair source hsourceNonempty x0 hR heps hgood hcell r hr
  refine hbase.trans ?_
  have hrR : (0 : ℝ) ≤ r / R := div_nonneg (le_trans hR.le hr) hR.le
  have hexpArg : -(epsilon * Real.log 2 / 3) * r / R ≤ -c * r / R := by
    have hstep : (epsilon * Real.log 2 / 3 - c) * (r / R) * (-1) ≤ 0 := by
      nlinarith [hrR, sub_nonneg.mpr hc]
    have hL : -(epsilon * Real.log 2 / 3) * r / R =
        -(epsilon * Real.log 2 / 3) * (r / R) := by field_simp
    have hRr : -c * r / R = -c * (r / R) := by field_simp
    rw [hL, hRr]
    nlinarith [hrR, sub_nonneg.mpr hc]
  have hexp : Real.exp (-(epsilon * Real.log 2 / 3) * r / R) ≤
      Real.exp (-c * r / R) := Real.exp_le_exp.mpr hexpArg
  have hE0 : (0 : ℝ) ≤ Real.exp (-(epsilon * Real.log 2 / 3) * r / R) :=
    (Real.exp_pos _).le
  have hstep1 : 2 * N * Real.exp (-(epsilon * Real.log 2 / 3) * r / R) * F ≤
      C * Real.exp (-(epsilon * Real.log 2 / 3) * r / R) * F :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC hE0) hF0
  have hC0 : (0 : ℝ) ≤ C := le_trans (by positivity) hC
  have hstep2 : C * Real.exp (-(epsilon * Real.log 2 / 3) * r / R) * F ≤
      C * Real.exp (-c * r / R) * F :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC0) hF0
  exact hstep1.trans hstep2

/-- **The exterior row from the local coarse contraction.**

`wholeSpaceSolution_translatedCube_mass_contraction_of_local` discharges the
per-cell hypothesis from the contraction proved for every local solution on the
enlargement — the form
`massive_local_l2_translatedCube_coarse_contraction_of_cells` produces — so this
is the row conjunct directly from the mesoscopic analysis. -/
theorem wholeSpaceSolution_exterior_row_of_coarse_stopping_cells
    [NeZero d] {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsourceNonempty : source.Nonempty) (x0 : Vec d) {R epsilon c C : ℝ}
    (hR : 0 < R) (heps : 0 < epsilon)
    (hc : c ≤ epsilon * Real.log 2 / 3)
    (hC : 2 * ((stoppingGraphLevelCells repairedStoppingGraph source
      hsourceNonempty 0).card : ℝ) ≤ C)
    (hgood : ∀ k : ℕ, ¬ RepairedStoppingShortCrossing source hsourceNonempty
      x0 R epsilon k)
    (hquiet : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
        ∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q), f x = 0)
    (hlocal : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
        ∀ v : H1Function (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q)),
          IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
            (translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q)) v (fun _ ↦ (0 : ℝ)) →
          (∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), v.toFun x ^ 2 ∂volume) ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), v.toFun x ^ 2 ∂volume) :
    ∀ r, R ≤ r →
      ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
        C * Real.exp (-c * r / R) * ∫ x, f x ^ 2 ∂volume :=
  wholeSpaceSolution_exterior_row_of_repaired_stopping_cells_of_constants u hL2
    hinitial hrepair source hsourceNonempty x0 hR heps hc hC hgood
    (fun q hq ↦ wholeSpaceSolution_translatedCube_mass_contraction_of_local u
      (hquiet q hq) (hlocal q hq))

/-! ## 3. The two numerical side conditions of the anchor -/

/-- The rate produced by §2 is positive, which is the `hc` hypothesis of
`whole_space_resolvent_estimates_of_rows`. -/
theorem exterior_row_rate_pos {epsilon : ℝ} (heps : 0 < epsilon) :
    0 < epsilon * Real.log 2 / 3 := by
  have h2 : (1:ℝ) < 2 := by norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos h2
  have h := mul_pos heps hlog
  exact div_pos h (by norm_num)

/-- The rate produced by §2 is below the constant, which is the `hcC`
hypothesis of `whole_space_resolvent_estimates_of_rows`.  A short-crossing
density `epsilon ≤ 1` and a nonempty level-zero set are all that is needed. -/
theorem exterior_row_rate_le_const {epsilon N : ℝ}
    (heps1 : epsilon ≤ 1) (hN : 1 ≤ N) :
    epsilon * Real.log 2 / 3 ≤ 2 * N := by
  have hlog1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlogpos : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  nlinarith [mul_le_mul heps1 hlog1.le hlogpos (by norm_num : (0:ℝ) ≤ 1), hN]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
