import SubdiffusiveProcess.Probability.Diffusion.Packet452DoobInputs
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic




set_option autoImplicit false

open MeasureTheory Filter Set

open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## The abstract `L²` maximal inequality -/

/-- **Doob's `L²` maximal inequality, abstract form, constant `4`.**  If a nonnegative measurable
`S` satisfies the *weak* maximal inequality `t·μ{S ≥ t} ≤ ∫_{S ≥ t} g` on every positive level,
against a nonnegative measurable `g`, then `‖S‖₂² ≤ 4‖g‖₂²`.

This is the only place where the `L²` constant is produced; `maximal_ineq` supplies the hypothesis
`hweak` and nothing else. -/
theorem lintegral_sq_le_of_weak_maximal [IsFiniteMeasure μ] {S g : Ω → ℝ}
    (hSmble : Measurable S) (hSnn : ∀ ω, 0 ≤ S ω)
    (hgmble : Measurable g) (hgnn : ∀ ω, 0 ≤ g ω)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t ≤ S ω} ≤
      ∫⁻ ω in {ω | t ≤ S ω}, ENNReal.ofReal (g ω) ∂μ) :
    ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ := by
  classical
  set B : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ with hBdef
  have hgennmble : Measurable fun ω => ENNReal.ofReal (g ω) := hgmble.ennreal_ofReal
  -- Hölder at `p = q = 2`, in the `Pi.mul_apply`-free form.
  have holder : ∀ F G : Ω → ℝ≥0∞, AEMeasurable F μ → AEMeasurable G μ →
      ∫⁻ ω, F ω * G ω ∂μ ≤
        (∫⁻ ω, F ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ ω, G ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro F G hF hG
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hF hG
    simpa only [Pi.mul_apply] using h
  -- The bound for the truncation `S ⊓ M`.
  have key : ∀ M : ℝ, 0 ≤ M → ∫⁻ ω, ENNReal.ofReal (min (S ω) M ^ 2) ∂μ ≤ 4 * B := by
    intro M hM
    set T : Ω → ℝ := fun ω => min (S ω) M with hTdef
    have hTmble : Measurable T := hSmble.min measurable_const
    have hTnn : ∀ ω, 0 ≤ T ω := fun ω => le_min (hSnn ω) hM
    have hTle : ∀ ω, T ω ≤ M := fun ω => min_le_right _ _
    have hTset : ∀ t : ℝ, MeasurableSet {ω | t ≤ T ω} := fun t =>
      measurableSet_le measurable_const hTmble
    -- The weak inequality survives the truncation.
    have hweakT : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t ≤ T ω} ≤
        ∫⁻ ω in {ω | t ≤ T ω}, ENNReal.ofReal (g ω) ∂μ := by
      intro t ht
      rcases le_or_gt t M with htM | htM
      · have hset : {ω | t ≤ T ω} = {ω | t ≤ S ω} := by
          ext ω; simp [hTdef, htM]
        rw [hset]; exact hweak t ht
      · have hset : {ω | t ≤ T ω} = (∅ : Set Ω) := by
          ext ω
          simp only [hTdef, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact lt_of_le_of_lt (min_le_right _ _) htM
        simp [hset]
    -- The tilted measure that turns the inner set integral into a measure of the same set.
    set ν : Measure Ω := μ.withDensity (fun ω => ENNReal.ofReal (g ω)) with hνdef
    have hνset : ∀ t : ℝ, ν {ω | t ≤ T ω} = ∫⁻ ω in {ω | t ≤ T ω}, ENNReal.ofReal (g ω) ∂μ :=
      fun t => withDensity_apply _ (hTset t)
    -- Layer cake for `T` under `μ`, with `g t = 2t` (primitive `t²`).
    have hlayer : ∫⁻ ω, ENNReal.ofReal (T ω ^ 2) ∂μ
        = ∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ T ω} * ENNReal.ofReal (2 * t) := by
      have hprim : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, 2 * t = x ^ 2 := by
        intro x
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      have h := MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul (μ := μ) (f := T)
        (g := fun t => 2 * t) (Eventually.of_forall hTnn) hTmble.aemeasurable
        (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
        ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall (fun t ht => by simp only [Set.mem_Ioi] at ht; linarith)))
      simpa only [hprim] using h
    -- Layer cake for `T` under `ν`: this is what replaces the Tonelli swap.
    have hlayerν : ∫⁻ t in Ioi (0 : ℝ), ν {ω | t ≤ T ω} = ∫⁻ ω, ENNReal.ofReal (T ω) ∂ν :=
      (lintegral_eq_lintegral_meas_le ν (Eventually.of_forall hTnn) hTmble.aemeasurable).symm
    have hνmul : ∫⁻ ω, ENNReal.ofReal (T ω) ∂ν
        = ∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (T ω) ∂μ := by
      rw [hνdef, lintegral_withDensity_eq_lintegral_mul μ hgennmble hTmble.ennreal_ofReal]
      simp only [Pi.mul_apply]
    -- Squares as `rpow 2`, for Hölder.
    have hsqg : ∀ ω, ENNReal.ofReal (g ω) ^ (2 : ℝ) = ENNReal.ofReal (g ω ^ 2) := by
      intro ω
      rw [ENNReal.ofReal_rpow_of_nonneg (hgnn ω) (by norm_num)]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hsqT : ∀ ω, ENNReal.ofReal (T ω) ^ (2 : ℝ) = ENNReal.ofReal (T ω ^ 2) := by
      intro ω
      rw [ENNReal.ofReal_rpow_of_nonneg (hTnn ω) (by norm_num)]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    set A : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (T ω ^ 2) ∂μ with hAdef
    -- The main chain.
    have main : A ≤ 2 * (B ^ (1 / (2 : ℝ)) * A ^ (1 / (2 : ℝ))) := by
      calc A = ∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ T ω} * ENNReal.ofReal (2 * t) := hlayer
        _ ≤ ∫⁻ t in Ioi (0 : ℝ), 2 * ν {ω | t ≤ T ω} := by
            refine setLIntegral_mono' measurableSet_Ioi ?_
            intro t ht
            have ht0 : (0 : ℝ) < t := ht
            have hofReal : ENNReal.ofReal (2 * t) = 2 * ENNReal.ofReal t := by
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
              norm_num
            rw [hofReal, hνset t]
            calc μ {ω | t ≤ T ω} * (2 * ENNReal.ofReal t)
                = 2 * (ENNReal.ofReal t * μ {ω | t ≤ T ω}) := by ring
              _ ≤ 2 * ∫⁻ ω in {ω | t ≤ T ω}, ENNReal.ofReal (g ω) ∂μ :=
                  mul_le_mul_right (hweakT t ht0) 2
        _ = 2 * ∫⁻ t in Ioi (0 : ℝ), ν {ω | t ≤ T ω} := by
            rw [lintegral_const_mul' 2 _ (by norm_num)]
        _ = 2 * ∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (T ω) ∂μ := by
            rw [hlayerν, hνmul]
        _ ≤ 2 * (B ^ (1 / (2 : ℝ)) * A ^ (1 / (2 : ℝ))) := by
            refine mul_le_mul_right ?_ 2
            refine le_trans (holder _ _ hgennmble.aemeasurable
              hTmble.ennreal_ofReal.aemeasurable) ?_
            simp only [hsqg, hsqT]
            rw [← hBdef, ← hAdef]
    -- `A` is finite: this is the whole point of the truncation.
    have hAfin : A ≠ ⊤ := by
      have hle : A ≤ ENNReal.ofReal (M ^ 2) * μ Set.univ := by
        calc A ≤ ∫⁻ _, ENNReal.ofReal (M ^ 2) ∂μ := by
              refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
              nlinarith [hTnn ω, hTle ω]
          _ = ENNReal.ofReal (M ^ 2) * μ Set.univ := by rw [lintegral_const]
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)) hle
    rcases eq_or_ne A 0 with hA0 | hA0
    · rw [hA0]; exact zero_le _
    have ha0 : A ^ (1 / (2 : ℝ)) ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hA0, hAfin]
    have hatop : A ^ (1 / (2 : ℝ)) ≠ ⊤ := by
      simp [ENNReal.rpow_eq_top_iff, hA0, hAfin]
    have hsq : A ^ (1 / (2 : ℝ)) * A ^ (1 / (2 : ℝ)) = A := by
      rw [← ENNReal.rpow_add _ _ hA0 hAfin]
      norm_num
    have hstep : A ^ (1 / (2 : ℝ)) * A ^ (1 / (2 : ℝ))
        ≤ 2 * B ^ (1 / (2 : ℝ)) * A ^ (1 / (2 : ℝ)) := by
      rw [hsq, mul_assoc]
      exact main
    have hroot : A ^ (1 / (2 : ℝ)) ≤ 2 * B ^ (1 / (2 : ℝ)) :=
      (ENNReal.mul_le_mul_iff_left ha0 hatop).mp hstep
    have hfour : (2 : ℝ≥0∞) ^ (2 : ℝ) = 4 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      norm_num
    calc A = (A ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by
          rw [← ENNReal.rpow_mul]
          norm_num
      _ ≤ (2 * B ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hroot (by norm_num)
      _ = (2 : ℝ≥0∞) ^ (2 : ℝ) * (B ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = 4 * B := by
          rw [hfour, ← ENNReal.rpow_mul]
          norm_num
  -- Monotone convergence `M → ∞`.
  have hmeas : ∀ m : ℕ, Measurable fun ω => ENNReal.ofReal (min (S ω) (m : ℝ) ^ 2) :=
    fun m => (((hSmble.min measurable_const).pow_const 2).ennreal_ofReal)
  have hmono : Monotone fun (m : ℕ) (ω : Ω) => ENNReal.ofReal (min (S ω) (m : ℝ) ^ 2) := by
    intro m m' hmm ω
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : min (S ω) (m : ℝ) ≤ min (S ω) (m' : ℝ) :=
      min_le_min le_rfl (by exact_mod_cast hmm)
    have h0 : 0 ≤ min (S ω) (m : ℝ) := le_min (hSnn ω) (Nat.cast_nonneg m)
    nlinarith
  have hsup : ∀ ω, ⨆ m : ℕ, ENNReal.ofReal (min (S ω) (m : ℝ) ^ 2)
      = ENNReal.ofReal (S ω ^ 2) := by
    intro ω
    refine le_antisymm (iSup_le fun m => ENNReal.ofReal_le_ofReal ?_) ?_
    · have h0 : 0 ≤ min (S ω) (m : ℝ) := le_min (hSnn ω) (Nat.cast_nonneg m)
      have h1 : min (S ω) (m : ℝ) ≤ S ω := min_le_left _ _
      nlinarith
    · obtain ⟨m, hm⟩ := exists_nat_ge (S ω)
      exact le_iSup_of_le m (by rw [min_eq_left hm])
  calc ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ
      = ∫⁻ ω, ⨆ m : ℕ, ENNReal.ofReal (min (S ω) (m : ℝ) ^ 2) ∂μ := by simp_rw [hsup]
    _ = ⨆ m : ℕ, ∫⁻ ω, ENNReal.ofReal (min (S ω) (m : ℝ) ^ 2) ∂μ := lintegral_iSup hmeas hmono
    _ ≤ 4 * B := iSup_le fun m => key m (Nat.cast_nonneg m)

/-! ## The submartingale instance -/

/-- **Doob's `L²` maximal inequality for a nonnegative submartingale**, constant `4`, on the
finite grid `{0, …, n}`.  Mathlib supplies only the weak form (`MeasureTheory.maximal_ineq`); this
is the strong form derived from it. -/
theorem lintegral_sq_gridSup_le [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => f k ω) ^ 2) ∂μ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂μ := by
  have hfmble : ∀ k, Measurable (f k) := fun k =>
    ((hsub.stronglyMeasurable k).mono (𝒢.le k)).measurable
  refine lintegral_sq_le_of_weak_maximal (S := fun ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one fun k => f k ω) (g := f n)
    (Finset.measurable_range_sup'' fun k _ => hfmble k) ?_ (hfmble n) (fun ω => hnonneg n ω) ?_
  · intro ω
    exact le_trans (hnonneg 0 ω) (Finset.le_sup' (fun k => f k ω) (by simp))
  · intro t ht
    have h := MeasureTheory.maximal_ineq hsub hnonneg (ε := t.toNNReal) n
    rw [Real.coe_toNNReal t ht.le, ENNReal.smul_def, smul_eq_mul] at h
    have hcoe : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := rfl
    rw [hcoe] at h
    refine h.trans_eq ?_
    refine ofReal_integral_eq_lintegral_ofReal ((hsub.integrable n).restrict) ?_
    exact Eventually.of_forall fun ω => hnonneg n ω

/-- **The form the Dynkin martingale needs.**  For a martingale `M` sampled along a monotone grid
`σ`, the running maximum of `|M|` over `{σ 0, …, σ n}` satisfies the `L²` bound with constant `4`.
The hypotheses are exactly what `Martingale.abs_grid_submartingale` produces. -/
theorem lintegral_sq_sup_abs_le [IsFiniteMeasure μ] {ι : Type*} [Preorder ι] {ℱ : Filtration ι m0}
    {M : ι → Ω → ℝ} (hM : Martingale M ℱ μ) (σ : ℕ → ι) (hσ : Monotone σ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => |M (σ k) ω|) ^ 2) ∂μ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (M (σ n) ω ^ 2) ∂μ := by
  have h := Martingale.abs_grid_submartingale hM σ hσ
  have hmain := lintegral_sq_gridSup_le h.1 h.2 n
  simpa only [sq_abs] using hmain

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
