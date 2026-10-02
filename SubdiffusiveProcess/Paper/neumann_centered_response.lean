import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
import SubdiffusiveProcess.Sobolev.CompactResponses
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.cor_14
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.in_normalization
import SubdiffusiveProcess.Paper.coefficient_physical_identity
import SubdiffusiveProcess.Paper.in_common_scale_coupling
import SubdiffusiveProcess.Paper.physical_scale_dictionary
import SubdiffusiveProcess.Paper.neumann_response_defect_transport


open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

lemma aux_neumann_centered_response_reindex
    {d : ℕ} (N : ℕ) (om eta : BilateralField d) (x : SpatialCoordinates d)
    (h : ∀ i : ℤ, ∀ y : SpatialCoordinates d,
      eta i y = om (i - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) :
    (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) =
      ∑ j ∈ Finset.range (N + 1), (eta (j : ℤ)) ((3 : ℝ) ^ N • x) := by
  calc
    _ = ∑ j ∈ Finset.range (N + 1),
        (eta (N - j : ℕ)) ((3 : ℝ) ^ N • x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [h]
      have hjN : j ≤ N := by
        have hjlt : j < N + 1 := Finset.mem_range.mp hj
        omega
      have hidx : ((N - j : ℕ) : ℤ) - (N : ℤ) = -(j : ℤ) := by
        rw [Int.ofNat_sub hjN]
        ring
      rw [hidx]
      congr 1
      ext k
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc]
      rw [← zpow_natCast]
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp
    _ = _ := by
      exact Finset.sum_range_reflect
        (fun j => (eta (j : ℤ)) ((3 : ℝ) ^ N • x)) (N + 1)

lemma aux_neumann_centered_response_cutoff_val
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (G : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) :
    ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M G om N (fun _ => (1 / 2 : ℝ)) one_pos).val x =
        cutoffCoefficient M G om N x := by
  letI : Fact ((centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Set (SpatialCoordinates d)) ⊆
      (↑(closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube (fun _ => (1 / 2 : ℝ)) one_pos⟩
  filter_upwards [normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
    (closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos)
    (cutoffCoefficientCM M G om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (cutoffCoefficientCM_pos M G om N (fun _ => (1 / 2 : ℝ)) one_pos)
    1 one_pos, ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with x hx hxQ
  have h := hx hxQ
  change (normalizedContinuousPositiveCoefficient
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
      (cutoffCoefficientCM M G om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
      (cutoffCoefficientCM_pos M G om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
      1 one_pos).val x = cutoffCoefficient M G om N x
  rw [h]
  simp [cutoffCoefficientCM, cutoffCoefficient]

lemma aux_neumann_centered_response_cutoff_compact
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (G : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ)
    (K : Compacts (SpatialCoordinates d))
    [Fact ((unitNeumannCube d : Set (SpatialCoordinates d)) ⊆ (K : Set (SpatialCoordinates d)))] :
    cutoffPositiveCoefficient M G om N (fun _ => (1 / 2 : ℝ)) one_pos =
      expPotentialCoefficient (compactPotentialToLp (Ω := unitNeumannCube d) K
        ((G om).restrict (K : Set (SpatialCoordinates d)) +
          (∑ j ∈ Finset.range (N + 1),
            (om (-(j : ℤ))).restrict (K : Set (SpatialCoordinates d))) +
          ContinuousMap.const K
            (-((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
              Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)))) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [aux_neumann_centered_response_cutoff_val M G om N,
    expPotentialCoefficient_coeFn
      (compactPotentialToLp (Ω := unitNeumannCube d) K
        ((G om).restrict (K : Set (SpatialCoordinates d)) +
          (∑ j ∈ Finset.range (N + 1),
            (om (-(j : ℤ))).restrict (K : Set (SpatialCoordinates d))) +
          ContinuousMap.const K
            (-((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
              Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)))),
    compactPotentialToLp_on_domain (Ω := unitNeumannCube d) K _,
    ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with x hx0 hxexp hxA hxQ
  rw [hx0, hxexp, hxA hxQ]
  dsimp [cutoffCoefficient]
  have hahom : (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ =
      Real.exp (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)) := by
    rw [Real.exp_neg, Real.exp_log (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)]
  rw [hahom, ← Real.exp_add]
  congr 1
  simp only [ContinuousMap.coe_sum, Finset.sum_apply]
  change -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
      ((G om) x + ∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x -
        ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
    (G om) x + ∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x +
      (-((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
        Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))
  ring

/-- Measurability in the environment of the inverse response at the cutoff coefficient. -/
theorem aux_neumann_centered_response_meas
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (G : BilateralField d → C(SpatialCoordinates d, ℝ)) (hG : Measurable G)
    (Sp : ResponseSpace (unitNeumannCube d)) (L : Sp.space →L[ℝ] ℝ) (N : ℕ) :
    Measurable (fun om : BilateralField d =>
      inverseResponse Sp
        (cutoffPositiveCoefficient M G om N (fun _ => (1 / 2 : ℝ)) one_pos) L) := by
  set Kroot : Compacts (SpatialCoordinates d) :=
    closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos with hKdef
  haveI : Fact ((unitNeumannCube d : Set (SpatialCoordinates d)) ⊆
      (Kroot : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube (fun _ => (1 / 2 : ℝ)) one_pos⟩
  letI : MeasurableSpace C(Kroot, ℝ) := borel _
  letI : BorelSpace C(Kroot, ℝ) := ⟨rfl⟩
  set A : BilateralField d → C(Kroot, ℝ) := fun om =>
    (G om).restrict (Kroot : Set (SpatialCoordinates d)) +
      (∑ j ∈ Finset.range (N + 1),
        (om (-(j : ℤ))).restrict (Kroot : Set (SpatialCoordinates d))) +
      ContinuousMap.const Kroot
        (-((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
          Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)) with hAdef
  have hAmeas : Measurable A := by
    rw [hAdef]
    refine Measurable.add (Measurable.add ?_ ?_) measurable_const
    · exact (ContinuousMap.continuous_restrict
        (Kroot : Set (SpatialCoordinates d))).measurable.comp hG
    · refine Finset.measurable_sum _ fun j _ => ?_
      exact (ContinuousMap.continuous_restrict
        (Kroot : Set (SpatialCoordinates d))).measurable.comp
        (measurable_pi_apply (-(j : ℤ)))
  have hfun : (fun om : BilateralField d =>
      inverseResponse Sp
        (cutoffPositiveCoefficient M G om N (fun _ => (1 / 2 : ℝ)) one_pos) L) =
      fun om => inverseResponse Sp
        (expPotentialCoefficient (compactPotentialToLp Kroot (A om))) L := by
    funext om
    rw [aux_neumann_centered_response_cutoff_compact M G om N Kroot]
  rw [hfun]
  exact (continuous_inverseResponse_compact Sp Kroot L).measurable.comp hAmeas

/-- The samplewise two-sided infrared comparison of the two inverse responses. -/
theorem aux_neumann_centered_response_compare
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Sp : ResponseSpace (unitNeumannCube d)) (L : Sp.space →L[ℝ] ℝ)
    (om : BilateralField d) (N : ℕ) (Sbound : ℝ)
    (hbound : ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      |H om x| ≤ Sbound) :
    |inverseResponse Sp
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) L -
        inverseResponse Sp
          (cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ => (1 / 2 : ℝ)) one_pos) L| ≤
      (Real.exp Sbound - 1) *
        inverseResponse Sp
          (cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ => (1 / 2 : ℝ)) one_pos) L := by
  have h0 := aux_neumann_centered_response_cutoff_val M (fun _ => 0) om N
  have h1 := aux_neumann_centered_response_cutoff_val M H om N
  have hi : 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ :=
    inv_nonneg.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).le
  have hlo : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      Real.exp (-Sbound) *
          (cutoffPositiveCoefficient M (fun _ => 0) om N
            (fun _ => (1 / 2 : ℝ)) one_pos).val x ≤
        (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos).val x := by
    filter_upwards [h0, h1, ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet]
      with x hx0 hx1 hxQ
    rw [hx0, hx1, cutoffCoefficient, cutoffCoefficient, cutoffPotential, cutoffPotential]
    have hh := hbound x hxQ
    have he : Real.exp (-Sbound) *
          Real.exp ((∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
            ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
        Real.exp (H om x + (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
          ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
      rw [← Real.exp_add]
      apply Real.exp_monotone
      linarith [abs_le.mp hh]
    calc
      Real.exp (-Sbound) *
            ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
              Real.exp ((0 : ℝ) + (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
                ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) =
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            (Real.exp (-Sbound) *
              Real.exp ((∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
                ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
              simp only [zero_add]; ring
      _ ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            Real.exp (H om x + (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
              ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) :=
            mul_le_mul_of_nonneg_left he hi
  have hup : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos).val x ≤
        Real.exp Sbound *
          (cutoffPositiveCoefficient M (fun _ => 0) om N
            (fun _ => (1 / 2 : ℝ)) one_pos).val x := by
    filter_upwards [h0, h1, ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet]
      with x hx0 hx1 hxQ
    rw [hx0, hx1, cutoffCoefficient, cutoffCoefficient, cutoffPotential, cutoffPotential]
    have hh := hbound x hxQ
    have he : Real.exp (H om x + (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
          ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
        Real.exp Sbound *
          Real.exp ((∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
            ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
      rw [← Real.exp_add]
      apply Real.exp_monotone
      linarith [abs_le.mp hh]
    calc
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            Real.exp (H om x + (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
              ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            (Real.exp Sbound *
              Real.exp ((∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
                ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) :=
            mul_le_mul_of_nonneg_left he hi
      _ = Real.exp Sbound *
            ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
              Real.exp ((0 : ℝ) + (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) -
                ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
              simp only [zero_add]; ring
  have hcmp := inverseResponse_exp_comparison Sp
    (cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) L Sbound hlo hup
  have hy0 : 0 ≤ inverseResponse Sp
      (cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ => (1 / 2 : ℝ)) one_pos) L :=
    inverseResponse_nonneg _ _ _
  have hleft : 1 - Real.exp (-Sbound) ≤ Sbound := by
    have h := Real.add_one_le_exp (-Sbound)
    linarith
  have hright : Sbound ≤ Real.exp Sbound - 1 := by
    have h := Real.add_one_le_exp Sbound
    linarith
  have hmul := mul_le_mul_of_nonneg_right (hleft.trans hright) hy0
  rw [abs_le]
  constructor
  · linarith [hcmp.1, hmul]
  · linarith [hcmp.2]

theorem aux_neumann_centered_response_exp_sub_one_le (t : ℝ) :
    Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hmul : (1 - Real.exp (-t)) * Real.exp t ≤ t * Real.exp t :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  have hinv : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [hmul, hinv]

theorem aux_neumann_centered_response_rpow_le_exp (t r lam : ℝ)
    (ht : 0 ≤ t) (hr : 0 < r) (hlam : 0 < lam) :
    t ^ r ≤ (r / (Real.exp 1 * lam)) ^ r * Real.exp (lam * t) := by
  have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hApos : 0 < r / (Real.exp 1 * lam) := by positivity
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, Real.zero_rpow hr.ne']
    positivity
  · rw [Real.rpow_def_of_pos h, Real.rpow_def_of_pos hApos, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hkey : Real.log (lam * t / r) ≤ lam * t / r - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hlog : Real.log (lam * t / r) = Real.log lam + Real.log t - Real.log r := by
      rw [Real.log_div (by positivity) hr.ne', Real.log_mul hlam.ne' h.ne']
    have hlogA : Real.log (r / (Real.exp 1 * lam)) =
        Real.log r - 1 - Real.log lam := by
      rw [Real.log_div hr.ne' (by positivity), Real.log_mul he1.ne' hlam.ne',
        Real.log_exp]
      ring
    rw [hlogA]
    rw [hlog] at hkey
    have h2 := mul_le_mul_of_nonneg_left hkey hr.le
    have h3 : r * (lam * t / r - 1) = lam * t - r := by field_simp
    rw [h3] at h2
    linarith

/-- Sub-Gaussian exponential-moment input gives an `L^r` bound of order `delta` for
`exp X - 1`, for a nonnegative `X`. -/
theorem aux_neumann_centered_response_expX_norm
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Omega → ℝ) (hX0 : ∀ om, 0 ≤ X om)
    (Cq : ℝ) (hCq : 0 ≤ Cq) (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hMGF : ∀ lam : ℝ, 0 ≤ lam →
      Integrable (fun om => Real.exp (lam * X om)) P ∧
      (∫ om, Real.exp (lam * X om) ∂P) ≤ 2 * Real.exp (Cq * lam ^ 2 * delta ^ 2))
    (r : ℝ) (hr : 1 ≤ r) :
    eLpNorm (fun om => Real.exp (X om) - 1) (ENNReal.ofReal r) P ≤
      ENNReal.ofReal
        (2 * Real.sqrt r * Real.exp (Cq * (Real.sqrt r + r) ^ 2) * delta) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  set lam : ℝ := Real.sqrt r / delta with hlamdef
  have hlam : 0 < lam := by positivity
  set A : ℝ := r / (Real.exp 1 * lam) with hAdef
  have hApos : 0 < A := by positivity
  set B : ℝ := 2 * Real.sqrt r * Real.exp (Cq * (Real.sqrt r + r) ^ 2) * delta with hBdef
  have hBpos : 0 < B := by positivity
  have hss : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
  have hlammul : lam * delta = Real.sqrt r := by
    rw [hlamdef]; field_simp
  have hexp1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hprod : delta * Real.sqrt r * (Real.exp 1 * lam) = Real.exp 1 * r := by
    have h1 : delta * Real.sqrt r * (Real.exp 1 * lam)
        = Real.exp 1 * Real.sqrt r * (lam * delta) := by ring
    rw [h1, hlammul, mul_assoc, hss]
  have hAle : A ≤ delta * Real.sqrt r := by
    rw [hAdef, div_le_iff₀ (by positivity), hprod]
    nlinarith [hr0.le, hexp1]
  -- pointwise bound
  have hnn : ∀ om, (0 : ℝ) ≤ Real.exp (X om) - 1 := by
    intro om
    have := Real.add_one_le_exp (X om)
    linarith [hX0 om]
  have hpt : ∀ om, (Real.exp (X om) - 1) ^ r ≤ A ^ r * Real.exp ((lam + r) * X om) := by
    intro om
    have h2 : Real.exp (X om) - 1 ≤ X om * Real.exp (X om) :=
      aux_neumann_centered_response_exp_sub_one_le (X om)
    have h4 : (Real.exp (X om) - 1) ^ r ≤ (X om * Real.exp (X om)) ^ r :=
      Real.rpow_le_rpow (hnn om) h2 hr0.le
    refine h4.trans ?_
    have h5 : (X om * Real.exp (X om)) ^ r =
        (X om) ^ r * Real.exp (r * X om) := by
      rw [Real.mul_rpow (hX0 om) (Real.exp_pos _).le]
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      ring_nf
    rw [h5]
    have h6 := aux_neumann_centered_response_rpow_le_exp (X om) r lam (hX0 om) hr0 hlam
    calc
      (X om) ^ r * Real.exp (r * X om) ≤
          (A ^ r * Real.exp (lam * X om)) * Real.exp (r * X om) := by
        exact mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
      _ = A ^ r * Real.exp ((lam + r) * X om) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
  -- integrate
  have hMG := hMGF (lam + r) (by positivity)
  have hlint : (∫⁻ om, ‖Real.exp (X om) - 1‖ₑ ^ r ∂P) ≤
      ENNReal.ofReal (A ^ r * (2 * Real.exp (Cq * (lam + r) ^ 2 * delta ^ 2))) := by
    have hstep1 : (∫⁻ om, ‖Real.exp (X om) - 1‖ₑ ^ r ∂P) ≤
        ∫⁻ om, ENNReal.ofReal (A ^ r * Real.exp ((lam + r) * X om)) ∂P := by
      refine lintegral_mono fun om => ?_
      rw [Real.enorm_eq_ofReal (hnn om),
        ENNReal.ofReal_rpow_of_nonneg (hnn om) hr0.le]
      exact ENNReal.ofReal_le_ofReal (hpt om)
    refine hstep1.trans ?_
    have hAr : (0 : ℝ) ≤ A ^ r := Real.rpow_nonneg hApos.le r
    calc
      (∫⁻ om, ENNReal.ofReal (A ^ r * Real.exp ((lam + r) * X om)) ∂P)
          = ENNReal.ofReal (A ^ r) *
              ∫⁻ om, ENNReal.ofReal (Real.exp ((lam + r) * X om)) ∂P := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun om => ?_
            rw [← ENNReal.ofReal_mul hAr]
      _ = ENNReal.ofReal (A ^ r) *
            ENNReal.ofReal (∫ om, Real.exp ((lam + r) * X om) ∂P) := by
            rw [← ofReal_integral_eq_lintegral_ofReal hMG.1
              (ae_of_all _ fun om => (Real.exp_pos _).le)]
      _ ≤ ENNReal.ofReal (A ^ r) *
            ENNReal.ofReal (2 * Real.exp (Cq * (lam + r) ^ 2 * delta ^ 2)) :=
            mul_le_mul_of_nonneg_left (ENNReal.ofReal_mono hMG.2) (zero_le _)
      _ = ENNReal.ofReal (A ^ r * (2 * Real.exp (Cq * (lam + r) ^ 2 * delta ^ 2))) := by
            rw [← ENNReal.ofReal_mul hAr]
  -- the real arithmetic: A^r * (2 * exp(...)) ≤ B^r
  have hreal : A ^ r * (2 * Real.exp (Cq * (lam + r) ^ 2 * delta ^ 2)) ≤ B ^ r := by
    have hid : (lam + r) * delta = Real.sqrt r + r * delta := by
      have h1 : (lam + r) * delta = lam * delta + r * delta := by ring
      rw [h1, hlammul]
    have hexp : (lam + r) ^ 2 * delta ^ 2 ≤ (Real.sqrt r + r) ^ 2 := by
      have hsq : (lam + r) ^ 2 * delta ^ 2 = (Real.sqrt r + r * delta) ^ 2 := by
        rw [← hid]; ring
      rw [hsq]
      have h1 : Real.sqrt r + r * delta ≤ Real.sqrt r + r := by nlinarith [hr0.le]
      have h0 : (0 : ℝ) ≤ Real.sqrt r + r * delta := by positivity
      nlinarith [h1, h0]
    have hEle : (2 : ℝ) * Real.exp (Cq * (lam + r) ^ 2 * delta ^ 2) ≤
        2 * Real.exp (Cq * (Real.sqrt r + r) ^ 2) := by
      have : Cq * (lam + r) ^ 2 * delta ^ 2 ≤ Cq * (Real.sqrt r + r) ^ 2 := by
        nlinarith [hexp, hCq]
      nlinarith [Real.exp_le_exp.2 this, Real.exp_pos (Cq * (lam + r) ^ 2 * delta ^ 2)]
    set E : ℝ := 2 * Real.exp (Cq * (Real.sqrt r + r) ^ 2) with hEdef
    have hE1 : (1 : ℝ) ≤ E := by
      have : (1 : ℝ) ≤ Real.exp (Cq * (Real.sqrt r + r) ^ 2) :=
        Real.one_le_exp (by positivity)
      linarith
    have hBeq : B = (delta * Real.sqrt r) * E := by rw [hBdef, hEdef]; ring
    have hArle : A ^ r ≤ (delta * Real.sqrt r) ^ r :=
      Real.rpow_le_rpow hApos.le hAle hr0.le
    have hEr : E ≤ E ^ r := by
      nth_rewrite 1 [← Real.rpow_one E]
      exact Real.rpow_le_rpow_of_exponent_le hE1 hr
    calc
      A ^ r * (2 * Real.exp (Cq * (lam + r) ^ 2 * delta ^ 2)) ≤
          (delta * Real.sqrt r) ^ r * E := by
            exact mul_le_mul hArle hEle (by positivity) (Real.rpow_nonneg (by positivity) r)
      _ ≤ (delta * Real.sqrt r) ^ r * E ^ r := by
            exact mul_le_mul_of_nonneg_left hEr (Real.rpow_nonneg (by positivity) r)
      _ = B ^ r := by
            rw [hBeq, ← Real.mul_rpow (x := delta * Real.sqrt r) (y := E)
              (by positivity) (by linarith)]
  -- assemble
  have hne0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr0).ne'
  have hnetop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm hne0 hnetop, ENNReal.toReal_ofReal hr0.le]
  have hfinal : (∫⁻ om, ‖Real.exp (X om) - 1‖ₑ ^ r ∂P) ≤ ENNReal.ofReal (B ^ r) :=
    hlint.trans (ENNReal.ofReal_mono hreal)
  calc
    (∫⁻ om, ‖Real.exp (X om) - 1‖ₑ ^ r ∂P) ^ (1 / r) ≤
        (ENNReal.ofReal (B ^ r)) ^ (1 / r) :=
      ENNReal.rpow_le_rpow hfinal (by positivity)
    _ = ENNReal.ofReal B := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hBpos.le r) (by positivity),
          ← Real.rpow_mul hBpos.le]
        rw [mul_one_div, div_self hr0.ne', Real.rpow_one]

theorem aux_neumann_centered_response_sqrt_mul_sq
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (ENNReal.ofReal (a * t ^ 2)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt a * t) := by
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_pow ht]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  norm_num
  rw [ENNReal.ofReal_rpow_of_nonneg ha (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Real.sqrt_eq_rpow]

/-- From the samplewise matrix-deviation bound and the published defect moment bank,
the centred `L^q` bound of order `delta`. -/
theorem aux_neumann_centered_response_err_norm
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Y D : Omega → ℝ) (hD0 : ∀ om, 0 ≤ D om)
    (Cdev : ℝ) (hCdev : 0 < Cdev)
    (hdev : ∀ᵐ om ∂P, (Y om - 1) ^ 2 ≤ Cdev * D om * (1 + D om))
    (CR : ℝ) (hCR : 0 < CR) (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (qmax : ℝ)
    (hDmem : ∀ xi : ℝ, 1 ≤ xi → xi ≤ qmax → MemLp D (ENNReal.ofReal xi) P)
    (hDnorm : ∀ xi : ℝ, 1 ≤ xi → xi ≤ qmax →
      eLpNorm D (ENNReal.ofReal xi) P ≤
        ENNReal.ofReal (CR * xi * Real.log (2 + xi) * delta ^ 2))
    (q : ℝ) (hq : 2 ≤ q) (hqmax : q ≤ qmax) :
    eLpNorm (fun om => Y om - 1) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal
        (Real.sqrt Cdev *
          (Real.sqrt (CR * q * Real.log (2 + q)) + CR * q * Real.log (2 + q)) * delta) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log (2 + q) := Real.log_pos (by linarith)
  have hlogh : 0 < Real.log (2 + q / 2) := Real.log_pos (by linarith)
  set W : ℝ := CR * q * Real.log (2 + q) with hWdef
  set Wh : ℝ := CR * (q / 2) * Real.log (2 + q / 2) with hWhdef
  have hW0 : 0 < W := by rw [hWdef]; positivity
  have hWh0 : 0 < Wh := by rw [hWhdef]; positivity
  have hWhW : Wh ≤ W := by
    rw [hWhdef, hWdef]
    have h1 : Real.log (2 + q / 2) ≤ Real.log (2 + q) :=
      Real.log_le_log (by linarith) (by linarith)
    nlinarith [hCR.le, hq0.le, hlogh.le]
  -- L^{q/2} membership of D
  have hDmemh : MemLp D (ENNReal.ofReal (q / 2)) P := hDmem (q / 2) (by linarith) (by linarith)
  have hDmemq : MemLp D (ENNReal.ofReal q) P := hDmem q (by linarith) hqmax
  -- sqrt D
  have hsqrt_mem : MemLp (fun om => Real.sqrt (D om)) (ENNReal.ofReal q) P := by
    have hi := (memLp_norm_rpow_iff (p := ENNReal.ofReal (q / 2))
      (q := ENNReal.ofReal (1 / 2 : ℝ)) hDmemh.aestronglyMeasurable
      (by positivity) (by exact ENNReal.ofReal_ne_top)).2 hDmemh
    convert hi using 1
    · ext om
      rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (hD0 om)]
      simp
    · rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hhalf, div_eq_mul_inv, inv_inv]
      simpa using (ENNReal.div_mul_cancel (a := (2 : ℝ≥0∞))
        (b := ENNReal.ofReal q) (by norm_num) (by norm_num)).symm
  have hsqrt_norm : eLpNorm (fun om => Real.sqrt (D om)) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (Real.sqrt Wh * delta) := by
    have heqfun : eLpNorm (fun om => Real.sqrt (D om)) (ENNReal.ofReal q) P =
        eLpNorm (fun om => ‖D om‖ ^ (1 / 2 : ℝ)) (ENNReal.ofReal q) P := by
      apply eLpNorm_congr_ae
      filter_upwards [] with om
      rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (hD0 om)]
    rw [heqfun, eLpNorm_norm_rpow D (by norm_num : (0 : ℝ) < 1 / 2)]
    have heqexp : ENNReal.ofReal q * ENNReal.ofReal (1 / 2 : ℝ) =
        ENNReal.ofReal (q / 2) := by
      rw [← ENNReal.ofReal_mul (le_of_lt hq0)]
      ring_nf
    rw [heqexp]
    calc
      (eLpNorm D (ENNReal.ofReal (q / 2)) P) ^ (1 / 2 : ℝ) ≤
          (ENNReal.ofReal (Wh * delta ^ 2)) ^ (1 / 2 : ℝ) := by
            refine ENNReal.rpow_le_rpow ?_ (by norm_num)
            exact hDnorm (q / 2) (by linarith) (by linarith)
      _ = ENNReal.ofReal (Real.sqrt Wh * delta) :=
            aux_neumann_centered_response_sqrt_mul_sq Wh delta hWh0.le hdelta.le
  -- pointwise
  have hpoint : ∀ᵐ om ∂P,
      ‖Y om - 1‖ ≤ Real.sqrt Cdev * (Real.sqrt (D om) + D om) := by
    filter_upwards [hdev] with om hom
    have hroot : Real.sqrt (D om) * Real.sqrt (1 + D om) ≤
        Real.sqrt (D om) + D om := by
      have hsqD : (Real.sqrt (D om)) ^ 2 = D om := Real.sq_sqrt (hD0 om)
      have hsqone : (Real.sqrt (1 + D om)) ^ 2 = 1 + D om :=
        Real.sq_sqrt (by linarith [hD0 om])
      have hsquares :
          (Real.sqrt (D om) * Real.sqrt (1 + D om)) ^ 2 ≤
            (Real.sqrt (D om) + D om) ^ 2 := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg (D om)) (hD0 om)]
      nlinarith [mul_nonneg (Real.sqrt_nonneg (D om)) (Real.sqrt_nonneg (1 + D om)),
        add_nonneg (Real.sqrt_nonneg (D om)) (hD0 om)]
    have hroot' : Real.sqrt (D om * (1 + D om)) ≤ Real.sqrt (D om) + D om := by
      simpa only [Real.sqrt_mul (hD0 om)] using hroot
    have htotal : Real.sqrt (Cdev * D om * (1 + D om)) ≤
        Real.sqrt Cdev * (Real.sqrt (D om) + D om) := by
      rw [show Cdev * D om * (1 + D om) = Cdev * (D om * (1 + D om)) by ring,
        Real.sqrt_mul hCdev.le]
      exact mul_le_mul_of_nonneg_left hroot' (Real.sqrt_nonneg _)
    have habs : |Y om - 1| ≤ Real.sqrt (Cdev * D om * (1 + D om)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hom
    simpa only [Real.norm_eq_abs] using habs.trans htotal
  have hsum : eLpNorm (fun om => Real.sqrt (D om) + D om) (ENNReal.ofReal q) P ≤
      eLpNorm (fun om => Real.sqrt (D om)) (ENNReal.ofReal q) P +
        eLpNorm D (ENNReal.ofReal q) P := by
    have h := eLpNorm_add_le (μ := P) (p := ENNReal.ofReal q)
      hsqrt_mem.aestronglyMeasurable hDmemq.aestronglyMeasurable
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
    simpa using h
  have hsmul := eLpNorm_const_smul_le (c := Real.sqrt Cdev)
    (f := fun om => Real.sqrt (D om) + D om) (p := ENNReal.ofReal q) (μ := P)
  have hnormC : ‖Real.sqrt Cdev‖ₑ = ENNReal.ofReal (Real.sqrt Cdev) :=
    (ofReal_norm_eq_enorm (Real.sqrt Cdev)).symm.trans (by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)])
  calc
    eLpNorm (fun om => Y om - 1) (ENNReal.ofReal q) P ≤
        eLpNorm (fun om => Real.sqrt Cdev * (Real.sqrt (D om) + D om))
          (ENNReal.ofReal q) P := eLpNorm_mono_ae_real (p := ENNReal.ofReal q) hpoint
    _ ≤ ‖Real.sqrt Cdev‖ₑ *
        eLpNorm (fun om => Real.sqrt (D om) + D om) (ENNReal.ofReal q) P := by
          simpa [Pi.smul_apply, smul_eq_mul] using hsmul
    _ ≤ ‖Real.sqrt Cdev‖ₑ *
        (eLpNorm (fun om => Real.sqrt (D om)) (ENNReal.ofReal q) P +
          eLpNorm D (ENNReal.ofReal q) P) := mul_le_mul_of_nonneg_left hsum (zero_le _)
    _ ≤ ENNReal.ofReal (Real.sqrt Cdev) *
        (ENNReal.ofReal (Real.sqrt Wh * delta) +
          ENNReal.ofReal (W * delta ^ 2)) := by
          rw [hnormC]
          exact mul_le_mul_of_nonneg_left
            (add_le_add hsqrt_norm (hDnorm q (by linarith) hqmax)) (zero_le _)
    _ ≤ ENNReal.ofReal (Real.sqrt Cdev * (Real.sqrt W + W) * delta) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
          apply ENNReal.ofReal_mono
          have h1 : Real.sqrt Wh ≤ Real.sqrt W := Real.sqrt_le_sqrt hWhW
          have hd2 : delta ^ 2 ≤ delta := by nlinarith [hdelta.le, hdelta1]
          have h2 : W * delta ^ 2 ≤ W * delta := mul_le_mul_of_nonneg_left hd2 hW0.le
          have ha : Real.sqrt Wh * delta ≤ Real.sqrt W * delta :=
            mul_le_mul_of_nonneg_right h1 hdelta.le
          have hinner : Real.sqrt Wh * delta + W * delta ^ 2 ≤ (Real.sqrt W + W) * delta := by
            nlinarith [ha, h2]
          calc Real.sqrt Cdev * (Real.sqrt Wh * delta + W * delta ^ 2)
              ≤ Real.sqrt Cdev * ((Real.sqrt W + W) * delta) :=
                mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg _)
            _ = Real.sqrt Cdev * (Real.sqrt W + W) * delta := by ring

/-- The samplewise matrix-deviation bound for the infrared-removed inverse response,
transported to the physical cube by `neumann_response_defect_transport`. -/
theorem aux_neumann_centered_response_dev
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Rinput : Paper.in_responses d M)
    (pvec : Fin d → ℝ) (hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
    (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (Cdev : ℝ)
    (hdev : ∀ (U : Homogenization.Book.Ch02.Domain d)
        (a : Homogenization.Book.Ch02.CoeffOn U),
        Homogenization.Book.Ch02.CoeffOn.IsSymmetric a →
      ∀ a0 : ℝ, 0 < a0 →
      ∀ Jmax : ℝ,
        IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
            Homogenization.vecNormSq e = 1 ∧
            t = Homogenization.Book.Ch02.responseJ U a
              ((Real.sqrt a0)⁻¹ • e) (Real.sqrt a0 • e)} Jmax →
      ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
        (a0⁻¹ * Homogenization.vecDot e
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaCoarse U a) e) - 1) ^ 2 +
          (a0 * Homogenization.vecDot e
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) e) - 1) ^ 2 ≤
        Cdev * Jmax * (1 + Jmax))
    (N : ℕ) (om eta : BilateralField d)
    (hsum : ∀ x : SpatialCoordinates d,
      (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) =
        ∑ j ∈ Finset.range (N + 1), (eta (j : ℤ)) ((3 : ℝ) ^ N • x)) :
    (inverseResponse (meanZeroResponseSpace hP)
          (cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ => (1 / 2 : ℝ)) one_pos)
          ((affineNeumannLoad pvec).comp
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) - 1) ^ 2 ≤
      Cdev * Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) eta *
        (1 + Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) eta) := by
  obtain ⟨U, f, data, hUset, hdata, hfirst, hresp, hgreat⟩ :=
    neumann_response_defect_transport M Rinput pvec hP N om eta hsum
  have hpvec' : Homogenization.vecNormSq pvec = 1 := by
    simpa [Homogenization.vecNormSq, Homogenization.vecDot, pow_two] using hpvec
  have hv := hdev U data.toCoeffOn data.isSymmetric
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
    (Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) eta) hgreat
    pvec hpvec'
  rw [← hresp] at hv
  have hnon : 0 ≤
      ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
        Homogenization.vecDot pvec
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaCoarse U data.toCoeffOn) pvec) - 1) ^ 2 :=
    sq_nonneg _
  nlinarith [hv, hnon]

theorem aux_neumann_centered_response_holderTriple (a b : ℝ) (ha : 0 < a)
    (hb : b = 2 * a) :
    ENNReal.HolderTriple (ENNReal.ofReal b) (ENNReal.ofReal b) (ENNReal.ofReal a) := by
  subst hb
  have h2 : (0 : ℝ) < 2 * a := by linarith
  constructor
  rw [← ENNReal.ofReal_inv_of_pos h2, ← ENNReal.ofReal_inv_of_pos ha,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- The explicit centred constant: matrix deviation against the published defect moment
bank at orders `p` and `2p`, times the infrared amplitude factor. -/
def aux_neumann_centered_response_const (Cdev Cresp p Cinf : ℝ) : ℝ :=
  Real.sqrt Cdev *
      (Real.sqrt (Cresp * p * Real.log (2 + p)) + Cresp * p * Real.log (2 + p)) +
    2 * Real.sqrt (2 * p) * Real.exp (Cinf * (Real.sqrt (2 * p) + 2 * p) ^ 2) *
      (Real.sqrt Cdev *
        (Real.sqrt (Cresp * (2 * p) * Real.log (2 + 2 * p)) +
          Cresp * (2 * p) * Real.log (2 + 2 * p)) + 1)

theorem aux_neumann_centered_response_const_nonneg (Cdev Cresp p Cinf : ℝ)
    (hCresp : 0 ≤ Cresp) (hp : 2 ≤ p) :
    0 ≤ aux_neumann_centered_response_const Cdev Cresp p Cinf := by
  have hlp : 0 ≤ Real.log (2 + p) := Real.log_nonneg (by linarith)
  have hl2p : 0 ≤ Real.log (2 + 2 * p) := Real.log_nonneg (by linarith)
  have hp0 : (0 : ℝ) ≤ p := by linarith
  rw [aux_neumann_centered_response_const]
  have h3 : 0 ≤ Real.sqrt Cdev *
      (Real.sqrt (Cresp * p * Real.log (2 + p)) + Cresp * p * Real.log (2 + p)) := by
    positivity
  have h4 : 0 ≤ Real.sqrt Cdev *
        (Real.sqrt (Cresp * (2 * p) * Real.log (2 + 2 * p)) +
          Cresp * (2 * p) * Real.log (2 + 2 * p)) + 1 := by positivity
  have h5 : 0 ≤ 2 * Real.sqrt (2 * p) *
      Real.exp (Cinf * (Real.sqrt (2 * p) + 2 * p) ^ 2) := by positivity
  nlinarith [h3, h4, h5]

/-- The abstract `L^p` core: from the samplewise matrix-deviation bound, the published
defect moment bank and a sub-Gaussian infrared amplitude, the integrability and the three
centred bounds of order `delta`. -/
theorem aux_neumann_centered_response_lp
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (y0 y D Xf : Omega → ℝ)
    (hy0meas : Measurable y0) (hymeas : Measurable y)
    (hy0nonneg : ∀ om, 0 ≤ y0 om)
    (hXmeas : Measurable Xf) (hXnonneg : ∀ om, 0 ≤ Xf om)
    (hD0 : ∀ om, 0 ≤ D om)
    (p Cresp Cdev Cinf delta : ℝ) (hp : 2 ≤ p) (hCresp : 0 < Cresp) (hCdev : 0 < Cdev)
    (hCinf : 0 ≤ Cinf) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdev : ∀ᵐ om ∂P, (y0 om - 1) ^ 2 ≤ Cdev * D om * (1 + D om))
    (hDmem : ∀ xi : ℝ, 1 ≤ xi → xi ≤ 4 * p → MemLp D (ENNReal.ofReal xi) P)
    (hDnorm : ∀ xi : ℝ, 1 ≤ xi → xi ≤ 4 * p →
      eLpNorm D (ENNReal.ofReal xi) P ≤
        ENNReal.ofReal (Cresp * xi * Real.log (2 + xi) * delta ^ 2))
    (hExp : ∀ lam : ℝ, 0 ≤ lam →
      Integrable (fun om => Real.exp (lam * Xf om)) P ∧
      (∫ om, Real.exp (lam * Xf om) ∂P) ≤ 2 * Real.exp (Cinf * lam ^ 2 * delta ^ 2))
    (hcmp : ∀ᵐ om ∂P, |y om - y0 om| ≤ (Real.exp (Xf om) - 1) * y0 om) :
    (MemLp y (ENNReal.ofReal (2 * p)) P ∧ MemLp y0 (ENNReal.ofReal (2 * p)) P) ∧
      eLpNorm (fun om => y0 om - 1) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal
            (aux_neumann_centered_response_const Cdev Cresp p Cinf * delta) ∧
        eLpNorm (fun om => y om - y0 om) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal
            (aux_neumann_centered_response_const Cdev Cresp p Cinf * delta) ∧
        eLpNorm (fun om => y om - ∫ omega, y omega ∂P) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal
            (4 * aux_neumann_centered_response_const Cdev Cresp p Cinf * delta) := by
  set A1 : ℝ := aux_neumann_centered_response_const Cdev Cresp p Cinf with hA1def
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 < Real.log (2 + p) := Real.log_pos (by linarith)
  have hlog2p : 0 < Real.log (2 + 2 * p) := Real.log_pos (by linarith)
  set Wp : ℝ := Cresp * p * Real.log (2 + p) with hWpdef
  set Wq : ℝ := Cresp * (2 * p) * Real.log (2 + 2 * p) with hWqdef
  have hWp0 : 0 < Wp := by rw [hWpdef]; positivity
  have hWq0 : 0 < Wq := by rw [hWqdef]; positivity
  set K0 : ℝ := Real.sqrt Cdev * (Real.sqrt Wq + Wq) + 1 with hK0def
  have hK00 : 0 < K0 := by rw [hK0def]; positivity
  set cX : ℝ :=
    2 * Real.sqrt (2 * p) * Real.exp (Cinf * (Real.sqrt (2 * p) + 2 * p) ^ 2) with hcXdef
  have hcX0 : 0 < cX := by rw [hcXdef]; positivity
  have hA1eq : A1 = Real.sqrt Cdev * (Real.sqrt Wp + Wp) + cX * K0 := by
    rw [hA1def, hWpdef, hcXdef, hK0def, hWqdef, aux_neumann_centered_response_const]
  have hA10 : 0 < A1 := by
    rw [hA1eq]
    have h0 : 0 ≤ Real.sqrt Cdev * (Real.sqrt Wp + Wp) := by positivity
    nlinarith [mul_pos hcX0 hK00]
  have hErrNorm : ∀ q : ℝ, 2 ≤ q → q ≤ 4 * p →
      eLpNorm (fun om => y0 om - 1) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (Real.sqrt Cdev *
          (Real.sqrt (Cresp * q * Real.log (2 + q)) +
            Cresp * q * Real.log (2 + q)) * delta) :=
    fun q hq hq4 =>
      aux_neumann_centered_response_err_norm P y0 D hD0 Cdev hCdev hdev
        Cresp hCresp delta hdelta0 hdelta1 (4 * p) hDmem hDnorm q hq hq4
  have hExpMem : ∀ q : ℝ, 0 < q →
      MemLp (fun om => Real.exp (Xf om)) (ENNReal.ofReal q) P := by
    intro q hq
    have he := hExp q hq.le
    have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
    have hqtop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
    have hpow : MemLp (fun om => ‖Real.exp (Xf om)‖ ^ q) 1 P := by
      have hbase : MemLp (fun om => Real.exp (q * Xf om)) 1 P :=
        (memLp_one_iff_integrable).2 he.1
      have heq : (fun om => ‖Real.exp (Xf om)‖ ^ q) =
          (fun om => Real.exp (q * Xf om)) := by
        funext om
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
      rw [heq]
      exact hbase
    have hiff := memLp_norm_rpow_iff (μ := P) (p := ENNReal.ofReal q)
      (q := ENNReal.ofReal q) hXmeas.exp.aestronglyMeasurable hq0 hqtop
    have hpow' : MemLp (fun om => ‖Real.exp (Xf om)‖ ^
        (ENNReal.ofReal q).toReal) (ENNReal.ofReal q / ENNReal.ofReal q) P := by
      simpa [ENNReal.toReal_ofReal hq.le, ENNReal.div_self hq0 hqtop] using hpow
    exact hiff.mp hpow'
  have hExpNorm : eLpNorm (fun om => Real.exp (Xf om) - 1)
      (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (cX * delta) := by
    have h := aux_neumann_centered_response_expX_norm P Xf hXnonneg Cinf hCinf
      delta hdelta0 hdelta1 hExp (2 * p) (by linarith)
    rwa [← hcXdef] at h
  have hErrMem : ∀ q : ℝ, 2 ≤ q → q ≤ 4 * p →
      MemLp (fun om => y0 om - 1) (ENNReal.ofReal q) P := by
    intro q hq hq4
    refine ⟨hy0meas.aestronglyMeasurable.sub aestronglyMeasurable_const, ?_⟩
    exact (hErrNorm q hq hq4).trans_lt (by finiteness)
  have hY0mem4 : MemLp y0 (ENNReal.ofReal (4 * p)) P := by
    have h := (hErrMem (4 * p) (by linarith) le_rfl).add
      (memLp_const (μ := P) (p := ENNReal.ofReal (4 * p)) (1 : ℝ))
    have heq : ((fun om => y0 om - 1) + fun _ : Omega => (1 : ℝ)) = y0 := by
      funext om; simp only [Pi.add_apply]; ring
    rwa [heq] at h
  have hY0mem2 : MemLp y0 (ENNReal.ofReal (2 * p)) P :=
    hY0mem4.mono_exponent (ENNReal.ofReal_le_ofReal (by linarith))
  have hEminusMem2 : MemLp (fun om => Real.exp (Xf om) - 1)
      (ENNReal.ofReal (2 * p)) P := by
    have h := (hExpMem (2 * p) (by linarith)).sub
      (memLp_const (μ := P) (p := ENNReal.ofReal (2 * p)) (1 : ℝ))
    have heq : ((fun om => Real.exp (Xf om)) - fun _ : Omega => (1 : ℝ)) =
        fun om => Real.exp (Xf om) - 1 := by
      funext om; simp only [Pi.sub_apply]
    rwa [heq] at h
  letI := aux_neumann_centered_response_holderTriple p (2 * p) hp0 rfl
  have hdiffPoint : ∀ᵐ om ∂P, ‖y om - y0 om‖ ≤ (Real.exp (Xf om) - 1) * y0 om := by
    filter_upwards [hcmp] with om hom
    simpa [Real.norm_eq_abs] using hom
  have hdiffMem : MemLp (fun om => y om - y0 om) (ENNReal.ofReal p) P := by
    have hprod : MemLp (fun om => (Real.exp (Xf om) - 1) * y0 om)
        (ENNReal.ofReal p) P := hY0mem2.mul'
      (p := ENNReal.ofReal (2 * p)) (q := ENNReal.ofReal (2 * p))
      (r := ENNReal.ofReal p) hEminusMem2
    exact hprod.mono'
      (hymeas.aestronglyMeasurable.sub hy0meas.aestronglyMeasurable) hdiffPoint
  have hone2p : eLpNorm (fun _ : Omega => (1 : ℝ)) (ENNReal.ofReal (2 * p)) P = 1 := by
    rw [eLpNorm_const (1 : ℝ) (by simp [ENNReal.ofReal_eq_zero]; linarith)
      (IsProbabilityMeasure.ne_zero P)]
    simp
  have hY0norm : eLpNorm y0 (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal K0 := by
    have hsplit : y0 = (fun om => y0 om - 1) + (fun _ => (1 : ℝ)) := by
      funext om; simp only [Pi.add_apply]; ring
    have hadd := eLpNorm_add_le (μ := P) (p := ENNReal.ofReal (2 * p))
      (hErrMem (2 * p) (by linarith) (by linarith)).aestronglyMeasurable
      (aestronglyMeasurable_const (b := (1 : ℝ)))
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
    rw [hsplit]
    refine hadd.trans ?_
    rw [hone2p]
    refine le_trans (add_le_add (hErrNorm (2 * p) (by linarith) (by linarith))
      (le_refl (1 : ℝ≥0∞))) ?_
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by simp,
      ← ENNReal.ofReal_add (by positivity) (by norm_num)]
    apply ENNReal.ofReal_mono
    rw [hK0def, ← hWqdef]
    have h0 : 0 ≤ Real.sqrt Cdev * (Real.sqrt Wq + Wq) := by positivity
    nlinarith [h0, hdelta1, hdelta0.le]
  have hgoal3 : eLpNorm (fun om => y0 om - 1) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (A1 * delta) := by
    refine (hErrNorm p hp (by linarith)).trans ?_
    apply ENNReal.ofReal_mono
    rw [hA1eq, ← hWpdef]
    have h0 : 0 ≤ Real.sqrt Cdev * (Real.sqrt Wp + Wp) := by positivity
    have h1 : 0 ≤ cX * K0 := by positivity
    nlinarith [h0, h1, hdelta0.le]
  have hgoal4 : eLpNorm (fun om => y om - y0 om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (A1 * delta) := by
    have hmono : eLpNorm (fun om => y om - y0 om) (ENNReal.ofReal p) P ≤
        eLpNorm (fun om => (Real.exp (Xf om) - 1) * y0 om)
          (ENNReal.ofReal p) P := eLpNorm_mono_ae_real hdiffPoint
    have hholder := eLpNorm_smul_le_mul_eLpNorm (μ := P)
      (p := ENNReal.ofReal (2 * p)) (q := ENNReal.ofReal (2 * p))
      (r := ENNReal.ofReal p) (f := y0)
      (φ := fun om => Real.exp (Xf om) - 1)
      hy0meas.aestronglyMeasurable
      (hXmeas.exp.sub measurable_const).aestronglyMeasurable
    have hholder' : eLpNorm (fun om => (Real.exp (Xf om) - 1) * y0 om)
        (ENNReal.ofReal p) P ≤
        eLpNorm (fun om => Real.exp (Xf om) - 1) (ENNReal.ofReal (2 * p)) P *
          eLpNorm y0 (ENNReal.ofReal (2 * p)) P := by
      simpa [Pi.smul_apply, smul_eq_mul] using hholder
    refine (hmono.trans hholder').trans ?_
    refine (mul_le_mul' hExpNorm hY0norm).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_mono
    rw [hA1eq]
    have h0 : 0 ≤ Real.sqrt Cdev * (Real.sqrt Wp + Wp) := by positivity
    nlinarith [h0, hdelta0.le, mul_pos hcX0 hK00]
  have hyN1 : eLpNorm (fun om => y om - 1) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (2 * A1 * delta) := by
    have hsplit : (fun om => y om - 1) =
        (fun om => y om - y0 om) + (fun om => y0 om - 1) := by
      funext om; simp only [Pi.add_apply]; ring
    have hadd := eLpNorm_add_le (μ := P) (p := ENNReal.ofReal p)
      hdiffMem.aestronglyMeasurable
      (hErrMem p hp (by linarith)).aestronglyMeasurable
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
    rw [hsplit]
    refine hadd.trans ?_
    refine (add_le_add hgoal4 hgoal3).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_mono
    linarith
  refine ⟨⟨?_, hY0mem2⟩, hgoal3, hgoal4, ?_⟩
  · letI := aux_neumann_centered_response_holderTriple (2 * p) (4 * p)
      (by linarith) (by ring)
    have hprod_2p : MemLp (fun om => Real.exp (Xf om) * y0 om)
        (ENNReal.ofReal (2 * p)) P :=
      hY0mem4.mul' (p := ENNReal.ofReal (4 * p)) (q := ENNReal.ofReal (4 * p))
        (r := ENNReal.ofReal (2 * p)) (hExpMem (4 * p) (by linarith))
    have hbound : ∀ᵐ om ∂P, ‖y om‖ ≤ Real.exp (Xf om) * y0 om := by
      filter_upwards [hcmp] with om h
      have hy0 : 0 ≤ y0 om := hy0nonneg om
      have h_tri : |y om| ≤ |y om - y0 om| + |y0 om| := by
        calc
          |y om| = |(y om - y0 om) + y0 om| := by ring_nf
          _ ≤ |y om - y0 om| + |y0 om| := abs_add_le _ _
      rw [Real.norm_eq_abs]
      have h_tri' : |y om| ≤ |y om - y0 om| + y0 om := by
        simpa [abs_of_nonneg hy0] using h_tri
      nlinarith [h_tri', h]
    exact hprod_2p.mono' hymeas.aestronglyMeasurable hbound
  · have hyNmem1 : MemLp (fun om => y om - 1) (ENNReal.ofReal p) P :=
      ⟨hymeas.aestronglyMeasurable.sub aestronglyMeasurable_const,
        hyN1.trans_lt (by finiteness)⟩
    have hyNint : Integrable (fun om => y om - 1) P :=
      (memLp_one_iff_integrable).1 (hyNmem1.mono_exponent
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)))
    set m : ℝ := ∫ omega, y omega ∂P with hmdef
    have hyNint' : Integrable y P := by
      have h := hyNint.add (integrable_const (1 : ℝ))
      have heq : ((fun om => y om - 1) + fun _ : Omega => (1 : ℝ)) = y := by
        funext om; simp only [Pi.add_apply]; ring
      rwa [heq] at h
    have hmean : (∫ om, (y om - 1) ∂P) = m - 1 := by
      rw [integral_sub hyNint' (integrable_const (1 : ℝ))]
      simp [hmdef]
    have habs : |m - 1| ≤ 2 * A1 * delta := by
      have h1 : |∫ om, (y om - 1) ∂P| ≤ ∫ om, |y om - 1| ∂P := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := P) (f := fun om => y om - 1)
      have h2 : ENNReal.ofReal (∫ om, |y om - 1| ∂P) =
          eLpNorm (fun om => y om - 1) 1 P := by
        rw [eLpNorm_one_eq_lintegral_enorm,
          ofReal_integral_eq_lintegral_ofReal hyNint.abs
            (ae_of_all _ fun om => abs_nonneg _)]
        refine lintegral_congr fun om => ?_
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
      have h3 : eLpNorm (fun om => y om - 1) 1 P ≤
          eLpNorm (fun om => y om - 1) (ENNReal.ofReal p) P :=
        eLpNorm_le_eLpNorm_of_exponent_le
          (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
          (hymeas.aestronglyMeasurable.sub aestronglyMeasurable_const)
      have h5 : (∫ om, |y om - 1| ∂P) ≤ 2 * A1 * delta :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
          (by rw [h2]; exact h3.trans hyN1)
      rw [← hmean]
      exact h1.trans h5
    have hsplit : (fun om => y om - m) =
        (fun om => y om - 1) + (fun _ => (1 : ℝ) - m) := by
      funext om; simp only [Pi.add_apply]; ring
    have hadd : eLpNorm ((fun om => y om - 1) + fun _ : Omega => (1 : ℝ) - m)
        (ENNReal.ofReal p) P ≤
        eLpNorm (fun om => y om - 1) (ENNReal.ofReal p) P +
          eLpNorm (fun _ : Omega => (1 : ℝ) - m) (ENNReal.ofReal p) P :=
      eLpNorm_add_le (hymeas.aestronglyMeasurable.sub aestronglyMeasurable_const)
        aestronglyMeasurable_const
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
    have hconst : eLpNorm (fun _ : Omega => (1 : ℝ) - m) (ENNReal.ofReal p) P =
        ENNReal.ofReal |1 - m| := by
      rw [eLpNorm_const ((1 : ℝ) - m)
        (by simp [ENNReal.ofReal_eq_zero]; linarith) (IsProbabilityMeasure.ne_zero P)]
      simp [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    rw [hsplit]
    refine hadd.trans ?_
    rw [hconst]
    have habs' : |(1 : ℝ) - m| ≤ 2 * A1 * delta := by
      rw [abs_sub_comm]; exact habs
    refine (add_le_add hyN1 (ENNReal.ofReal_mono habs')).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_mono
    linarith


/-- The published defect moment bank, read at the relabelled sample and weakened to the
deterministic constant bound `Cresp`. -/
theorem aux_neumann_centered_response_defect_moments
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rinput : Paper.in_responses d M)
    (Cresp p : ℝ) (hCresp : 0 < Cresp) (hRC : Rinput.C ≤ Cresp)
    (hscale : 4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹)
    (relab : ℕ → BilateralField d → BilateralField d)
    (hrelabMP : ∀ N, MeasurePreserving (relab N)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure)
    (N : ℕ) :
    (∀ xi : ℝ, 1 ≤ xi → xi ≤ 4 * p →
        MemLp (fun om => Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) (relab N om))
          (ENNReal.ofReal xi) (chaosSampleLaw M).toMeasure) ∧
      (∀ xi : ℝ, 1 ≤ xi → xi ≤ 4 * p →
        eLpNorm (fun om => Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) (relab N om))
            (ENNReal.ofReal xi) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cresp * xi * Real.log (2 + xi) * M.delta ^ 2)) := by
  have hbound4 : 4 * p ≤ Rinput.C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    have hCinv : Cresp⁻¹ ≤ Rinput.C⁻¹ := (inv_le_inv₀ hCresp Rinput.C_pos).2 hRC
    calc
      4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := hscale
      _ ≤ Rinput.C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by gcongr
  refine ⟨fun xi hxi hxi4 => ?_, fun xi hxi hxi4 => ?_⟩
  · have hmem := Rinput.defect_memLp xi hxi (hxi4.trans hbound4) N
      (fun _ => (3 : ℝ) ^ N / 2)
    simpa [Function.comp_def] using hmem.comp_measurePreserving (hrelabMP N)
  · have hxi_pos : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
    have hmem := Rinput.defect_memLp xi hxi (hxi4.trans hbound4) N
      (fun _ => (3 : ℝ) ^ N / 2)
    have hnorm := hmem.eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_pos.mpr hxi_pos).ne' ENNReal.ofReal_ne_top
    have heq : eLpNorm (fun om => Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) (relab N om))
        (ENNReal.ofReal xi) (chaosSampleLaw M).toMeasure =
        eLpNorm (Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2))
          (ENNReal.ofReal xi) (chaosSampleLaw M).toMeasure := by
      simpa [Function.comp_def] using
        eLpNorm_comp_measurePreserving hmem.aestronglyMeasurable (hrelabMP N)
    rw [heq, hnorm]
    apply ENNReal.ofReal_mono
    have hm := Rinput.moment xi hxi (hxi4.trans hbound4) N (fun _ => (3 : ℝ) ^ N / 2)
    have hm' : (∫ om, ‖Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) om‖ ^
          (ENNReal.ofReal xi).toReal ∂(chaosSampleLaw M).toMeasure) ^
          ((ENNReal.ofReal xi).toReal)⁻¹ ≤
        Rinput.C * xi * Real.log (2 + xi) * M.delta ^ 2 := by
      simpa [ENNReal.toReal_ofReal hxi_pos.le, Real.norm_eq_abs, one_div,
        abs_of_nonneg (Rinput.defect_nonneg N (fun _ => (3 : ℝ) ^ N / 2) _)] using hm
    refine hm'.trans ?_
    have hlogxi : 0 ≤ Real.log (2 + xi) := Real.log_nonneg (by linarith)
    have hstep : Rinput.C * xi * Real.log (2 + xi) ≤ Cresp * xi * Real.log (2 + xi) := by
      have hxl : 0 ≤ xi * Real.log (2 + xi) := mul_nonneg hxi_pos.le hlogxi
      linarith [mul_le_mul_of_nonneg_right hRC hxl]
    nlinarith [hstep, sq_nonneg M.delta]




theorem neumann_centered_response :
    ∀ (d : ℕ) (hd : 2 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (I : Paper.in_J d) (Cresp : ℝ) (hCresp : 0 < Cresp)
      (p : ℝ) (hp : 2 ≤ p)
      (pvec : Fin d → ℝ)
      (hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
      (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      let Q := unitNeumannCube d
      let S := meanZeroResponseSpace hP
      let L : S.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
      ∃ delta0 C : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ 0 < C ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
          (0 < M.delta ∧ M.delta ≤ delta0) →
          ∀ (Rinput : Paper.in_responses d M),
            Rinput.C ≤ Cresp →
            4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
            ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
              InfraredCharacterization M H →
              ∀ (relab : ℕ → BilateralField d → BilateralField d),
                (∀ N, MeasurePreserving (relab N)
                  (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure) →
                (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
                  ∀ i : ℤ, ∀ x : SpatialCoordinates d,
                    relab N omega i x = omega (i - (N : ℤ))
                      ((3 : ℝ) ^ (-(N : ℤ)) • x)) →
              let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
              let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
              let aN0 : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                cutoffPositiveCoefficient M (fun _ => 0) om N
                  (fun _ => (1 / 2 : ℝ)) one_pos
              let yN : ℕ → BilateralField d → ℝ := fun N om =>
                inverseResponse S (aN N om) L
              let yN0 : ℕ → BilateralField d → ℝ := fun N om =>
                inverseResponse S (aN0 N om) L
              ∀ N : ℕ,
                (∀ᵐ om ∂P, ∀ Sbound : ℝ, 0 ≤ Sbound →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)), |H om x| ≤ Sbound) →
                  |yN N om - yN0 N om| ≤
                    (Real.exp Sbound - 1) * yN0 N om) ∧
                (MemLp (yN N) (ENNReal.ofReal (2 * p)) P ∧
                  MemLp (yN0 N) (ENNReal.ofReal (2 * p)) P) ∧
                eLpNorm (yN0 N - (fun _ => (1 : ℝ))) (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal (C * M.delta) ∧
                  eLpNorm (yN N - yN0 N) (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal (C * M.delta) ∧
                  eLpNorm
                      (fun om => yN N om - ∫ omega, yN N omega ∂P)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal (C * M.delta) := by
  intro d hd _ _ I Cresp hCresp p hp pvec hpvec hP Q S L
  obtain ⟨Cdev, hCdev, hdev⟩ := I.deviation_by_J
  obtain ⟨Cinfra, hCinfra, hExpAll⟩ :=
    exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  have hQK : (Q : Set (SpatialCoordinates d)) ⊆
      (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d)) :=
    centeredCube_subset_closedCube _ one_pos
  have hconst0 : 0 ≤ aux_neumann_centered_response_const Cdev Cresp p
      (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) :=
    aux_neumann_centered_response_const_nonneg _ _ _ _ hCresp.le hp
  refine ⟨1, 4 * aux_neumann_centered_response_const Cdev Cresp p
      (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) + 1,
    one_pos, le_refl 1, by linarith, ?_⟩
  intro M hM Rinput hRC hscale H hH relab hrelabMP hrelabId P aN aN0 yN yN0 N
  have hdelta0 : 0 < M.delta := hM.1
  have hdelta1 : M.delta ≤ 1 := hM.2
  obtain ⟨hDmem, hDnorm⟩ :=
    aux_neumann_centered_response_defect_moments M Rinput Cresp p hCresp hRC hscale
      relab hrelabMP N
  have hdev_ae : ∀ᵐ om ∂P, (yN0 N om - 1) ^ 2 ≤
      Cdev * (fun om => Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) (relab N om)) om * (1 + (fun om => Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) (relab N om)) om) := by
    filter_upwards [hrelabId] with om hom
    exact aux_neumann_centered_response_dev M Rinput pvec hpvec hP Cdev hdev N om
      (relab N om)
      (fun x => aux_neumann_centered_response_reindex N om (relab N om) x
        (fun i y => hom N i y))
  have hY0meas : Measurable (yN0 N) :=
    aux_neumann_centered_response_meas M (fun _ => 0) measurable_const S L N
  have hYmeas : Measurable (yN N) :=
    aux_neumann_centered_response_meas M H hH.1 S L N
  have hXmeas : Measurable (fun om => ‖(H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d))‖) :=
    (continuous_norm.comp (ContinuousMap.continuous_restrict
      (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))).measurable.comp hH.1
  have hXbound : ∀ om, ∀ x ∈ (Q : Set (SpatialCoordinates d)),
      |H om x| ≤ (fun om => ‖(H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d))‖) om := by
    intro om x hx
    exact ContinuousMap.norm_coe_le_norm
      ((H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))) ⟨x, hQK hx⟩
  have hPoint : ∀ᵐ om ∂P, ∀ Sbound : ℝ, 0 ≤ Sbound →
      (∀ x ∈ (Q : Set (SpatialCoordinates d)), |H om x| ≤ Sbound) →
      |yN N om - yN0 N om| ≤ (Real.exp Sbound - 1) * yN0 N om := by
    filter_upwards [] with om
    intro Sbound _ hbound
    exact aux_neumann_centered_response_compare M H S L om N Sbound hbound
  have hcmp : ∀ᵐ om ∂P,
      |yN N om - yN0 N om| ≤ (Real.exp ((fun om => ‖(H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d))‖) om) - 1) * yN0 N om := by
    filter_upwards [hPoint] with om hom
    exact hom _ (norm_nonneg _) (hXbound om)
  obtain ⟨hmem, h3, h4, h5⟩ :=
    aux_neumann_centered_response_lp P (yN0 N) (yN N) (fun om => Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) (relab N om)) (fun om => ‖(H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d))‖)
      hY0meas hYmeas (fun om => inverseResponse_nonneg S (aN0 N om) L) hXmeas
      (fun om => norm_nonneg _)
      (fun om => Rinput.defect_nonneg N (fun _ => (3 : ℝ) ^ N / 2) (relab N om))
      p Cresp Cdev (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) M.delta hp hCresp hCdev
      (hCinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) hdelta0 hdelta1 hdev_ae hDmem hDnorm
      (fun lam hlam => hExpAll M H hH (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) lam hlam) hcmp
  have hmono1 : aux_neumann_centered_response_const Cdev Cresp p
        (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) * M.delta ≤
      (4 * aux_neumann_centered_response_const Cdev Cresp p
        (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) + 1) * M.delta := by
    nlinarith [hconst0, hdelta0.le]
  have hmono2 : 4 * aux_neumann_centered_response_const Cdev Cresp p
        (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) * M.delta ≤
      (4 * aux_neumann_centered_response_const Cdev Cresp p
        (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) + 1) * M.delta := by
    nlinarith [hconst0, hdelta0.le]
  exact ⟨hPoint, hmem, h3.trans (ENNReal.ofReal_mono hmono1),
    h4.trans (ENNReal.ofReal_mono hmono1), h5.trans (ENNReal.ofReal_mono hmono2)⟩

end Paper
