module

public import SubdiffusiveProcess.Paper.lem_borel_weights_closed_core
public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.conv_energy_measure_normalization


@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

section AuxWEM
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

namespace SubdiffusiveProcess.DirichletForm

variable [OpensMeasurableSpace X] {m : Measure X}

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_integrable_bounded [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : Measurable w) (C : ℝ)
    (hC : ∀ x, |w x| ≤ C) : Integrable w μ := by
  apply (integrable_const C : Integrable (fun _ : X => C) μ).mono'
    hw.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using hC x)

lemma aux_setIntegral_add (μ η : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (w : X → ℝ) (hw : Measurable w) (C : ℝ)
    (hC : ∀ x, |w x| ≤ C) (B : Set X) :
    (∫ x in B, w x ∂(μ + η)) =
      (∫ x in B, w x ∂μ) + (∫ x in B, w x ∂η) := by
  rw [Measure.restrict_add]
  exact integral_add_measure
    (aux_integrable_bounded (μ.restrict B) w hw C hC)
    (aux_integrable_bounded (η.restrict B) w hw C hC)

lemma aux_signedIntegralOn_rep
    (w : X → ℝ) (hw : Measurable w) (C : ℝ)
    (hC : ∀ x, |w x| ≤ C)
    (ν : SignedMeasure X) (P N : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure N]
    (hν : ν = P.toSignedMeasure - N.toSignedMeasure) (B : Set X) :
    signedIntegralOn ν B w =
      (∫ x in B, w x ∂P) - (∫ x in B, w x ∂N) := by
  have hJ :
      ν.toJordanDecomposition.posPart.toSignedMeasure -
        ν.toJordanDecomposition.negPart.toSignedMeasure = ν :=
    SignedMeasure.toSignedMeasure_toJordanDecomposition ν
  have hrep :
      ν.toJordanDecomposition.posPart.toSignedMeasure -
        ν.toJordanDecomposition.negPart.toSignedMeasure =
      P.toSignedMeasure - N.toSignedMeasure := hJ.trans hν
  have hmeasure : ν.toJordanDecomposition.posPart + N =
      ν.toJordanDecomposition.negPart + P := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    calc
      ν.toJordanDecomposition.posPart.toSignedMeasure + N.toSignedMeasure =
          (ν.toJordanDecomposition.posPart.toSignedMeasure -
            ν.toJordanDecomposition.negPart.toSignedMeasure) +
          (ν.toJordanDecomposition.negPart.toSignedMeasure + N.toSignedMeasure) := by
        abel
      _ = (P.toSignedMeasure - N.toSignedMeasure) +
          (ν.toJordanDecomposition.negPart.toSignedMeasure + N.toSignedMeasure) := by
        rw [hrep]
      _ = ν.toJordanDecomposition.negPart.toSignedMeasure + P.toSignedMeasure := by
        abel
  have hI : (∫ x in B, w x ∂(ν.toJordanDecomposition.posPart + N)) =
      ∫ x in B, w x ∂(ν.toJordanDecomposition.negPart + P) :=
    congrArg (fun μ : Measure X => ∫ x in B, w x ∂μ) hmeasure
  rw [aux_setIntegral_add _ _ w hw C hC B,
    aux_setIntegral_add _ _ w hw C hC B] at hI
  unfold signedIntegralOn
  linarith only [hI]

lemma aux_signedIntegralOn_add (ν₁ ν₂ : SignedMeasure X)
    (B : Set X) (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x, |w x| ≤ C) :
    signedIntegralOn (ν₁ + ν₂) B w =
      signedIntegralOn ν₁ B w + signedIntegralOn ν₂ B w := by
  have h₁ : ν₁ = ν₁.toJordanDecomposition.posPart.toSignedMeasure -
      ν₁.toJordanDecomposition.negPart.toSignedMeasure :=
    (SignedMeasure.toSignedMeasure_toJordanDecomposition ν₁).symm
  have h₂ : ν₂ = ν₂.toJordanDecomposition.posPart.toSignedMeasure -
      ν₂.toJordanDecomposition.negPart.toSignedMeasure :=
    (SignedMeasure.toSignedMeasure_toJordanDecomposition ν₂).symm
  have hrep : ν₁ + ν₂ =
      (ν₁.toJordanDecomposition.posPart +
        ν₂.toJordanDecomposition.posPart).toSignedMeasure -
      (ν₁.toJordanDecomposition.negPart +
        ν₂.toJordanDecomposition.negPart).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    calc
      ν₁ + ν₂ =
          (ν₁.toJordanDecomposition.posPart.toSignedMeasure -
            ν₁.toJordanDecomposition.negPart.toSignedMeasure) +
          (ν₂.toJordanDecomposition.posPart.toSignedMeasure -
            ν₂.toJordanDecomposition.negPart.toSignedMeasure) :=
        congrArg₂ (fun s t : SignedMeasure X => s + t) h₁ h₂
      _ = _ := by abel
  rw [aux_signedIntegralOn_rep w hw C hC (ν₁ + ν₂) _ _ hrep B,
    aux_setIntegral_add _ _ w hw C hC B,
    aux_setIntegral_add _ _ w hw C hC B]
  unfold signedIntegralOn
  ring

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_setIntegral_nnreal_smul [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] (μ : Measure X) (w : X → ℝ)
    (a : ℝ≥0) (B : Set X) :
    (∫ x in B, w x ∂(a • μ)) = (a : ℝ) * (∫ x in B, w x ∂μ) := by
  rw [Measure.restrict_smul]
  exact integral_smul_nnreal_measure w a

lemma aux_signedIntegralOn_smul (ν : SignedMeasure X) (c : ℝ)
    (B : Set X) (w : X → ℝ) :
    signedIntegralOn (c • ν) B w = c * signedIntegralOn ν B w := by
  unfold signedIntegralOn
  rw [SignedMeasure.toJordanDecomposition_smul_real]
  by_cases hc : 0 ≤ c
  · rw [JordanDecomposition.real_smul_posPart_nonneg _ c hc,
      JordanDecomposition.real_smul_negPart_nonneg _ c hc,
      aux_setIntegral_nnreal_smul, aux_setIntegral_nnreal_smul,
      Real.coe_toNNReal c hc]
    ring
  · have hc' : c < 0 := lt_of_not_ge hc
    rw [JordanDecomposition.real_smul_posPart_neg _ c hc',
      JordanDecomposition.real_smul_negPart_neg _ c hc',
      aux_setIntegral_nnreal_smul, aux_setIntegral_nnreal_smul,
      Real.coe_toNNReal (-c) (neg_nonneg.mpr hc'.le)]
    ring

lemma aux_signedIntegralOn_toSignedMeasure (μ : Measure X)
    [IsFiniteMeasure μ] (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x, |w x| ≤ C) (B : Set X) :
    signedIntegralOn μ.toSignedMeasure B w = ∫ x in B, w x ∂μ := by
  have hrep : μ.toSignedMeasure =
      μ.toSignedMeasure - (0 : Measure X).toSignedMeasure := by
    rw [Measure.toSignedMeasure_zero, sub_zero]
  have h : signedIntegralOn μ.toSignedMeasure B w =
      (∫ x in B, w x ∂μ) - (∫ x in B, w x ∂(0 : Measure X)) :=
    aux_signedIntegralOn_rep w hw C hC μ.toSignedMeasure μ 0 hrep B
  simpa only [Measure.restrict_zero, integral_zero_measure, sub_zero] using h

def aux_weightedCross (w : X → ℝ) (ν : SignedMeasure X) : SignedMeasure X :=
  ν.toJordanDecomposition.posPart.withDensityᵥ w -
    ν.toJordanDecomposition.negPart.withDensityᵥ w

lemma aux_weightedCross_apply (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x, |w x| ≤ C)
    (ν : SignedMeasure X) (B : Set X) (hB : MeasurableSet B) :
    aux_weightedCross w ν B = signedIntegralOn ν B w := by
  unfold aux_weightedCross signedIntegralOn
  rw [sub_apply,
    withDensityᵥ_apply
      (aux_integrable_bounded ν.toJordanDecomposition.posPart w hw C hC) hB,
    withDensityᵥ_apply
      (aux_integrable_bounded ν.toJordanDecomposition.negPart w hw C hC) hB]

lemma aux_weightedCross_add (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x, |w x| ≤ C) (ν₁ ν₂ : SignedMeasure X) :
    aux_weightedCross w (ν₁ + ν₂) =
      aux_weightedCross w ν₁ + aux_weightedCross w ν₂ := by
  apply VectorMeasure.ext
  intro B hB
  rw [add_apply,
    aux_weightedCross_apply w hw C hC (ν₁ + ν₂) B hB,
    aux_weightedCross_apply w hw C hC ν₁ B hB,
    aux_weightedCross_apply w hw C hC ν₂ B hB]
  exact aux_signedIntegralOn_add ν₁ ν₂ B w hw C hC

lemma aux_weightedCross_smul (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x, |w x| ≤ C) (ν : SignedMeasure X) (c : ℝ) :
    aux_weightedCross w (c • ν) = c • aux_weightedCross w ν := by
  apply VectorMeasure.ext
  intro B hB
  rw [smul_apply,
    aux_weightedCross_apply w hw C hC (c • ν) B hB,
    aux_weightedCross_apply w hw C hC ν B hB]
  exact aux_signedIntegralOn_smul ν c B w

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_withDensity_toReal [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] (μ : Measure X) (w : X → ℝ)
    (hw : Measurable w) (h0 : ∀ x, 0 ≤ w x)
    (B : Set X) (hB : MeasurableSet B) :
    ((μ.withDensity (fun x => ENNReal.ofReal (w x))) B).toReal =
      ∫ x in B, w x ∂μ := by
  rw [withDensity_apply _ hB]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall h0)
    (hw.aestronglyMeasurable : AEStronglyMeasurable w (μ.restrict B))).symm

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_withDensity_le [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] (μ : Measure X) (ρ : X → ENNReal)
    (C : ℝ) (hC : ∀ x, ρ x ≤ ENNReal.ofReal C) :
    μ.withDensity ρ ≤ ENNReal.ofReal C • μ := by
  calc
    μ.withDensity ρ ≤ μ.withDensity (fun _ => ENNReal.ofReal C) :=
      withDensity_mono (Filter.Eventually.of_forall hC)
    _ = ENNReal.ofReal C • μ := withDensity_const _

lemma aux_finite_withDensity (μ : Measure X) [IsFiniteMeasure μ]
    (ρ : X → ENNReal) (C : ℝ) (hC : ∀ x, ρ x ≤ ENNReal.ofReal C) :
    IsFiniteMeasure (μ.withDensity ρ) := by
  refine ⟨?_⟩
  have h : μ.withDensity ρ Set.univ ≤ (ENNReal.ofReal C • μ) Set.univ :=
    Measure.le_iff'.mp (aux_withDensity_le μ ρ C hC) Set.univ
  have hfin : (ENNReal.ofReal C • μ) Set.univ < ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)
  exact h.trans_lt hfin

omit [OpensMeasurableSpace X] in
lemma aux_regular_of_le [_instPreserved0 : OpensMeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure μ]
    [μ.Regular] (h : ν ≤ μ) : ν.Regular := by
  let : IsFiniteMeasure ν :=
    ⟨(Measure.le_iff'.mp h Set.univ).trans_lt (measure_lt_top μ Set.univ)⟩
  let δ : Measure X := μ - ν
  let : IsFiniteMeasure δ := inferInstance
  have hsum : δ + ν = μ := Measure.sub_add_cancel_of_le h
  have hmass (S : Set X) : μ S = δ S + ν S := by
    calc
      μ S = (δ + ν) S := congrArg (fun τ : Measure X => τ S) hsum.symm
      _ = δ S + ν S := Measure.add_apply _ _ _
  refine {
    toIsFiniteMeasureOnCompacts := inferInstance
    toOuterRegular := ⟨?_⟩
    innerRegular := ?_
  }
  · intro A _ r hr
    have hAr : μ A < δ A + r := by
      rw [hmass]
      exact (ENNReal.add_lt_add_iff_left (measure_lt_top δ A).ne).mpr hr
    obtain ⟨U, hAU, hUo, hU⟩ := A.exists_isOpen_lt_of_lt (δ A + r) hAr
    refine ⟨U, hAU, hUo, ?_⟩
    apply (ENNReal.add_lt_add_iff_left (measure_lt_top δ A).ne).mp
    calc
      δ A + ν U ≤ δ U + ν U := add_le_add (measure_mono hAU) le_rfl
      _ = μ U := (hmass U).symm
      _ < δ A + r := hU
  · intro U hU r hr
    have ht : δ U + r < μ U := by
      rw [hmass]
      exact (ENNReal.add_lt_add_iff_left (measure_lt_top δ U).ne).mpr hr
    obtain ⟨K, hKU, hK, hlt⟩ :=
      Measure.Regular.innerRegular (μ := μ) hU (δ U + r) ht
    refine ⟨K, hKU, hK, ?_⟩
    apply (ENNReal.add_lt_add_iff_left (measure_lt_top δ U).ne).mp
    calc
      δ U + r < μ K := hlt
      _ = δ K + ν K := hmass K
      _ ≤ δ U + ν K := add_le_add (measure_mono hKU) le_rfl

lemma aux_regular_withDensity_of_bounded (μ : Measure X)
    [IsFiniteMeasure μ] [μ.Regular] (ρ : X → ENNReal)
    (C : ℝ) (hC : ∀ x, ρ x ≤ ENNReal.ofReal C) :
    (μ.withDensity ρ).Regular := by
  let : IsFiniteMeasure (ENNReal.ofReal C • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)⟩
  let : (ENNReal.ofReal C • μ).Regular :=
    Measure.Regular.smul (μ := μ) ENNReal.ofReal_ne_top
  exact aux_regular_of_le (ENNReal.ofReal C • μ) (μ.withDensity ρ)
    (aux_withDensity_le μ ρ C hC)

lemma aux_quadratic_discriminant (a b c : ℝ) (hb : 0 ≤ b)
    (hq : ∀ t : ℝ, 0 ≤ a + 2 * t * c + t ^ 2 * b) :
    c ^ 2 ≤ a * b := by
  by_cases hb0 : b = 0
  · have hc0 : c = 0 := by
      by_contra hc
      have ht : 0 ≤ a + 2 * (-(a + 1) / (2 * c)) * c +
          (-(a + 1) / (2 * c)) ^ 2 * b := hq (-(a + 1) / (2 * c))
      have hid : a + 2 * (-(a + 1) / (2 * c)) * c +
          (-(a + 1) / (2 * c)) ^ 2 * b = -1 := by
        rw [hb0, mul_zero, add_zero]
        field_simp [hc] ; ring
      rw [hid] at ht
      norm_num at ht
    simp only [hc0, hb0, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, le_refl]
  · have ht : 0 ≤ (a + 2 * (-c / b) * c + (-c / b) ^ 2 * b) * b :=
      mul_nonneg (hq (-c / b)) hb
    have hid : (a + 2 * (-c / b) * c + (-c / b) ^ 2 * b) * b =
        a * b - c ^ 2 := by
      field_simp [hb0] ; ring
    rw [hid] at ht
    linarith only [ht]

lemma aux_bilinear_abs_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Submodule ℝ V) (b : V → V → ℝ)
    (hsym : ∀ u ∈ D, ∀ v ∈ D, b u v = b v u)
    (hadd : ∀ u ∈ D, ∀ v ∈ D, ∀ z ∈ D,
      b u (v + z) = b u v + b u z)
    (hsmul : ∀ (c : ℝ), ∀ u ∈ D, ∀ v ∈ D, b u (c • v) = c * b u v)
    (h0 : ∀ u ∈ D, 0 ≤ b u u)
    {u v : V} (hu : u ∈ D) (hv : v ∈ D) :
    |b u v| ≤ Real.sqrt (b u u) * Real.sqrt (b v v) := by
  have hquad (t : ℝ) : b (u + t • v) (u + t • v) =
      b u u + 2 * t * b u v + t ^ 2 * b v v := by
    have htv : t • v ∈ D := D.smul_mem t hv
    have hs : u + t • v ∈ D := D.add_mem hu htv
    rw [hadd (u + t • v) hs u hu (t • v) htv,
      hsmul t (u + t • v) hs v hv,
      hsym (u + t • v) hs u hu,
      hsym (u + t • v) hs v hv,
      hadd u hu u hu (t • v) htv,
      hadd v hv u hu (t • v) htv,
      hsmul t u hu v hv, hsmul t v hv v hv, hsym v hv u hu]
    ring
  have hq : ∀ t : ℝ, 0 ≤ b u u + 2 * t * b u v + t ^ 2 * b v v := by
    intro t
    rw [← hquad t]
    exact h0 (u + t • v) (D.add_mem hu (D.smul_mem t hv))
  have hcs : (b u v) ^ 2 ≤ b u u * b v v :=
    aux_quadratic_discriminant (b u u) (b v v) (b u v) (h0 v hv) hq
  refine abs_le_of_sq_le_sq ?_
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt (h0 u hu), Real.sq_sqrt (h0 v hv)]
  exact hcs

lemma aux_signedIntegralOn_sub (ν₁ ν₂ : SignedMeasure X)
    (B : Set X) (f : X → ℝ) (hf : Measurable f)
    (D : ℝ) (hD : ∀ x, |f x| ≤ D) :
    signedIntegralOn (ν₁ - ν₂) B f =
      signedIntegralOn ν₁ B f - signedIntegralOn ν₂ B f := by
  have h₁ :
      ν₁.toJordanDecomposition.posPart.toSignedMeasure -
        ν₁.toJordanDecomposition.negPart.toSignedMeasure = ν₁ :=
    SignedMeasure.toSignedMeasure_toJordanDecomposition ν₁
  have h₂ :
      ν₂.toJordanDecomposition.posPart.toSignedMeasure -
        ν₂.toJordanDecomposition.negPart.toSignedMeasure = ν₂ :=
    SignedMeasure.toSignedMeasure_toJordanDecomposition ν₂
  have hrep : ν₁ - ν₂ =
      (ν₁.toJordanDecomposition.posPart +
        ν₂.toJordanDecomposition.negPart).toSignedMeasure -
      (ν₁.toJordanDecomposition.negPart +
        ν₂.toJordanDecomposition.posPart).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    calc
      ν₁ - ν₂ =
          (ν₁.toJordanDecomposition.posPart.toSignedMeasure -
            ν₁.toJordanDecomposition.negPart.toSignedMeasure) -
          (ν₂.toJordanDecomposition.posPart.toSignedMeasure -
            ν₂.toJordanDecomposition.negPart.toSignedMeasure) :=
        congrArg₂ (fun s t : SignedMeasure X => s - t) h₁.symm h₂.symm
      _ = _ := by abel
  rw [aux_signedIntegralOn_rep f hf D hD (ν₁ - ν₂) _ _ hrep B,
    aux_setIntegral_add _ _ f hf D hD B,
    aux_setIntegral_add _ _ f hf D hD B]
  unfold signedIntegralOn
  ring

lemma aux_abs_toReal_ofReal_le (t : ℝ) :
    |(ENNReal.ofReal t).toReal| ≤ |t| := by
  by_cases ht : 0 ≤ t
  · simpa only [ENNReal.toReal_ofReal ht] using
      (le_rfl : |t| ≤ |t|)
  · have ht' : t ≤ 0 := (lt_of_not_ge ht).le
    rw [ENNReal.ofReal_of_nonpos ht', ENNReal.toReal_zero, abs_zero]
    exact abs_nonneg t

lemma aux_toReal_ofReal_sub (t : ℝ) :
    (ENNReal.ofReal t).toReal - (ENNReal.ofReal (-t)).toReal = t := by
  by_cases ht : 0 ≤ t
  · rw [ENNReal.toReal_ofReal ht,
      ENNReal.ofReal_of_nonpos (neg_nonpos.mpr ht),
      ENNReal.toReal_zero, sub_zero]
  · have ht' : t ≤ 0 := (lt_of_not_ge ht).le
    rw [ENNReal.ofReal_of_nonpos ht', ENNReal.toReal_zero,
      ENNReal.toReal_ofReal (neg_nonneg.mpr ht'), zero_sub, neg_neg]

lemma aux_integrable_mul_ofReal_toReal
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f)
    (D : ℝ) (hD : ∀ x, |f x| ≤ D)
    (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x, |w x| ≤ C) :
    Integrable (fun x => f x * (ENNReal.ofReal (w x)).toReal) μ := by
  apply aux_integrable_bounded μ
    (fun x => f x * (ENNReal.ofReal (w x)).toReal)
    (hf.mul hw.ennreal_ofReal.ennreal_toReal) (|D| * |C|)
  intro x
  rw [abs_mul]
  exact mul_le_mul
    ((hD x).trans (le_abs_self D))
    ((aux_abs_toReal_ofReal_le (w x)).trans
      ((hC x).trans (le_abs_self C)))
    (abs_nonneg _) (abs_nonneg _)

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_setIntegral_withDensity_toReal [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X]
    (μ : Measure X) [SFinite μ]
    (w : X → ℝ) (hw : Measurable w)
    (f : X → ℝ) (B : Set X) :
    (∫ x in B, f x ∂(μ.withDensity (fun x => ENNReal.ofReal (w x)))) =
      ∫ x in B, f x * (ENNReal.ofReal (w x)).toReal ∂μ := by
  rw [restrict_withDensity' (μ := μ) B
    (fun x => ENNReal.ofReal (w x))]
  have htop :
      ∀ᵐ x ∂(μ.restrict B), ENNReal.ofReal (w x) < ⊤ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  simpa only [smul_eq_mul, mul_comm] using
    (integral_withDensity_eq_integral_toReal_smul
      (μ := μ.restrict B) hw.ennreal_ofReal htop f)

lemma aux_signedIntegralOn_withDensity
    (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x, |w x| ≤ C)
    (f : X → ℝ) (hf : Measurable f)
    (D : ℝ) (hD : ∀ x, |f x| ≤ D)
    (B : Set X) :
    signedIntegralOn (μ.withDensityᵥ w) B f =
      ∫ x in B, f x * w x ∂μ := by
  let P : Measure X :=
    μ.withDensity (fun x => ENNReal.ofReal (w x))
  let N : Measure X :=
    μ.withDensity (fun x => ENNReal.ofReal (-w x))
  let : IsFiniteMeasure P :=
    aux_finite_withDensity μ (fun x => ENNReal.ofReal (w x)) C
      (fun x => ENNReal.ofReal_le_ofReal
        ((le_abs_self (w x)).trans (hC x)))
  let : IsFiniteMeasure N :=
    aux_finite_withDensity μ (fun x => ENNReal.ofReal (-w x)) C
      (fun x => ENNReal.ofReal_le_ofReal
        ((neg_le_abs (w x)).trans (hC x)))
  have hrep :
      μ.withDensityᵥ w = P.toSignedMeasure - N.toSignedMeasure :=
    withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part
      (aux_integrable_bounded μ w hw C hC)
  rw [aux_signedIntegralOn_rep f hf D hD
    (μ.withDensityᵥ w) P N hrep B]
  change
    (∫ x in B, f x ∂(μ.withDensity (fun x => ENNReal.ofReal (w x)))) -
      (∫ x in B, f x ∂(μ.withDensity (fun x => ENNReal.ofReal (-w x)))) =
        ∫ x in B, f x * w x ∂μ
  rw [aux_setIntegral_withDensity_toReal μ w hw f B,
    aux_setIntegral_withDensity_toReal μ (fun x => -w x) hw.neg f B]
  have hneg : ∀ x, |(-w x)| ≤ C := by
    intro x
    simpa only [abs_neg] using hC x
  have hP :
      Integrable (fun x => f x * (ENNReal.ofReal (w x)).toReal)
        (μ.restrict B) :=
    aux_integrable_mul_ofReal_toReal
      (μ.restrict B) f hf D hD w hw C hC
  have hN :
      Integrable (fun x => f x * (ENNReal.ofReal (-w x)).toReal)
        (μ.restrict B) :=
    aux_integrable_mul_ofReal_toReal
      (μ.restrict B) f hf D hD (fun x => -w x) hw.neg C hneg
  rw [← integral_sub hP hN]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [← mul_sub, aux_toReal_ofReal_sub (w x)])

lemma aux_signedIntegralOn_weightedCross
    (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x, |w x| ≤ C)
    (ν : SignedMeasure X)
    (f : X → ℝ) (hf : Measurable f)
    (D : ℝ) (hD : ∀ x, |f x| ≤ D)
    (B : Set X) :
    signedIntegralOn (aux_weightedCross w ν) B f =
      signedIntegralOn ν B (fun x => f x * w x) := by
  unfold aux_weightedCross
  rw [aux_signedIntegralOn_sub _ _ B f hf D hD,
    aux_signedIntegralOn_withDensity
      ν.toJordanDecomposition.posPart w hw C hC f hf D hD B,
    aux_signedIntegralOn_withDensity
      ν.toJordanDecomposition.negPart w hw C hC f hf D hD B]
  rfl

lemma aux_integral_weighted_measure
    (μ : Measure X) [SFinite μ]
    (w : X → ℝ) (hw : Measurable w)
    (h0 : ∀ x, 0 ≤ w x)
    (f : X → ℝ) (B : Set X) :
    (∫ x in B, f x ∂(μ.withDensity (fun x => ENNReal.ofReal (w x)))) =
      ∫ x in B, f x * w x ∂μ := by
  rw [aux_setIntegral_withDensity_toReal μ w hw f B]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (h0 x)])

def aux_BM (f : X → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x : X, |f x| ≤ C

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_bm_const [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] (c : ℝ) : aux_BM (fun _ : X => c) := by
  exact ⟨measurable_const, |c|, fun _ : X => le_rfl⟩

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_bm_add [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] {f g : X → ℝ} (hf : aux_BM f) (hg : aux_BM g) :
    aux_BM (fun x : X => f x + g x) := by
  rcases hf with ⟨hf, C, hC⟩
  rcases hg with ⟨hg, D, hD⟩
  refine ⟨hf.add hg, C + D, ?_⟩
  intro x
  exact (abs_add_le (f x) (g x)).trans (add_le_add (hC x) (hD x))

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_bm_mul [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] {f g : X → ℝ} (hf : aux_BM f) (hg : aux_BM g) :
    aux_BM (fun x : X => f x * g x) := by
  rcases hf with ⟨hf, C, hC⟩
  rcases hg with ⟨hg, D, hD⟩
  refine ⟨hf.mul hg, |C| * |D|, ?_⟩
  intro x
  rw [abs_mul]
  exact mul_le_mul ((hC x).trans (le_abs_self C))
    ((hD x).trans (le_abs_self D)) (abs_nonneg _) (abs_nonneg _)

lemma aux_bm_sq {f : X → ℝ} (hf : aux_BM f) :
    aux_BM (fun x : X => f x ^ 2) := by
  simpa only [pow_two] using aux_bm_mul hf hf

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_bm_comp [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] {f : X → ℝ} (hf : aux_BM f)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    aux_BM (fun x : X => Φ (f x)) := by
  rcases hf with ⟨hf, C, hC⟩
  refine ⟨hΦ.measurable.comp hf, ?_⟩
  have hcompact : IsCompact ((fun t : ℝ => |Φ t|) '' Set.Icc (-|C|) |C|) :=
    isCompact_Icc.image (continuous_abs.comp hΦ)
  obtain ⟨D, hD⟩ := hcompact.bddAbove
  refine ⟨D, ?_⟩
  intro x
  apply hD
  refine ⟨f x, ?_, rfl⟩
  exact abs_le.mp ((hC x).trans (le_abs_self C))

lemma aux_bm_integrable (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : aux_BM f) : Integrable f μ := by
  rcases hf with ⟨hf, C, hC⟩
  exact aux_integrable_bounded μ f hf C hC

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_rep_add [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] {m : Measure X} (u v : Lp ℝ 2 m) (f g : X → ℝ)
    (hu : ⇑u =ᵐ[m] f) (hv : ⇑v =ᵐ[m] g) :
    ⇑(u + v) =ᵐ[m] fun x : X => f x + g x := by
  filter_upwards [Lp.coeFn_add u v, hu, hv] with x hx hux hvx
  simpa only [Pi.add_apply, hux, hvx] using hx

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_rep_smul [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] {m : Measure X} (c : ℝ) (u : Lp ℝ 2 m) (f : X → ℝ)
    (hu : ⇑u =ᵐ[m] f) :
    ⇑(c • u) =ᵐ[m] fun x : X => c * f x := by
  filter_upwards [Lp.coeFn_smul c u, hu] with x hx hux
  simpa only [Pi.smul_apply, smul_eq_mul, hux] using hx

lemma aux_memCore_add (E : ClosedForm m) (u v : Lp ℝ 2 m)
    (hu : E.MemCore u) (hv : E.MemCore v) : E.MemCore (u + v) := by
  rcases hu with ⟨hu, f, hf, hfc, hfs, huf⟩
  rcases hv with ⟨hv, g, hg, hgc, hgs, hvg⟩
  refine ⟨E.domain.add_mem hu hv, f + g, hf.add hg, hfc.add hgc,
    Set.subset_univ _, ?_⟩
  exact aux_rep_add u v f g huf hvg

lemma aux_core_bounded_rep (E : ClosedForm m) (u : Lp ℝ 2 m)
    (hu : E.MemCore u) :
    ∃ f : X → ℝ, Continuous f ∧ aux_BM f ∧ ⇑u =ᵐ[m] f := by
  rcases hu with ⟨hu, f, hf, hfc, hfs, huf⟩
  have hcompact : IsCompact (abs '' Set.range f) :=
    (hfc.isCompact_range hf).image continuous_abs
  obtain ⟨C, hC⟩ := hcompact.bddAbove
  refine ⟨f, hf, ⟨hf.measurable, C, ?_⟩, huf⟩
  intro x
  exact hC ⟨f x, ⟨x, rfl⟩, rfl⟩

lemma aux_setIntegral_fun_add (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → ℝ) (hf : aux_BM f) (hg : aux_BM g) (B : Set X) :
    (∫ x in B, f x + g x ∂μ) =
      (∫ x in B, f x ∂μ) + (∫ x in B, g x ∂μ) := by
  have hfi : Integrable (fun x : X => f x) (μ.restrict B) :=
    aux_bm_integrable (μ.restrict B) hf
  have hgi : Integrable (fun x : X => g x) (μ.restrict B) :=
    aux_bm_integrable (μ.restrict B) hg
  simpa only [Pi.add_apply] using integral_add hfi hgi

lemma aux_signedIntegralOn_fun_add (ν : SignedMeasure X)
    (f g : X → ℝ) (hf : aux_BM f) (hg : aux_BM g) (B : Set X) :
    signedIntegralOn ν B (fun x : X => f x + g x) =
      signedIntegralOn ν B f + signedIntegralOn ν B g := by
  unfold signedIntegralOn
  rw [aux_setIntegral_fun_add ν.toJordanDecomposition.posPart f g hf hg B,
    aux_setIntegral_fun_add ν.toJordanDecomposition.negPart f g hf hg B]
  ring

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_signedIntegralOn_congr_ae [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] (ν : SignedMeasure X)
    (B : Set X) (f g : X → ℝ) (h : f =ᵐ[ν.totalVariation] g) :
    signedIntegralOn ν B f = signedIntegralOn ν B g := by
  have hz : ν.toJordanDecomposition.posPart {x : X | f x ≠ g x} +
      ν.toJordanDecomposition.negPart {x : X | f x ≠ g x} = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply] using
      (ae_iff.mp h)
  have hp : f =ᵐ[ν.toJordanDecomposition.posPart] g :=
    ae_iff.mpr (add_eq_zero.mp hz).1
  have hn : f =ᵐ[ν.toJordanDecomposition.negPart] g :=
    ae_iff.mpr (add_eq_zero.mp hz).2
  unfold signedIntegralOn
  exact congrArg₂ (fun a b : ℝ => a - b)
    (integral_congr_ae (ae_restrict_of_ae hp))
    (integral_congr_ae (ae_restrict_of_ae hn))

lemma aux_integral_square_shift_diff (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : aux_BM f) (B : Set X) :
    (∫ x in B, (f x + 1) ^ 2 ∂μ) -
        (∫ x in B, (f x + (-1)) ^ 2 ∂μ) =
      4 * (∫ x in B, f x ∂μ) := by
  have hp : Integrable (fun x : X => (f x + 1) ^ 2) (μ.restrict B) :=
    aux_bm_integrable (μ.restrict B) (aux_bm_sq (aux_bm_add hf (aux_bm_const 1)))
  have hn : Integrable (fun x : X => (f x + (-1)) ^ 2) (μ.restrict B) :=
    aux_bm_integrable (μ.restrict B) (aux_bm_sq (aux_bm_add hf (aux_bm_const (-1))))
  rw [← integral_sub hp hn]
  calc
    _ = ∫ x in B, (4 : ℝ) * f x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x : X => by dsimp only; ring)
    _ = _ := integral_const_mul 4 f

lemma aux_integral_mul_shift_diff (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → ℝ) (hf : aux_BM f) (hg : aux_BM g) (B : Set X) :
    (∫ x in B, f x * (g x + 1) ∂μ) -
        (∫ x in B, f x * (g x + (-1)) ∂μ) =
      2 * (∫ x in B, f x ∂μ) := by
  have hp : Integrable (fun x : X => f x * (g x + 1)) (μ.restrict B) :=
    aux_bm_integrable (μ.restrict B)
      (aux_bm_mul hf (aux_bm_add hg (aux_bm_const 1)))
  have hn : Integrable (fun x : X => f x * (g x + (-1))) (μ.restrict B) :=
    aux_bm_integrable (μ.restrict B)
      (aux_bm_mul hf (aux_bm_add hg (aux_bm_const (-1))))
  rw [← integral_sub hp hn]
  calc
    _ = ∫ x in B, (2 : ℝ) * f x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x : X => by dsimp only; ring)
    _ = _ := integral_const_mul 2 f

lemma aux_signedIntegralOn_mul_shift_diff (ν : SignedMeasure X)
    (f g : X → ℝ) (hf : aux_BM f) (hg : aux_BM g) (B : Set X) :
    signedIntegralOn ν B (fun x : X => f x * (g x + 1)) -
        signedIntegralOn ν B (fun x : X => f x * (g x + (-1))) =
      2 * signedIntegralOn ν B f := by
  have hp : (∫ x in B, f x * (g x + 1) ∂ν.toJordanDecomposition.posPart) -
      (∫ x in B, f x * (g x + (-1)) ∂ν.toJordanDecomposition.posPart) =
      2 * (∫ x in B, f x ∂ν.toJordanDecomposition.posPart) :=
    aux_integral_mul_shift_diff ν.toJordanDecomposition.posPart f g hf hg B
  have hn : (∫ x in B, f x * (g x + 1) ∂ν.toJordanDecomposition.negPart) -
      (∫ x in B, f x * (g x + (-1)) ∂ν.toJordanDecomposition.negPart) =
      2 * (∫ x in B, f x ∂ν.toJordanDecomposition.negPart) :=
    aux_integral_mul_shift_diff ν.toJordanDecomposition.negPart f g hf hg B
  unfold signedIntegralOn
  linarith only [hp, hn]

omit [OpensMeasurableSpace X] in
lemma aux_measure_zero [_instPreserved0 : OpensMeasurableSpace X] {m : Measure X} (E : ClosedForm m) (Γ : EnergyMeasure E) :
    Γ.measure (0 : Lp ℝ 2 m) = 0 := by
  have he : E.form 0 0 = 0 := by
    simpa only [zero_smul, zero_mul] using
      E.form_smul_left 0 0 E.domain.zero_mem 0 E.domain.zero_mem
  have hz : Γ.measure (0 : Lp ℝ 2 m) Set.univ = 0 := by
    calc
      _ = ENNReal.ofReal ((Γ.measure (0 : Lp ℝ 2 m) Set.univ).toReal) :=
        (ENNReal.ofReal_toReal (Γ.measure_univ_lt_top 0 E.domain.zero_mem).ne).symm
      _ = 0 := by rw [Γ.measure_univ 0 E.domain.zero_mem, he, ENNReal.ofReal_zero]
  apply Measure.ext
  intro B hB
  exact measure_mono_null (Set.subset_univ B) hz

lemma aux_measure_open_null (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (O : Set X) (hO : IsOpen O) (hmO : m O = 0) : Γ.measure u O = 0 := by
  have hrestrict : m.restrict O = 0 := Measure.restrict_zero_set hmO
  have hu0 : ⇑u =ᵐ[m.restrict O] ⇑(0 : Lp ℝ 2 m) := by
    apply ae_iff.mpr
    rw [hrestrict]
    rfl
  have hlocal : (Γ.measure u).restrict O = (Γ.measure 0).restrict O :=
    Γ.locality u hu 0 E.domain.zero_mem O hO hu0
  have hmass : Γ.measure u O = Γ.measure 0 O := by
    simpa only [Measure.restrict_apply_univ] using
      congrArg (fun μ : Measure X => μ Set.univ) hlocal
  rw [hmass, aux_measure_zero E Γ]
  rfl

lemma aux_continuous_ae_energy (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[m] g) : f =ᵐ[Γ.measure u] g := by
  apply ae_iff.mpr
  have hO : IsOpen {x : X | f x ≠ g x} := (isClosed_eq hf hg).isOpen_compl
  exact aux_measure_open_null E Γ u hu {x : X | f x ≠ g x} hO (ae_iff.mp hfg)

lemma aux_continuous_ae_weighted_energy (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain) (ρ : X → ℝ≥0∞)
    (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[m] g) : f =ᵐ[(Γ.measure u).withDensity ρ] g := by
  exact (withDensity_absolutelyContinuous (Γ.measure u) ρ).ae_eq
    (aux_continuous_ae_energy E Γ u hu f g hf hg hfg)

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_totalVariation_ac_of_null [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] (ν : SignedMeasure X) (μ : Measure X)
    (h : ∀ B : Set X, MeasurableSet B → μ B = 0 → ν B = 0) :
    ν.totalVariation ≪ μ := by
  have hv : ν ≪ᵥ μ.toENNRealVectorMeasure := by
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro B hB hzero
    apply h B hB
    simpa only [Measure.toENNRealVectorMeasure_apply_measurable hB] using hzero
  have ht : ν.totalVariation ≪ μ.toENNRealVectorMeasure.ennrealToMeasure :=
    (SignedMeasure.absolutelyContinuous_ennreal_iff ν μ.toENNRealVectorMeasure).mp hv
  simpa only [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] using ht

lemma aux_cross_totalVariation_ac (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (v : Lp ℝ 2 m) (hv : v ∈ E.domain) :
    (Γ.cross u v).totalVariation ≪ Γ.measure u := by
  apply aux_totalVariation_ac_of_null
  intro B hB hzero
  have hbound : |Γ.cross u v B| ≤ 0 := by
    simpa only [hzero, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] using
      Γ.abs_cross_le u hu v hv B hB
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

lemma aux_weightedCross_totalVariation_ac (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x : X, |w x| ≤ C) (ν : SignedMeasure X) :
    (aux_weightedCross w ν).totalVariation ≪ ν.totalVariation := by
  apply aux_totalVariation_ac_of_null
  intro B hB hzero
  have hz : ν.toJordanDecomposition.posPart B +
      ν.toJordanDecomposition.negPart B = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply] using hzero
  rw [aux_weightedCross_apply w hw C hC ν B hB]
  unfold signedIntegralOn
  simp only [Measure.restrict_zero_set (add_eq_zero.mp hz).1,
    Measure.restrict_zero_set (add_eq_zero.mp hz).2,
    integral_zero_measure, sub_self]

lemma aux_continuous_ae_weighted_cross (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (v : Lp ℝ 2 m) (hv : v ∈ E.domain)
    (w : X → ℝ) (hw : Measurable w) (C : ℝ) (hC : ∀ x : X, |w x| ≤ C)
    (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[m] g) :
    f =ᵐ[(aux_weightedCross w (Γ.cross u v)).totalVariation] g := by
  exact (aux_weightedCross_totalVariation_ac w hw C hC (Γ.cross u v)).ae_eq
    ((aux_cross_totalVariation_ac E Γ u hu v hv).ae_eq
      (aux_continuous_ae_energy E Γ u hu f g hf hg hfg))

lemma aux_measure_eq_withDensity_of_setIntegral
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (h0 : ∀ x : X, 0 ≤ f x)
    (h : ∀ B : Set X, MeasurableSet B → (ν B).toReal = ∫ x in B, f x ∂μ) :
    ν = μ.withDensity (fun x : X => ENNReal.ofReal (f x)) := by
  let S : ℕ → Set X := fun n : ℕ => {x : X | f x ≤ (n : ℝ)}
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le hf measurable_const
  have hcover : (⋃ n : ℕ, S n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (f x)
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro n
  let fN : X → ℝ := fun x : X => min (f x) (n : ℝ)
  have hfN : Measurable fN := hf.min measurable_const
  have h0N (x : X) : 0 ≤ fN x := le_min (h0 x) (Nat.cast_nonneg n)
  have hbN (x : X) : fN x ≤ (n : ℝ) := min_le_right _ _
  have heq : f =ᵐ[μ.restrict (S n)] fN := by
    filter_upwards [ae_restrict_mem (hS n)] with x hx
    change f x ≤ (n : ℝ) at hx
    exact (min_eq_left hx).symm
  have hd : (μ.withDensity (fun x : X => ENNReal.ofReal (f x))).restrict (S n) =
      (μ.restrict (S n)).withDensity (fun x : X => ENNReal.ofReal (fN x)) := by
    rw [restrict_withDensity' (μ := μ) (S n) (fun x : X => ENNReal.ofReal (f x))]
    apply withDensity_congr_ae
    exact heq.mono (fun x hx => congrArg ENNReal.ofReal hx)
  rw [hd]
  let : IsFiniteMeasure
      ((μ.restrict (S n)).withDensity (fun x : X => ENNReal.ofReal (fN x))) :=
    aux_finite_withDensity (μ.restrict (S n))
      (fun x : X => ENNReal.ofReal (fN x)) (n : ℝ)
      (fun x : X => ENNReal.ofReal_le_ofReal (hbN x))
  apply Measure.ext
  intro B hB
  have hreal : ((ν.restrict (S n)) B).toReal =
      (((μ.restrict (S n)).withDensity (fun x : X => ENNReal.ofReal (fN x))) B).toReal := by
    calc
      _ = (ν (B ∩ S n)).toReal := by rw [Measure.restrict_apply hB]
      _ = ∫ x in B ∩ S n, f x ∂μ := h (B ∩ S n) (hB.inter (hS n))
      _ = ∫ x in B, f x ∂(μ.restrict (S n)) := by rw [Measure.restrict_restrict hB]
      _ = ∫ x in B, fN x ∂(μ.restrict (S n)) :=
        integral_congr_ae (ae_restrict_of_ae heq)
      _ = _ := (aux_withDensity_toReal (μ.restrict (S n)) fN hfN h0N B hB).symm
  calc
    _ = ENNReal.ofReal (((ν.restrict (S n)) B).toReal) :=
      (ENNReal.ofReal_toReal (measure_lt_top (ν.restrict (S n)) B).ne).symm
    _ = ENNReal.ofReal
        ((((μ.restrict (S n)).withDensity (fun x : X => ENNReal.ofReal (fN x))) B).toReal) :=
      congrArg ENNReal.ofReal hreal
    _ = _ := ENNReal.ofReal_toReal (measure_lt_top _ B).ne

lemma aux_chain_rule_measure (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (uc : X → ℝ) (huc : Continuous uc) (hurep : ⇑u =ᵐ[m] uc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    (v : Lp ℝ 2 m) (hv : v ∈ E.domain)
    (hvrep : ⇑v =ᵐ[m] fun x : X => Φ (uc x)) :
    Γ.measure v = (Γ.measure u).withDensity
      (fun x : X => ENNReal.ofReal ((deriv Φ (uc x)) ^ 2)) := by
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
  let : IsFiniteMeasure (Γ.measure v) := ⟨Γ.measure_univ_lt_top v hv⟩
  exact aux_measure_eq_withDensity_of_setIntegral (Γ.measure u) (Γ.measure v)
    (fun x : X => (deriv Φ (uc x)) ^ 2)
    ((hΦ.continuous_deriv_one.comp huc).pow 2).measurable
    (fun x : X => sq_nonneg _) (Γ.chain_rule u hu uc huc hurep Φ hΦ hΦ0 v hv hvrep)

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_withDensity_comm [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : OpensMeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity f).withDensity g = (μ.withDensity g).withDensity f := by
  rw [← withDensity_mul μ hf hg, ← withDensity_mul μ hg hf, mul_comm f g]

lemma aux_weighted_chain_rule (E : ClosedForm m) (Γ : EnergyMeasure E)
    (w : X → ℝ) (hw : Measurable w)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (uc : X → ℝ) (huc : Continuous uc) (hurep : ⇑u =ᵐ[m] uc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    (v : Lp ℝ 2 m) (hv : v ∈ E.domain)
    (hvrep : ⇑v =ᵐ[m] fun x : X => Φ (uc x))
    (B : Set X) (hB : MeasurableSet B) :
    (((Γ.measure v).withDensity (fun x : X => ENNReal.ofReal (w x))) B).toReal =
      ∫ x in B, (deriv Φ (uc x)) ^ 2
        ∂((Γ.measure u).withDensity (fun x : X => ENNReal.ofReal (w x))) := by
  rw [aux_chain_rule_measure E Γ u hu uc huc hurep Φ hΦ hΦ0 v hv hvrep,
    aux_withDensity_comm (Γ.measure u)
      (fun x : X => ENNReal.ofReal ((deriv Φ (uc x)) ^ 2))
      (fun x : X => ENNReal.ofReal (w x))
      (((hΦ.continuous_deriv_one.comp huc).pow 2).measurable.ennreal_ofReal)
      hw.ennreal_ofReal]
  exact aux_withDensity_toReal _ (fun x : X => (deriv Φ (uc x)) ^ 2)
    ((hΦ.continuous_deriv_one.comp huc).pow 2).measurable
    (fun x : X => sq_nonneg _) B hB

lemma aux_weighted_set_identity
    (μ₀ μ₁ μ₂ : Measure X)
    [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (ν : SignedMeasure X) (a b c : X → ℝ)
    (ha : aux_BM a) (hb : aux_BM b) (hc : aux_BM c)
    (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x : X, |w x| ≤ C) (h0 : ∀ x : X, 0 ≤ w x)
    (h : ∀ A : Set X, MeasurableSet A →
      (μ₀ A).toReal = (∫ x in A, a x ∂μ₁) +
        2 * signedIntegralOn ν A b + (∫ x in A, c x ∂μ₂))
    (B : Set X) (hB : MeasurableSet B) :
    ((μ₀.withDensity (fun x : X => ENNReal.ofReal (w x))) B).toReal =
      (∫ x in B, a x ∂(μ₁.withDensity (fun x : X => ENNReal.ofReal (w x)))) +
        2 * signedIntegralOn (aux_weightedCross w ν) B b +
        (∫ x in B, c x ∂(μ₂.withDensity (fun x : X => ENNReal.ofReal (w x)))) := by
  obtain ⟨A, hA⟩ := ha.2
  obtain ⟨D, hD⟩ := hb.2
  obtain ⟨K, hK⟩ := hc.2
  have hs : μ₀.toSignedMeasure =
      μ₁.withDensityᵥ a + (2 : ℝ) • aux_weightedCross b ν + μ₂.withDensityᵥ c := by
    apply VectorMeasure.ext
    intro T hT
    simp only [Measure.toSignedMeasure_apply_measurable hT,
      add_apply, smul_apply, smul_eq_mul]
    rw [withDensityᵥ_apply (aux_bm_integrable μ₁ ha) hT,
      aux_weightedCross_apply b hb.1 D hD ν T hT,
      withDensityᵥ_apply (aux_bm_integrable μ₂ hc) hT]
    exact h T hT
  have hI : signedIntegralOn μ₀.toSignedMeasure B w =
      signedIntegralOn
        (μ₁.withDensityᵥ a + (2 : ℝ) • aux_weightedCross b ν + μ₂.withDensityᵥ c) B w :=
    congrArg (fun s : SignedMeasure X => signedIntegralOn s B w) hs
  rw [aux_signedIntegralOn_toSignedMeasure μ₀ w hw C hC B,
    aux_signedIntegralOn_add _ _ B w hw C hC,
    aux_signedIntegralOn_add _ _ B w hw C hC,
    aux_signedIntegralOn_smul _ 2 B w,
    aux_signedIntegralOn_withDensity μ₁ a ha.1 A hA w hw C hC B,
    aux_signedIntegralOn_weightedCross b hb.1 D hD ν w hw C hC B,
    aux_signedIntegralOn_withDensity μ₂ c hc.1 K hK w hw C hC B] at hI
  rw [aux_withDensity_toReal μ₀ w hw h0 B hB,
    aux_integral_weighted_measure μ₁ w hw h0 a B,
    aux_signedIntegralOn_weightedCross w hw C hC ν b hb.1 D hD B,
    aux_integral_weighted_measure μ₂ w hw h0 c B]
  simpa only [mul_comm] using hI

lemma aux_weighted_leibniz_bounded (E : ClosedForm m) (Γ : EnergyMeasure E)
    (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x : X, |w x| ≤ C) (h0 : ∀ x : X, 0 ≤ w x)
    (u v : Lp ℝ 2 m) (hu : E.MemCore u) (hv : E.MemCore v)
    (uc vc : X → ℝ) (huc : Continuous uc) (hvc : Continuous vc)
    (hurep : ⇑u =ᵐ[m] uc) (hvrep : ⇑v =ᵐ[m] vc)
    (hub : aux_BM uc) (hvb : aux_BM vc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (z : Lp ℝ 2 m) (hz : z ∈ E.domain)
    (hzrep : ⇑z =ᵐ[m] fun x : X => vc x * Φ (uc x))
    (B : Set X) (hB : MeasurableSet B) :
    (((Γ.measure z).withDensity (fun x : X => ENNReal.ofReal (w x))) B).toReal =
      (∫ x in B, (vc x) ^ 2 * (deriv Φ (uc x)) ^ 2
        ∂((Γ.measure u).withDensity (fun x : X => ENNReal.ofReal (w x)))) +
        2 * signedIntegralOn (aux_weightedCross w (Γ.cross u v)) B
          (fun x : X => vc x * Φ (uc x) * deriv Φ (uc x)) +
        (∫ x in B, (Φ (uc x)) ^ 2
          ∂((Γ.measure v).withDensity (fun x : X => ENNReal.ofReal (w x)))) := by
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu.1⟩
  let : IsFiniteMeasure (Γ.measure v) := ⟨Γ.measure_univ_lt_top v hv.1⟩
  let : IsFiniteMeasure (Γ.measure z) := ⟨Γ.measure_univ_lt_top z hz⟩
  have hΦb : aux_BM (fun x : X => Φ (uc x)) := aux_bm_comp hub Φ hΦ.continuous
  have hdb : aux_BM (fun x : X => deriv Φ (uc x)) :=
    aux_bm_comp hub (deriv Φ) hΦ.continuous_deriv_one
  exact aux_weighted_set_identity (Γ.measure z) (Γ.measure u) (Γ.measure v)
    (Γ.cross u v)
    (fun x : X => (vc x) ^ 2 * (deriv Φ (uc x)) ^ 2)
    (fun x : X => vc x * Φ (uc x) * deriv Φ (uc x))
    (fun x : X => (Φ (uc x)) ^ 2)
    (aux_bm_mul (aux_bm_sq hvb) (aux_bm_sq hdb))
    (aux_bm_mul (aux_bm_mul hvb hΦb) hdb) (aux_bm_sq hΦb)
    w hw C hC h0
    (Γ.leibniz u v hu hv uc vc huc hvc hurep hvrep Φ hΦ z hz hzrep) B hB

lemma aux_weighted_leibniz (E : ClosedForm m) (Γ : EnergyMeasure E)
    (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x : X, |w x| ≤ C) (h0 : ∀ x : X, 0 ≤ w x)
    (u v : Lp ℝ 2 m) (hu : E.MemCore u) (hv : E.MemCore v)
    (uc vc : X → ℝ) (huc : Continuous uc) (hvc : Continuous vc)
    (hurep : ⇑u =ᵐ[m] uc) (hvrep : ⇑v =ᵐ[m] vc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (z : Lp ℝ 2 m) (hz : z ∈ E.domain)
    (hzrep : ⇑z =ᵐ[m] fun x : X => vc x * Φ (uc x))
    (B : Set X) (hB : MeasurableSet B) :
    (((Γ.measure z).withDensity (fun x : X => ENNReal.ofReal (w x))) B).toReal =
      (∫ x in B, (vc x) ^ 2 * (deriv Φ (uc x)) ^ 2
        ∂((Γ.measure u).withDensity (fun x : X => ENNReal.ofReal (w x)))) +
        2 * signedIntegralOn (aux_weightedCross w (Γ.cross u v)) B
          (fun x : X => vc x * Φ (uc x) * deriv Φ (uc x)) +
        (∫ x in B, (Φ (uc x)) ^ 2
          ∂((Γ.measure v).withDensity (fun x : X => ENNReal.ofReal (w x)))) := by
  obtain ⟨u₀, hu₀c, hu₀b, hu₀rep⟩ := aux_core_bounded_rep E u hu
  obtain ⟨v₀, hv₀c, hv₀b, hv₀rep⟩ := aux_core_bounded_rep E v hv
  have heu : uc =ᵐ[m] u₀ := hurep.symm.trans hu₀rep
  have hev : vc =ᵐ[m] v₀ := hvrep.symm.trans hv₀rep
  have hz₀rep : ⇑z =ᵐ[m] fun x : X => v₀ x * Φ (u₀ x) := by
    filter_upwards [hzrep, heu, hev] with x hx hux hvx
    simpa only [hux, hvx] using hx
  have hemeasure (a : Lp ℝ 2 m) (ha : a ∈ E.domain) :
      uc =ᵐ[(Γ.measure a).withDensity (fun x : X => ENNReal.ofReal (w x))] u₀ ∧
      vc =ᵐ[(Γ.measure a).withDensity (fun x : X => ENNReal.ofReal (w x))] v₀ :=
    ⟨aux_continuous_ae_weighted_energy E Γ a ha _ uc u₀ huc hu₀c heu,
      aux_continuous_ae_weighted_energy E Γ a ha _ vc v₀ hvc hv₀c hev⟩
  have hecrossu : uc =ᵐ[(aux_weightedCross w (Γ.cross u v)).totalVariation] u₀ :=
    aux_continuous_ae_weighted_cross E Γ u hu.1 v hv.1 w hw C hC
      uc u₀ huc hu₀c heu
  have hecrossv : vc =ᵐ[(aux_weightedCross w (Γ.cross u v)).totalVariation] v₀ :=
    aux_continuous_ae_weighted_cross E Γ u hu.1 v hv.1 w hw C hC
      vc v₀ hvc hv₀c hev
  have haeq :
      (∫ x in B, (vc x) ^ 2 * (deriv Φ (uc x)) ^ 2
        ∂((Γ.measure u).withDensity (fun x : X => ENNReal.ofReal (w x)))) =
      (∫ x in B, (v₀ x) ^ 2 * (deriv Φ (u₀ x)) ^ 2
        ∂((Γ.measure u).withDensity (fun x : X => ENNReal.ofReal (w x)))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (hemeasure u hu.1).1,
      ae_restrict_of_ae (hemeasure u hu.1).2] with x hux hvx
    try dsimp only
    rw [hux, hvx]
  have hbeq :
      signedIntegralOn (aux_weightedCross w (Γ.cross u v)) B
        (fun x : X => vc x * Φ (uc x) * deriv Φ (uc x)) =
      signedIntegralOn (aux_weightedCross w (Γ.cross u v)) B
        (fun x : X => v₀ x * Φ (u₀ x) * deriv Φ (u₀ x)) := by
    apply aux_signedIntegralOn_congr_ae
    filter_upwards [hecrossu, hecrossv] with x hux hvx
    try dsimp only
    rw [hux, hvx]
  have hceq :
      (∫ x in B, (Φ (uc x)) ^ 2
        ∂((Γ.measure v).withDensity (fun x : X => ENNReal.ofReal (w x)))) =
      (∫ x in B, (Φ (u₀ x)) ^ 2
        ∂((Γ.measure v).withDensity (fun x : X => ENNReal.ofReal (w x)))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (hemeasure v hv.1).1] with x hux
    try dsimp only
    rw [hux]
  rw [haeq, hbeq, hceq]
  exact aux_weighted_leibniz_bounded E Γ w hw C hC h0 u v hu hv
    u₀ v₀ hu₀c hv₀c hu₀rep hv₀rep hu₀b hv₀b Φ hΦ z hz hz₀rep B hB

omit [OpensMeasurableSpace X] in
lemma aux_cross_add_left [_instPreserved0 : OpensMeasurableSpace X] {m : Measure X} (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (v : Lp ℝ 2 m) (hv : v ∈ E.domain)
    (z : Lp ℝ 2 m) (hz : z ∈ E.domain) :
    Γ.cross (u + v) z = Γ.cross u z + Γ.cross v z := by
  rw [Γ.cross_symm (u + v) (E.domain.add_mem hu hv) z hz,
    Γ.cross_add_right z hz u hu v hv,
    Γ.cross_symm z hz u hu, Γ.cross_symm z hz v hv]

omit [OpensMeasurableSpace X] in
lemma aux_cross_quad [_instPreserved0 : OpensMeasurableSpace X] {m : Measure X} (E : ClosedForm m) (Γ : EnergyMeasure E)
    (p : Lp ℝ 2 m) (hp : p ∈ E.domain)
    (a : Lp ℝ 2 m) (ha : a ∈ E.domain) (t : ℝ) (B : Set X) :
    Γ.cross (p + t • a) (p + t • a) B =
      Γ.cross p p B + 2 * t * Γ.cross a p B + t ^ 2 * Γ.cross a a B := by
  have hta : t • a ∈ E.domain := E.domain.smul_mem t ha
  have hs : p + t • a ∈ E.domain := E.domain.add_mem hp hta
  rw [Γ.cross_add_right (p + t • a) hs p hp (t • a) hta,
    Γ.cross_smul_right t (p + t • a) hs a ha,
    Γ.cross_symm (p + t • a) hs p hp,
    Γ.cross_symm (p + t • a) hs a ha,
    Γ.cross_add_right p hp p hp (t • a) hta,
    Γ.cross_add_right a ha p hp (t • a) hta,
    Γ.cross_smul_right t p hp a ha,
    Γ.cross_smul_right t a ha a ha, Γ.cross_symm p hp a ha]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma aux_cross_diag_add (E : ClosedForm m) (Γ : EnergyMeasure E)
    (a : Lp ℝ 2 m) (ha : a ∈ E.domain)
    (b : Lp ℝ 2 m) (hb : b ∈ E.domain) :
    Γ.cross (a + b) (a + b) =
      Γ.cross a a + (2 : ℝ) • Γ.cross a b + Γ.cross b b := by
  apply VectorMeasure.ext
  intro B hB
  simp only [add_apply, smul_apply, smul_eq_mul]
  simpa only [one_smul, one_pow, mul_one, one_mul,
    Γ.cross_symm b hb a ha] using aux_cross_quad E Γ a ha b hb 1 B

omit [OpensMeasurableSpace X] in
lemma aux_cross_self_toSignedMeasure [_instPreserved0 : OpensMeasurableSpace X] {m : Measure X} (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain) [IsFiniteMeasure (Γ.measure u)] :
    Γ.cross u u = (Γ.measure u).toSignedMeasure := by
  apply VectorMeasure.ext
  intro B hB
  exact (Γ.cross_self u hu B hB).trans
    (Measure.toSignedMeasure_apply_measurable hB).symm

lemma aux_signedIntegralOn_cross_self (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (f : X → ℝ) (hf : aux_BM f) (B : Set X) :
    signedIntegralOn (Γ.cross u u) B f = ∫ x in B, f x ∂(Γ.measure u) := by
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
  obtain ⟨C, hC⟩ := hf.2
  rw [aux_cross_self_toSignedMeasure E Γ u hu]
  exact aux_signedIntegralOn_toSignedMeasure (Γ.measure u) f hf.1 C hC B

lemma aux_integral_measure_add (E : ClosedForm m) (Γ : EnergyMeasure E)
    (a : Lp ℝ 2 m) (ha : a ∈ E.domain)
    (b : Lp ℝ 2 m) (hb : b ∈ E.domain)
    (f : X → ℝ) (hf : aux_BM f) (B : Set X) :
    (∫ x in B, f x ∂(Γ.measure (a + b))) =
      (∫ x in B, f x ∂(Γ.measure a)) +
        2 * signedIntegralOn (Γ.cross a b) B f +
        (∫ x in B, f x ∂(Γ.measure b)) := by
  obtain ⟨C, hC⟩ := hf.2
  rw [← aux_signedIntegralOn_cross_self E Γ (a + b) (E.domain.add_mem ha hb) f hf B,
    aux_cross_diag_add E Γ a ha b hb,
    aux_signedIntegralOn_add _ _ B f hf.1 C hC,
    aux_signedIntegralOn_add _ _ B f hf.1 C hC,
    aux_signedIntegralOn_smul _ 2 B f,
    aux_signedIntegralOn_cross_self E Γ a ha f hf B,
    aux_signedIntegralOn_cross_self E Γ b hb f hf B]

lemma aux_deriv_affine (t s : ℝ) : deriv (fun x : ℝ => x + t) s = 1 := by
  exact ((hasDerivAt_id s).add_const t).deriv

lemma aux_cross_product (E : ClosedForm m) (Γ : EnergyMeasure E)
    (a b : Lp ℝ 2 m) (ha : E.MemCore a) (hb : E.MemCore b)
    (ac bc : X → ℝ) (hac : Continuous ac) (hbc : Continuous bc)
    (harep : ⇑a =ᵐ[m] ac) (hbrep : ⇑b =ᵐ[m] bc)
    (hab : aux_BM ac) (hbb : aux_BM bc)
    (p : Lp ℝ 2 m) (hp : p ∈ E.domain)
    (hprep : ⇑p =ᵐ[m] fun x : X => ac x * bc x)
    (B : Set X) (hB : MeasurableSet B) :
    Γ.cross a p B = (∫ x in B, bc x ∂(Γ.measure a)) +
      signedIntegralOn (Γ.cross a b) B ac := by
  let : IsFiniteMeasure (Γ.measure a) := ⟨Γ.measure_univ_lt_top a ha.1⟩
  let : IsFiniteMeasure (Γ.measure b) := ⟨Γ.measure_univ_lt_top b hb.1⟩
  have hshift (t : ℝ) :
      Γ.cross p p B + 2 * t * Γ.cross a p B + t ^ 2 * Γ.cross a a B =
        (∫ x in B, (ac x) ^ 2 ∂(Γ.measure b)) +
          2 * signedIntegralOn (Γ.cross b a) B (fun x : X => ac x * (bc x + t)) +
          (∫ x in B, (bc x + t) ^ 2 ∂(Γ.measure a)) := by
    have hpa : p + t • a ∈ E.domain := E.domain.add_mem hp (E.domain.smul_mem t ha.1)
    have hparep : ⇑(p + t • a) =ᵐ[m] fun x : X => ac x * (bc x + t) := by
      have hsumrep : ⇑(p + t • a) =ᵐ[m]
          fun x : X => ac x * bc x + t * ac x :=
        aux_rep_add p (t • a) (fun x : X => ac x * bc x)
          (fun x : X => t * ac x) hprep (aux_rep_smul t a ac harep)
      filter_upwards [hsumrep] with x hx
      try dsimp only at hx ⊢
      rw [hx]
      ring
    calc
      _ = Γ.cross (p + t • a) (p + t • a) B :=
        (aux_cross_quad E Γ p hp a ha.1 t B).symm
      _ = (Γ.measure (p + t • a) B).toReal := Γ.cross_self (p + t • a) hpa B hB
      _ = _ := by
        simpa only [aux_deriv_affine, one_pow, mul_one] using
          Γ.leibniz b a hb ha bc ac hbc hac hbrep harep
            (fun s : ℝ => s + t) (contDiff_id.add contDiff_const)
            (p + t • a) hpa hparep B hB
  have hIdiff :
      (∫ x in B, (bc x + 1) ^ 2 ∂(Γ.measure a)) -
        (∫ x in B, (bc x + (-1)) ^ 2 ∂(Γ.measure a)) =
      4 * (∫ x in B, bc x ∂(Γ.measure a)) :=
    aux_integral_square_shift_diff (Γ.measure a) bc hbb B
  have hSdiff :
      signedIntegralOn (Γ.cross b a) B (fun x : X => ac x * (bc x + 1)) -
        signedIntegralOn (Γ.cross b a) B (fun x : X => ac x * (bc x + (-1))) =
      2 * signedIntegralOn (Γ.cross b a) B ac :=
    aux_signedIntegralOn_mul_shift_diff (Γ.cross b a) ac bc hab hbb B
  have hresult : Γ.cross a p B = (∫ x in B, bc x ∂(Γ.measure a)) +
      signedIntegralOn (Γ.cross b a) B ac := by
    linarith only [hshift 1, hshift (-1), hIdiff, hSdiff]
  rw [Γ.cross_symm b hb.1 a ha.1] at hresult
  exact hresult

lemma aux_cross_square (E : ClosedForm m) (Γ : EnergyMeasure E)
    (a b : Lp ℝ 2 m) (ha : E.MemCore a) (hb : E.MemCore b)
    (ac bc : X → ℝ) (hac : Continuous ac) (hbc : Continuous bc)
    (harep : ⇑a =ᵐ[m] ac) (hbrep : ⇑b =ᵐ[m] bc)
    (hab : aux_BM ac) (hbb : aux_BM bc)
    (p s : Lp ℝ 2 m) (hp : p ∈ E.domain) (hs : s ∈ E.domain)
    (hprep : ⇑p =ᵐ[m] fun x : X => ac x * bc x)
    (hsrep : ⇑s =ᵐ[m] fun x : X => ac x ^ 2)
    (B : Set X) (hB : MeasurableSet B) :
    Γ.cross s b B = 2 * signedIntegralOn (Γ.cross a b) B ac := by
  let : IsFiniteMeasure (Γ.measure a) := ⟨Γ.measure_univ_lt_top a ha.1⟩
  let : IsFiniteMeasure (Γ.measure b) := ⟨Γ.measure_univ_lt_top b hb.1⟩
  have hsrep' : ⇑s =ᵐ[m] fun x : X => ac x * ac x := by
    simpa only [pow_two] using hsrep
  have hprep' : ⇑p =ᵐ[m] fun x : X => bc x * ac x := by
    simpa only [mul_comm] using hprep
  have hsumcore : E.MemCore (a + b) := aux_memCore_add E a b ha hb
  have hsumrep : ⇑(a + b) =ᵐ[m] fun x : X => ac x + bc x :=
    aux_rep_add a b ac bc harep hbrep
  have hsp : s + p ∈ E.domain := E.domain.add_mem hs hp
  have hsprep : ⇑(s + p) =ᵐ[m] fun x : X => (ac x + bc x) * ac x := by
    have hrep : ⇑(s + p) =ᵐ[m] fun x : X => ac x ^ 2 + ac x * bc x :=
      aux_rep_add s p (fun x : X => ac x ^ 2) (fun x : X => ac x * bc x) hsrep hprep
    filter_upwards [hrep] with x hx
    try dsimp only at hx ⊢
    rw [hx]
    ring
  have haa : Γ.cross a s B = (∫ x in B, ac x ∂(Γ.measure a)) +
      signedIntegralOn (Γ.cross a a) B ac :=
    aux_cross_product E Γ a a ha ha ac ac hac hac harep harep hab hab s hs hsrep' B hB
  rw [aux_signedIntegralOn_cross_self E Γ a ha.1 ac hab B] at haa
  have habp : Γ.cross a p B = (∫ x in B, bc x ∂(Γ.measure a)) +
      signedIntegralOn (Γ.cross a b) B ac :=
    aux_cross_product E Γ a b ha hb ac bc hac hbc harep hbrep hab hbb p hp hprep B hB
  have hbap : Γ.cross b p B = (∫ x in B, ac x ∂(Γ.measure b)) +
      signedIntegralOn (Γ.cross b a) B bc :=
    aux_cross_product E Γ b a hb ha bc ac hbc hac hbrep harep hbb hab p hp hprep' B hB
  rw [Γ.cross_symm b hb.1 a ha.1] at hbap
  have hsum : Γ.cross (a + b) (s + p) B =
      (∫ x in B, ac x ∂(Γ.measure (a + b))) +
        signedIntegralOn (Γ.cross (a + b) a) B (fun x : X => ac x + bc x) :=
    aux_cross_product E Γ (a + b) a hsumcore ha (fun x : X => ac x + bc x) ac
      (hac.add hbc) hac hsumrep harep (aux_bm_add hab hbb) hab (s + p) hsp hsprep B hB
  have hleft : Γ.cross (a + b) (s + p) B =
      Γ.cross a s B + Γ.cross a p B + Γ.cross b s B + Γ.cross b p B := by
    rw [aux_cross_add_left E Γ a ha.1 b hb.1 (s + p) hsp,
      Γ.cross_add_right a ha.1 s hs p hp, Γ.cross_add_right b hb.1 s hs p hp]
    simp only [add_apply]
    ring
  have hI : (∫ x in B, ac x ∂(Γ.measure (a + b))) =
      (∫ x in B, ac x ∂(Γ.measure a)) +
        2 * signedIntegralOn (Γ.cross a b) B ac +
        (∫ x in B, ac x ∂(Γ.measure b)) :=
    aux_integral_measure_add E Γ a ha.1 b hb.1 ac hab B
  have hS : signedIntegralOn (Γ.cross (a + b) a) B (fun x : X => ac x + bc x) =
      (∫ x in B, ac x ∂(Γ.measure a)) + (∫ x in B, bc x ∂(Γ.measure a)) +
        signedIntegralOn (Γ.cross a b) B ac + signedIntegralOn (Γ.cross a b) B bc := by
    obtain ⟨D, hD⟩ := (aux_bm_add hab hbb).2
    rw [aux_cross_add_left E Γ a ha.1 b hb.1 a ha.1,
      Γ.cross_symm b hb.1 a ha.1,
      aux_signedIntegralOn_add _ _ B (fun x : X => ac x + bc x)
        (aux_bm_add hab hbb).1 D hD,
      aux_signedIntegralOn_cross_self E Γ a ha.1 (fun x : X => ac x + bc x)
        (aux_bm_add hab hbb) B,
      aux_setIntegral_fun_add (Γ.measure a) ac bc hab hbb B,
      aux_signedIntegralOn_fun_add (Γ.cross a b) ac bc hab hbb B]
    ring
  rw [Γ.cross_symm s hs b hb.1]
  linarith only [haa, habp, hbap, hsum, hleft, hI, hS]

lemma aux_defining_cross_identity (E : ClosedForm m) (Γ : EnergyMeasure E)
    (u φ : Lp ℝ 2 m) (hu : E.MemCore u) (hφ : E.MemCore φ)
    (uc φc : X → ℝ) (huc : Continuous uc) (hφc : Continuous φc)
    (hurep : ⇑u =ᵐ[m] uc) (hφrep : ⇑φ =ᵐ[m] φc)
    (hub : aux_BM uc) (hφb : aux_BM φc)
    (uφ u2 : Lp ℝ 2 m) (huφ : uφ ∈ E.domain) (hu2 : u2 ∈ E.domain)
    (huφrep : ⇑uφ =ᵐ[m] fun x : X => uc x * φc x)
    (hu2rep : ⇑u2 =ᵐ[m] fun x : X => uc x ^ 2) :
    (Γ.measure u).withDensityᵥ φc =
      Γ.cross u uφ - (1 / 2 : ℝ) • Γ.cross u2 φ := by
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu.1⟩
  apply VectorMeasure.ext
  intro B hB
  rw [withDensityᵥ_apply (aux_bm_integrable (Γ.measure u) hφb) hB,
    sub_apply, smul_apply, smul_eq_mul]
  have hp : Γ.cross u uφ B = (∫ x in B, φc x ∂(Γ.measure u)) +
      signedIntegralOn (Γ.cross u φ) B uc :=
    aux_cross_product E Γ u φ hu hφ uc φc huc hφc hurep hφrep hub hφb uφ huφ huφrep B hB
  have hs : Γ.cross u2 φ B = 2 * signedIntegralOn (Γ.cross u φ) B uc :=
    aux_cross_square E Γ u φ hu hφ uc φc huc hφc hurep hφrep hub hφb
      uφ u2 huφ hu2 huφrep hu2rep B hB
  linarith only [hp, hs]

lemma aux_weighted_defining_identity_bounded (E : ClosedForm m) (Γ : EnergyMeasure E)
    (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x : X, |w x| ≤ C) (h0 : ∀ x : X, 0 ≤ w x)
    (F : ClosedForm m) (hweighted : IsWeightedForm E F Γ w)
    (u φ : Lp ℝ 2 m) (hu : E.MemCore u) (hφ : E.MemCore φ)
    (uc φc : X → ℝ) (huc : Continuous uc) (hφc : Continuous φc)
    (hurep : ⇑u =ᵐ[m] uc) (hφrep : ⇑φ =ᵐ[m] φc)
    (hub : aux_BM uc) (hφb : aux_BM φc)
    (uφ u2 : Lp ℝ 2 m) (huφ : uφ ∈ E.domain) (hu2 : u2 ∈ E.domain)
    (huφrep : ⇑uφ =ᵐ[m] fun x : X => uc x * φc x)
    (hu2rep : ⇑u2 =ᵐ[m] fun x : X => uc x ^ 2) :
    (∫ x, φc x ∂((Γ.measure u).withDensity (fun x : X => ENNReal.ofReal (w x)))) =
      F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ := by
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu.1⟩
  obtain ⟨D, hD⟩ := hφb.2
  have hmeasure : (Γ.measure u).withDensityᵥ φc =
      Γ.cross u uφ - (1 / 2 : ℝ) • Γ.cross u2 φ :=
    aux_defining_cross_identity E Γ u φ hu hφ uc φc huc hφc hurep hφrep hub hφb
      uφ u2 huφ hu2 huφrep hu2rep
  have hI : signedIntegralOn ((Γ.measure u).withDensityᵥ φc) Set.univ w =
      signedIntegralOn (Γ.cross u uφ - (1 / 2 : ℝ) • Γ.cross u2 φ) Set.univ w :=
    congrArg (fun ν : SignedMeasure X => signedIntegralOn ν Set.univ w) hmeasure
  rw [aux_signedIntegralOn_withDensity (Γ.measure u) φc hφb.1 D hD
      w hw C hC Set.univ,
    aux_signedIntegralOn_sub _ _ Set.univ w hw C hC,
    aux_signedIntegralOn_smul _ (1 / 2 : ℝ) Set.univ w] at hI
  rw [hweighted.form_eq u hu.1 uφ huφ, hweighted.form_eq u2 hu2 φ hφ.1]
  calc
    _ = ∫ x, φc x * w x ∂(Γ.measure u) := by
      simpa only [Measure.restrict_univ] using
        aux_integral_weighted_measure (Γ.measure u) w hw h0 φc Set.univ
    _ = _ := by simpa only [Measure.restrict_univ, mul_comm] using hI

lemma aux_weighted_defining_identity (E : ClosedForm m) (Γ : EnergyMeasure E)
    (w : X → ℝ) (hw : Measurable w)
    (C : ℝ) (hC : ∀ x : X, |w x| ≤ C) (h0 : ∀ x : X, 0 ≤ w x)
    (F : ClosedForm m) (hweighted : IsWeightedForm E F Γ w)
    (u φ : Lp ℝ 2 m) (hu : E.MemCore u) (hφ : E.MemCore φ)
    (uc φc : X → ℝ) (_huc : Continuous uc) (hφc : Continuous φc)
    (hurep : ⇑u =ᵐ[m] uc) (hφrep : ⇑φ =ᵐ[m] φc)
    (uφ u2 : Lp ℝ 2 m) (huφ : uφ ∈ E.domain) (hu2 : u2 ∈ E.domain)
    (huφrep : ⇑uφ =ᵐ[m] fun x : X => uc x * φc x)
    (hu2rep : ⇑u2 =ᵐ[m] fun x : X => uc x ^ 2) :
    (∫ x, φc x ∂((Γ.measure u).withDensity (fun x : X => ENNReal.ofReal (w x)))) =
      F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ := by
  obtain ⟨u₀, hu₀c, hu₀b, hu₀rep⟩ := aux_core_bounded_rep E u hu
  obtain ⟨φ₀, hφ₀c, hφ₀b, hφ₀rep⟩ := aux_core_bounded_rep E φ hφ
  have heu : uc =ᵐ[m] u₀ := hurep.symm.trans hu₀rep
  have heφ : φc =ᵐ[m] φ₀ := hφrep.symm.trans hφ₀rep
  have huφ₀rep : ⇑uφ =ᵐ[m] fun x : X => u₀ x * φ₀ x := by
    filter_upwards [huφrep, heu, heφ] with x hx hux hφx
    simpa only [hux, hφx] using hx
  have hu2₀rep : ⇑u2 =ᵐ[m] fun x : X => u₀ x ^ 2 := by
    filter_upwards [hu2rep, heu] with x hx hux
    simpa only [hux] using hx
  have heint :
      (∫ x, φc x ∂((Γ.measure u).withDensity (fun x : X => ENNReal.ofReal (w x)))) =
      (∫ x, φ₀ x ∂((Γ.measure u).withDensity (fun x : X => ENNReal.ofReal (w x)))) := by
    apply integral_congr_ae
    exact aux_continuous_ae_weighted_energy E Γ u hu.1 _ φc φ₀ hφc hφ₀c heφ
  rw [heint]
  exact aux_weighted_defining_identity_bounded E Γ w hw C hC h0 F hweighted u φ hu hφ
    u₀ φ₀ hu₀c hφ₀c hu₀rep hφ₀rep hu₀b hφ₀b uφ u2 huφ hu2 huφ₀rep hu2₀rep

def aux_weightedEnergyMeasure (E : ClosedForm m) (Γ : EnergyMeasure E)
    (w : X → ℝ) (hw : Measurable w) (C : ℝ)
    (hC : ∀ x, |w x| ≤ C) (h0 : ∀ x, 0 ≤ w x)
    (F : ClosedForm m) (hweighted : IsWeightedForm E F Γ w) :
    EnergyMeasure F := by
  let ρ : X → ENNReal := fun x => ENNReal.ofReal (w x)
  let μ : Lp ℝ 2 m → Measure X := fun u => (Γ.measure u).withDensity ρ
  let k : Lp ℝ 2 m → Lp ℝ 2 m → SignedMeasure X :=
    fun u v => aux_weightedCross w (Γ.cross u v)
  have hdom (u : Lp ℝ 2 m) (hu : u ∈ F.domain) : u ∈ E.domain := by
    rw [hweighted.domain_eq] at hu
    exact hu
  have hρ (x : X) : ρ x ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal ((le_abs_self (w x)).trans (hC x))
  have hsym (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
      (v : Lp ℝ 2 m) (hv : v ∈ E.domain) : k u v = k v u := by
    change aux_weightedCross w (Γ.cross u v) = aux_weightedCross w (Γ.cross v u)
    rw [Γ.cross_symm u hu v hv]
  have hadd (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
      (v : Lp ℝ 2 m) (hv : v ∈ E.domain)
      (z : Lp ℝ 2 m) (hz : z ∈ E.domain) :
      k u (v + z) = k u v + k u z := by
    change aux_weightedCross w (Γ.cross u (v + z)) =
      aux_weightedCross w (Γ.cross u v) + aux_weightedCross w (Γ.cross u z)
    rw [Γ.cross_add_right u hu v hv z hz]
    exact aux_weightedCross_add w hw C hC (Γ.cross u v) (Γ.cross u z)
  have hsmul (c : ℝ) (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
      (v : Lp ℝ 2 m) (hv : v ∈ E.domain) : k u (c • v) = c • k u v := by
    change aux_weightedCross w (Γ.cross u (c • v)) =
      c • aux_weightedCross w (Γ.cross u v)
    rw [Γ.cross_smul_right c u hu v hv]
    exact aux_weightedCross_smul w hw C hC (Γ.cross u v) c
  have hself (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
      (B : Set X) (hB : MeasurableSet B) : k u u B = (μ u B).toReal := by
    let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
    have hdiag : Γ.cross u u = (Γ.measure u).toSignedMeasure := by
      apply VectorMeasure.ext
      intro A hA
      calc
        Γ.cross u u A = (Γ.measure u A).toReal := Γ.cross_self u hu A hA
        _ = (Γ.measure u).toSignedMeasure A :=
          (Measure.toSignedMeasure_apply_measurable hA).symm
    change aux_weightedCross w (Γ.cross u u) B =
      (((Γ.measure u).withDensity (fun x => ENNReal.ofReal (w x))) B).toReal
    rw [aux_weightedCross_apply w hw C hC (Γ.cross u u) B hB, hdiag,
      aux_signedIntegralOn_toSignedMeasure (Γ.measure u) w hw C hC B]
    exact (aux_withDensity_toReal (Γ.measure u) w hw h0 B hB).symm
  have hcore (u : Lp ℝ 2 m) (hu : F.MemCore u) : E.MemCore u :=
    ⟨hdom u hu.1, hu.2⟩
  refine {
    measure := μ
    cross := k
    measure_univ_lt_top := ?_
    measure_univ := ?_
    cross_symm := ?_
    cross_self := ?_
    cross_add_right := ?_
    cross_smul_right := ?_
    cross_univ := ?_
    abs_cross_le := ?_
    locality := ?_
    regular := ?_
    measure_compl_tsupport := ?_
    chain_rule := ?_
    leibniz := ?_
    defining_identity := ?_
  }
  · intro u hu
    let : IsFiniteMeasure (Γ.measure u) :=
      ⟨Γ.measure_univ_lt_top u (hdom u hu)⟩
    let : IsFiniteMeasure (μ u) := aux_finite_withDensity (Γ.measure u) ρ C hρ
    exact measure_lt_top (μ u) Set.univ
  · intro u hu
    change (((Γ.measure u).withDensity (fun x => ENNReal.ofReal (w x)))
      Set.univ).toReal = F.form u u
    calc
      _ = ∫ x, w x ∂(Γ.measure u) := by
        simpa only [Measure.restrict_univ] using
          aux_withDensity_toReal (Γ.measure u) w hw h0 Set.univ MeasurableSet.univ
      _ = F.form u u := (hweighted.energy_eq u (hdom u hu)).symm
  · intro u hu v hv
    exact hsym u (hdom u hu) v (hdom v hv)
  · intro u hu B hB
    exact hself u (hdom u hu) B hB
  · intro u hu v hv z hz
    exact hadd u (hdom u hu) v (hdom v hv) z (hdom z hz)
  · intro c u hu v hv
    exact hsmul c u (hdom u hu) v (hdom v hv)
  · intro u hu v hv
    change aux_weightedCross w (Γ.cross u v) Set.univ = F.form u v
    rw [aux_weightedCross_apply w hw C hC (Γ.cross u v) Set.univ MeasurableSet.univ]
    exact (hweighted.form_eq u (hdom u hu) v (hdom v hv)).symm
  · intro u hu v hv B hB
    have hb0 (a : Lp ℝ 2 m) (ha : a ∈ E.domain) : 0 ≤ k a a B := by
      rw [hself a ha B hB]
      exact ENNReal.toReal_nonneg
    have hbadd : ∀ a ∈ E.domain, ∀ b ∈ E.domain, ∀ c ∈ E.domain,
        k a (b + c) B = k a b B + k a c B := by
      intro a ha b hb c hc
      rw [hadd a ha b hb c hc, add_apply]
    have hbsmul : ∀ (c : ℝ), ∀ a ∈ E.domain, ∀ b ∈ E.domain,
        k a (c • b) B = c * k a b B := by
      intro c a ha b hb
      rw [hsmul c a ha b hb, smul_apply, smul_eq_mul]
    have hb : |k u v B| ≤ Real.sqrt (k u u B) * Real.sqrt (k v v B) :=
      aux_bilinear_abs_le E.domain (fun a b => k a b B)
        (fun a ha b hb => congrArg (fun ν : SignedMeasure X => ν B) (hsym a ha b hb))
        hbadd hbsmul hb0 (hdom u hu) (hdom v hv)
    rw [hself u (hdom u hu) B hB, hself v (hdom v hv) B hB] at hb
    exact hb
  · intro u hu v hv O hO huv
    let : IsFiniteMeasure (Γ.measure u) :=
      ⟨Γ.measure_univ_lt_top u (hdom u hu)⟩
    let : IsFiniteMeasure (Γ.measure v) :=
      ⟨Γ.measure_univ_lt_top v (hdom v hv)⟩
    change ((Γ.measure u).withDensity ρ).restrict O =
      ((Γ.measure v).withDensity ρ).restrict O
    rw [restrict_withDensity' (μ := Γ.measure u) O ρ,
      restrict_withDensity' (μ := Γ.measure v) O ρ]
    exact congrArg (fun ν : Measure X => ν.withDensity ρ)
      (Γ.locality u (hdom u hu) v (hdom v hv) O hO huv)
  · intro u hu
    let : IsFiniteMeasure (Γ.measure u) :=
      ⟨Γ.measure_univ_lt_top u (hdom u hu)⟩
    let : (Γ.measure u).Regular := Γ.regular u (hdom u hu)
    exact aux_regular_withDensity_of_bounded (Γ.measure u) ρ C hρ
  · intro u hu f hf huf
    exact (withDensity_absolutelyContinuous (Γ.measure u) ρ)
      (Γ.measure_compl_tsupport u (hdom u hu) f hf huf)
  · intro u hu uc huc hurep Φ hΦ hΦ0 z hz hzrep B hB
    exact aux_weighted_chain_rule E Γ w hw u (hdom u hu) uc huc hurep
      Φ hΦ hΦ0 z (hdom z hz) hzrep B hB
  · intro u v hu hv uc vc huc hvc hurep hvrep Φ hΦ z hz hzrep B hB
    exact aux_weighted_leibniz E Γ w hw C hC h0 u v (hcore u hu) (hcore v hv)
      uc vc huc hvc hurep hvrep Φ hΦ z (hdom z hz) hzrep B hB
  · intro u φ hu hφ uc φc huc hφc hurep hφrep uφ u2 huφ hu2 huφrep hu2rep
    exact aux_weighted_defining_identity E Γ w hw C hC h0 F hweighted
      u φ (hcore u hu) (hcore φ hφ) uc φc huc hφc hurep hφrep
      uφ u2 (hdom uφ huφ) (hdom u2 hu2) huφrep hu2rep

omit [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] in
lemma aux_exp_abs_bound [_instPreserved0 : MeasurableSpace X] [_instPreserved1 : TopologicalSpace X] [_instPreserved2 : OpensMeasurableSpace X] (g : X → ℝ) (M : ℝ)
    (hgbdd : ∀ x, |g x| ≤ M) : ∀ x, |Real.exp (g x)| ≤ Real.exp M := by
  intro x
  rw [abs_of_pos (Real.exp_pos (g x))]
  exact Real.exp_le_exp.mpr ((le_abs_self (g x)).trans (hgbdd x))

def aux_weightedEnergyMeasure_exp (E : ClosedForm m) (Γ : EnergyMeasure E)
    (g : X → ℝ) (hg : Measurable g) (M : ℝ) (hgbdd : ∀ x : X, |g x| ≤ M)
    (F : ClosedForm m)
    (hweighted : IsWeightedForm E F Γ (fun x => Real.exp (g x))) :
    EnergyMeasure F :=
  aux_weightedEnergyMeasure E Γ (fun x => Real.exp (g x)) hg.exp
    (Real.exp M) (aux_exp_abs_bound g M hgbdd)
    (fun x => (Real.exp_pos (g x)).le) F hweighted

lemma aux_weightedEnergyMeasure_measure (E : ClosedForm m) (Γ : EnergyMeasure E)
    (g : X → ℝ) (hg : Measurable g) (M : ℝ) (hgbdd : ∀ x : X, |g x| ≤ M)
    (F : ClosedForm m)
    (hweighted : IsWeightedForm E F Γ (fun x => Real.exp (g x)))
    (u : Lp ℝ 2 m) :
    (aux_weightedEnergyMeasure_exp E Γ g hg M hgbdd F hweighted).measure u =
      (Γ.measure u).withDensity (fun x => ENNReal.ofReal (Real.exp (g x))) := by
  rfl

theorem aux_exists_weighted_energyMeasure (E : ClosedForm m) (Γ : EnergyMeasure E)
    (g : X → ℝ) (hg : Measurable g) (M : ℝ) (hgbdd : ∀ x : X, |g x| ≤ M)
    (_halg : IsCoreAlgebra E)
    (F : ClosedForm m)
    (hweighted : IsWeightedForm E F Γ (fun x => Real.exp (g x))) :
    ∃ GammaF : EnergyMeasure F,
      ∀ u ∈ E.domain, ∀ v ∈ E.domain,
        ∀ B : Set X, MeasurableSet B →
          GammaF.cross u v B =
            signedIntegralOn (Γ.cross u v) B (fun x => Real.exp (g x)) := by
  refine ⟨aux_weightedEnergyMeasure_exp E Γ g hg M hgbdd F hweighted, ?_⟩
  intro u hu v hv B hB
  change aux_weightedCross (fun x => Real.exp (g x)) (Γ.cross u v) B =
    signedIntegralOn (Γ.cross u v) B (fun x => Real.exp (g x))
  exact aux_weightedCross_apply (fun x => Real.exp (g x)) hg.exp
    (Real.exp M) (aux_exp_abs_bound g M hgbdd) (Γ.cross u v) B hB

theorem aux_weightedEnergyMeasure_chain_rule_measure
    (E : ClosedForm m) (Γ : EnergyMeasure E)
    (g : X → ℝ) (hg : Measurable g) (M : ℝ) (hgbdd : ∀ x : X, |g x| ≤ M)
    (F : ClosedForm m)
    (hweighted : IsWeightedForm E F Γ (fun x : X => Real.exp (g x)))
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (uc : X → ℝ) (huc : Continuous uc) (hurep : ⇑u =ᵐ[m] uc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    (v : Lp ℝ 2 m) (hv : v ∈ E.domain)
    (hvrep : ⇑v =ᵐ[m] fun x : X => Φ (uc x)) :
    (aux_weightedEnergyMeasure_exp E Γ g hg M hgbdd F hweighted).measure v =
      ((aux_weightedEnergyMeasure_exp E Γ g hg M hgbdd F hweighted).measure u).withDensity
        (fun x : X => ENNReal.ofReal ((deriv Φ (uc x)) ^ 2)) := by
  have huF : u ∈ F.domain := by rw [hweighted.domain_eq]; exact hu
  have hvF : v ∈ F.domain := by rw [hweighted.domain_eq]; exact hv
  exact aux_chain_rule_measure F (aux_weightedEnergyMeasure_exp E Γ g hg M hgbdd F hweighted)
    u huF uc huc hurep Φ hΦ hΦ0 v hvF hvrep

end SubdiffusiveProcess.DirichletForm

end AuxWEM

namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}



theorem lem_borel_weights_energy_measure
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (M : ℝ) (hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (halg : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra E.toClosedForm)
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hweighted : _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm E.toClosedForm F Gamma
      (fun x => Real.exp (g x))) :
    ∃ GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F,
      ∀ u ∈ E.toClosedForm.domain, ∀ v ∈ E.toClosedForm.domain,
        ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
          GammaF.cross u v B =
            _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) B
              (fun x => Real.exp (g x)) := by
  exact _root_.SubdiffusiveProcess.DirichletForm.aux_exists_weighted_energyMeasure E.toClosedForm Gamma g hg M hgbdd halg F hweighted

end SubdiffusiveProcess.Paper
