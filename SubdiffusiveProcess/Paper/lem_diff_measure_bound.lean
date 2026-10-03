module

public import SubdiffusiveProcess.Paper.lem_diff_measure_density
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

theorem aux_lem_diff_measure_bound_tv
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Integrable f μ) (B : Set α) (hB : MeasurableSet B) :
    (SignedMeasure.totalVariation (μ.withDensityᵥ f) B).toReal ≤
      ∫ x in B, |f x| ∂μ := by
  classical
  let s : SignedMeasure α := μ.withDensityᵥ f
  obtain ⟨i, hi, hipos, hineg, hpos, hneg⟩ := s.toJordanDecomposition_spec
  have hpos' : s.toJordanDecomposition.posPart B =
      s.toMeasureOfZeroLE i hi hipos B := by rw [hpos]
  have hneg' : s.toJordanDecomposition.negPart B =
      s.toMeasureOfLEZero iᶜ hi.compl hineg B := by rw [hneg]
  rw [show SignedMeasure.totalVariation s B =
      s.toJordanDecomposition.posPart B + s.toJordanDecomposition.negPart B by
        rfl, hpos', hneg', ENNReal.toReal_add]
  change (s.toMeasureOfZeroLE i hi hipos).real B +
      (s.toMeasureOfLEZero iᶜ hi.compl hineg).real B ≤ ∫ x in B, |f x| ∂μ
  · rw [SignedMeasure.toMeasureOfZeroLE_real_apply s hipos hi hB,
      SignedMeasure.toMeasureOfLEZero_real_apply s hineg hi.compl hB]
    rw [withDensityᵥ_apply hf (hi.inter hB),
      withDensityᵥ_apply hf (hi.compl.inter hB)]
    have hfi : Integrable (fun x => |f x|) μ := hf.norm
    have hfi_i : IntegrableOn (fun x => |f x|) (i ∩ B) μ :=
      hfi.mono_measure Measure.restrict_le_self
    have hfi_ic : IntegrableOn (fun x => |f x|) (iᶜ ∩ B) μ :=
      hfi.mono_measure Measure.restrict_le_self
    have hi_f : ∫ x in i ∩ B, f x ∂μ ≤ ∫ x in i ∩ B, |f x| ∂μ := by
      apply setIntegral_mono_ae_restrict hf.integrableOn hfi_i
      filter_upwards [] with x
      exact le_abs_self _
    have hic_f : ∫ x in iᶜ ∩ B, -f x ∂μ ≤ ∫ x in iᶜ ∩ B, |f x| ∂μ := by
      apply setIntegral_mono_ae_restrict hf.neg.integrableOn hfi_ic
      filter_upwards [] with x
      exact neg_le_abs _
    have hdisj : Disjoint (i ∩ B) (iᶜ ∩ B) :=
      Set.disjoint_of_subset_left inter_subset_left
        (Set.disjoint_of_subset_right inter_subset_left disjoint_compl_right)
    have hunion : i ∩ B ∪ iᶜ ∩ B = B := by
      rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
    have hpart :
        (∫ x in i ∩ B, |f x| ∂μ) + (∫ x in iᶜ ∩ B, |f x| ∂μ) =
          ∫ x in B, |f x| ∂μ := by
      calc
        _ = ∫ x in i ∩ B ∪ iᶜ ∩ B, |f x| ∂μ :=
          (integral_union_ae hdisj.aedisjoint (hi.compl.inter hB).nullMeasurableSet
            hfi_i hfi_ic).symm
        _ = ∫ x in B, |f x| ∂μ := by rw [hunion]
    have hneg_eq : -(∫ x in iᶜ ∩ B, f x ∂μ) = ∫ x in iᶜ ∩ B, -f x ∂μ := by
      rw [integral_neg]
    calc
      (∫ x in i ∩ B, f x ∂μ) + -(∫ x in iᶜ ∩ B, f x ∂μ) =
          (∫ x in i ∩ B, f x ∂μ) + (∫ x in iᶜ ∩ B, -f x ∂μ) := by rw [hneg_eq]
      _ ≤ (∫ x in i ∩ B, |f x| ∂μ) + (∫ x in iᶜ ∩ B, |f x| ∂μ) :=
        add_le_add hi_f hic_f
      _ = ∫ x in B, |f x| ∂μ := hpart
  · rw [← hpos']
    exact (measure_lt_top _ _).ne
  · rw [← hneg']
    exact (measure_lt_top _ _).ne

theorem aux_lem_diff_measure_bound_density_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Integrable f μ) (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x)
    (B : Set α) (hB : MeasurableSet B) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x)) B).toReal =
      ∫ x in B, f x ∂μ := by
  rw [withDensity_apply _ hB]
  symm
  exact integral_eq_lintegral_of_nonneg_ae (μ := μ.restrict B)
    (ae_restrict_of_ae hf_nonneg) hf.aestronglyMeasurable.restrict

theorem aux_lem_diff_measure_bound_sqrt_product_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (eU eV : α → ℝ) (hU : Integrable eU μ) (hV : Integrable eV μ)
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ eU x ∧ 0 ≤ eV x) :
    Integrable (fun x => Real.sqrt (eU x * eV x)) μ := by
  have h_nonneg_U : ∀ᵐ x ∂μ, 0 ≤ eU x :=
    h_nonneg.mono fun x hx => hx.1
  have h_nonneg_V : ∀ᵐ x ∂μ, 0 ≤ eV x :=
    h_nonneg.mono fun x hx => hx.2
  have hU_sqrt_meas : AEStronglyMeasurable (fun x => Real.sqrt (eU x)) μ :=
    (hU.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hV_sqrt_meas : AEStronglyMeasurable (fun x => Real.sqrt (eV x)) μ :=
    (hV.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hU_sqrt_sq : Integrable (fun x => (Real.sqrt (eU x)) ^ 2) μ := by
    apply hU.congr
    filter_upwards [h_nonneg_U] with x hx
    exact (Real.sq_sqrt hx).symm
  have hV_sqrt_sq : Integrable (fun x => (Real.sqrt (eV x)) ^ 2) μ := by
    apply hV.congr
    filter_upwards [h_nonneg_V] with x hx
    exact (Real.sq_sqrt hx).symm
  have hU_mem : MemLp (fun x => Real.sqrt (eU x)) (2 : ℝ≥0∞) μ :=
    (memLp_two_iff_integrable_sq hU_sqrt_meas).2 hU_sqrt_sq
  have hV_mem : MemLp (fun x => Real.sqrt (eV x)) (2 : ℝ≥0∞) μ :=
    (memLp_two_iff_integrable_sq hV_sqrt_meas).2 hV_sqrt_sq
  have hprod : Integrable
      (fun x => Real.sqrt (eU x) * Real.sqrt (eV x)) μ :=
    hU_mem.integrable_mul hV_mem
  apply hprod.congr
  filter_upwards [h_nonneg] with x hx
  rw [Real.sqrt_mul hx.1]

theorem aux_lem_diff_measure_bound_sqrt_cs
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (eU eV : α → ℝ) (hU : Integrable eU μ) (hV : Integrable eV μ)
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ eU x ∧ 0 ≤ eV x)
    (B : Set α) :
    (∫ x in B, Real.sqrt (eU x * eV x) ∂μ) ≤
      Real.sqrt ((∫ x in B, eU x ∂μ) * (∫ x in B, eV x ∂μ)) := by
  have h_nonneg_U : ∀ᵐ x ∂μ, 0 ≤ eU x :=
    h_nonneg.mono fun x hx => hx.1
  have h_nonneg_V : ∀ᵐ x ∂μ, 0 ≤ eV x :=
    h_nonneg.mono fun x hx => hx.2
  have hU_sqrt_meas : AEStronglyMeasurable (fun x => Real.sqrt (eU x))
      (μ.restrict B) :=
    ((hU.aestronglyMeasurable.restrict.aemeasurable.sqrt)).aestronglyMeasurable
  have hV_sqrt_meas : AEStronglyMeasurable (fun x => Real.sqrt (eV x))
      (μ.restrict B) :=
    ((hV.aestronglyMeasurable.restrict.aemeasurable.sqrt)).aestronglyMeasurable
  have hU_sqrt_sq : Integrable (fun x => (Real.sqrt (eU x)) ^ 2) (μ.restrict B) := by
    apply hU.restrict.congr
    filter_upwards [ae_restrict_of_ae h_nonneg_U] with x hx
    exact (Real.sq_sqrt hx).symm
  have hV_sqrt_sq : Integrable (fun x => (Real.sqrt (eV x)) ^ 2) (μ.restrict B) := by
    apply hV.restrict.congr
    filter_upwards [ae_restrict_of_ae h_nonneg_V] with x hx
    exact (Real.sq_sqrt hx).symm
  have hU_mem : MemLp (fun x => Real.sqrt (eU x)) (ENNReal.ofReal (2 : ℝ))
      (μ.restrict B) := by
    simpa only [ENNReal.ofReal_ofNat] using
      ((memLp_two_iff_integrable_sq hU_sqrt_meas).2 hU_sqrt_sq)
  have hV_mem : MemLp (fun x => Real.sqrt (eV x)) (ENNReal.ofReal (2 : ℝ))
      (μ.restrict B) := by
    simpa only [ENNReal.ofReal_ofNat] using
      ((memLp_two_iff_integrable_sq hV_sqrt_meas).2 hV_sqrt_sq)
  have hholder :
      (∫ x in B, Real.sqrt (eU x) * Real.sqrt (eV x) ∂μ) ≤
        (∫ x in B, (Real.sqrt (eU x)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x in B, (Real.sqrt (eV x)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa only [ENNReal.ofReal_ofNat] using
      (integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict B) (p := (2 : ℝ))
        (q := (2 : ℝ)) (by rw [Real.holderConjugate_iff]; norm_num)
        ((ae_restrict_of_ae h_nonneg_U).mono
          (fun x _ => Real.sqrt_nonneg (eU x)))
        ((ae_restrict_of_ae h_nonneg_V).mono
          (fun x _ => Real.sqrt_nonneg (eV x)))
        hU_mem hV_mem)
  have hpowU :
      (∫ x in B, (Real.sqrt (eU x)) ^ (2 : ℝ) ∂μ) = ∫ x in B, eU x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae h_nonneg_U] with x hx
    rw [Real.rpow_two, Real.sq_sqrt hx]
  have hpowV :
      (∫ x in B, (Real.sqrt (eV x)) ^ (2 : ℝ) ∂μ) = ∫ x in B, eV x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae h_nonneg_V] with x hx
    rw [Real.rpow_two, Real.sq_sqrt hx]
  have hprod :
      (∫ x in B, Real.sqrt (eU x * eV x) ∂μ) =
        ∫ x in B, Real.sqrt (eU x) * Real.sqrt (eV x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae h_nonneg] with x hx
    rw [Real.sqrt_mul hx.1]
  have hU_int_nonneg : 0 ≤ ∫ x in B, eU x ∂μ :=
    integral_nonneg_of_ae (ae_restrict_of_ae h_nonneg_U)
  calc
    (∫ x in B, Real.sqrt (eU x * eV x) ∂μ) =
        ∫ x in B, Real.sqrt (eU x) * Real.sqrt (eV x) ∂μ := hprod
    _ ≤ (∫ x in B, (Real.sqrt (eU x)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x in B, (Real.sqrt (eV x)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
    _ = Real.sqrt ((∫ x in B, eU x ∂μ) * (∫ x in B, eV x ∂μ)) := by
      rw [hpowU, hpowV]
      calc
        (∫ x in B, eU x ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ x in B, eV x ∂μ) ^ (1 / (2 : ℝ)) =
            Real.sqrt (∫ x in B, eU x ∂μ) * Real.sqrt (∫ x in B, eV x ∂μ) := by
              exact congrArg₂ (fun a b : ℝ => a * b)
                (Real.sqrt_eq_rpow _).symm (Real.sqrt_eq_rpow _).symm
        _ = Real.sqrt ((∫ x in B, eU x ∂μ) * (∫ x in B, eV x ∂μ)) :=
          (Real.sqrt_mul hU_int_nonneg _).symm



theorem lem_diff_measure_bound
    (d : ℕ) (hd : 2 ≤ d)
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ) :
    let Q : Opens (SpatialCoordinates d) := centeredCube zQ rQ hrQ
    ∀ (E F : DirichletForm.ClosedForm
        (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : DirichletForm.EnergyMeasure E)
      (GammaF : DirichletForm.EnergyMeasure F)
      (hdom : E.domain = F.domain)
      (m M c : ℝ) (hm : 0 < m) (hmc : m ≤ c) (hcM : c ≤ M)
      (horder : ∀ h ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          m * (GammaE.measure h A).toReal ≤ (GammaF.measure h A).toReal ∧
            (GammaF.measure h A).toReal ≤ M * (GammaE.measure h A).toReal)
      (u v : DomainL2 Q) (hu : u ∈ E.domain) (hv : v ∈ E.domain),
    ∀ (B : Set (SpatialCoordinates d)), MeasurableSet B →
      ((GammaF.cross u v - c • GammaE.cross u v).totalVariation B).toReal ≤
        (M - m) * Real.sqrt
          ((GammaE.measure u B).toReal * (GammaE.measure v B).toReal) := by
  dsimp
  intro E F GammaE GammaF hdom m M c hm hmc hcM horder u v hu hv B hB
  let sigma := GammaE.measure u + GammaE.measure v
  obtain ⟨eU, eV, dUV, heU, heV, hdUV, h_nonneg, hmuU, hmuV, hdiff, hbound⟩ :=
    lem_diff_measure_density d hd zQ rQ hrQ E F GammaE GammaF hdom m M c hm hmc hcM
      horder u v hu hv
  have hdelta : 0 ≤ M - m := sub_nonneg.mpr (hmc.trans hcM)
  have hmuU_B : (GammaE.measure u B).toReal = ∫ x in B, eU x ∂sigma := by
    rw [hmuU]
    exact aux_lem_diff_measure_bound_density_integral sigma eU heU
      (h_nonneg.mono fun x hx => hx.1) B hB
  have hmuV_B : (GammaE.measure v B).toReal = ∫ x in B, eV x ∂sigma := by
    rw [hmuV]
    exact aux_lem_diff_measure_bound_density_integral sigma eV heV
      (h_nonneg.mono fun x hx => hx.2) B hB
  have htv :
      (SignedMeasure.totalVariation (sigma.withDensityᵥ dUV) B).toReal ≤
        ∫ x in B, |dUV x| ∂sigma :=
    aux_lem_diff_measure_bound_tv sigma dUV hdUV B hB
  have hsqrt_int : Integrable (fun x => Real.sqrt (eU x * eV x)) sigma :=
    aux_lem_diff_measure_bound_sqrt_product_integrable sigma eU eV heU heV h_nonneg
  have hscaled_int : Integrable
      (fun x => (M - m) * Real.sqrt (eU x * eV x)) sigma :=
    hsqrt_int.const_mul (M - m)
  have habs_int : Integrable (fun x => |dUV x|) sigma := hdUV.norm
  have hbound_B :
      (∫ x in B, |dUV x| ∂sigma) ≤
        ∫ x in B, (M - m) * Real.sqrt (eU x * eV x) ∂sigma := by
    apply setIntegral_mono_ae_restrict habs_int.integrableOn hscaled_int.integrableOn
    exact ae_restrict_of_ae hbound
  have hbound_B' :
      (∫ x in B, |dUV x| ∂sigma) ≤
        (M - m) * (∫ x in B, Real.sqrt (eU x * eV x) ∂sigma) := by
    simpa only [integral_const_mul] using hbound_B
  have hcs :
      (∫ x in B, Real.sqrt (eU x * eV x) ∂sigma) ≤
        Real.sqrt ((∫ x in B, eU x ∂sigma) * (∫ x in B, eV x ∂sigma)) :=
    aux_lem_diff_measure_bound_sqrt_cs sigma eU eV heU heV h_nonneg B
  have hfinal :
      (SignedMeasure.totalVariation (sigma.withDensityᵥ dUV) B).toReal ≤
        (M - m) * Real.sqrt
          ((∫ x in B, eU x ∂sigma) * (∫ x in B, eV x ∂sigma)) := by
    exact htv.trans (hbound_B'.trans (mul_le_mul_of_nonneg_left hcs hdelta))
  rw [hdiff, hmuU_B, hmuV_B]
  simpa [sigma] using hfinal

end
end Paper
