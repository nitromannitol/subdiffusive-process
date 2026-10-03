module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureRiesz

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal RealInnerProductSpace CompactlySupported ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace DirichletForm.FOTConstruction.CoreRiesz

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
variable {F : _root_.DirichletForm m} {U : Set X} {u : Lp ℝ 2 m}

theorem globalFunctional_eq_zero_of_ae (h : Data F U) (a : Input F U u)
    (f : X →ᵇ ℝ) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hf0 : ⇑f =ᵐ[m] fun _ => (0 : ℝ)) : globalFunctional h a f = 0 := by
  have hE : 0 ≤ F.form u u := F.form_nonneg u a.core.1
  have hb (ε : ℝ) (hε : 0 < ε) : ‖globalFunctional h a f‖ ≤ 2 * ε * F.form u u := by
    obtain ⟨C, hcore⟩ := h.core
    obtain ⟨w, hw, g, hg, hgc, hgU, hwae, hgf⟩ :=
      hcore.denseUniform f f.continuous hfc hfU ε hε
    let gc : C_c(X, ℝ) := ⟨⟨g, hg⟩, hgc⟩
    let gt : tests F U := ⟨bounded gc, hgc, hgU, w, (hcore.memCoreOn w hw).1, hwae⟩
    have hdist : ‖f - gt.1‖ ≤ ε := by
      apply (BoundedContinuousFunction.norm_le hε.le).mpr
      intro x
      change |f x - g x| ≤ ε
      rw [abs_sub_comm]
      exact (hgf x).le
    have hwε : ∀ᵐ x ∂m, |testLp gt x| ≤ ε := by
      filter_upwards [testLp_ae gt, hf0] with x h1 h2
      change |testLp gt x| ≤ ε
      rw [h1]
      change |g x| ≤ ε
      simpa [h2] using (hgf x).le
    have hprod : ⇑(productLp a gt) =ᵐ[m] fun x => u x * testLp gt x := by
      filter_upwards [productLp_ae a gt, testLp_ae gt] with x h1 h2
      rw [h1, h2]
    have hgt : ‖globalFunctional h a gt.1‖ ≤ ε * F.form u u := by
      rw [globalFunctional_apply]
      change |F.form u (productLp a gt) - (1 / 2 : ℝ) * F.form a.square (testLp gt)| ≤ _
      exact core_functional_bound F h a.core (testLp_core gt) hε.le hwε
        (productLp_mem a gt) a.square_mem hprod a.square_ae
    calc
      ‖globalFunctional h a f‖ =
          ‖globalFunctional h a (f - gt.1) + globalFunctional h a gt.1‖ := by
            rw [map_sub, sub_add_cancel]
      _ ≤ ‖globalFunctional h a (f - gt.1)‖ + ‖globalFunctional h a gt.1‖ := norm_add_le _ _
      _ ≤ F.form u u * ε + ε * F.form u u := by
        exact add_le_add (((globalFunctional h a).le_opNorm _).trans
          (mul_le_mul (globalFunctional_norm_le h a) hdist (norm_nonneg _) hE)) hgt
      _ = 2 * ε * F.form u u := by ring
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (2 * (F.form u u + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ * (2 * (F.form u u + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hsmall : 2 * δ * F.form u u ≤ ε := by nlinarith
  simpa only [zero_add] using (hb δ hδ).trans hsmall

variable [T2Space X] [LocallyCompactSpace X] [BorelSpace X]

theorem measure_open_eq_zero (h : Data F U) (a : Input F U u) (χ : Cutoff a)
    {O : Set X} (hO : IsOpen O)
    (hf : ∀ f : C_c(X, ℝ), tsupport f ⊆ O → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      positive h a χ f = 0) : measure h a χ O = 0 := by
  apply le_antisymm _ zero_le
  rw [hO.measure_eq_iSup_isCompact (measure h a χ)]
  refine iSup_le fun K => iSup_le fun hKO => iSup_le fun hK => ?_
  obtain ⟨f, hf1, hfc, hfs, h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  let fc : C_c(X, ℝ) := ⟨f, hfc⟩
  have hzero := hf fc hfs h01
  have hle := RealRMK.rieszMeasure_le_of_eq_one (positive h a χ)
    (f := fc) (fun x => (h01 x).1) hK hf1
  simpa [measure, hzero] using hle

theorem measure_compl_cutoff_support (h : Data F U) (a : Input F U u) (χ : Cutoff a) :
    measure h a χ (tsupport χ.test.1)ᶜ = 0 := by
  apply measure_open_eq_zero h a χ isClosed_closure.isOpen_compl
  intro f hf h01
  change globalFunctional h a (bounded f * χ.test.1) = 0
  have he : bounded f * χ.test.1 = 0 := by
    ext x
    change f x * χ.test.1 x = 0
    by_cases hx : x ∈ tsupport f
    · rw [image_eq_zero_of_notMem_tsupport (hf hx), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [he, map_zero]

theorem measure_carried (h : Data F U) (a : Input F U u) (χ : Cutoff a) :
    measure h a χ Uᶜ = 0 :=
  measure_mono_null (compl_subset_compl.mpr χ.test.property.2.1)
    (measure_compl_cutoff_support h a χ)

theorem measure_null_open (h : Data F U) (a : Input F U u) (χ : Cutoff a)
    {O : Set X} (hO : IsOpen O) (hmO : m O = 0) : measure h a χ O = 0 := by
  apply measure_open_eq_zero h a χ hO
  intro f hf h01
  change globalFunctional h a (bounded f * χ.test.1) = 0
  have hfc : HasCompactSupport (fun x => f x * χ.test.1 x) :=
    HasCompactSupport.mul_left χ.test.property.1
  have hs : tsupport (fun x => f x * χ.test.1 x) ⊆ U :=
    (tsupport_mul_subset_right (f := ⇑f) (g := ⇑χ.test.1)).trans χ.test.property.2.1
  have hae : (fun x => f x * χ.test.1 x) =ᵐ[m] fun _ => (0 : ℝ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hmO] with x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hxf => hx (hf hxf)), zero_mul]
  exact globalFunctional_eq_zero_of_ae h a (bounded f * χ.test.1) hfc hs hae

theorem measure_ae_eq_of_continuous (h : Data F U) (a : Input F U u) (χ : Cutoff a)
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hfg : f =ᵐ[m] g) :
    f =ᵐ[measure h a χ] g := by
  apply ae_iff.mpr
  exact measure_null_open h a χ (isClosed_eq hf hg).isOpen_compl (ae_iff.mp hfg)

theorem measure_defining (h : Data F U) (a : Input F U u) (χ : Cutoff a)
    {φ : Lp ℝ 2 m} (hφ : F.toClosedForm.MemCoreOn U φ)
    (uc φc : X → ℝ) (huc : Continuous uc) (hφc : Continuous φc)
    (huae : ⇑u =ᵐ[m] uc) (hφae : ⇑φ =ᵐ[m] φc)
    (uφ u2 : Lp ℝ 2 m) (huφ : uφ ∈ F.domain) (hu2 : u2 ∈ F.domain)
    (hprod : ⇑uφ =ᵐ[m] fun x => uc x * φc x)
    (hsq : ⇑u2 =ᵐ[m] fun x => uc x ^ 2) :
    (∫ x, φc x ∂measure h a χ) = F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ := by
  obtain ⟨f, hf, hfc, hfU, hfae⟩ := hφ.2
  let fc : C_c(X, ℝ) := ⟨⟨f, hf⟩, hfc⟩
  let ft : tests F U := ⟨bounded fc, hfc, hfU, φ, hφ.1, hfae⟩
  have heφ : testLp ft = φ := Lp.ext ((testLp_ae ft).trans hfae.symm)
  have heprod : productLp a ft = uφ := by
    apply Lp.ext
    filter_upwards [productLp_ae a ft, hprod, huae, hφae, hfae] with x h1 h2 h3 h4 h5
    change productLp a ft x = uφ x
    rw [h1, h2, h3]
    change uc x * f x = uc x * φc x
    rw [← h5, h4]
  have hesq : a.square = u2 := by
    apply Lp.ext
    filter_upwards [a.square_ae, hsq, huae] with x h1 h2 h3
    rw [h1, h2, h3]
  have heae : φc =ᵐ[measure h a χ] f :=
    measure_ae_eq_of_continuous h a χ hφc hf (hφae.symm.trans hfae)
  calc
    (∫ x, φc x ∂measure h a χ) = ∫ x, fc x ∂measure h a χ := integral_congr_ae heae
    _ = positive h a χ fc := RealRMK.integral_rieszMeasure _ _
    _ = functional h a ft := localized_test h a χ ft
    _ = F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ := by
      change F.form u (productLp a ft) - (1 / 2 : ℝ) * F.form a.square (testLp ft) = _
      rw [heprod, hesq, heφ]

end DirichletForm.FOTConstruction.CoreRiesz
