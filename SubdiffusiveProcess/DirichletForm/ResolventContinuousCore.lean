module

public import SubdiffusiveProcess.DirichletForm.ResolventRootCore
public import SubdiffusiveProcess.DirichletForm.ThresholdCore
public import SubdiffusiveProcess.Geometry.Cube

@[expose] public section

/-! Extracted local form data for the relative concentration proof.
This module proves the stated deterministic implications; it does not construct random bounds. -/

open MeasureTheory Filter Set Topology TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.LimitFormCore
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- **Regularity (core) of the limit form.**  The Q-core of `F` is a core relative to `Q`:
energy-dense by the truncations `T_s(G f)` of the form-dense responses of smooth sources
(`SubdiffusiveProcess.LimitFormCore.core_dense`), uniformly dense by `hunif`. -/
theorem isCoreOn (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hNC : _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions F)
    (G R : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hE : ∀ u : DomainL2 (centeredCube z r hr), F.toClosedForm.energy u = limitFormEnergy G u)
    (hRsymm : ∀ x y : DomainL2 (centeredCube z r hr), inner ℝ (R x) y = inner ℝ x (R y))
    (hGinj : Function.Injective G) (hRR : R.comp R = G)
    (hdomR : limitFormDomain G = Set.range R)
    (hdenseG : ∀ u ∈ limitFormDomain G, ∀ ε : ℝ, 0 < ε →
      ∃ f : DomainL2 (centeredCube z r hr),
        (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) ∧
        ‖u - G f‖ ≤ ε ∧ limitFormEnergy G (u - G f) ≤ ((ε : ℝ) : EReal))
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        ((G f : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (hunif : ∀ f0 : SpatialCoordinates d → ℝ, Continuous f0 → HasCompactSupport f0 →
      tsupport f0 ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ ε : ℝ, 0 < ε → ∃ w ∈ F.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
        Continuous g ∧ HasCompactSupport g ∧
        tsupport g ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g ∧
        ∀ x, |g x - f0 x| < ε) :
    _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm (centeredCube z r hr : Set (SpatialCoordinates d))
      (SubdiffusiveProcess.LimitFormCore.coreSubmodule F.toClosedForm : Set (DomainL2 (centeredCube z r hr))) := by
  have finiteCubeMeasure := SubdiffusiveProcess.LimitFormCore.isFiniteMeasure_cube z r hr
  have hRinj : Function.Injective R := by
    intro x y hxy
    apply hGinj
    rw [← hRR]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hxy]
  have hdom := SubdiffusiveProcess.LimitFormCore.domain_eq_range F.toClosedForm G R hE hdomR
  have hGdom : ∀ f, G f ∈ F.toClosedForm.domain := fun f =>
    (hdom _).mpr ⟨R f, by rw [← hRR]; rfl⟩
  have hdomG : ∀ u, u ∈ F.toClosedForm.domain → u ∈ limitFormDomain G := by
    intro u hu
    show limitFormEnergy G u < ⊤
    rw [← hE]
    exact (F.toClosedForm.energy_lt_top_iff u).mpr hu
  refine ⟨fun u hu => hu, ?_, ?_⟩
  · -- energy density
    refine SubdiffusiveProcess.LimitFormCore.core_dense F.toClosedForm G R hE hRsymm hRinj hRR hdomR
      (SubdiffusiveProcess.LimitFormCore.coreSubmodule F.toClosedForm) (fun x hx => hx.1)
      {v | ∃ f : DomainL2 (centeredCube z r hr),
        (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) ∧
        v = G f} ?_ ?_
    · intro u hu ε hε
      set ε1 : ℝ := min (ε / 3) 1 with hε1
      have hε1pos : 0 < ε1 := lt_min (by positivity) one_pos
      obtain ⟨f, hfs, hfn, hfe⟩ := hdenseG u (hdomG u hu) ε1 hε1pos
      refine ⟨G f, ⟨f, hfs, rfl⟩, hGdom f, ?_⟩
      have hsub : u - G f ∈ F.toClosedForm.domain := F.toClosedForm.domain.sub_mem hu (hGdom f)
      have hform : F.toClosedForm.form (u - G f) (u - G f) ≤ ε1 := by
        have h := hE (u - G f)
        rw [F.toClosedForm.energy_of_mem hsub] at h
        rw [← h] at hfe
        exact EReal.coe_le_coe_iff.mp hfe
      have hn : ‖u - G f‖ ^ 2 ≤ ε1 := by
        have h1 : ε1 ≤ 1 := min_le_right _ _
        have h0 : 0 ≤ ‖u - G f‖ := norm_nonneg _
        nlinarith only [h1, h0, hfn]
      rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq]
      have : ε1 ≤ ε / 3 := min_le_left _ _
      linarith only [hn, hform, this, hε]
    · rintro v ⟨f, hfs, rfl⟩
      obtain ⟨U, hUc, hUae, hU0⟩ := hcont f hfs
      refine ⟨F.toClosedForm.form (G f) (G f), fun η hη => ?_⟩
      set c : ℝ := ((measureUnivNNReal (volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d)))) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ with hc
      have hc0 : 0 ≤ c := by positivity
      set s : ℝ := η / (2 * (c + 1)) with hs
      have hspos : 0 < s := by positivity
      have hUmem : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
        (Lp.memLp (G f)).ae_eq hUae
      have hTmem : MemLp (fun y => SubdiffusiveProcess.LimitFormCore.softThreshold s (U y)) 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
        refine hUmem.of_le
          ((SubdiffusiveProcess.LimitFormCore.continuous_softThreshold s).comp hUc).aestronglyMeasurable ?_
        refine Eventually.of_forall fun y => ?_
        have h := (SubdiffusiveProcess.LimitFormCore.softThreshold_isNormalContraction hspos.le).dist_le (U y) 0
        rw [SubdiffusiveProcess.LimitFormCore.softThreshold_zero hspos.le, sub_zero, sub_zero] at h
        simpa only [Real.norm_eq_abs] using h
      set x : DomainL2 (centeredCube z r hr) := hTmem.toLp _ with hx
      have hxae : (x : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
            fun y => SubdiffusiveProcess.LimitFormCore.softThreshold s (G f y) := by
        filter_upwards [hTmem.coeFn_toLp, hUae] with y h1 h2
        rw [h1, h2]
      obtain ⟨hxdom, hxle⟩ := hNC.operatesOn _
        (SubdiffusiveProcess.LimitFormCore.softThreshold_isNormalContraction hspos.le) (G f) (hGdom f) x hxae
      obtain ⟨hsupp1, hsupp2⟩ := SubdiffusiveProcess.LimitFormCore.softThreshold_support z r hr hspos U hUc hU0
      refine ⟨x, ⟨hxdom, fun y => SubdiffusiveProcess.LimitFormCore.softThreshold s (U y),
        (SubdiffusiveProcess.LimitFormCore.continuous_softThreshold s).comp hUc, hsupp1, hsupp2,
        hTmem.coeFn_toLp⟩, hxle, ?_⟩
      have hb : ∀ᵐ y ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          ‖(x - G f : DomainL2 (centeredCube z r hr)) y‖ ≤ s := by
        filter_upwards [Lp.coeFn_sub x (G f), hTmem.coeFn_toLp, hUae] with y h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]
        exact SubdiffusiveProcess.LimitFormCore.softThreshold_sub_le hspos.le _
      have hle := Lp.norm_le_of_ae_bound hspos.le hb
      calc ‖x - G f‖ ≤ c * s := hle
        _ < η := by
          rw [hs]
          have : c * (η / (2 * (c + 1))) = η * (c / (2 * (c + 1))) := by ring
          rw [this]
          have hlt : c / (2 * (c + 1)) < 1 := by
            rw [div_lt_one (by positivity)]; linarith only [hc0]
          exact (mul_lt_mul_of_pos_left hlt hη).trans_eq (mul_one η)
  · -- uniform density
    intro f0 hf0 hf0c hf0s ε hε
    obtain ⟨w, hwdom, g, hgc, hgcs, hgs, hwg, hgf⟩ := hunif f0 hf0 hf0c hf0s ε hε
    exact ⟨w, ⟨hwdom, g, hgc, hgcs, hgs, hwg⟩, g, hgc, hgcs, hgs, hwg, hgf⟩

/-- A core on the open cube is a regular core for the restricted volume measure. -/
theorem isRegular_of_isCoreOn (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (C : Set (DomainL2 (centeredCube z r hr)))
    (hC : _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F (centeredCube z r hr : Set (SpatialCoordinates d)) C) :
    _root_.SubdiffusiveProcess.DirichletForm.IsRegular F := by
  refine ⟨(centeredCube z r hr : Set (SpatialCoordinates d)), (centeredCube z r hr).isOpen,
    ?_, C, hC⟩
  rw [Measure.restrict_apply (centeredCube z r hr).isOpen.measurableSet.compl,
    compl_inter_self, measure_empty]

/-- The bilinear dual form vanishing forces the closed form to vanish (polarization). -/
theorem form_eq_zero_of_bilinear
    {Q : TopologicalSpace.Opens (SpatialCoordinates d)}
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hF : ∀ w, F.energy w = limitFormEnergy G w)
    (u v : DomainL2 Q) (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (h0 : limitFormBilinear G u v = 0) : F.form u v = 0 := by
  unfold limitFormBilinear at h0
  rw [← hF (u + v), ← hF (u - v),
    F.energy_of_mem (F.domain.add_mem hu hv),
    F.energy_of_mem (F.domain.sub_mem hu hv)] at h0
  have h4 : (4 : EReal) = ((4 : ℝ) : EReal) := (EReal.coe_natCast (n := 4)).symm
  rw [h4, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_eq_zero] at h0
  have hA : F.form (u + v) (u + v) = F.form u u + 2 * F.form u v + F.form v v :=
    F.form_add_self hu hv
  have hB : F.form (u - v) (u - v) = F.form u u - 2 * F.form u v + F.form v v := by
    rw [F.form_sub_left hu hv (F.domain.sub_mem hu hv),
      F.form_sub_right hu hu hv, F.form_sub_right hv hu hv, F.form_symm v hv u hu]
    ring
  rw [hA, hB] at h0
  linarith only [h0]

end SubdiffusiveProcess.LimitFormCore
