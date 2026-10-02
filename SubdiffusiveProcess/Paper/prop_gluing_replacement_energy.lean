import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.MeshError
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import SubdiffusiveProcess.Paper.prop_gluing_replacement_patch
import SubdiffusiveProcess.Paper.prop_gluing_replacement_localization
import SubdiffusiveProcess.Paper.prop_gluing
import SubdiffusiveProcess.Paper.conv_represented_sequence

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

theorem aux_ae_restrict_mono {X : Type*} [MeasurableSpace X] {m : Measure X} {s t : Set X}
    (hst : s ⊆ t) {f g : X → ℝ} (h : f =ᵐ[m.restrict t] g) : f =ᵐ[m.restrict s] g :=
  h.filter_mono (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hst (le_refl m)))

theorem aux_cross_locality {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    {E : DirichletForm.ClosedForm m} (Γ : DirichletForm.EnergyMeasure E)
    {u a b : Lp ℝ 2 m} (hu : u ∈ E.domain) (ha : a ∈ E.domain) (hb : b ∈ E.domain)
    {O : Set X} (hO : IsOpen O) (hae : (a : X → ℝ) =ᵐ[m.restrict O] (b : X → ℝ))
    {B : Set X} (hB : MeasurableSet B) (hBO : B ⊆ O) :
    Γ.cross u a B = Γ.cross u b B := by
  have hrestr : ∀ {f g : X → ℝ}, f =ᵐ[m] g → f =ᵐ[m.restrict O] g := fun h =>
    h.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
  have hua : (⇑(u + a) : X → ℝ) =ᵐ[m.restrict O] (⇑(u + b) : X → ℝ) :=
    (hrestr (Lp.coeFn_add u a)).trans
      (Filter.EventuallyEq.add (Filter.Eventually.of_forall fun x => rfl) hae) |>.trans
      (hrestr (Lp.coeFn_add u b)).symm
  have hum : (⇑(u - a) : X → ℝ) =ᵐ[m.restrict O] (⇑(u - b) : X → ℝ) :=
    (hrestr (Lp.coeFn_sub u a)).trans
      (Filter.EventuallyEq.sub (Filter.Eventually.of_forall fun x => rfl) hae) |>.trans
      (hrestr (Lp.coeFn_sub u b)).symm
  have e1 : Γ.measure (u + a) B = Γ.measure (u + b) B := by
    have hres := Γ.locality (u + a) (E.domain.add_mem hu ha) (u + b) (E.domain.add_mem hu hb)
      O hO hua
    have h := congrArg (fun ν : Measure X => ν B) hres
    simpa only [Measure.restrict_apply hB, Set.inter_eq_left.mpr hBO] using h
  have e2 : Γ.measure (u - a) B = Γ.measure (u - b) B := by
    have hres := Γ.locality (u - a) (E.domain.sub_mem hu ha) (u - b) (E.domain.sub_mem hu hb)
      O hO hum
    have h := congrArg (fun ν : Measure X => ν B) hres
    simpa only [Measure.restrict_apply hB, Set.inter_eq_left.mpr hBO] using h
  rw [Γ.cross_eq_polarization hu ha B, Γ.cross_eq_polarization hu hb B,
    Γ.cross_self (u + a) (E.domain.add_mem hu ha) B hB,
    Γ.cross_self (u - a) (E.domain.sub_mem hu ha) B hB,
    Γ.cross_self (u + b) (E.domain.add_mem hu hb) B hB,
    Γ.cross_self (u - b) (E.domain.sub_mem hu hb) B hB, e1, e2]

theorem aux_memLp_indicator {X : Type*} [MeasurableSpace X] {m : Measure X}
    {S : Set X} (hS : MeasurableSet S) {f g : X → ℝ}
    (hg : MemLp g 2 m) (hae : f =ᵐ[m] g) : MemLp (S.indicator f) 2 m := by
  classical
  have h : (S.indicator g : X → ℝ) =ᵐ[m] (S.indicator f : X → ℝ) := by
    filter_upwards [hae] with x hx
    simp only [Set.indicator_apply, hx]
  exact (MemLp.indicator hS hg).ae_eq h

theorem aux_killed_cross_zero {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    {E : DirichletForm.ClosedForm m} (Γ : DirichletForm.EnergyMeasure E)
    {C : Set X} (hCmeas : MeasurableSet C) {D : Submodule ℝ (Lp ℝ 2 m)}
    (hD : DirichletForm.IsKilledDomain E C D)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (horth : ∀ φ ∈ D, E.form u φ = 0)
    {v : Lp ℝ 2 m} (hv : v ∈ D) : Γ.cross u v C = 0 := by
  have hCcmeas : MeasurableSet Cᶜ := hCmeas.compl
  have hsplit : Γ.cross u v C + Γ.cross u v Cᶜ = Γ.cross u v Set.univ := by
    have h := VectorMeasure.restrict_add_restrict_compl (Γ.cross u v) hCmeas
    have h2 : ((Γ.cross u v).restrict C + (Γ.cross u v).restrict Cᶜ) Set.univ
        = (Γ.cross u v) Set.univ := by rw [h]
    rw [VectorMeasure.add_apply] at h2
    rw [VectorMeasure.restrict_apply (Γ.cross u v) (i := C) hCmeas (j := Set.univ)
          MeasurableSet.univ,
        VectorMeasure.restrict_apply (Γ.cross u v) (i := Cᶜ) hCcmeas (j := Set.univ)
          MeasurableSet.univ] at h2
    simpa using h2
  obtain ⟨w, hwc, hconv⟩ := hD.exists_seq hv
  have hzero : ∀ n, Γ.cross u (w n) Cᶜ = 0 := by
    intro n
    obtain ⟨f, hf, _hcs, hsupp, hae⟩ := (hwc n).hasCoreRep
    have hmeas0 : Γ.measure (w n) (tsupport f)ᶜ = 0 :=
      Γ.measure_compl_tsupport (w n) (hwc n).mem_domain f hf hae
    have hsub : Cᶜ ⊆ (tsupport f)ᶜ := by
      intro x hx hx2
      exact hx (hsupp hx2)
    have hle : Γ.measure (w n) Cᶜ ≤ 0 := by
      rw [← hmeas0]
      exact measure_mono hsub
    have hzero' : Γ.measure (w n) Cᶜ = 0 := le_antisymm hle (zero_le _)
    have hcs := Γ.abs_cross_le u hu (w n) (hwc n).mem_domain Cᶜ hCcmeas
    rw [hzero', ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] at hcs
    exact abs_eq_zero.mp (le_antisymm hcs (abs_nonneg _))
  have hstep : ∀ n, |Γ.cross u v Cᶜ| = |Γ.cross u (v - w n) Cᶜ| := by
    intro n
    have hvsub : (v - w n) ∈ E.domain := E.domain.sub_mem (hD.le_domain hv) (hwc n).mem_domain
    have hvsplit : v = w n + (v - w n) := by abel
    conv_lhs => rw [hvsplit]
    rw [Γ.cross_add_right u hu (w n) (hwc n).mem_domain (v - w n) hvsub,
      VectorMeasure.add_apply, hzero n, zero_add]
  have hbound : ∀ n, |Γ.cross u v Cᶜ| ≤ Real.sqrt ((Γ.measure u Cᶜ).toReal) *
      Real.sqrt (E.energyNormSq (v - w n)) := by
    intro n
    rw [hstep n]
    have hvsub : (v - w n) ∈ E.domain := E.domain.sub_mem (hD.le_domain hv) (hwc n).mem_domain
    refine (Γ.abs_cross_le u hu (v - w n) hvsub Cᶜ hCcmeas).trans ?_
    have h1 : (Γ.measure (v - w n) Cᶜ).toReal ≤ E.energyNormSq (v - w n) :=
      (Γ.toReal_measure_le_form hvsub Cᶜ).trans E.form_le_energyNormSq
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _)
  have h0 : |Γ.cross u v Cᶜ| ≤ 0 := by
    have htend : Tendsto (fun n => Real.sqrt ((Γ.measure u Cᶜ).toReal) *
        Real.sqrt (E.energyNormSq (v - w n))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => E.energyNormSq (v - w n)) atTop (𝓝 0) := hconv
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      have h3 : Tendsto (fun n => Real.sqrt ((Γ.measure u Cᶜ).toReal) *
          Real.sqrt (E.energyNormSq (v - w n))) atTop
          (𝓝 (Real.sqrt ((Γ.measure u Cᶜ).toReal) * Real.sqrt 0)) := h2.const_mul _
      simpa using h3
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend (Filter.Eventually.of_forall hbound)
  have hcz : Γ.cross u v Cᶜ = 0 := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  rw [hcz, add_zero, Γ.cross_univ u hu v (hD.le_domain hv), horth v hv] at hsplit
  exact hsplit



theorem prop_gluing_replacement_energy
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : DirichletForm.EnergyMeasure E)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i : Fin m, 0 < rad i)
    (hcellQ : ∀ i : Fin m,
      closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise fun i j : Fin m =>
      Disjoint (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
        (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (Dq : Fin m → Submodule ℝ (DomainL2 Q))
    (hDq : ∀ i : Fin m, DirichletForm.IsKilledDomain E
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (Dq i))
    (V : DomainL2 Q) (hV : V ∈ E.domain)
    (Vc : SpatialCoordinates d → ℝ)
    (hVcont : ContinuousOn Vc (closure (Q : Set (SpatialCoordinates d))))
    (hVrep : (V : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Vc)
    (Ui : Fin m → SpatialCoordinates d → ℝ)
    (UiL2 : Fin m → DomainL2 Q)
    (hUiDomain : ∀ i : Fin m, UiL2 i ∈ E.domain)
    (hUiRep : ∀ i : Fin m, (UiL2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Ui i)
    (hUicont : ∀ i : Fin m, ContinuousOn (Ui i)
      (closure (Q : Set (SpatialCoordinates d))))
    (hUibdry : ∀ i : Fin m,
      ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), Ui i x = Vc x)
    (hUiOrth : ∀ i : Fin m, ∀ φ : DomainL2 Q, φ ∈ Dq i →
      E.form (UiL2 i) φ = 0)
    (Lam : Fin m → ℝ)
    (hUiEnergy : ∀ i : Fin m, (Γ.measure (UiL2 i)
      (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))).toReal = Lam i)
    (hZeroTrace : ∀ i : Fin m, ∀ (w : DomainL2 Q), w ∈ E.domain →
      ∀ (wc : SpatialCoordinates d → ℝ),
      ContinuousOn wc (closure (Q : Set (SpatialCoordinates d))) →
      ((w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc) →
      (∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), wc x = 0) →
      ∀ (wq : DomainL2 Q),
      ((wq : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          Set.indicator (closure (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) wc) →
      wq ∈ Dq i ∧ E.form wq wq = (Γ.measure w
        (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))).toReal)
    (V' : DomainL2 Q) (V'c : SpatialCoordinates d → ℝ)
    (hV'rep : (V' : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V'c)
    (hV'out : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      x ∉ ⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) → V'c x = Vc x)
    (hV'in : ∀ i : Fin m,
      ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), V'c x = Ui i x)
    (hpatch : V' ∈ E.domain ∧
      ContinuousOn V'c (closure (Q : Set (SpatialCoordinates d))))
    (hlocal :
      (∀ i : Fin m, ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)) →
        Γ.measure V' B = Γ.measure (UiL2 i) B) ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (Q : Set (SpatialCoordinates d)) \
          (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) →
        Γ.measure V' B = Γ.measure V B)) :
    (∀ i : Fin m,
      Lam i ≤ (Γ.measure V
        (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))).toReal) ∧
      E.form V' V' = E.form V V - ∑ i : Fin m,
        ((Γ.measure V (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))).toReal - Lam i) ∧
      E.form V' V' ≤ E.form V V := by
  let cub : Fin m → Set (SpatialCoordinates d) :=
    fun i => (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
  have hcubm : ∀ i : Fin m, MeasurableSet (cub i) :=
    fun i => (centeredCube (cent i) (rad i) (hrad i)).isOpen.measurableSet
  have hCopen : ∀ i : Fin m, IsOpen (cub i) :=
    fun i => (centeredCube (cent i) (rad i) (hrad i)).isOpen
  have hQm : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  have hQcm : MeasurableSet ((Q : Set (SpatialCoordinates d))ᶜ) := hQm.compl
  have hcubQ : (⋃ i : Fin m, cub i) ⊆ (Q : Set (SpatialCoordinates d)) :=
    Set.iUnion_subset (fun i => subset_closure.trans (hcellQ i))
  have hUmeas : MeasurableSet (⋃ i : Fin m, cub i) := MeasurableSet.iUnion (fun i => hcubm i)
  have hclsub : (⋃ i : Fin m, closure (cub i)) ⊆ (Q : Set (SpatialCoordinates d)) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hcellQ i hi
  have hUclosed : IsClosed (⋃ i : Fin m, closure (cub i)) :=
    isClosed_iUnion_of_finite (fun i => isClosed_closure)
  have hUm : MeasurableSet (⋃ i : Fin m, closure (cub i)) := hUclosed.measurableSet
  have hUopen : IsOpen ((⋃ i : Fin m, closure (cub i))ᶜ) := hUclosed.isOpen_compl
  have hext : ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
      B ⊆ (Q : Set (SpatialCoordinates d))ᶜ → Γ.measure V' B = Γ.measure V B := by
    intro B hB hBQ
    have hpt : ∀ x ∈ (Q : Set (SpatialCoordinates d)) ∩ (⋃ i : Fin m, closure (cub i))ᶜ,
        V'c x = Vc x := by
      intro x hx
      obtain ⟨hxQ, hxO⟩ := hx
      have hxA : x ∉ ⋃ i : Fin m, cub i := by
        intro hmem
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
        exact hxO (Set.mem_iUnion.mpr ⟨j, subset_closure hj⟩)
      exact hV'out x (subset_closure hxQ) hxA
    have hBs : B ⊆ (⋃ i : Fin m, closure (cub i))ᶜ := by
      intro x hx hmem
      exact hBQ hx (hclsub hmem)
    have h1 : (V' : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d))).restrict ((⋃ i : Fin m, closure (cub i))ᶜ)] V'c :=
      hV'rep.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
    have h2 : (V : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d))).restrict ((⋃ i : Fin m, closure (cub i))ᶜ)] Vc :=
      hVrep.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
    have h3 : (V'c : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d))).restrict ((⋃ i : Fin m, closure (cub i))ᶜ)] Vc := by
      have hQae : ∀ᵐ x ∂((volume.restrict (Q : Set (SpatialCoordinates d))).restrict ((⋃ i : Fin m, closure (cub i))ᶜ)),
          x ∈ (Q : Set (SpatialCoordinates d)) :=
        (MeasureTheory.ae_restrict_mem hQm).filter_mono
          (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
      filter_upwards [hQae, MeasureTheory.ae_restrict_mem hUm.compl] with x hxQ hxO
      exact hpt x ⟨hxQ, hxO⟩
    have hae := h1.trans (h3.trans h2.symm)
    have hloc := Γ.locality V' hpatch.1 V hV ((⋃ i : Fin m, closure (cub i))ᶜ) hUopen hae
    have e1 : (Γ.measure V') B = ((Γ.measure V').restrict ((⋃ i : Fin m, closure (cub i))ᶜ)) B := by
      rw [Measure.restrict_apply hB, Set.inter_eq_left.mpr hBs]
    have e2 : (Γ.measure V) B = ((Γ.measure V).restrict ((⋃ i : Fin m, closure (cub i))ᶜ)) B := by
      rw [Measure.restrict_apply hB, Set.inter_eq_left.mpr hBs]
    rw [e1, e2, hloc]
  have hUn : (⋃ i : Fin m, cub i) = ⋃ i ∈ (Finset.univ : Finset (Fin m)), cub i := by
    ext x; simp
  have hdisjU : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint cub :=
    fun i _ j _ hij => hdisj hij
  have hmuA : ∀ ν : Measure (SpatialCoordinates d),
      ν (⋃ i : Fin m, cub i) = ∑ i : Fin m, ν (cub i) := by
    intro ν
    rw [hUn, measure_biUnion_finset hdisjU (fun b _ => hcubm b)]
  have hAc : (⋃ i : Fin m, cub i)ᶜ =
      ((Q : Set (SpatialCoordinates d)) \ (⋃ i : Fin m, cub i)) ∪ (Q : Set (SpatialCoordinates d))ᶜ := by
    ext x; constructor
    · intro hx
      by_cases hxQ : x ∈ (Q : Set (SpatialCoordinates d))
      · exact Or.inl ⟨hxQ, hx⟩
      · exact Or.inr hxQ
    · rintro (⟨-, hxA⟩ | hxQ)
      · exact hxA
      · exact fun hxQ' => hxQ (hcubQ hxQ')
  have hdisjAc : Disjoint ((Q : Set (SpatialCoordinates d)) \ (⋃ i : Fin m, cub i))
      (Q : Set (SpatialCoordinates d))ᶜ := by
    rw [Set.disjoint_left]; intro x hx hx2; exact hx2 hx.1
  have hQAmeas : MeasurableSet ((Q : Set (SpatialCoordinates d)) \ (⋃ i : Fin m, cub i)) :=
    hQm.diff hUmeas
  have hsumfin : ∀ i ∈ (Finset.univ : Finset (Fin m)), Γ.measure (UiL2 i) (cub i) ≠ ⊤ :=
    fun i _ => (Γ.measure_lt_top (hUiDomain i) (cub i)).ne
  have key' : (Γ.measure V' Set.univ).toReal =
      (∑ i : Fin m, Lam i) + ((Γ.measure V ((Q : Set (SpatialCoordinates d)) \ (⋃ i : Fin m, cub i))).toReal
        + (Γ.measure V ((Q : Set (SpatialCoordinates d))ᶜ)).toReal) := by
    have e1 : Γ.measure V' Set.univ =
        Γ.measure V' (⋃ i : Fin m, cub i) + Γ.measure V' ((⋃ i : Fin m, cub i)ᶜ) :=
      (measure_add_measure_compl hUmeas).symm
    have e2 : Γ.measure V' (⋃ i : Fin m, cub i) = ∑ i : Fin m, Γ.measure (UiL2 i) (cub i) := by
      rw [hmuA (Γ.measure V')]
      exact Finset.sum_congr rfl (fun i _ => hlocal.1 i (cub i) (hcubm i) subset_rfl)
    have e3 : Γ.measure V' ((⋃ i : Fin m, cub i)ᶜ) =
        Γ.measure V ((Q : Set (SpatialCoordinates d)) \ (⋃ i : Fin m, cub i)) +
          Γ.measure V ((Q : Set (SpatialCoordinates d))ᶜ) := by
      rw [hAc, measure_union hdisjAc hQcm, hlocal.2 _ hQAmeas subset_rfl, hext _ hQcm subset_rfl]
    calc (Γ.measure V' Set.univ).toReal
        = (Γ.measure V' (⋃ i : Fin m, cub i)).toReal + (Γ.measure V' ((⋃ i : Fin m, cub i)ᶜ)).toReal := by
          rw [e1, ENNReal.toReal_add (Γ.measure_lt_top hpatch.1 _).ne (Γ.measure_lt_top hpatch.1 _).ne]
      _ = (∑ i : Fin m, Γ.measure (UiL2 i) (cub i)).toReal + (Γ.measure V' ((⋃ i : Fin m, cub i)ᶜ)).toReal := by
          rw [e2]
      _ = (∑ i : Fin m, (Γ.measure (UiL2 i) (cub i)).toReal) + (Γ.measure V' ((⋃ i : Fin m, cub i)ᶜ)).toReal := by
          rw [ENNReal.toReal_sum hsumfin]
      _ = (∑ i : Fin m, Lam i) + (Γ.measure V' ((⋃ i : Fin m, cub i)ᶜ)).toReal := by
          rw [Finset.sum_congr rfl (fun i _ => hUiEnergy i)]
      _ = (∑ i : Fin m, Lam i) + ((Γ.measure V ((Q : Set (SpatialCoordinates d)) \ (⋃ i : Fin m, cub i))).toReal
            + (Γ.measure V ((Q : Set (SpatialCoordinates d))ᶜ)).toReal) := by
          rw [e3, ENNReal.toReal_add (Γ.measure_lt_top hV _).ne (Γ.measure_lt_top hV _).ne] <;> try ring
  have hmu : (Γ.measure V Set.univ).toReal =
      (∑ i : Fin m, (Γ.measure V (cub i)).toReal) + ((Γ.measure V ((Q : Set (SpatialCoordinates d)) \ (⋃ i : Fin m, cub i))).toReal
        + (Γ.measure V ((Q : Set (SpatialCoordinates d))ᶜ)).toReal) := by
    have e1 : Γ.measure V Set.univ =
        Γ.measure V (⋃ i : Fin m, cub i) + Γ.measure V ((⋃ i : Fin m, cub i)ᶜ) :=
      (measure_add_measure_compl hUmeas).symm
    have e3 : Γ.measure V ((⋃ i : Fin m, cub i)ᶜ) =
        Γ.measure V ((Q : Set (SpatialCoordinates d)) \ (⋃ i : Fin m, cub i)) +
          Γ.measure V ((Q : Set (SpatialCoordinates d))ᶜ) := by
      rw [hAc, measure_union hdisjAc hQcm]
    calc (Γ.measure V Set.univ).toReal
        = (Γ.measure V (⋃ i : Fin m, cub i)).toReal + (Γ.measure V ((⋃ i : Fin m, cub i)ᶜ)).toReal := by
          rw [e1, ENNReal.toReal_add (Γ.measure_lt_top hV _).ne (Γ.measure_lt_top hV _).ne]
      _ = (∑ i : Fin m, Γ.measure V (cub i)).toReal + (Γ.measure V ((⋃ i : Fin m, cub i)ᶜ)).toReal := by
          rw [hmuA (Γ.measure V)]
      _ = (∑ i : Fin m, (Γ.measure V (cub i)).toReal) + (Γ.measure V ((⋃ i : Fin m, cub i)ᶜ)).toReal := by
          rw [ENNReal.toReal_sum (fun i _ => (Γ.measure_lt_top hV (cub i)).ne)]
      _ = (∑ i : Fin m, (Γ.measure V (cub i)).toReal)
            + ((Γ.measure V ((Q : Set (SpatialCoordinates d)) \ (⋃ i : Fin m, cub i))).toReal
              + (Γ.measure V ((Q : Set (SpatialCoordinates d))ᶜ)).toReal) := by
          rw [e3, ENNReal.toReal_add (Γ.measure_lt_top hV _).ne (Γ.measure_lt_top hV _).ne] <;> try ring
  have key : (Γ.measure V' Set.univ).toReal - (Γ.measure V Set.univ).toReal =
      - ∑ i : Fin m, ((Γ.measure V (cub i)).toReal - Lam i) := by
    rw [key', hmu, Finset.sum_sub_distrib]
    ring
  have hcell : ∀ i : Fin m, Lam i ≤ (Γ.measure V (cub i)).toReal := by
    intro i
    let w : DomainL2 Q := V - UiL2 i
    have hwd : w ∈ E.domain := E.domain.sub_mem hV (hUiDomain i)
    let wc : SpatialCoordinates d → ℝ := fun x => Vc x - Ui i x
    have hwcont : ContinuousOn wc (closure (Q : Set (SpatialCoordinates d))) := hVcont.sub (hUicont i)
    have hwae : (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc :=
      (Lp.coeFn_sub V (UiL2 i)).trans (hVrep.sub (hUiRep i))
    have hwbdry : ∀ x ∈ frontier (cub i), wc x = 0 := by
      intro x hx
      show Vc x - Ui i x = 0
      rw [hUibdry i x hx, sub_self]
    have hmemLp : MemLp ((closure (cub i)).indicator wc) 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      aux_memLp_indicator isClosed_closure.measurableSet (Lp.memLp (V - UiL2 i)) hwae.symm
    let wq : DomainL2 Q := MemLp.toLp ((closure (cub i)).indicator wc) hmemLp
    have hwqae : (wq : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (closure (cub i)).indicator wc :=
      MemLp.coeFn_toLp hmemLp
    obtain ⟨hwqD, _hwqE⟩ := hZeroTrace i w hwd wc hwcont hwae hwbdry wq hwqae
    have haeC : (w : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d))).restrict (cub i)] (wq : SpatialCoordinates d → ℝ) := by
      have h1 : (w : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d))).restrict (cub i)] wc :=
        hwae.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
      have h2 : (wq : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d))).restrict (cub i)] wc := by
        refine (hwqae.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)).trans ?_
        filter_upwards [MeasureTheory.ae_restrict_mem (hcubm i)] with x hx
        exact Set.indicator_of_mem (subset_closure hx) wc
      exact h1.trans h2.symm
    have hcross0 : Γ.cross (UiL2 i) wq (cub i) = 0 :=
      aux_killed_cross_zero Γ (hcubm i) (hDq i) (hUiDomain i) (hUiOrth i) hwqD
    have hcross : Γ.cross (UiL2 i) w (cub i) = 0 := by
      rw [aux_cross_locality Γ (hUiDomain i) hwd ((hDq i).le_domain hwqD) (hCopen i) haeC (hcubm i) subset_rfl, hcross0]
    have hmain : (Γ.measure V (cub i)).toReal = Lam i + (Γ.measure w (cub i)).toReal := by
      rw [← Γ.cross_self V hV (cub i) (hcubm i), show V = UiL2 i + w from by
            show V = UiL2 i + (V - UiL2 i); abel,
        Γ.cross_add_self_apply (hUiDomain i) hwd (cub i),
        Γ.cross_self (UiL2 i) (hUiDomain i) (cub i) (hcubm i),
        Γ.cross_self w hwd (cub i) (hcubm i), hcross, hUiEnergy i]
      ring
    rw [hmain]
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  have hdef : E.form V' V' = E.form V V - ∑ i : Fin m, ((Γ.measure V (cub i)).toReal - Lam i) := by
    rw [← Γ.measure_univ V' hpatch.1, ← Γ.measure_univ V hV]
    linarith [key]
  refine ⟨hcell, hdef, ?_⟩
  rw [hdef]
  have h0 : 0 ≤ ∑ i : Fin m, ((Γ.measure V (cub i)).toReal - Lam i) :=
    Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hcell i))
  linarith


end Paper
