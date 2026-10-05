module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblyCross
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section
namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] {m : Measure X}

omit [BorelSpace X] in
/-- A countable collection of core cutoff plateaux covers the state space. -/
theorem assembly_cutoff_cover {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [_t2 : T2Space X] [_lc : LocallyCompactSpace X] [_borel : BorelSpace X] [_second : SecondCountableTopology X] {m : Measure X}
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} (h : Data F U) :
    ∃ (β : ℕ → Lp ℝ 2 m) (f : ℕ → X → ℝ) (V : ℕ → Set X),
      (∀ n, F.toClosedForm.MemCoreOn U (β n)) ∧
      (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U ∧
        ⇑(β n) =ᵐ[m] f n) ∧
      (∀ n, IsOpen (V n) ∧ V n ⊆ U ∧ ∀ x ∈ V n, f n x = 1) ∧
      ⋃ n, V n = U := by
  let : LocallyCompactSpace U := h.isOpen.locallyCompactSpace
  let K : ℕ → Set X := fun n => Subtype.val '' compactCovering U n
  have hK : ∀ n, IsCompact (K n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hKU : ∀ n, K n ⊆ U := fun n x hx => by
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  obtain ⟨C, hC⟩ := h.core
  choose β f V hβ hf hfc hfU hfae _ hV hKV hfV using fun n =>
    hC.exists_cutoff F (hK n) h.isOpen (hKU n) subset_rfl
  have hVU : ∀ n, V n ⊆ U := by
    intro n x hx
    apply hfU n
    apply subset_closure
    show f n x ≠ 0
    rw [hfV n x hx]
    exact one_ne_zero
  refine ⟨β, f, V, hβ, fun n => ⟨hf n, hfc n, hfU n, hfae n⟩,
    fun n => ⟨hV n, hVU n, hfV n⟩, ?_⟩
  apply le_antisymm (iUnion_subset hVU)
  intro x hx
  obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
  exact mem_iUnion.mpr ⟨n, hKV n (mem_image_of_mem Subtype.val hn)⟩

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
/-- Multiplication by a core cutoff turns a global core function into a
relative core function, without changing it on the cutoff plateau. -/
theorem assembly_localize_core {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [_t2 : T2Space X] [_lc : LocallyCompactSpace X] [_borel : BorelSpace X] [_second : SecondCountableTopology X] {m : Measure X}
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    {u β : Lp ℝ 2 m} (hu : F.toClosedForm.MemCore u)
    (hβ : F.toClosedForm.MemCoreOn U β) {uc f : X → ℝ}
    (huae : ⇑u =ᵐ[m] uc) (hfae : ⇑β =ᵐ[m] f) :
    ∃ u' : Lp ℝ 2 m, F.toClosedForm.MemCoreOn U u' ∧
      ⇑u' =ᵐ[m] fun x => f x * uc x := by
  obtain ⟨u', hu', hrep⟩ := exists_memCoreOn_mul_comp F U hu hβ huae hfae
    (Φ := id) contDiff_id
  exact ⟨u', hu', hrep⟩

/-- The relative-core Leibniz identity is valid on a cutoff plateau for any
continuous compactly supported domain representatives. -/
theorem EnergyFamily.leibniz_on_plateau {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U)
    {u v β : Lp ℝ 2 m} (hu : F.toClosedForm.MemCore u) (hv : F.toClosedForm.MemCore v)
    (hβ : F.toClosedForm.MemCoreOn U β)
    {uc vc f : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc) (hf : Continuous f)
    (hvcc : HasCompactSupport vc) (hfc : HasCompactSupport f)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc) (hfae : ⇑β =ᵐ[m] f)
    {V : Set X} (hV : IsOpen V) (hfV : ∀ x ∈ V, f x = 1)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => vc x * Φ (uc x))
    {B : Set X} (hB : MeasurableSet B) (hBV : B ⊆ V) :
    (Γ.measure w B).toReal =
      (∫ x in B, vc x ^ 2 * deriv Φ (uc x) ^ 2 ∂Γ.measure u) +
        2 * signedIntegralOn (Γ.cross u v) B
          (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) +
        (∫ x in B, Φ (uc x) ^ 2 ∂Γ.measure v) := by
  obtain ⟨u', hu', hu'rep⟩ := assembly_localize_core hu hβ huae hfae
  obtain ⟨v', hv', hv'rep⟩ := assembly_localize_core hv hβ hvae hfae
  let uc' : X → ℝ := fun x => f x * uc x
  let vc' : X → ℝ := fun x => f x * vc x
  have huc' : Continuous uc' := hf.mul huc
  have hvc' : Continuous vc' := hf.mul hvc
  have hequ : ⇑u =ᵐ[m.restrict V] ⇑u' := by
    filter_upwards [ae_restrict_of_ae huae, ae_restrict_of_ae hu'rep,
      ae_restrict_mem hV.measurableSet] with x hx hy hz
    rw [hx, hy, hfV x hz, one_mul]
  have heqv : ⇑v =ᵐ[m.restrict V] ⇑v' := by
    filter_upwards [ae_restrict_of_ae hvae, ae_restrict_of_ae hv'rep,
      ae_restrict_mem hV.measurableSet] with x hx hy hz
    rw [hx, hy, hfV x hz, one_mul]
  obtain ⟨z, hz, hzrep⟩ := exists_memCoreOn_mul_comp F U hu'.memCore hv' hu'rep hv'rep hΦ
  have heqw : ⇑w =ᵐ[m.restrict V] ⇑z := by
    filter_upwards [ae_restrict_of_ae hwae, ae_restrict_of_ae hzrep,
      ae_restrict_mem hV.measurableSet] with x hx hy hξ
    rw [hx, hy, hfV x hξ, one_mul, one_mul]
  have hru := Γ.locality h hu.1 hu'.1 hV hequ
  have hrv := Γ.locality h hv.1 hv'.1 hV heqv
  have hrw := Γ.locality h hw hz.1 hV heqw
  have hμw := congrArg (fun μ : Measure X => (μ B).toReal)
    (Measure.restrict_congr_mono hBV hrw)
  simp only [Measure.restrict_apply_self] at hμw
  have hchain := Γ.core_leibniz h hu' hv' huc' hvc' hu'rep hv'rep Φ hΦ hz.1 hzrep hB
  have hIu : (∫ x in B, vc' x ^ 2 * deriv Φ (uc' x) ^ 2 ∂Γ.measure u') =
      ∫ x in B, vc x ^ 2 * deriv Φ (uc x) ^ 2 ∂Γ.measure u := by
    have hr := Measure.restrict_congr_mono hBV hru
    rw [← hr]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hB] with x hx
    simp only [uc', vc', hfV x (hBV hx), one_mul]
  have hIv : (∫ x in B, Φ (uc' x) ^ 2 ∂Γ.measure v') =
      ∫ x in B, Φ (uc x) ^ 2 ∂Γ.measure v := by
    have hr := Measure.restrict_congr_mono hBV hrv
    rw [← hr]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hB] with x hx
    simp only [uc', hfV x (hBV hx), one_mul]
  let g : X → ℝ := fun x => vc x * Φ (uc x) * deriv Φ (uc x)
  let g' : X → ℝ := fun x => vc' x * Φ (uc' x) * deriv Φ (uc' x)
  have hg : Continuous g := (hvc.mul (hΦ.continuous.comp huc)).mul
    ((hΦ.continuous_deriv (by norm_num)).comp huc)
  have hg' : Continuous g' := (hvc'.mul (hΦ.continuous.comp huc')).mul
    ((hΦ.continuous_deriv (by norm_num)).comp huc')
  have hgc : HasCompactSupport g := hvcc.mul_right.mul_right
  have hg'c : HasCompactSupport g' := hfc.mul_right.mul_right.mul_right
  obtain ⟨R, hR⟩ := hgc.exists_bound_of_continuous hg
  obtain ⟨R', hR'⟩ := hg'c.exists_bound_of_continuous hg'
  have hcross := Γ.cross_locality h hu.1 hv.1 hu'.1 hv'.1 hV hequ heqv
  have hcrossI : signedIntegralOn (Γ.cross u' v') B g' =
      signedIntegralOn (Γ.cross u v) B g := by
    rw [← inter_eq_left.mpr hBV,
      ← assembly_signedIntegral_restrict _ hV.measurableSet hB g' hg'.measurable R' hR',
      ← assembly_signedIntegral_restrict _ hV.measurableSet hB g hg.measurable R hR,
      ← hcross]
    -- The two integrands agree on V; restricting the measure removes its complement.
    have hg'res := assembly_signedIntegral_restrict (Γ.cross u v) hV.measurableSet hB
      g' hg'.measurable R' hR'
    rw [hg'res]
    have hgres := assembly_signedIntegral_restrict (Γ.cross u v) hV.measurableSet hB
      g hg.measurable R hR
    rw [hgres]
    simp only [signedIntegralOn]
    congr 1 <;> apply integral_congr_ae <;>
      filter_upwards [ae_restrict_mem (hB.inter hV.measurableSet)] with x hx <;>
      simp only [g', g, uc', vc', hfV x hx.2, one_mul]
  change signedIntegralOn (Γ.cross u' v') B g' = _ at hcrossI
  rw [hμw, hchain, hIu, hIv]
  exact congrArg (fun t : ℝ =>
    (∫ x in B, vc x ^ 2 * deriv Φ (uc x) ^ 2 ∂Γ.measure u) + 2 * t +
      ∫ x in B, Φ (uc x) ^ 2 ∂Γ.measure v) hcrossI

end SubdiffusiveProcess.DirichletForm.FOTConstruction
