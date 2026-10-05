module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamilyCompletion
public import Mathlib.Topology.Metrizable.Urysohn

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section
namespace SubdiffusiveProcess.DirichletForm.FOTConstruction
open _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.EnergyHilbert

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

omit X [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X] m in
theorem family_memCoreOn_sub
    {X : Type u_1} [_portMeas : MeasurableSpace X] [_portTop : TopologicalSpace X] [_portT2 : T2Space X] [_portLC : LocallyCompactSpace X] [_portBorel : BorelSpace X] {m : Measure X} {E : ClosedForm m} {U : Set X} {u v : Lp ℝ 2 m}
    (hu : E.MemCoreOn U u) (hv : E.MemCoreOn U v) : E.MemCoreOn U (u - v) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hu.add (hv.smul (-1))

structure CompletedCoreFamily (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) (Γ : CoreMeasure F U) where
  measure : EnergySpace F.toClosedForm → Measure X
  finite : ∀ u, IsFiniteMeasure (measure u)
  limit : ∀ (u : EnergySpace F.toClosedForm) (an : ℕ → EnergySpace F.toClosedForm),
    (∀ n, F.toClosedForm.MemCoreOn U (an n).1) → Tendsto an atTop (𝓝 u) →
    ∀ B, MeasurableSet B →
      Tendsto (fun n => (Γ.measure (an n).1 B).toReal) atTop (𝓝 (measure u B).toReal)

theorem exists_completedCoreFamily {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : CoreMeasure F U) : Nonempty (CompletedCoreFamily F U Γ) := by
  choose μ hfinite hlim using family_domain_measure h Γ
  exact ⟨⟨μ, hfinite, hlim⟩⟩

namespace CompletedCoreFamily

variable {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {Γ : CoreMeasure F U}
  (M : CompletedCoreFamily F U Γ)

omit X [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X] m F U Γ M in
theorem core_eq
    {X : Type u_1} [_portMeas : MeasurableSpace X] [_portTop : TopologicalSpace X] [_portT2 : T2Space X] [_portLC : LocallyCompactSpace X] [_portBorel : BorelSpace X] {m : Measure X} {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {Γ : CoreMeasure F U} (M : CompletedCoreFamily F U Γ) (u : EnergySpace F.toClosedForm) (hu : F.toClosedForm.MemCoreOn U u.1) :
    M.measure u = Γ.measure u.1 := by
  let : IsFiniteMeasure (M.measure u) := M.finite u
  let : IsFiniteMeasure (Γ.measure u.1) := ⟨Γ.finite u.1 hu⟩
  ext B hB
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (tendsto_nhds_unique (M.limit u (fun _ => u) (fun _ => hu) tendsto_const_nhds B hB)
    tendsto_const_nhds)

omit X [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X] m F U Γ M in
theorem mass
    {X : Type u_1} [_portMeas : MeasurableSpace X] [_portTop : TopologicalSpace X] [_portT2 : T2Space X] [_portLC : LocallyCompactSpace X] [_portBorel : BorelSpace X] {m : Measure X} {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {Γ : CoreMeasure F U} (M : CompletedCoreFamily F U Γ) (h : Data F U) (u : EnergySpace F.toClosedForm) :
    (M.measure u univ).toReal = F.form u.1 u.1 := by
  obtain ⟨an, han, halim⟩ := family_core_approx F h u
  have hn : Tendsto (fun n => F.energyNormSq ((an n).1 - u.1)) atTop (𝓝 0) := by
    have ht := (tendsto_iff_norm_sub_tendsto_zero.mp halim).pow 2
    simpa only [zero_pow two_ne_zero, ← family_energyNormSq_eq_norm] using! ht
  exact tendsto_nhds_unique (M.limit u an han halim univ MeasurableSet.univ)
    ((F.toClosedForm.tendsto_form_self_of_tendsto_energyNormSq
      (fun n => (an n).2) u.2 hn).congr fun n => (Γ.mass (an n).1 (han n)).symm)

omit X [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X] m F U Γ M in
theorem carried
    {X : Type u_1} [_portMeas : MeasurableSpace X] [_portTop : TopologicalSpace X] [_portT2 : T2Space X] [_portLC : LocallyCompactSpace X] [_portBorel : BorelSpace X] {m : Measure X} {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {Γ : CoreMeasure F U} (M : CompletedCoreFamily F U Γ) (h : Data F U) (u : EnergySpace F.toClosedForm) : M.measure u Uᶜ = 0 := by
  let : IsFiniteMeasure (M.measure u) := M.finite u
  obtain ⟨an, han, halim⟩ := family_core_approx F h u
  have ht := M.limit u an han halim Uᶜ h.isOpen.measurableSet.compl
  have hz : (M.measure u Uᶜ).toReal = 0 := (tendsto_nhds_unique ht
    (by simpa only [Γ.carried _ (han _), ENNReal.toReal_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))))
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top _ _)

theorem regular [SecondCountableTopology X] (u : EnergySpace F.toClosedForm) :
    (M.measure u).Regular := by
  let : IsFiniteMeasure (M.measure u) := M.finite u
  infer_instance

theorem parallelogram (h : Data F U) (u v : EnergySpace F.toClosedForm)
    {B : Set X} (hB : MeasurableSet B) :
    (M.measure (u + v) B).toReal + (M.measure (u - v) B).toReal =
      2 * (M.measure u B).toReal + 2 * (M.measure v B).toReal := by
  obtain ⟨an, han, halim⟩ := family_core_approx F h u
  obtain ⟨bn, hbn, hblim⟩ := family_core_approx F h v
  have hl := (M.limit (u + v) (fun n => an n + bn n)
    (fun n => (han n).add (hbn n)) (halim.add hblim) B hB).add
      (M.limit (u - v) (fun n => an n - bn n)
        (fun n => family_memCoreOn_sub (han n) (hbn n)) (halim.sub hblim) B hB)
  have hr := ((M.limit u an han halim B hB).const_mul 2).add
    ((M.limit v bn hbn hblim B hB).const_mul 2)
  exact tendsto_nhds_unique hl (hr.congr fun n => (Γ.parallelogram h (han n) (hbn n) hB).symm)

theorem difference_bound (h : Data F U) (u v : EnergySpace F.toClosedForm)
    {B : Set X} (hB : MeasurableSet B) :
    |(M.measure u B).toReal - (M.measure v B).toReal| ≤ ‖u - v‖ * (‖u‖ + ‖v‖) := by
  obtain ⟨an, han, halim⟩ := family_core_approx F h u
  obtain ⟨bn, hbn, hblim⟩ := family_core_approx F h v
  exact le_of_tendsto_of_tendsto'
    (((M.limit u an han halim B hB).sub (M.limit v bn hbn hblim B hB)).abs)
    (((continuous_norm.tendsto (u - v)).comp (halim.sub hblim)).mul
      (((continuous_norm.tendsto u).comp halim).add ((continuous_norm.tendsto v).comp hblim)))
    (fun n => Γ.norm_difference_bound h (an n) (bn n) (han n) (hbn n) hB)

theorem continuous (h : Data F U) {B : Set X} (hB : MeasurableSet B) :
    Continuous (fun u => (M.measure u B).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let R : ℝ := 2 * ‖u‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨min 1 (ε / R), lt_min zero_lt_one (div_pos hε hR), ?_⟩
  intro v hv
  rw [dist_eq_norm] at hv
  have hv1 : ‖v - u‖ < 1 := hv.trans_le (min_le_left _ _)
  have hvδ : ‖v - u‖ < ε / R := hv.trans_le (min_le_right _ _)
  have hvnorm : ‖v‖ ≤ ‖u‖ + 1 := by
    have hn := norm_sub_le_norm_sub_add_norm_sub v u 0
    simp only [sub_zero] at hn
    linarith
  rw [Real.dist_eq]
  calc
    _ ≤ ‖v - u‖ * (‖v‖ + ‖u‖) := M.difference_bound h v u hB
    _ ≤ ‖v - u‖ * R := mul_le_mul_of_nonneg_left (by dsimp [R]; linarith) (norm_nonneg _)
    _ < ε := (lt_div_iff₀ hR).mp hvδ

end CompletedCoreFamily
end SubdiffusiveProcess.DirichletForm.FOTConstruction
