module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamilyMeasureLimit
public import SubdiffusiveProcess.DirichletForm.FOTDomainHilbert
public import Mathlib.Topology.Order.Bornology
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal

noncomputable section
namespace SubdiffusiveProcess.DirichletForm.FOTConstruction
open _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.EnergyHilbert

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

omit [TopologicalSpace X] in
theorem family_energyNormSq_eq_norm {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X}
    (E : ClosedForm m) (u : EnergySpace E) :
    E.energyNormSq u.1 = ‖u‖ ^ 2 := (energy_norm_sq E u).symm

theorem family_core_approx (F : _root_.SubdiffusiveProcess.DirichletForm m) {U : Set X} (h : Data F U)
    (u : EnergySpace F.toClosedForm) :
    ∃ an : ℕ → EnergySpace F.toClosedForm,
      (∀ n, F.toClosedForm.MemCoreOn U (an n).1) ∧ Tendsto an atTop (𝓝 u) := by
  obtain ⟨C, hC⟩ := h.core
  choose v hvC hvε using fun n : ℕ =>
    hC.denseEnergy u.1 u.2 (1 / ((n : ℝ) + 1)) (by positivity)
  let an : ℕ → EnergySpace F.toClosedForm := fun n => ⟨v n, (hC.memCoreOn _ (hvC n)).1⟩
  refine ⟨an, fun n => hC.memCoreOn _ (hvC n), ?_⟩
  have hs : Tendsto (fun n => ‖an n - u‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [← family_energyNormSq_eq_norm]
    change F.energyNormSq (v n - u.1) ≤ _
    rw [F.toClosedForm.energyNormSq_sub_comm (an n).2 u.2]
    exact (hvε n).le
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto 0).comp hs
  rw [Real.sqrt_zero] at ht
  exact ht.congr fun n => Real.sqrt_sq (norm_nonneg (an n - u))

theorem CoreMeasure.norm_difference_bound [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} (h : Data F U) (Γ : CoreMeasure F U)
    (u v : EnergySpace F.toClosedForm)
    (hu : F.toClosedForm.MemCoreOn U u.1) (hv : F.toClosedForm.MemCoreOn U v.1)
    {B : Set X} (hB : MeasurableSet B) :
    |(Γ.measure u.1 B).toReal - (Γ.measure v.1 B).toReal| ≤
      ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have hsqrt : ∀ z : EnergySpace F.toClosedForm,
      Real.sqrt (F.form z.1 z.1) ≤ ‖z‖ := by
    intro z
    calc
      _ ≤ Real.sqrt (F.energyNormSq z.1) :=
        Real.sqrt_le_sqrt F.toClosedForm.form_le_energyNormSq
      _ = ‖z‖ := by rw [family_energyNormSq_eq_norm, Real.sqrt_sq (norm_nonneg z)]
  exact (Γ.difference_bound h hu hv hB).trans
    (mul_le_mul (hsqrt (u - v)) (add_le_add (hsqrt u) (hsqrt v))
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (norm_nonneg _))

/-- Every form-domain element has a unique measure limit along any strong core approximation. -/
theorem family_domain_measure [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} (h : Data F U) (Γ : CoreMeasure F U)
    (u : EnergySpace F.toClosedForm) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧
      ∀ an : ℕ → EnergySpace F.toClosedForm,
        (∀ n, F.toClosedForm.MemCoreOn U (an n).1) → Tendsto an atTop (𝓝 u) →
        ∀ B, MeasurableSet B →
          Tendsto (fun n => (Γ.measure (an n).1 B).toReal) atTop (𝓝 (μ B).toReal) := by
  obtain ⟨an, han, halim⟩ := family_core_approx F h u
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto (fun n => ‖an n‖)
    ((continuous_norm.tendsto u).comp halim)).bddAbove
  let R : ℝ := max 1 C
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hanR : ∀ n, ‖an n‖ ≤ R := fun n => (hC (mem_range_self n)).trans (le_max_right _ _)
  have hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      ∀ B, MeasurableSet B →
        |(Γ.measure (an n).1 B).toReal - (Γ.measure (an k).1 B).toReal| < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp halim.cauchySeq (ε / (2 * R)) (by positivity)
    refine ⟨N, ?_⟩
    intro n hn k hk B hB
    calc
      _ ≤ ‖an n - an k‖ * (‖an n‖ + ‖an k‖) :=
        Γ.norm_difference_bound h (an n) (an k) (han n) (han k) hB
      _ ≤ ‖an n - an k‖ * (2 * R) :=
        mul_le_mul_of_nonneg_left (by linarith [hanR n, hanR k]) (norm_nonneg _)
      _ < ε := by
        have hd := hN n hn k hk
        rw [dist_eq_norm] at hd
        exact (lt_div_iff₀ (by positivity : 0 < 2 * R)).mp hd
  obtain ⟨μ, hμ, hμuni⟩ := family_cauchy_measure_limit
    (fun n => Γ.measure (an n).1) (fun n => ⟨Γ.finite _ (han n)⟩) hc
  have hμlim : ∀ B, MeasurableSet B →
      Tendsto (fun n => (Γ.measure (an n).1 B).toReal) atTop (𝓝 (μ B).toReal) := by
    intro B hB
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hμuni (ε / 2) (by positivity)
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact (hN n hn B hB).trans_lt (by linarith)⟩
  refine ⟨μ, hμ, ?_⟩
  intro bn hbn hblim B hB
  have hdiff : Tendsto (fun n =>
      (Γ.measure (bn n).1 B).toReal - (Γ.measure (an n).1 B).toReal) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => Γ.norm_difference_bound h (bn n) (an n)
      (hbn n) (han n) hB)
    have hz := (continuous_norm.tendsto (u - u)).comp
      (hblim.sub halim)
    have hn := ((continuous_norm.tendsto u).comp hblim).add
      ((continuous_norm.tendsto u).comp halim)
    simpa only [sub_self, norm_zero, zero_mul] using! hz.mul hn
  have ht := hdiff.add (hμlim B hB)
  simpa only [sub_add_cancel, zero_add] using ht

end SubdiffusiveProcess.DirichletForm.FOTConstruction
