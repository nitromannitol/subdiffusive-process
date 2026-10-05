module

public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.prop_regularity
public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

namespace SubdiffusiveProcess.DirichletForm
namespace ClosedForm

variable {m : Measure X} (E : ClosedForm m)

omit [TopologicalSpace X] in
theorem aux_form_zero_left {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} (E : ClosedForm m)
    {v : Lp ℝ 2 m} (hv : v ∈ E.domain) :
    E.form 0 v = 0 := by
  simpa using E.form_smul_left 0 0 E.domain.zero_mem v hv

omit [TopologicalSpace X] in
theorem aux_form_add_right {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} (E : ClosedForm m)
    {u v w : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) (hw : w ∈ E.domain) :
    E.form u (v + w) = E.form u v + E.form u w := by
  rw [E.form_symm u hu (v + w) (E.domain.add_mem hv hw),
    E.form_add_left v hv w hw u hu,
    E.form_symm v hv u hu, E.form_symm w hw u hu]

omit [TopologicalSpace X] in
theorem aux_form_smul_right {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} (E : ClosedForm m)
    (c : ℝ) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form u (c • v) = c * E.form u v := by
  rw [E.form_symm u hu (c • v) (E.domain.smul_mem c hv),
    E.form_smul_left c v hv u hu, E.form_symm v hv u hu]

omit [TopologicalSpace X] in
theorem aux_form_neg_left {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} (E : ClosedForm m)
    {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (-u) v = -E.form u v := by
  simpa using E.form_smul_left (-1) u hu v hv

theorem aux_form_neg_right {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form u (-v) = -E.form u v := by
  simpa using E.aux_form_smul_right (-1) hu hv

theorem aux_form_sub_left {u v w : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) (hw : w ∈ E.domain) :
    E.form (u - v) w = E.form u w - E.form v w := by
  simpa only [sub_eq_add_neg, E.aux_form_neg_left hv hw] using
    E.form_add_left u hu (-v) (E.domain.neg_mem hv) w hw

theorem aux_form_sub_right {u v w : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) (hw : w ∈ E.domain) :
    E.form u (v - w) = E.form u v - E.form u w := by
  simpa only [sub_eq_add_neg, E.aux_form_neg_right hu hw] using
    E.aux_form_add_right hu hv (E.domain.neg_mem hw)

theorem aux_form_add_self {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (u + v) (u + v) = E.form u u + 2 * E.form u v + E.form v v := by
  rw [E.form_add_left u hu v hv (u + v) (E.domain.add_mem hu hv),
    E.aux_form_add_right hu hu hv, E.aux_form_add_right hv hu hv,
    E.form_symm v hv u hu]
  ring

theorem aux_form_sub_self {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (u - v) (u - v) = E.form u u - 2 * E.form u v + E.form v v := by
  rw [E.aux_form_sub_left hu hv (E.domain.sub_mem hu hv),
    E.aux_form_sub_right hu hu hv, E.aux_form_sub_right hv hu hv,
    E.form_symm v hv u hu]
  ring

omit [TopologicalSpace X] in
theorem aux_energy_nonneg {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} (E : ClosedForm m)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    0 ≤ E.energyNormSq u := by
  exact add_nonneg (E.form_nonneg u hu) (sq_nonneg ‖u‖)

omit [TopologicalSpace X] in
theorem aux_norm_sq_le_energy {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} (E : ClosedForm m)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    ‖u‖ ^ 2 ≤ E.energyNormSq u := by
  exact le_add_of_nonneg_left (E.form_nonneg u hu)

theorem aux_energy_neg {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    E.energyNormSq (-u) = E.energyNormSq u := by
  unfold energyNormSq
  rw [E.aux_form_neg_left hu (E.domain.neg_mem hu), E.aux_form_neg_right hu hu]
  simp

theorem aux_energy_sub_symm {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.energyNormSq (u - v) = E.energyNormSq (v - u) := by
  rw [← neg_sub v u, E.aux_energy_neg (E.domain.sub_mem hv hu)]

theorem aux_energy_add_le {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.energyNormSq (u + v) ≤ 2 * (E.energyNormSq u + E.energyNormSq v) := by
  have hminus := E.form_nonneg (u - v) (E.domain.sub_mem hu hv)
  rw [E.aux_form_sub_self hu hv] at hminus
  have hnorm := mul_self_le_mul_self (norm_nonneg (u + v)) (norm_add_le u v)
  unfold energyNormSq
  rw [E.aux_form_add_self hu hv]
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

theorem aux_tendsto_Lp_of_energy {w : ℕ → Lp ℝ 2 m} {v : Lp ℝ 2 m}
    (hw : ∀ n, w n ∈ E.domain) (hv : v ∈ E.domain)
    (h : Tendsto (fun n => E.energyNormSq (w n - v)) atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 v) := by
  have hsq : Tendsto (fun n => ‖w n - v‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) (fun n =>
      E.aux_norm_sq_le_energy (E.domain.sub_mem (hw n) hv)) h
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  have hn' : Tendsto (fun n => ‖w n - v‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

end ClosedForm

namespace EnergyMeasure

variable {m : Measure X} {E : ClosedForm m} (Γ : EnergyMeasure E)

def aux_p (B : Set X) (u : Lp ℝ 2 m) : ℝ := Real.sqrt (Γ.measure u B).toReal

theorem aux_finite {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (B : Set X) :
    Γ.measure u B ≠ ⊤ := by
  exact ne_of_lt ((measure_mono (Set.subset_univ B)).trans_lt
    (Γ.measure_univ_lt_top u hu))

theorem aux_mass_le_energy {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (B : Set X) :
    (Γ.measure u B).toReal ≤ E.energyNormSq u := by
  have h : (Γ.measure u B).toReal ≤ (Γ.measure u Set.univ).toReal :=
    ENNReal.toReal_mono (Γ.aux_finite hu Set.univ) (measure_mono (Set.subset_univ B))
  rw [Γ.measure_univ u hu] at h
  exact h.trans (le_add_of_nonneg_right (sq_nonneg ‖u‖))

theorem aux_p_nonneg (B : Set X) (u : Lp ℝ 2 m) : 0 ≤ Γ.aux_p B u :=
  Real.sqrt_nonneg _

theorem aux_p_sq (B : Set X) (u : Lp ℝ 2 m) :
    Γ.aux_p B u ^ 2 = (Γ.measure u B).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

theorem aux_p_le_sqrt_energy {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (B : Set X) :
    Γ.aux_p B u ≤ Real.sqrt (E.energyNormSq u) :=
  Real.sqrt_le_sqrt (Γ.aux_mass_le_energy hu B)

theorem aux_cross_add_left {u v w : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) (hw : w ∈ E.domain) :
    Γ.cross (u + v) w = Γ.cross u w + Γ.cross v w := by
  rw [Γ.cross_symm (u + v) (E.domain.add_mem hu hv) w hw,
    Γ.cross_add_right w hw u hu v hv,
    Γ.cross_symm w hw u hu, Γ.cross_symm w hw v hv]

theorem aux_cross_smul_left (c : ℝ) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    Γ.cross (c • u) v = c • Γ.cross u v := by
  rw [Γ.cross_symm (c • u) (E.domain.smul_mem c hu) v hv,
    Γ.cross_smul_right c v hv u hu, Γ.cross_symm v hv u hu]

theorem aux_mass_add {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure (u + v) B).toReal =
      (Γ.measure u B).toReal + 2 * Γ.cross u v B + (Γ.measure v B).toReal := by
  rw [← Γ.cross_self (u + v) (E.domain.add_mem hu hv) B hB,
    Γ.aux_cross_add_left hu hv (E.domain.add_mem hu hv),
    Γ.cross_add_right u hu u hu v hv, Γ.cross_add_right v hv u hu v hv,
    Γ.cross_symm v hv u hu]
  simp only [add_apply, Γ.cross_self u hu B hB, Γ.cross_self v hv B hB]
  ring

theorem aux_mass_smul (c : ℝ) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure (c • u) B).toReal = c ^ 2 * (Γ.measure u B).toReal := by
  rw [← Γ.cross_self (c • u) (E.domain.smul_mem c hu) B hB,
    Γ.aux_cross_smul_left c hu (E.domain.smul_mem c hu),
    Γ.cross_smul_right c u hu u hu]
  simp only [smul_apply, smul_eq_mul, Γ.cross_self u hu B hB]
  ring

theorem aux_p_zero {B : Set X} (hB : MeasurableSet B) : Γ.aux_p B 0 = 0 := by
  have h := Γ.aux_mass_smul 0 E.domain.zero_mem hB
  simp only [zero_smul, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  simp only [aux_p, h, Real.sqrt_zero]

theorem aux_p_smul (c : ℝ) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) {B : Set X} (hB : MeasurableSet B) :
    Γ.aux_p B (c • u) = |c| * Γ.aux_p B u := by
  have h := Γ.aux_mass_smul c hu hB
  have hs₁ := Γ.aux_p_sq B (c • u)
  have hs₂ := Γ.aux_p_sq B u
  have hn₁ := Γ.aux_p_nonneg B (c • u)
  have hn₂ := mul_nonneg (abs_nonneg c) (Γ.aux_p_nonneg B u)
  have heq : (Γ.aux_p B (c • u)) ^ 2 = (|c| * Γ.aux_p B u) ^ 2 := by
    rw [mul_pow, sq_abs, hs₁, hs₂, h]
  nlinarith

theorem aux_p_neg {u : Lp ℝ 2 m} (hu : u ∈ E.domain)
    {B : Set X} (hB : MeasurableSet B) : Γ.aux_p B (-u) = Γ.aux_p B u := by
  simpa using Γ.aux_p_smul (-1) hu hB

theorem aux_p_add_le {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) {B : Set X} (hB : MeasurableSet B) :
    Γ.aux_p B (u + v) ≤ Γ.aux_p B u + Γ.aux_p B v := by
  have hc := (le_abs_self (Γ.cross u v B)).trans (Γ.abs_cross_le u hu v hv B hB)
  change Γ.cross u v B ≤ Γ.aux_p B u * Γ.aux_p B v at hc
  have hmass := Γ.aux_mass_add hu hv hB
  have ha := Γ.aux_p_sq B u
  have hb := Γ.aux_p_sq B v
  have hab := Γ.aux_p_sq B (u + v)
  have hn := Γ.aux_p_nonneg B (u + v)
  have hn' := add_nonneg (Γ.aux_p_nonneg B u) (Γ.aux_p_nonneg B v)
  nlinarith

theorem aux_p_sub_le {a b : Lp ℝ 2 m}
    (ha : a ∈ E.domain) (hb : b ∈ E.domain) {B : Set X} (hB : MeasurableSet B) :
    |Γ.aux_p B a - Γ.aux_p B b| ≤ Γ.aux_p B (a - b) := by
  have h₁ := Γ.aux_p_add_le (E.domain.sub_mem ha hb) hb hB
  rw [sub_add_cancel] at h₁
  have h₂ := Γ.aux_p_add_le (E.domain.sub_mem hb ha) ha hB
  rw [sub_add_cancel] at h₂
  have hneg : Γ.aux_p B (b - a) = Γ.aux_p B (a - b) := by
    rw [← neg_sub a b, Γ.aux_p_neg (E.domain.sub_mem ha hb) hB]
  rw [hneg] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem aux_p_tendsto {w : ℕ → Lp ℝ 2 m} {v : Lp ℝ 2 m}
    (hw : ∀ n, w n ∈ E.domain) (hv : v ∈ E.domain)
    (h : Tendsto (fun n => E.energyNormSq (w n - v)) atTop (𝓝 0))
    {B : Set X} (hB : MeasurableSet B) :
    Tendsto (fun n => Γ.aux_p B (w n)) atTop (𝓝 (Γ.aux_p B v)) := by
  have hs : Tendsto (fun n => Real.sqrt (E.energyNormSq (w n - v))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero] using! (Real.continuous_sqrt.tendsto 0).comp h
  have hz : Tendsto (fun n => |Γ.aux_p B (w n) - Γ.aux_p B v|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n =>
      (Γ.aux_p_sub_le (hw n) hv hB).trans
        (Γ.aux_p_le_sqrt_energy (E.domain.sub_mem (hw n) hv) B)) hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)

theorem aux_p_mono {u v : Lp ℝ 2 m} (hv : v ∈ E.domain)
    (h : Γ.measure u ≤ Γ.measure v) (B : Set X) : Γ.aux_p B u ≤ Γ.aux_p B v := by
  exact Real.sqrt_le_sqrt (ENNReal.toReal_mono (Γ.aux_finite hv B)
    ((Measure.le_iff').mp h B))

theorem aux_measure_le_of_p_le {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (h : ∀ B : Set X, MeasurableSet B → Γ.aux_p B u ≤ Γ.aux_p B v) :
    Γ.measure u ≤ Γ.measure v := by
  apply Measure.le_iff.mpr
  intro B hB
  apply (ENNReal.toReal_le_toReal (Γ.aux_finite hu B) (Γ.aux_finite hv B)).mp
  have hs := mul_self_le_mul_self (Γ.aux_p_nonneg B u) (h B hB)
  nlinarith [Γ.aux_p_sq B u, Γ.aux_p_sq B v]

end EnergyMeasure

def aux_cesaro {m : Measure X} (w : ℕ → Lp ℝ 2 m) (n : ℕ) : Lp ℝ 2 m :=
  (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, w k

def aux_CesaroEnergyCauchy {m : Measure X} (E : ClosedForm m) : Prop :=
  ∀ (w : ℕ → Lp ℝ 2 m) (C : ℝ),
    (∀ k, w k ∈ E.domain) → (∀ k, E.energyNormSq (w k) ≤ C) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
          E.energyNormSq
            (aux_cesaro (w ∘ σ) p - aux_cesaro (w ∘ σ) q) < ε

omit [TopologicalSpace X] in
theorem aux_cesaro_mem {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    {m : Measure X} (E : ClosedForm m)
    {w : ℕ → Lp ℝ 2 m} (hw : ∀ n, w n ∈ E.domain) (n : ℕ) :
    aux_cesaro w n ∈ E.domain := by
  exact E.domain.smul_mem _ (E.domain.sum_mem (fun k _ => hw k))

theorem aux_energy_subsequence_of_cauchy {m : Measure X} (E : ClosedForm m)
    (hBS : aux_CesaroEnergyCauchy E) {w : ℕ → Lp ℝ 2 m} {v : Lp ℝ 2 m}
    (hw : ∀ n, w n ∈ E.domain) {C : ℝ} (hC : ∀ n, E.energyNormSq (w n) ≤ C)
    (hwv : Tendsto w atTop (𝓝 v)) :
    v ∈ E.domain ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => E.energyNormSq (aux_cesaro (w ∘ σ) n - v)) atTop (𝓝 0) := by
  obtain ⟨σ, hσ, hc⟩ := hBS w C hw hC
  have hmem : ∀ n, aux_cesaro (w ∘ σ) n ∈ E.domain :=
    aux_cesaro_mem E (fun k => hw (σ k))
  obtain ⟨z, hz, hlim⟩ := E.complete (aux_cesaro (w ∘ σ)) hmem (by
    simpa only [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq] using hc)
  change Tendsto (fun n => E.energyNormSq (aux_cesaro (w ∘ σ) n - z))
    atTop (𝓝 0) at hlim
  have hzlim := E.aux_tendsto_Lp_of_energy hmem hz hlim
  have hvlim : Tendsto (aux_cesaro (w ∘ σ)) atTop (𝓝 v) := by
    simpa only [aux_cesaro, Function.comp_apply] using!
      (hwv.comp hσ.tendsto_atTop).cesaro_smul
  have heq : z = v := tendsto_nhds_unique hzlim hvlim
  subst z
  exact ⟨hz, σ, hσ, hlim⟩

namespace EnergyMeasure

variable {m : Measure X} {E : ClosedForm m} (Γ : EnergyMeasure E)

theorem aux_p_sum_le {w : ℕ → Lp ℝ 2 m} (hw : ∀ n, w n ∈ E.domain)
    {B : Set X} (hB : MeasurableSet B) (s : Finset ℕ) :
    Γ.aux_p B (∑ i ∈ s, w i) ≤ ∑ i ∈ s, Γ.aux_p B (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Γ.aux_p_zero hB]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (Γ.aux_p_add_le (hw i) (E.domain.sum_mem (fun k _ => hw k)) hB).trans
        (add_le_add le_rfl ih)

theorem aux_p_cesaro_le {w : ℕ → Lp ℝ 2 m} (hw : ∀ n, w n ∈ E.domain)
    {B : Set X} (hB : MeasurableSet B) {b : ℕ → ℝ}
    (hb : ∀ n, Γ.aux_p B (w n) ≤ b n) (n : ℕ) :
    Γ.aux_p B (aux_cesaro w n) ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, b i := by
  unfold aux_cesaro
  rw [Γ.aux_p_smul _ (E.domain.sum_mem (fun k _ => hw k)) hB,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact (Γ.aux_p_sum_le hw hB _).trans (Finset.sum_le_sum (fun k _ => hb k))

theorem aux_p_lsc_of_cesaroCauchy (hBS : aux_CesaroEnergyCauchy E)
    {w : ℕ → Lp ℝ 2 m} {v : Lp ℝ 2 m}
    (hw : ∀ n, w n ∈ E.domain) {C : ℝ} (hC : ∀ n, E.energyNormSq (w n) ≤ C)
    (hwv : Tendsto w atTop (𝓝 v)) {B : Set X} (hB : MeasurableSet B)
    {b : ℕ → ℝ} {b₀ : ℝ} (hb : ∀ n, Γ.aux_p B (w n) ≤ b n)
    (hblim : Tendsto b atTop (𝓝 b₀)) : Γ.aux_p B v ≤ b₀ := by
  obtain ⟨hv, σ, hσ, henergy⟩ := aux_energy_subsequence_of_cauchy E hBS hw hC hwv
  have hmem : ∀ n, aux_cesaro (w ∘ σ) n ∈ E.domain :=
    aux_cesaro_mem E (fun k => hw (σ k))
  have hp := Γ.aux_p_tendsto hmem hv henergy hB
  have hbmean := (hblim.comp hσ.tendsto_atTop).cesaro
  exact le_of_tendsto_of_tendsto hp hbmean (Filter.Eventually.of_forall
    (Γ.aux_p_cesaro_le (fun k => hw (σ k)) hB (fun k => hb (σ k))))

end EnergyMeasure

def aux_delta (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem aux_delta_pos (n : ℕ) : 0 < aux_delta n := by
  unfold aux_delta
  positivity

theorem aux_delta_le_one (n : ℕ) : aux_delta n ≤ 1 := by
  unfold aux_delta
  apply (inv_le_one₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem aux_delta_tendsto : Tendsto aux_delta atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact tendsto_inv_atTop_zero.comp ht

def aux_smoothAbs (δ t : ℝ) : ℝ := Real.sqrt (t ^ 2 + δ ^ 2)

def aux_smoothClamp (δ t : ℝ) : ℝ :=
  (aux_smoothAbs δ t - aux_smoothAbs δ (t - 1) -
    aux_smoothAbs δ 0 + aux_smoothAbs δ (-1)) / 2

theorem aux_smoothAbs_contDiff {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ 1 (aux_smoothAbs δ) := by
  unfold aux_smoothAbs
  apply ((contDiff_id.pow 2).add contDiff_const).sqrt
  intro t
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  exact ne_of_gt (by nlinarith [sq_nonneg t])

theorem aux_shifted_sqrt_hasDerivAt {δ : ℝ} (hδ : 0 < δ) (a t : ℝ) :
    HasDerivAt (fun s : ℝ => aux_smoothAbs δ (s - a))
      ((t - a) / aux_smoothAbs δ (t - a)) t := by
  have hrad : 0 < (t - a) ^ 2 + δ ^ 2 := by
    nlinarith [sq_nonneg (t - a), sq_pos_of_pos hδ]
  have hroot : Real.sqrt ((t - a) ^ 2 + δ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  have hq : HasDerivAt (fun s : ℝ => (s - a) ^ 2 + δ ^ 2) (2 * (t - a)) t := by
    convert (((hasDerivAt_id t).sub_const a).pow 2).add_const (δ ^ 2) using 1 <;> simp only [id, Pi.pow_apply] ; ring
  have hs := hq.sqrt (ne_of_gt hrad)
  convert hs using 1 <;> dsimp [aux_smoothAbs] ; field_simp [hroot]

theorem aux_smoothClamp_contDiff {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ 1 (aux_smoothClamp δ) := by
  unfold aux_smoothClamp
  exact ((((aux_smoothAbs_contDiff hδ).sub
    ((aux_smoothAbs_contDiff hδ).comp (contDiff_id.sub contDiff_const))).sub
      contDiff_const).add contDiff_const).div_const 2

theorem aux_smoothClamp_zero (δ : ℝ) : aux_smoothClamp δ 0 = 0 := by
  unfold aux_smoothClamp
  simp only [zero_sub]
  ring

theorem aux_smoothClamp_deriv {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    deriv (aux_smoothClamp δ) t =
      (t / aux_smoothAbs δ t - (t - 1) / aux_smoothAbs δ (t - 1)) / 2 := by
  have h₀ := aux_shifted_sqrt_hasDerivAt hδ 0 t
  have h₁ := aux_shifted_sqrt_hasDerivAt hδ 1 t
  have h := (((h₀.sub h₁).sub_const (aux_smoothAbs δ 0)).add_const
    (aux_smoothAbs δ (-1))).div_const 2
  simpa only [sub_zero, aux_smoothClamp, Pi.sub_apply] using! h.deriv

theorem aux_smoothAbs_error {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ aux_smoothAbs δ t - |t| ∧ aux_smoothAbs δ t - |t| ≤ δ := by
  have hl : |t| ≤ aux_smoothAbs δ t := by
    rw [← Real.sqrt_sq_eq_abs t]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg δ))
  have hu : aux_smoothAbs δ t ≤ |t| + δ := by
    calc
      aux_smoothAbs δ t ≤ Real.sqrt ((|t| + δ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_abs t, mul_nonneg (abs_nonneg t) hδ.le]
      _ = |t| + δ := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (add_nonneg (abs_nonneg t) hδ.le)]
  exact ⟨sub_nonneg.mpr hl, by linarith⟩

theorem aux_smoothAbs_ratio_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |t / aux_smoothAbs δ t| ≤ 1 := by
  have hroot : 0 < aux_smoothAbs δ t := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg t, sq_pos_of_pos hδ]
  rw [abs_div, abs_of_pos hroot]
  apply (div_le_iff₀ hroot).mpr
  simpa only [one_mul] using sub_nonneg.mp (aux_smoothAbs_error hδ t).1

theorem aux_smoothClamp_deriv_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |deriv (aux_smoothClamp δ) t| ≤ 1 := by
  rw [aux_smoothClamp_deriv hδ t, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : 0 < (2 : ℝ))).mpr
  have htriangle :
      |t / aux_smoothAbs δ t - (t - 1) / aux_smoothAbs δ (t - 1)| ≤
        |t / aux_smoothAbs δ t| + |(t - 1) / aux_smoothAbs δ (t - 1)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (t / aux_smoothAbs δ t) (-((t - 1) / aux_smoothAbs δ (t - 1)))
  linarith [aux_smoothAbs_ratio_le hδ t, aux_smoothAbs_ratio_le hδ (t - 1)]

theorem aux_unitTruncation_abs (t : ℝ) :
    unitTruncation t = (|t| - |t - 1| + 1) / 2 := by
  by_cases h₀ : t ≤ 0
  · have h₁ : t ≤ 1 := by linarith
    have hm : t - 1 ≤ 0 := by linarith
    simp only [unitTruncation, min_eq_left h₁, max_eq_right h₀,
      abs_of_nonpos h₀, abs_of_nonpos hm]
    ring
  · have ht : 0 ≤ t := (lt_of_not_ge h₀).le
    by_cases h₁ : t ≤ 1
    · have hm : t - 1 ≤ 0 := by linarith
      simp only [unitTruncation, min_eq_left h₁, max_eq_left ht,
        abs_of_nonneg ht, abs_of_nonpos hm]
      ring
    · have ht₁ : 1 ≤ t := (lt_of_not_ge h₁).le
      have hm : 0 ≤ t - 1 := by linarith
      simp only [unitTruncation, min_eq_right ht₁,
        max_eq_left (by norm_num : (0 : ℝ) ≤ 1),
        abs_of_nonneg ht, abs_of_nonneg hm]
      ring

theorem aux_smoothClamp_error {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |aux_smoothClamp δ t - unitTruncation t| ≤ δ := by
  obtain ⟨hl₀, hu₀⟩ := aux_smoothAbs_error hδ t
  obtain ⟨hl₁, hu₁⟩ := aux_smoothAbs_error hδ (t - 1)
  obtain ⟨hl₂, hu₂⟩ := aux_smoothAbs_error hδ 0
  obtain ⟨hl₃, hu₃⟩ := aux_smoothAbs_error hδ (-1)
  norm_num only [abs_zero, sub_zero, abs_neg, abs_one] at hl₂ hu₂ hl₃ hu₃
  rw [aux_unitTruncation_abs]
  unfold aux_smoothClamp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem aux_unitTruncation_lipschitz : LipschitzWith 1 unitTruncation := by
  simpa only [unitTruncation, id_eq] using!
    (((LipschitzWith.id : LipschitzWith 1 (fun t : ℝ => t)).min_const 1).max_const 0)

theorem aux_unitTruncation_zero : unitTruncation 0 = 0 := by
  norm_num [unitTruncation]

theorem aux_lipschitz_of_deriv {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    (hderiv : ∀ t, |deriv Φ t| ≤ 1) : LipschitzWith 1 Φ := by
  apply lipschitzWith_of_nnnorm_deriv_le (hΦ.differentiable (by norm_num))
  intro t
  have h : ‖deriv Φ t‖ ≤ (1 : ℝ) := by
    simpa only [Real.norm_eq_abs] using hderiv t
  exact_mod_cast h

theorem aux_lipschitz_abs {Φ : ℝ → ℝ} (hΦ : LipschitzWith 1 Φ)
    (h₀ : Φ 0 = 0) (t : ℝ) : |Φ t| ≤ |t| := by
  simpa only [Real.dist_eq, h₀, sub_zero, NNReal.coe_one, one_mul] using hΦ.dist_le_mul t 0

def aux_truncLp {m : Measure X} (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  aux_unitTruncation_lipschitz.compLp aux_unitTruncation_zero u

omit [TopologicalSpace X] in
theorem aux_truncLp_rep {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    {m : Measure X} (u : Lp ℝ 2 m) :
    ⇑(aux_truncLp u) =ᵐ[m] fun x => unitTruncation (u x) := by
  exact aux_unitTruncation_lipschitz.coeFn_compLp aux_unitTruncation_zero u

omit [TopologicalSpace X] in
theorem aux_truncLp_norm {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    {m : Measure X} (u : Lp ℝ 2 m) :
    ‖aux_truncLp u‖ ≤ ‖u‖ := by
  simpa only [NNReal.coe_one, one_mul, aux_truncLp] using!
    aux_unitTruncation_lipschitz.norm_compLp_le aux_unitTruncation_zero u

omit [TopologicalSpace X] in
theorem aux_truncLp_tendsto {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    {m : Measure X} {w : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (h : Tendsto w atTop (𝓝 u)) :
    Tendsto (fun n => aux_truncLp (w n)) atTop (𝓝 (aux_truncLp u)) := by
  exact (aux_unitTruncation_lipschitz.continuous_compLp
    aux_unitTruncation_zero).continuousAt.tendsto.comp h

omit [TopologicalSpace X] in
theorem aux_Lp_norm_sq {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    {m : Measure X} (u : Lp ℝ 2 m) :
    ‖u‖ ^ 2 = ∫ x, (u x) ^ 2 ∂m := by
  calc
    ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
    _ = ∫ x, inner ℝ (u x) (u x) ∂m := rfl
    _ = ∫ x, (u x) ^ 2 ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs])

theorem aux_Lp_compositions_tendsto {m : Measure X}
    (u v : Lp ℝ 2 m) (w : ℕ → Lp ℝ 2 m) (Φ : ℕ → ℝ → ℝ)
    (hbound : ∀ n t, |Φ n t| ≤ |t|)
    (hwrep : ∀ n, ⇑(w n) =ᵐ[m] fun x => Φ n (u x))
    (hvrep : ⇑v =ᵐ[m] fun x => unitTruncation (u x))
    (hpoint : ∀ t, Tendsto (fun n => Φ n t) atTop (𝓝 (unitTruncation t))) :
    Tendsto w atTop (𝓝 v) := by
  have hreps : ∀ᵐ x ∂m, (∀ n, w n x = Φ n (u x)) ∧
      v x = unitTruncation (u x) :=
    (ae_all_iff.mpr hwrep).and hvrep
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => (w n x - v x) ^ 2) m := by
    intro n
    have hd := (Lp.aestronglyMeasurable (w n)).sub (Lp.aestronglyMeasurable v)
    simpa only [pow_two, Pi.mul_apply, Pi.sub_apply] using! hd.mul hd
  have hdom : Integrable (fun x => 4 * (u x) ^ 2) m :=
    (Lp.memLp u).integrable_sq.const_mul 4
  have hle : ∀ n, ∀ᵐ x ∂m, ‖(w n x - v x) ^ 2‖ ≤ 4 * (u x) ^ 2 := by
    intro n
    filter_upwards [hreps] with x hx
    have hw : |w n x| ≤ |u x| := by
      rw [hx.1 n]
      exact hbound n (u x)
    have hv : |v x| ≤ |u x| := by
      rw [hx.2]
      exact aux_lipschitz_abs aux_unitTruncation_lipschitz aux_unitTruncation_zero (u x)
    have hd : |w n x - v x| ≤ 2 * |u x| := by
      have ht : |w n x - v x| ≤ |w n x| + |v x| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (w n x) (-v x)
      linarith
    have hs := mul_self_le_mul_self (abs_nonneg (w n x - v x)) hd
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (w n x - v x), sq_abs (u x)]
  have hpoint' : ∀ᵐ x ∂m,
      Tendsto (fun n => (w n x - v x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hreps] with x hx
    simpa only [hx.1, hx.2, sub_self, zero_pow (by decide : 2 ≠ 0)] using
      ((hpoint (u x)).sub_const (unitTruncation (u x))).pow 2
  have hint : Tendsto (fun n => ∫ x, (w n x - v x) ^ 2 ∂m) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence (fun x => 4 * (u x) ^ 2)
        hmeas hdom hle hpoint'
  have heq : (fun n => ∫ x, (w n x - v x) ^ 2 ∂m) =
      (fun n => ‖w n - v‖ ^ 2) := by
    funext n
    rw [aux_Lp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (w n) v] with x hx
    simp only [hx, Pi.sub_apply]
  rw [heq] at hint
  have hn := (Real.continuous_sqrt.tendsto 0).comp hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

namespace EnergyMeasure

variable {m : Measure X} {E : ClosedForm m} (Γ : EnergyMeasure E)

theorem aux_smooth_measure_le {u w : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hw : w ∈ E.domain) {uc : X → ℝ}
    (hc : Continuous uc) (hurep : ⇑u =ᵐ[m] uc)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦ₀ : Φ 0 = 0)
    (hderiv : ∀ t, |deriv Φ t| ≤ 1)
    (hwrep : ⇑w =ᵐ[m] fun x => Φ (uc x)) : Γ.measure w ≤ Γ.measure u := by
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
  apply Measure.le_iff.mpr
  intro B hB
  apply (ENNReal.toReal_le_toReal (Γ.aux_finite hw B) (Γ.aux_finite hu B)).mp
  rw [Γ.chain_rule u hu uc hc hurep Φ hΦ hΦ₀ w hw hwrep B hB]
  calc
    (∫ x in B, (deriv Φ (uc x)) ^ 2 ∂(Γ.measure u)) ≤
        ∫ x in B, (1 : ℝ) ∂(Γ.measure u) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => sq_nonneg _)) (integrable_const 1)
      exact Filter.Eventually.of_forall (fun x => by
        have hs := mul_self_le_mul_self (abs_nonneg (deriv Φ (uc x))) (hderiv (uc x))
        nlinarith [sq_abs (deriv Φ (uc x))])
    _ = (Γ.measure u B).toReal := by simp [Measure.real]

end EnergyMeasure

theorem aux_core_truncation_measure_contraction {m : Measure X}
    (E : _root_.SubdiffusiveProcess.DirichletForm m) (Γ : EnergyMeasure E.toClosedForm)
    (halg : IsCoreAlgebra E.toClosedForm)
    (hBS : aux_CesaroEnergyCauchy E.toClosedForm)
    {u v : Lp ℝ 2 m} (hu : E.toClosedForm.MemCore u)
    (hvrep : ⇑v =ᵐ[m] fun x => unitTruncation (u x)) :
    v ∈ E.toClosedForm.domain ∧ Γ.measure v ≤ Γ.measure u := by
  classical
  have hv := (E.markov u hu.1 v hvrep).1
  obtain ⟨uc, huc, huccomp, hucsup, hurep⟩ := hu.2
  let Φ : ℕ → ℝ → ℝ := fun n => aux_smoothClamp (aux_delta n)
  have hΦ : ∀ n, ContDiff ℝ 1 (Φ n) := fun n =>
    aux_smoothClamp_contDiff (aux_delta_pos n)
  have hΦ₀ : ∀ n, Φ n 0 = 0 := fun n => aux_smoothClamp_zero _
  have hderiv : ∀ n t, |deriv (Φ n) t| ≤ 1 := fun n t =>
    aux_smoothClamp_deriv_le (aux_delta_pos n) t
  have hbound : ∀ n t, |Φ n t| ≤ |t| := fun n t =>
    aux_lipschitz_abs (aux_lipschitz_of_deriv (hΦ n) (hderiv n)) (hΦ₀ n) t
  have hex : ∀ n, ∃ w : Lp ℝ 2 m,
      E.toClosedForm.MemCore w ∧ (⇑w =ᵐ[m] fun x => Φ n (u x)) := fun n =>
    halg.comp_mem u hu (Φ n) (hΦ n) (hΦ₀ n)
  choose w hwcore hwrep using hex
  have hw : ∀ n, w n ∈ E.toClosedForm.domain := fun n => (hwcore n).1
  have hwrepuc : ∀ n, ⇑(w n) =ᵐ[m] fun x => Φ n (uc x) := by
    intro n
    filter_upwards [hwrep n, hurep] with x hx huₓ
    rw [hx, huₓ]
  have hwmeasure : ∀ n, Γ.measure (w n) ≤ Γ.measure u := fun n =>
    Γ.aux_smooth_measure_le hu.1 (hw n) huc hurep (hΦ n) (hΦ₀ n)
      (hderiv n) (hwrepuc n)
  have hwnorm : ∀ n, ‖w n‖ ≤ ‖u‖ := by
    intro n
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hwrep n] with x hx
    simpa only [Real.norm_eq_abs, hx] using hbound n (u x)
  have hwenergy : ∀ n,
      E.toClosedForm.energyNormSq (w n) ≤ E.toClosedForm.energyNormSq u := by
    intro n
    have hmass : (Γ.measure (w n) Set.univ).toReal ≤ (Γ.measure u Set.univ).toReal :=
      ENNReal.toReal_mono (Γ.aux_finite hu.1 Set.univ)
        ((Measure.le_iff').mp (hwmeasure n) Set.univ)
    rw [Γ.measure_univ (w n) (hw n), Γ.measure_univ u hu.1] at hmass
    have hnorm := mul_self_le_mul_self (norm_nonneg (w n)) (hwnorm n)
    unfold _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq
    nlinarith
  have hpoint : ∀ t, Tendsto (fun n => Φ n t) atTop (𝓝 (unitTruncation t)) := by
    intro t
    have habs : Tendsto (fun n => |Φ n t - unitTruncation t|) atTop (𝓝 0) :=
      squeeze_zero (fun n => abs_nonneg _)
        (fun n => aux_smoothClamp_error (aux_delta_pos n) t) aux_delta_tendsto
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by
      simpa only [Real.norm_eq_abs] using habs)
  have hwv := aux_Lp_compositions_tendsto u v w Φ hbound hwrep hvrep hpoint
  refine ⟨hv, Γ.aux_measure_le_of_p_le hv hu.1 ?_⟩
  intro B hB
  exact Γ.aux_p_lsc_of_cesaroCauchy hBS hw hwenergy hwv hB
    (fun n => Γ.aux_p_mono hu.1 (hwmeasure n) B) tendsto_const_nhds

theorem aux_core_energy_approximation {m : Measure X} (E : ClosedForm m)
    (hreg : IsRegular E) {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    ∃ a : ℕ → Lp ℝ 2 m,
      (∀ n, E.MemCore (a n)) ∧
      (∀ n, E.energyNormSq (a n) ≤ 2 * (E.energyNormSq u + 1)) ∧
      Tendsto (fun n => E.energyNormSq (a n - u)) atTop (𝓝 0) := by
  classical
  obtain ⟨U, hU, hmU, C, hC⟩ := hreg
  have hex : ∀ n, ∃ a ∈ C, E.energyNormSq (u - a) < aux_delta n :=
    fun n => hC.denseEnergy u hu (aux_delta n) (aux_delta_pos n)
  choose a haC haerror using hex
  have hacore : ∀ n, E.MemCore (a n) := by
    intro n
    obtain ⟨hadom, f, hfc, hfcomp, hfsup, hfrep⟩ := hC.memCoreOn (a n) (haC n)
    exact ⟨hadom, f, hfc, hfcomp, Set.subset_univ _, hfrep⟩
  have hadom : ∀ n, a n ∈ E.domain := fun n => (hacore n).1
  have haerror' : ∀ n, E.energyNormSq (a n - u) < aux_delta n := by
    intro n
    rw [E.aux_energy_sub_symm (hadom n) hu]
    exact haerror n
  have habound : ∀ n, E.energyNormSq (a n) ≤ 2 * (E.energyNormSq u + 1) := by
    intro n
    have hsmall : E.energyNormSq (a n - u) ≤ 1 :=
      (haerror' n).le.trans (aux_delta_le_one n)
    have hsum := E.aux_energy_add_le (E.domain.sub_mem (hadom n) hu) hu
    rw [sub_add_cancel] at hsum
    linarith
  have halim : Tendsto (fun n => E.energyNormSq (a n - u)) atTop (𝓝 0) :=
    squeeze_zero (fun n => E.aux_energy_nonneg (E.domain.sub_mem (hadom n) hu))
      (fun n => (haerror' n).le) aux_delta_tendsto
  exact ⟨a, hacore, habound, halim⟩

theorem aux_truncation_measure_contraction {m : Measure X}
    (E : _root_.SubdiffusiveProcess.DirichletForm m) (Γ : EnergyMeasure E.toClosedForm)
    (hreg : IsRegular E.toClosedForm) (halg : IsCoreAlgebra E.toClosedForm)
    (hBS : aux_CesaroEnergyCauchy E.toClosedForm)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.toClosedForm.domain)
    (hvrep : ⇑v =ᵐ[m] fun x => unitTruncation (u x)) :
    v ∈ E.toClosedForm.domain ∧ Γ.measure v ≤ Γ.measure u := by
  have hv := (E.markov u hu v hvrep).1
  obtain ⟨a, hacore, habound, halim⟩ :=
    aux_core_energy_approximation E.toClosedForm hreg hu
  have ha : ∀ n, a n ∈ E.toClosedForm.domain := fun n => (hacore n).1
  let b : ℕ → Lp ℝ 2 m := fun n => aux_truncLp (a n)
  have hbrep : ∀ n, ⇑(b n) =ᵐ[m] fun x => unitTruncation (a n x) :=
    fun n => aux_truncLp_rep (a n)
  have hb : ∀ n, b n ∈ E.toClosedForm.domain :=
    fun n => (E.markov (a n) (ha n) (b n) (hbrep n)).1
  have hbenergy : ∀ n,
      E.toClosedForm.energyNormSq (b n) ≤ 2 * (E.toClosedForm.energyNormSq u + 1) := by
    intro n
    have he := (E.markov (a n) (ha n) (b n) (hbrep n)).2
    have hn : ‖b n‖ ≤ ‖a n‖ := aux_truncLp_norm (a n)
    have hsq := mul_self_le_mul_self (norm_nonneg (b n)) hn
    have hba : E.toClosedForm.energyNormSq (b n) ≤
        E.toClosedForm.energyNormSq (a n) := by
      unfold _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq
      nlinarith
    exact hba.trans (habound n)
  have hvEq : v = aux_truncLp u :=
    Lp.ext (hvrep.trans (aux_truncLp_rep u).symm)
  have hblim : Tendsto b atTop (𝓝 v) := by
    rw [hvEq]
    exact aux_truncLp_tendsto (E.toClosedForm.aux_tendsto_Lp_of_energy ha hu halim)
  have hmeasure : ∀ n, Γ.measure (b n) ≤ Γ.measure (a n) := fun n =>
    (aux_core_truncation_measure_contraction E Γ halg hBS (hacore n) (hbrep n)).2
  refine ⟨hv, Γ.aux_measure_le_of_p_le hv hu ?_⟩
  intro B hB
  exact Γ.aux_p_lsc_of_cesaroCauchy hBS hb hbenergy hblim hB
    (fun n => Γ.aux_p_mono (ha n) (hmeasure n) B)
    (Γ.aux_p_tendsto ha hu halim hB)

end SubdiffusiveProcess.DirichletForm

namespace SubdiffusiveProcess.DirichletForm

theorem aux_hilbert_cesaro_subsequence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (w : ℕ → H) {R : ℝ} (hw : ∀ n, ‖w n‖ ≤ R) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ z : H,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, w (σ i))
        atTop (𝓝 z) := by
  classical
  let f : ℕ → WeakDual ℝ H := fun n => InnerProductSpace.toDual ℝ H (w n)
  let K : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) R
  have hK : IsCompact K := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) R
  have hfK : Filter.map f atTop ≤ 𝓟 K := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ n in atTop, f n ∈ K
    exact Eventually.of_forall fun n => by
      show WeakDual.toStrongDual (f n) ∈ Metric.closedBall (0 : StrongDual ℝ H) R
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖InnerProductSpace.toDual ℝ H (w n)‖ ≤ R
      rw [(InnerProductSpace.toDual ℝ H).norm_map]
      exact hw n
  obtain ⟨L, hLK, hcluster⟩ := hK.exists_clusterPt hfK
  let z : H := (InnerProductSpace.toDual ℝ H).symm
    (show H →L[ℝ] ℝ from L)
  have hz : ∀ s : H, inner ℝ z s = L s := by
    intro s
    exact InnerProductSpace.toDual_symm_apply
  have hchoose : ∀ (N : ℕ) (s : H),
      ∃ k : ℕ, N < k ∧ inner ℝ (w k - z) s ≤ 1 := by
    intro N s
    by_contra h
    have hlarge : ∀ k : ℕ, N < k → 1 < inner ℝ (w k - z) s := by
      intro k hk
      exact lt_of_not_ge (fun hle => h ⟨k, hk, hle⟩)
    have hct : Tendsto (fun A : WeakDual ℝ H => A s - L s) (𝓝 L) (𝓝 0) := by
      simpa only [Pi.sub_apply, sub_self] using!
        ((WeakDual.eval_continuous (𝕜 := ℝ) s).sub (continuous_const (y := L s))).tendsto L
    have hnear : ∀ᶠ A : WeakDual ℝ H in 𝓝 L, A s - L s < 1 :=
      hct.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    have hfar : ∀ᶠ A : WeakDual ℝ H in Filter.map f atTop, 1 < A s - L s := by
      change ∀ᶠ n in atTop, 1 < f n s - L s
      filter_upwards [eventually_gt_atTop N] with n hn
      change 1 < inner ℝ (w n) s - L s
      simpa only [inner_sub_left, hz s] using hlarge n hn
    let : (𝓝 L ⊓ Filter.map f atTop).NeBot := hcluster
    have hfalse : ∀ᶠ A : WeakDual ℝ H in 𝓝 L ⊓ Filter.map f atTop, False := by
      filter_upwards [hnear.filter_mono inf_le_left, hfar.filter_mono inf_le_right]
        with A hA₁ hA₂
      exact (not_lt_of_ge hA₁.le) hA₂
    obtain ⟨A, hA⟩ := hfalse.exists
    exact hA
  choose k hk hinner using hchoose
  let p : ℕ → ℕ × H := Nat.rec (0, 0)
    (fun _ p => (k p.1 p.2, p.2 + (w (k p.1 p.2) - z)))
  let σ : ℕ → ℕ := fun n => k (p n).1 (p n).2
  have hfst : ∀ n, (p (n + 1)).1 = σ n := fun n => rfl
  have hσ : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h := hk (p (n + 1)).1 (p (n + 1)).2
    rw [hfst n] at h
    exact h
  have hsum : ∀ n, (p n).2 = ∑ i ∈ Finset.range n, (w (σ i) - z) := by
    intro n
    induction n with
    | zero => simp [p]
    | succ n ih =>
        rw [Finset.sum_range_succ]
        change (p n).2 + (w (σ n) - z) =
          (∑ i ∈ Finset.range n, (w (σ i) - z)) + (w (σ n) - z)
        rw [ih]
  let D : ℝ := (R + ‖z‖) ^ 2
  have hD : ∀ n, ‖w n - z‖ ^ 2 ≤ D := by
    intro n
    have hn : ‖w n - z‖ ≤ R + ‖z‖ :=
      (norm_sub_le (w n) z).trans (add_le_add (hw n) le_rfl)
    have hs := mul_self_le_mul_self (norm_nonneg (w n - z)) hn
    change ‖w n - z‖ ^ 2 ≤ (R + ‖z‖) ^ 2
    nlinarith
  have hadd : ∀ a b : H,
      ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ b a + ‖b‖ ^ 2 := by
    intro a b
    rw [← real_inner_self_eq_norm_sq (a + b)]
    simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm a b]
    ring
  have hpbound : ∀ n, ‖(p n).2‖ ^ 2 ≤ (n : ℝ) * (D + 2) := by
    intro n
    induction n with
    | zero => simp [p]
    | succ n ih =>
        change ‖(p n).2 + (w (σ n) - z)‖ ^ 2 ≤ ((n + 1 : ℕ) : ℝ) * (D + 2)
        rw [hadd, Nat.cast_add, Nat.cast_one]
        have hi := hinner (p n).1 (p n).2
        change inner ℝ (w (σ n) - z) (p n).2 ≤ 1 at hi
        linarith [hD (σ n)]
  let c : ℕ → H := fun n => (n : ℝ)⁻¹ • (p n).2
  have hcbound : ∀ n, ‖c n‖ ^ 2 ≤ (D + 2) * (n : ℝ)⁻¹ := by
    intro n
    by_cases hn : n = 0
    · simp [c, hn]
    · have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      calc
        ‖c n‖ ^ 2 = ((n : ℝ)⁻¹) ^ 2 * ‖(p n).2‖ ^ 2 := by
          simp only [c, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        _ ≤ ((n : ℝ)⁻¹) ^ 2 * ((n : ℝ) * (D + 2)) :=
          mul_le_mul_of_nonneg_left (hpbound n) (sq_nonneg _)
        _ = (D + 2) * (n : ℝ)⁻¹ := by
          field_simp [hnreal]
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcsq : Tendsto (fun n => ‖c n‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) hcbound (by
      simpa only [mul_zero] using hinv.const_mul (D + 2))
  have hcnorm : Tendsto (fun n => ‖c n‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hcsq
  have hc : Tendsto c atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hcnorm)
  have hmean : ∀ n : ℕ, n ≠ 0 →
      (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, w (σ i)) = c n + z := by
    intro n hn
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hconst : (∑ _i ∈ Finset.range n, z) = (n : ℝ) • z := by
      rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ]
    have htotal : (∑ i ∈ Finset.range n, w (σ i)) = (p n).2 + (n : ℝ) • z := by
      rw [hsum n, Finset.sum_sub_distrib, hconst, sub_add_cancel]
    rw [htotal, smul_add, smul_smul, inv_mul_cancel₀ hnreal, one_smul]
    try rfl
  refine ⟨σ, hσ, z, ?_⟩
  have ht : Tendsto (fun n => c n + z) atTop (𝓝 z) := by
    simpa only [zero_add] using hc.add_const z
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (hmean n (Nat.ne_of_gt hn)).symm

def aux_EnergySpace {m : Measure X} (E : ClosedForm m) : Type _ := E.domain

instance aux_energySpaceAddCommGroup {m : Measure X} (E : ClosedForm m) :
    AddCommGroup (aux_EnergySpace E) := inferInstanceAs (AddCommGroup E.domain)

instance aux_energySpaceModule {m : Measure X} (E : ClosedForm m) :
    Module ℝ (aux_EnergySpace E) := inferInstanceAs (Module ℝ E.domain)

def aux_energyVal {m : Measure X} (E : ClosedForm m)
    (u : aux_EnergySpace E) : Lp ℝ 2 m := (show E.domain from u).val

omit [TopologicalSpace X] in
theorem aux_energyVal_mem {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    {m : Measure X} (E : ClosedForm m)
    (u : aux_EnergySpace E) : aux_energyVal E u ∈ E.domain :=
  (show E.domain from u).property

def aux_energyValLinear {m : Measure X} (E : ClosedForm m) :
    aux_EnergySpace E →ₗ[ℝ] Lp ℝ 2 m where
  toFun := aux_energyVal E
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance aux_energySpaceCore {m : Measure X} (E : ClosedForm m) :
    InnerProductSpace.Core ℝ (aux_EnergySpace E) where
  inner u v := E.form (aux_energyVal E u) (aux_energyVal E v) +
    inner ℝ (aux_energyVal E u) (aux_energyVal E v)
  conj_inner_symm u v := by
    change E.form (aux_energyVal E v) (aux_energyVal E u) +
        inner ℝ (aux_energyVal E v) (aux_energyVal E u) =
      E.form (aux_energyVal E u) (aux_energyVal E v) +
        inner ℝ (aux_energyVal E u) (aux_energyVal E v)
    rw [E.form_symm _ (aux_energyVal_mem E v) _ (aux_energyVal_mem E u),
      real_inner_comm (aux_energyVal E v) (aux_energyVal E u)]
  re_inner_nonneg u := by
    change 0 ≤ E.form (aux_energyVal E u) (aux_energyVal E u) +
      inner ℝ (aux_energyVal E u) (aux_energyVal E u)
    rw [real_inner_self_eq_norm_sq]
    exact add_nonneg (E.form_nonneg _ (aux_energyVal_mem E u)) (sq_nonneg _)
  add_left u v w := by
    change E.form (aux_energyVal E u + aux_energyVal E v) (aux_energyVal E w) +
        inner ℝ (aux_energyVal E u + aux_energyVal E v) (aux_energyVal E w) =
      (E.form (aux_energyVal E u) (aux_energyVal E w) +
        inner ℝ (aux_energyVal E u) (aux_energyVal E w)) +
      (E.form (aux_energyVal E v) (aux_energyVal E w) +
        inner ℝ (aux_energyVal E v) (aux_energyVal E w))
    rw [E.form_add_left _ (aux_energyVal_mem E u) _ (aux_energyVal_mem E v)
      _ (aux_energyVal_mem E w), inner_add_left]
    ring
  smul_left u v r := by
    change E.form (r • aux_energyVal E u) (aux_energyVal E v) +
        inner ℝ (r • aux_energyVal E u) (aux_energyVal E v) =
      r * (E.form (aux_energyVal E u) (aux_energyVal E v) +
        inner ℝ (aux_energyVal E u) (aux_energyVal E v))
    rw [E.form_smul_left r _ (aux_energyVal_mem E u) _ (aux_energyVal_mem E v),
      real_inner_smul_left]
    ring
  definite u hu := by
    change E.form (aux_energyVal E u) (aux_energyVal E u) +
      inner ℝ (aux_energyVal E u) (aux_energyVal E u) = 0 at hu
    rw [real_inner_self_eq_norm_sq] at hu
    have hnonneg := E.form_nonneg _ (aux_energyVal_mem E u)
    have hs : ‖aux_energyVal E u‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (sq_nonneg _)
    have hn : ‖aux_energyVal E u‖ = 0 := eq_zero_of_pow_eq_zero hs
    have hv : aux_energyVal E u = 0 := norm_eq_zero.mp hn
    apply Subtype.ext
    exact hv

instance aux_energySpaceNormedAddCommGroup {m : Measure X} (E : ClosedForm m) :
    NormedAddCommGroup (aux_EnergySpace E) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance aux_energySpaceInnerProductSpace {m : Measure X} (E : ClosedForm m) :
    InnerProductSpace ℝ (aux_EnergySpace E) :=
  InnerProductSpace.ofCore (aux_energySpaceCore E).toCore

theorem aux_energySpace_norm_sq {m : Measure X} (E : ClosedForm m)
    (u : aux_EnergySpace E) : ‖u‖ ^ 2 = E.energyNormSq (aux_energyVal E u) := by
  rw [← real_inner_self_eq_norm_sq u]
  change E.form (aux_energyVal E u) (aux_energyVal E u) +
      inner ℝ (aux_energyVal E u) (aux_energyVal E u) =
    E.form (aux_energyVal E u) (aux_energyVal E u) + ‖aux_energyVal E u‖ ^ 2
  rw [real_inner_self_eq_norm_sq]

theorem aux_cauchy_norm_sq {H : Type*} [NormedAddCommGroup H]
    {w : ℕ → H} (hw : CauchySeq w) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      ‖w p - w q‖ ^ 2 < ε := by
  intro ε hε
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hw (Real.sqrt ε) hs
  refine ⟨N, ?_⟩
  intro p hp q hq
  have hd := hN p hp q hq
  rw [dist_eq_norm] at hd
  have hprod : 0 < (Real.sqrt ε - ‖w p - w q‖) *
      (Real.sqrt ε + ‖w p - w q‖) :=
    mul_pos (sub_pos.mpr hd) (add_pos_of_pos_of_nonneg hs (norm_nonneg _))
  nlinarith [Real.sq_sqrt hε.le]

instance aux_energySpaceComplete {m : Measure X} (E : ClosedForm m) :
    CompleteSpace (aux_EnergySpace E) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro a ha
  let w : ℕ → Lp ℝ 2 m := fun n => aux_energyVal E (a n)
  have hw : ∀ n, w n ∈ E.domain := fun n => aux_energyVal_mem E (a n)
  have hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      E.form (w p - w q) (w p - w q) + ‖w p - w q‖ ^ 2 < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := aux_cauchy_norm_sq ha ε hε
    refine ⟨N, ?_⟩
    intro p hp q hq
    have h := hN p hp q hq
    rw [aux_energySpace_norm_sq E] at h
    exact h
  obtain ⟨z, hz, hlim⟩ := E.complete w hw hc
  let Z : aux_EnergySpace E := (show E.domain from ⟨z, hz⟩)
  have hs : Tendsto (fun n => ‖a n - Z‖ ^ 2) atTop (𝓝 0) := by
    convert hlim using 1
    funext n
    exact aux_energySpace_norm_sq E (a n - Z)
  refine ⟨Z, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

theorem aux_cesaroEnergyCauchy {m : Measure X} (E : ClosedForm m) :
    aux_CesaroEnergyCauchy E := by
  intro w C hw hC
  let W : ℕ → aux_EnergySpace E := fun n => (show E.domain from ⟨w n, hw n⟩)
  have hW : ∀ n, ‖W n‖ ≤ Real.sqrt C := by
    intro n
    have hsq : ‖W n‖ ^ 2 ≤ C := by
      rw [aux_energySpace_norm_sq E]
      exact hC n
    have hs := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq_eq_abs, abs_norm] using hs
  obtain ⟨σ, hσ, z, hlim⟩ := aux_hilbert_cesaro_subsequence W hW
  have hval : ∀ n : ℕ, aux_energyValLinear E
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W (σ i)) = aux_cesaro (w ∘ σ) n := by
    intro n
    simp only [map_smul, map_sum, aux_cesaro, Function.comp_apply] ; rfl
  refine ⟨σ, hσ, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := aux_cauchy_norm_sq hlim.cauchySeq ε hε
  refine ⟨N, ?_⟩
  intro p hp q hq
  have h := hN p hp q hq
  rw [aux_energySpace_norm_sq E] at h
  change E.energyNormSq (aux_energyValLinear E
    (((p : ℝ)⁻¹ • ∑ i ∈ Finset.range p, W (σ i)) -
     ((q : ℝ)⁻¹ • ∑ i ∈ Finset.range q, W (σ i)))) < ε at h
  rw [map_sub, hval p, hval q] at h
  exact h

end SubdiffusiveProcess.DirichletForm

namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Fine step of `mfd:lem-borel-weights`, paper label `mfd:lem-borel-weights`.

Inputs:
- `d`, `Q`, `E`, and `Gamma` are the original concrete spatial,
  restricted-volume, Dirichlet-form, and energy-measure carriers.
- The finite energy-measure calculus, including the smooth chain rule,
  is the FOT input exposed by `obl_FOT`.
- The regular core and its full-domain form closure are supplied by
  `prop_regularity`.
- `u`, `hu`, `v`, and `hvrep` are arbitrary full-domain elements and an
  arbitrary L2 representative of the unit truncation; domain membership and
  the measure inequality are conclusions, not hypotheses.
- The smooth-to-nonsmooth approximation and lower-semicontinuity passage
  are the construction isolated by this fine child; no energy-image-density
  premise is added.
- End of carried-input tick list.

Concludes the full-domain nonsmooth energy-measure contraction used by the
Markov step. 
- Supplier: halg is FOT Theorem 1.4.2 core algebra/composition closure, the same separately carried standing input as lem_borel_weights_energy_measure (paper label `mfd:lem-borel-weights`). Smooth approximation and the nonsmooth measure inequality remain conclusions.
-/
theorem lem_borel_weights_markov_energy_measure_contraction
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (hreg : _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm)
    (halg : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra E.toClosedForm) :
    ∀ u ∈ E.toClosedForm.domain,
      ∀ v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))),
        (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => _root_.SubdiffusiveProcess.DirichletForm.unitTruncation (u x))) →
          v ∈ E.toClosedForm.domain ∧ Gamma.measure v ≤ Gamma.measure u := by
  intro u hu v hvrep
  exact _root_.SubdiffusiveProcess.DirichletForm.aux_truncation_measure_contraction E Gamma hreg halg
    (_root_.SubdiffusiveProcess.DirichletForm.aux_cesaroEnergyCauchy E.toClosedForm) hu hvrep

end SubdiffusiveProcess.Paper
