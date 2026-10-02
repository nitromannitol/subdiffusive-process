import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.DirichletForm.FOTProduct

/-! # Local energy lower semicontinuity

This module constructs a closed form by adding a nonnegative local energy penalty
and uses it to pass uniform local energy-measure bounds to bounded-energy `L²`
limits. It does not assert convergence of the energy measures.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace DirichletForm.EnergyMeasure

/-- Add a nonnegative multiple of the energy measure on a measurable set to a closed form. -/
def withLocalEnergy
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} (E : DirichletForm.ClosedForm m)
    (Gamma : DirichletForm.EnergyMeasure E)
    (t : ℝ) (ht : 0 ≤ t) (B : Set X) (hB : MeasurableSet B) :
    DirichletForm.ClosedForm m := by
  refine {
    domain := E.domain
    form := fun u v => E.form u v + t * Gamma.cross u v B
    denseDomain := E.denseDomain
    form_symm := ?_
    form_add_left := ?_
    form_smul_left := ?_
    form_nonneg := ?_
    complete := ?_ }
  · intro u hu v hv
    rw [E.form_symm u hu v hv, Gamma.cross_symm u hu v hv]
  · intro u hu v hv w hw
    rw [E.form_add_left u hu v hv w hw, Gamma.cross_add_left hu hv hw,
      VectorMeasure.add_apply, mul_add]
    ring
  · intro c u hu v hv
    rw [E.form_smul_left c u hu v hv, Gamma.cross_smul_left c hu hv,
      VectorMeasure.smul_apply]
    simp only [smul_eq_mul]
    ring
  · intro u hu
    have hE := E.form_nonneg u hu
    have hGamma := Gamma.cross_self_nonneg hu hB
    exact add_nonneg hE (mul_nonneg ht hGamma)
  · intro u hu hCauchy
    have hECauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
        E.form (u p - u q) (u p - u q) + ‖u p - u q‖ ^ 2 < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hCauchy ε hε
      refine ⟨N, ?_⟩
      intro p hp q hq
      have hdiff : u p - u q ∈ E.domain := E.domain.sub_mem (hu p) (hu q)
      have hGamma := Gamma.cross_self_nonneg hdiff hB
      have hpenalty := mul_nonneg ht hGamma
      have hsmall := hN p hp q hq
      change (E.form (u p - u q) (u p - u q) +
        t * Gamma.cross (u p - u q) (u p - u q) B) +
        ‖u p - u q‖ ^ 2 < ε at hsmall
      linarith only [hpenalty, hsmall]
    obtain ⟨w, hw, hlim⟩ := E.complete u hu hECauchy
    refine ⟨w, hw, ?_⟩
    have hnonneg : ∀ n : ℕ, 0 ≤
        (E.form (u n - w) (u n - w) +
          t * Gamma.cross (u n - w) (u n - w) B) + ‖u n - w‖ ^ 2 := by
      intro n
      have hdiff : u n - w ∈ E.domain := E.domain.sub_mem (hu n) hw
      have hGamma := Gamma.cross_self_nonneg hdiff hB
      have hE := E.form_nonneg (u n - w) hdiff
      exact add_nonneg (add_nonneg hE (mul_nonneg ht hGamma)) (sq_nonneg _)
    have hbound : ∀ n : ℕ,
        (E.form (u n - w) (u n - w) +
          t * Gamma.cross (u n - w) (u n - w) B) + ‖u n - w‖ ^ 2 ≤
        (1 + t) * (E.form (u n - w) (u n - w) + ‖u n - w‖ ^ 2) := by
      intro n
      have hdiff : u n - w ∈ E.domain := E.domain.sub_mem (hu n) hw
      have hcross : Gamma.cross (u n - w) (u n - w) B ≤
          E.form (u n - w) (u n - w) := by
        rw [Gamma.cross_self (u n - w) hdiff B hB]
        exact Gamma.toReal_measure_le_form hdiff B
      have hform : E.form (u n - w) (u n - w) +
          t * Gamma.cross (u n - w) (u n - w) B ≤
          (1 + t) * E.form (u n - w) (u n - w) := by
        calc
          _ = t * Gamma.cross (u n - w) (u n - w) B +
              E.form (u n - w) (u n - w) := by ring
          _ ≤ t * E.form (u n - w) (u n - w) +
              E.form (u n - w) (u n - w) :=
                add_le_add_left (mul_le_mul_of_nonneg_left hcross ht) _
          _ = E.form (u n - w) (u n - w) +
              t * E.form (u n - w) (u n - w) := by ring
          _ = _ := by ring
      have hfactor : 1 ≤ 1 + t := by linarith only [ht]
      have hnorm : 0 ≤ ‖u n - w‖ ^ 2 := sq_nonneg _
      calc
        _ ≤ (1 + t) * E.form (u n - w) (u n - w) + ‖u n - w‖ ^ 2 :=
          add_le_add_left hform _
        _ = ‖u n - w‖ ^ 2 +
            (1 + t) * E.form (u n - w) (u n - w) := by ring
        _ ≤ (1 + t) * ‖u n - w‖ ^ 2 +
            (1 + t) * E.form (u n - w) (u n - w) := by
          simpa only [one_mul] using
            (add_le_add_left
              (mul_le_mul_of_nonneg_right hfactor hnorm)
              ((1 + t) * E.form (u n - w) (u n - w)))
        _ = _ := by ring
    have hscaled : Tendsto
        (fun n : ℕ => (1 + t) *
          (E.form (u n - w) (u n - w) + ‖u n - w‖ ^ 2)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlim.const_mul (1 + t)
    exact squeeze_zero hnonneg (fun n => hbound n) hscaled

/-- The local-energy perturbation lies above the original form. -/
theorem form_le_withLocalEnergy
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} (E : DirichletForm.ClosedForm m)
    (Gamma : DirichletForm.EnergyMeasure E)
    (t : ℝ) (ht : 0 ≤ t) (B : Set X) (hB : MeasurableSet B)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    E.form u u ≤ (withLocalEnergy E Gamma t ht B hB).form u u := by
  change E.form u u ≤ E.form u u + t * Gamma.cross u u B
  exact le_add_of_nonneg_right (mul_nonneg ht (Gamma.cross_self_nonneg hu hB))

/-- The local-energy perturbation is bounded by the total energy factor `1 + t`. -/
theorem withLocalEnergy_le_form
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} (E : DirichletForm.ClosedForm m)
    (Gamma : DirichletForm.EnergyMeasure E)
    (t : ℝ) (ht : 0 ≤ t) (B : Set X) (hB : MeasurableSet B)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    (withLocalEnergy E Gamma t ht B hB).form u u ≤ (1 + t) * E.form u u := by
  change E.form u u + t * Gamma.cross u u B ≤ (1 + t) * E.form u u
  have hcross : Gamma.cross u u B ≤ E.form u u := by
    rw [Gamma.cross_self u hu B hB]
    exact Gamma.toReal_measure_le_form hu B
  calc
    _ = t * Gamma.cross u u B + E.form u u := by ring
    _ ≤ t * E.form u u + E.form u u :=
      add_le_add_left (mul_le_mul_of_nonneg_left hcross ht) _
    _ = E.form u u + t * E.form u u := by ring
    _ = _ := by ring

/-- A bounded-energy L2 limit preserves every uniform local energy-measure bound. -/
theorem local_bound_of_tendsto_of_form_le
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} (E : DirichletForm.ClosedForm m)
    (Gamma : DirichletForm.EnergyMeasure E)
    (un : ℕ → Lp ℝ 2 m) (hu : ∀ n, un n ∈ E.domain)
    (u : Lp ℝ 2 m) (hlim : Tendsto un atTop (𝓝 u))
    (E0 K : ℝ) (hE0 : ∀ n, E.form (un n) (un n) ≤ E0)
    (B : Set X) (hB : MeasurableSet B)
    (hK : ∀ n, (Gamma.measure (un n) B).toReal ≤ K) :
    u ∈ E.domain ∧ (Gamma.measure u B).toReal ≤ K := by
  have hdomain := E.mem_domain_of_tendsto_of_form_le hu hlim hE0
  refine ⟨hdomain.1, ?_⟩
  have hE0nonneg : 0 ≤ E0 := le_trans (E.form_nonneg (un 0) (hu 0)) (hE0 0)
  apply le_of_forall_pos_le_add
  intro ε hε
  let t : ℝ := E0 / ε + 1
  have ht : 0 ≤ t := by
    dsimp [t]
    exact add_nonneg (div_nonneg hE0nonneg hε.le) zero_le_one
  have hEt : E0 ≤ t * ε := by
    dsimp [t]
    have hmul := (div_mul_cancel₀ E0 hε.ne')
    linarith only [hmul, hε]
  let F := withLocalEnergy E Gamma t ht B hB
  have hFbound : ∀ n, F.form (un n) (un n) ≤ E0 + t * K := by
    intro n
    have hcross : Gamma.cross (un n) (un n) B = (Gamma.measure (un n) B).toReal :=
      Gamma.cross_self (un n) (hu n) B hB
    change E.form (un n) (un n) + t * Gamma.cross (un n) (un n) B ≤ E0 + t * K
    rw [hcross]
    exact add_le_add (hE0 n) (mul_le_mul_of_nonneg_left (hK n) ht)
  have hFclosed := F.mem_domain_of_tendsto_of_form_le hu hlim hFbound
  have hFenergy : F.form u u ≤ E0 + t * K := hFclosed.2
  have htpos : 0 < t := by
    dsimp [t]
    have hdiv : 0 ≤ E0 / ε := div_nonneg hE0nonneg hε.le
    linarith only [hdiv]
  have hlocal : (Gamma.measure u B).toReal ≤ K + ε := by
    have hcross : Gamma.cross u u B = (Gamma.measure u B).toReal :=
      Gamma.cross_self u hdomain.1 B hB
    have hcompare : E.form u u + t * (Gamma.measure u B).toReal ≤ E0 + t * K := by
      change E.form u u + t * Gamma.cross u u B ≤ E0 + t * K at hFenergy
      rw [hcross] at hFenergy
      exact hFenergy
    have hEunonneg := E.form_nonneg u hdomain.1
    have htmul : t * (Gamma.measure u B).toReal ≤ E0 + t * K := by
      linarith only [hcompare, hEunonneg]
    have hratio : (Gamma.measure u B).toReal ≤ (E0 + t * K) / t :=
      (le_div_iff₀ htpos).2 (by simpa only [mul_comm] using htmul)
    have hEt' : E0 / t ≤ ε := (div_le_iff₀ htpos).2 (by simpa only [mul_comm] using hEt)
    have hratio' : (E0 + t * K) / t = E0 / t + K := by
      rw [add_div, mul_div_cancel_left₀ K htpos.ne']
    rw [hratio'] at hratio
    calc
      (Gamma.measure u B).toReal ≤ E0 / t + K := hratio
      _ ≤ ε + K := add_le_add_left hEt' K
      _ = K + ε := by ring
  exact hlocal





end DirichletForm.EnergyMeasure
