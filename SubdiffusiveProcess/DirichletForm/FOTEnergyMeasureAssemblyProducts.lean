import SubdiffusiveProcess.DirichletForm.FOTDomainHilbert
import SubdiffusiveProcess.DirichletForm.FOTCoreCalculus
import Mathlib.Topology.Order.Bornology

open MeasureTheory Filter Set Topology

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- Products with a common uniform bound are continuous in the ambient L² norm. -/
theorem assembly_product_tendsto (F : _root_.DirichletForm m)
    {un vn : ℕ → Lp ℝ 2 m} {u v p : Lp ℝ 2 m}
    (hun : ∀ n, un n ∈ F.domain) (hvn : ∀ n, vn n ∈ F.domain)
    (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (R : ℝ) (hunR : ∀ n, ∀ᵐ x ∂m, |un n x| ≤ R)
    (hvnR : ∀ n, ∀ᵐ x ∂m, |vn n x| ≤ R)
    (huR : ∀ᵐ x ∂m, |u x| ≤ R) (hvR : ∀ᵐ x ∂m, |v x| ≤ R)
    (hprod : ⇑p =ᵐ[m] fun x => u x * v x)
    (pn : ℕ → Lp ℝ 2 m) (hpn : ∀ n, ⇑(pn n) =ᵐ[m] fun x => un n x * vn n x)
    (hulim : Tendsto un atTop (𝓝 u)) (hvlim : Tendsto vn atTop (𝓝 v)) :
    Tendsto pn atTop (𝓝 p) := by
  choose mid hmid hmidae using fun n => exists_mul_mem F hu (hvn n) huR (hvnR n)
  have hbound : ∀ n, ‖pn n - p‖ ≤ R * (‖un n - u‖ + ‖vn n - v‖) := by
    intro n
    have h1 : ‖pn n - mid n‖ ≤ R * ‖un n - u‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (pn n) (mid n), Lp.coeFn_sub (un n) u,
        hpn n, hmidae n, hvnR n] with x hx hy hz ht hb
      simp only [hx, hy, Pi.sub_apply, hz, ht, Real.norm_eq_abs]
      rw [← sub_mul, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    have h2 : ‖mid n - p‖ ≤ R * ‖vn n - v‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (mid n) p, Lp.coeFn_sub (vn n) v,
        hmidae n, hprod, huR] with x hx hy hz ht hb
      simp only [hx, hy, Pi.sub_apply, hz, ht, Real.norm_eq_abs]
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    exact (norm_sub_le_norm_sub_add_norm_sub (pn n) (mid n) p).trans (by linarith)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  have hlim := ((tendsto_iff_norm_sub_tendsto_zero.mp hulim).add
    (tendsto_iff_norm_sub_tendsto_zero.mp hvlim)).const_mul R
  simpa only [zero_add, mul_zero] using hlim

/-- A converging energy sequence has a bound valid at every index. -/
theorem assembly_energy_bound (F : _root_.DirichletForm m)
    {un : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hun : ∀ n, un n ∈ F.domain) (hu : u ∈ F.domain)
    (hlim : Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ n, F.form (un n) (un n) ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _
    (F.toClosedForm.tendsto_form_self_of_tendsto_energyNormSq hun hu hlim)).bddAbove
  exact ⟨C, fun n => hC (mem_range_self n)⟩

/-- Pairing a strongly converging factor with an L²-converging bounded-energy
factor preserves the value of the form. -/
theorem assembly_form_tendsto (F : _root_.DirichletForm m)
    {un pn : ℕ → Lp ℝ 2 m} {u p : Lp ℝ 2 m}
    (hun : ∀ n, un n ∈ F.domain) (hpn : ∀ n, pn n ∈ F.domain)
    (hu : u ∈ F.domain) (hp : p ∈ F.domain)
    (henergy : Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0))
    (C : ℝ) (hC : ∀ n, F.form (pn n) (pn n) ≤ C)
    (hlim : Tendsto pn atTop (𝓝 p)) :
    Tendsto (fun n => F.form (un n) (pn n)) atTop (𝓝 (F.form u p)) := by
  have hnorm : Tendsto (fun n => ‖pn n - p‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hlim
  have hweak := EnergyHilbert.weak_null_form_tendsto_zero F.toClosedForm
    (fun n => pn n - p) (fun n => F.domain.sub_mem (hpn n) hp)
    (2 * C + 2 * F.form p p)
    (fun n => (F.toClosedForm.form_sub_self_le (hpn n) hp).trans (by linarith [hC n]))
    hnorm u hu
  have herr : Tendsto (fun n => F.form (un n - u) (pn n)) atTop (𝓝 0) := by
    have hbound : ∀ n, ‖F.form (un n - u) (pn n)‖ ≤
        Real.sqrt (F.energyNormSq (un n - u)) * Real.sqrt C := by
      intro n
      apply (F.toClosedForm.abs_form_le (F.domain.sub_mem (hun n) hu) (hpn n)).trans
      exact mul_le_mul
        (Real.sqrt_le_sqrt (F.toClosedForm.form_le_energyNormSq))
        (Real.sqrt_le_sqrt (hC n)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply squeeze_zero_norm hbound
    simpa only [Real.sqrt_zero, zero_mul] using
      ((Real.continuous_sqrt.tendsto 0).comp henergy).mul_const (Real.sqrt C)
  have hsum := herr.add hweak
  apply tendsto_sub_nhds_zero_iff.1
  convert hsum using 1
  · ext n
    rw [F.toClosedForm.form_sub_left (hun n) hu (hpn n),
      F.toClosedForm.form_sub_right hu (hpn n) hp]
    ring
  · simp only [zero_add]

end DirichletForm.FOTConstruction
