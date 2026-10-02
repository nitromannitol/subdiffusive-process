import SubdiffusiveProcess.DirichletForm.FOTConstructionData
import Mathlib.Analysis.InnerProductSpace.Adjoint

open MeasureTheory Filter Set Topology
open scoped RealInnerProductSpace

noncomputable section
namespace DirichletForm.FOTConstruction.EnergyHilbert

variable {X : Type*} [MeasurableSpace X] {m : Measure X} (E : ClosedForm m)

def EnergySpace : Type _ := E.domain

instance energyAddCommGroup : AddCommGroup (EnergySpace E) :=
  inferInstanceAs (AddCommGroup E.domain)

instance energyModule : Module ℝ (EnergySpace E) :=
  inferInstanceAs (Module ℝ E.domain)

def energyCore : InnerProductSpace.Core ℝ (EnergySpace E) where
  inner x y := E.form x.1 y.1 + inner ℝ x.1 y.1
  conj_inner_symm x y := by
    change E.form y.1 x.1 + inner ℝ y.1 x.1 =
      E.form x.1 y.1 + inner ℝ x.1 y.1
    rw [E.form_symm y.1 y.2 x.1 x.2, real_inner_comm]
  re_inner_nonneg x := by
    change 0 ≤ E.form x.1 x.1 + inner ℝ x.1 x.1
    rw [real_inner_self_eq_norm_sq]
    exact add_nonneg (E.form_nonneg x.1 x.2) (sq_nonneg _)
  add_left x y z := by
    change E.form (x.1 + y.1) z.1 + inner ℝ (x.1 + y.1) z.1 =
      (E.form x.1 z.1 + inner ℝ x.1 z.1) +
        (E.form y.1 z.1 + inner ℝ y.1 z.1)
    rw [E.form_add_left x.1 x.2 y.1 y.2 z.1 z.2, inner_add_left]
    ring
  smul_left x y c := by
    change E.form (c • x.1) y.1 + inner ℝ (c • x.1) y.1 =
      c * (E.form x.1 y.1 + inner ℝ x.1 y.1)
    rw [E.form_smul_left c x.1 x.2 y.1 y.2, real_inner_smul_left, mul_add]
  definite x hx := by
    change E.form x.1 x.1 + inner ℝ x.1 x.1 = 0 at hx
    rw [real_inner_self_eq_norm_sq] at hx
    have hsq : ‖x.1‖ ^ 2 = 0 := by
      apply le_antisymm
      · linarith [E.form_nonneg x.1 x.2]
      · exact sq_nonneg _
    have hxnorm : ‖x.1‖ = 0 :=
      mul_self_eq_zero.mp (by simpa only [pow_two] using hsq)
    apply Subtype.ext
    change x.1 = 0
    exact norm_eq_zero.mp hxnorm

instance energyNormedAddCommGroup : NormedAddCommGroup (EnergySpace E) :=
  @InnerProductSpace.Core.toNormedAddCommGroup
    ℝ (EnergySpace E) _ _ _ (energyCore E)

instance energyInnerProductSpace : InnerProductSpace ℝ (EnergySpace E) :=
  InnerProductSpace.ofCore (energyCore E).toCore

theorem energy_inner (x y : EnergySpace E) :
    inner ℝ x y = E.form x.1 y.1 + inner ℝ x.1 y.1 := rfl

theorem energy_norm_sq (x : EnergySpace E) :
    ‖x‖ ^ 2 = E.form x.1 x.1 + ‖x.1‖ ^ 2 := by
  calc
    ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
    _ = E.form x.1 x.1 + ‖x.1‖ ^ 2 := by
      rw [energy_inner, real_inner_self_eq_norm_sq]

theorem energy_norm (x : EnergySpace E) :
    ‖x‖ = Real.sqrt (E.form x.1 x.1 + ‖x.1‖ ^ 2) := by
  rw [← energy_norm_sq E x, Real.sqrt_sq (norm_nonneg x)]

theorem ambient_norm_le_energy_norm (x : EnergySpace E) :
    ‖x.1‖ ≤ ‖x‖ := by
  calc
    ‖x.1‖ = Real.sqrt (‖x.1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x.1)).symm
    _ ≤ Real.sqrt (E.form x.1 x.1 + ‖x.1‖ ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_left (E.form_nonneg x.1 x.2))
    _ = ‖x‖ := (energy_norm E x).symm

theorem square_strict_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a ^ 2 < b ^ 2 := by
  have hprod : 0 < (b - a) * (b + a) :=
    mul_pos (sub_pos.mpr hab) (by linarith)
  nlinarith

instance energyCompleteSpace : CompleteSpace (EnergySpace E) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro z hz
  have hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      E.form ((z p).1 - (z q).1) ((z p).1 - (z q).1) +
        ‖(z p).1 - (z q).1‖ ^ 2 < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hz)
      (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    refine ⟨N, ?_⟩
    intro p hp q hq
    have hn : ‖z p - z q‖ < Real.sqrt ε := by
      simpa only [dist_eq_norm] using hN p hp q hq
    have hs := square_strict_mono_nonneg (norm_nonneg (z p - z q)) hn
    rw [Real.sq_sqrt hε.le] at hs
    calc
      E.form ((z p).1 - (z q).1) ((z p).1 - (z q).1) +
          ‖(z p).1 - (z q).1‖ ^ 2 = ‖z p - z q‖ ^ 2 :=
        (energy_norm_sq E (z p - z q)).symm
      _ < ε := hs
  obtain ⟨v, hv, hlim⟩ := E.complete
    (fun n => (z n).1) (fun n => (z n).2) hc
  let z₀ : EnergySpace E := ⟨v, hv⟩
  refine ⟨z₀, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hsq : Tendsto (fun n => ‖z n - z₀‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [energy_norm_sq] using hlim
  have hsqrt : Tendsto (fun n => Real.sqrt (‖z n - z₀‖ ^ 2))
      atTop (𝓝 (Real.sqrt (0 : ℝ))) :=
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

def energyInclusion : EnergySpace E →L[ℝ] Lp ℝ 2 m :=
  ({ toFun := fun x => x.1
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : EnergySpace E →ₗ[ℝ] Lp ℝ 2 m).mkContinuous
    1 (by
      intro x
      simpa only [one_mul] using ambient_norm_le_energy_norm E x)

theorem energyInclusion_apply (x : EnergySpace E) :
    energyInclusion E x = x.1 := rfl

theorem energyInclusion_injective : Function.Injective (energyInclusion E) := by
  intro x y h
  apply Subtype.ext
  exact h

theorem dense_adjoint_range_of_injective
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (i : H →L[ℝ] K) (hi : Function.Injective i) :
    Dense (Set.range (ContinuousLinearMap.adjoint i)) := by
  let S : Submodule ℝ H := LinearMap.range (ContinuousLinearMap.adjoint i).toLinearMap
  have hperp : S.orthogonal = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hzero : inner ℝ ((ContinuousLinearMap.adjoint i) (i x)) x = 0 :=
        hx _ ⟨i x, rfl⟩
      have hself : inner ℝ (i x) (i x) = 0 := by
        simpa only [ContinuousLinearMap.adjoint_inner_left] using hzero
      have hix : i x = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hself
      rw [Submodule.mem_bot]
      apply hi
      simpa only [map_zero] using hix
    · exact bot_le
  have hclosure : S.topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr hperp
  change Dense (S : Set H)
  rw [dense_iff_closure_eq]
  change (S.topologicalClosure : Set H) = Set.univ
  exact congrArg (fun T : Submodule ℝ H => (T : Set H)) hclosure

theorem inner_tendsto_zero_of_injective
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (i : H →L[ℝ] K) (hi : Function.Injective i)
    (v : ℕ → H) (B : ℝ) (hB : 0 < B)
    (hbounded : ∀ᶠ n in atTop, ‖v n‖ ≤ B)
    (hsmall : Tendsto (fun n => ‖i (v n)‖) atTop (𝓝 0)) (u : H) :
    Tendsto (fun n => inner ℝ u (v n)) atTop (𝓝 0) := by
  have hd := dense_adjoint_range_of_injective i hi
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  obtain ⟨f, hf⟩ := (Metric.mem_closure_range_iff.mp (hd u))
    ((ε / 2) / B) (div_pos (half_pos hε) hB)
  have happrox : ‖u - (ContinuousLinearMap.adjoint i) f‖ * B < ε / 2 := by
    apply (lt_div_iff₀ hB).mp
    simpa only [dist_eq_norm] using hf
  have hadjoint : Tendsto
      (fun n => inner ℝ ((ContinuousLinearMap.adjoint i) f) (v n))
      atTop (𝓝 0) := by
    have hambient : Tendsto (fun n => inner ℝ f (i (v n))) atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun n => norm_inner_le_norm (𝕜 := ℝ) f (i (v n)))
      simpa only [mul_zero] using hsmall.const_mul ‖f‖
    simpa only [ContinuousLinearMap.adjoint_inner_left] using hambient
  have heventually : ∀ᶠ n in atTop,
      ‖inner ℝ ((ContinuousLinearMap.adjoint i) f) (v n)‖ < ε / 2 := by
    simpa only [dist_zero_right] using
      (Metric.tendsto_nhds.mp hadjoint) (ε / 2) (half_pos hε)
  filter_upwards [hbounded, heventually] with n hn hfn
  have herror : ‖inner ℝ (u - (ContinuousLinearMap.adjoint i) f) (v n)‖ < ε / 2 := by
    calc
      ‖inner ℝ (u - (ContinuousLinearMap.adjoint i) f) (v n)‖
          ≤ ‖u - (ContinuousLinearMap.adjoint i) f‖ * ‖v n‖ :=
        norm_inner_le_norm (𝕜 := ℝ) _ _
      _ ≤ ‖u - (ContinuousLinearMap.adjoint i) f‖ * B :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ < ε / 2 := happrox
  have hsplit : inner ℝ u (v n) =
      inner ℝ (u - (ContinuousLinearMap.adjoint i) f) (v n) +
        inner ℝ ((ContinuousLinearMap.adjoint i) f) (v n) := by
    rw [inner_sub_left, sub_add_cancel]
  rw [dist_zero_right, hsplit]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem weak_null_form_tendsto_zero
    (w : ℕ → Lp ℝ 2 m) (hw : ∀ n, w n ∈ E.domain) (C : ℝ)
    (hbdd : ∀ n, E.form (w n) (w n) ≤ C)
    (hnorm : Tendsto (fun n => ‖w n‖) atTop (𝓝 0))
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain) :
    Tendsto (fun n => E.form u (w n)) atTop (𝓝 0) := by
  let v : ℕ → EnergySpace E := fun n => ⟨w n, hw n⟩
  let uH : EnergySpace E := ⟨u, hu⟩
  have hC : 0 ≤ C := (E.form_nonneg (w 0) (hw 0)).trans (hbdd 0)
  let B : ℝ := Real.sqrt (C + 1)
  have hB : 0 < B := Real.sqrt_pos.mpr (by linarith)
  have hunit : ∀ᶠ n in atTop, ‖w n‖ < 1 :=
    hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hbounded : ∀ᶠ n in atTop, ‖v n‖ ≤ B := by
    filter_upwards [hunit] with n hn
    rw [energy_norm]
    apply Real.sqrt_le_sqrt
    change E.form (w n) (w n) + ‖w n‖ ^ 2 ≤ C + 1
    have hs : ‖w n‖ ^ 2 < (1 : ℝ) ^ 2 :=
      square_strict_mono_nonneg (norm_nonneg (w n)) hn
    nlinarith [hbdd n]
  have hsmall : Tendsto (fun n => ‖energyInclusion E (v n)‖)
      atTop (𝓝 0) := by
    simpa only [energyInclusion_apply] using hnorm
  have hH : Tendsto (fun n => inner ℝ uH (v n)) atTop (𝓝 0) :=
    inner_tendsto_zero_of_injective (energyInclusion E)
      (energyInclusion_injective E) v B hB hbounded hsmall uH
  have hL2 : Tendsto (fun n => inner ℝ u (w n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => norm_inner_le_norm (𝕜 := ℝ) u (w n))
    simpa only [mul_zero] using hnorm.const_mul ‖u‖
  have hdiff := hH.sub hL2
  change Tendsto
    (fun n => (E.form u (w n) + inner ℝ u (w n)) - inner ℝ u (w n))
    atTop (𝓝 ((0 : ℝ) - 0)) at hdiff
  simpa only [add_sub_cancel_right, sub_self] using hdiff


end DirichletForm.FOTConstruction.EnergyHilbert
