/-
# The extended energy functional, the order on forms, and Mosco convergence
-/
module

public import SubdiffusiveProcess.DirichletForm.Basic

@[expose] public section

/-!
# Extended energy, order of forms, Mosco convergence

For a closed form `E` we extend `u ↦ E(u, u)` to all of `L²(X, m)` by `⊤`
outside the domain (`SubdiffusiveProcess.DirichletForm.ClosedForm.energy`).  This makes the domain
readable off the functional and lets the order of forms and Mosco convergence be
stated without side conditions.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm.energy`: `E(u) ∈ EReal`, equal to `⊤` off `D(E)`.
* the `Preorder` on `ClosedForm m` given by `E ≤ F ↔ ∀ u, E(u) ≤ F(u)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.LEWithConst`: `E ≤ C · F` on `D(F)`.
* `SubdiffusiveProcess.DirichletForm.TendstoWeakly`: weak convergence in `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.MoscoConverges`: Mosco convergence (weak liminf bound and
  existence of a strong recovery sequence).

## References

* U. Mosco, *Composite media and asymptotic Dirichlet forms*, J. Funct. Anal.
  123 (1994).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

namespace SubdiffusiveProcess.DirichletForm

namespace ClosedForm

open scoped Classical in
/-- The energy functional extended to all of `L²(X, m)` by `⊤` off the domain. -/
noncomputable def energy (E : ClosedForm m) (u : Lp ℝ 2 m) : EReal :=
  if u ∈ E.domain then (E.form u u : EReal) else ⊤

variable (E F : ClosedForm m)

@[simp] theorem energy_of_mem {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    E.energy u = (E.form u u : EReal) := by
  simp [energy, hu]

@[simp] theorem energy_of_notMem {u : Lp ℝ 2 m} (hu : u ∉ E.domain) : E.energy u = ⊤ := by
  simp [energy, hu]

theorem energy_lt_top_iff (u : Lp ℝ 2 m) : E.energy u < ⊤ ↔ u ∈ E.domain := by
  by_cases hu : u ∈ E.domain
  · simp [hu, EReal.coe_lt_top]
  · simp [hu]

theorem mem_domain_of_energy_lt_top {u : Lp ℝ 2 m} (hu : E.energy u < ⊤) : u ∈ E.domain :=
  (E.energy_lt_top_iff u).mp hu

theorem energy_nonneg (u : Lp ℝ 2 m) : 0 ≤ E.energy u := by
  by_cases hu : u ∈ E.domain
  · simpa [hu] using (EReal.coe_nonneg).mpr (E.form_nonneg u hu)
  · simp [hu]

@[simp] theorem energy_zero : E.energy 0 = 0 := by
  simp [E.form_zero_left E.domain.zero_mem]

/-- `E ≤ C · F` on the domain of `F`: `D(F) ⊆ D(E)` and `E(u) ≤ C F(u)` there. -/
def LEWithConst (E F : ClosedForm m) (C : ℝ) : Prop :=
  ∀ u ∈ F.domain, u ∈ E.domain ∧ E.form u u ≤ C * F.form u u

theorem LEWithConst.mem_domain {E F : ClosedForm m} {C : ℝ} (h : LEWithConst E F C)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) : u ∈ E.domain := (h u hu).1

theorem LEWithConst.form_le {E F : ClosedForm m} {C : ℝ} (h : LEWithConst E F C)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) : E.form u u ≤ C * F.form u u := (h u hu).2

theorem LEWithConst.trans {E F G : ClosedForm m} {C D : ℝ} (hC : 0 ≤ C)
    (h₁ : LEWithConst E F C) (h₂ : LEWithConst F G D) : LEWithConst E G (C * D) := by
  intro u hu
  refine ⟨h₁.mem_domain (h₂.mem_domain hu), ?_⟩
  calc E.form u u ≤ C * F.form u u := h₁.form_le (h₂.mem_domain hu)
    _ ≤ C * (D * G.form u u) := mul_le_mul_of_nonneg_left (h₂.form_le hu) hC
    _ = C * D * G.form u u := by ring

theorem LEWithConst.rfl (E : ClosedForm m) : LEWithConst E E 1 :=
  fun u hu => ⟨hu, by simp⟩

/-- The form is continuous for the energy norm in its first argument: if
`E₁(uₙ - w) → 0` then `E(uₙ, v) → E(w, v)`.  This is the continuity used at
`eq:mfd-21` to extend an identity from a core to `D(E)`. -/
theorem tendsto_form_of_tendsto_energyNormSq {E : ClosedForm m} {u : ℕ → Lp ℝ 2 m}
    {w v : Lp ℝ 2 m} (hu : ∀ n : ℕ, u n ∈ E.domain) (hw : w ∈ E.domain)
    (hv : v ∈ E.domain)
    (h : Tendsto (fun n => E.energyNormSq (u n - w)) atTop (𝓝 0)) :
    Tendsto (fun n => E.form (u n) v) atTop (𝓝 (E.form w v)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : ∀ n : ℕ, dist (E.form (u n) v) (E.form w v) ≤
      Real.sqrt (E.energyNormSq (u n - w)) * Real.sqrt (E.form v v) := by
    intro n
    rw [Real.dist_eq, ← E.form_sub_left (hu n) hw hv]
    refine (E.abs_form_le (E.domain.sub_mem (hu n) hw) hv).trans ?_
    have := E.form_le_energyNormSq (u := u n - w)
    have hnn := E.form_nonneg _ (E.domain.sub_mem (hu n) hw)
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt this) (Real.sqrt_nonneg _)
  refine squeeze_zero (fun n => dist_nonneg) hb ?_
  have hs : Tendsto (fun n : ℕ => Real.sqrt (E.energyNormSq (u n - w))) atTop (𝓝 0) := by
    simpa using! (Real.continuous_sqrt.tendsto 0).comp h
  simpa using hs.mul_const (Real.sqrt (E.form v v))

/-- **`L²` bound from a pointwise bound by a constant times an indicator.**
If `‖f‖ ≤ C` on a set `S` of finite measure and `f = 0` off `S`, then
`‖f‖_{L²} ≤ C · m(S)^{1/2}`.

This is the estimate behind `|w_ε - v_q| ≤ ε` at
`mfd:lem-truncation`: the difference is bounded by `ε` and supported in
the closed cube, whose measure is finite, so it tends to `0` in `L²`. -/
theorem norm_le_of_ae_indicator_bound {f : Lp ℝ 2 m} {S : Set X} (hS : MeasurableSet S)
    (hSfin : m S ≠ ⊤) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂m, ‖f x‖ ≤ S.indicator (fun _ => C) x) :
    ‖f‖ ≤ C * Real.sqrt ((m S).toReal) := by
  have hmono : eLpNorm (⇑f) 2 m ≤ eLpNorm (S.indicator fun _ => C) 2 m := by
    refine eLpNorm_mono_ae (Lp.aestronglyMeasurable f) ?_
    filter_upwards [hbound] with x hx
    refine hx.trans ?_
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hind := eLpNorm_indicator_const (μ := m) (c := C) hS.nullMeasurableSet
    (p := 2) (by norm_num) (by norm_num)
  have hfin : eLpNorm (S.indicator fun _ => C) 2 m ≠ ⊤ := by
    rw [hind]
    refine ENNReal.mul_ne_top (by simp) ?_
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSfin
  rw [Lp.norm_def]
  refine (ENNReal.toReal_mono hfin hmono).trans ?_
  rw [hind, ENNReal.toReal_mul]
  have h1 : (m S ^ (1 / (2 : ℝ≥0∞).toReal)).toReal = Real.sqrt ((m S).toReal) := by
    rw [← ENNReal.toReal_rpow, Real.sqrt_eq_rpow]
    norm_num
  rw [h1]
  have h2 : ((‖C‖ₑ : ℝ≥0∞)).toReal = C := by
    simp [enorm_eq_nnnorm, Real.norm_eq_abs, abs_of_nonneg hC]
  rw [h2]

/-- Energy-norm convergence gives convergence of the energies themselves.

`E(uₙ) = E₁(uₙ) - ‖uₙ‖²`, and each term converges: the energy norms by the
triangle inequality `|√E₁(uₙ) - √E₁(w)| ≤ √E₁(uₙ - w)`, the `L²` norms because
`‖·‖² ≤ E₁`.  This is the step `E^Q(v_q) = lim Γ_E(v)(q ∩ {|v| > ε})` of
`mfd:lem-truncation`. -/
theorem tendsto_form_self_of_tendsto_energyNormSq (E : ClosedForm m)
    {u : ℕ → Lp ℝ 2 m} {w : Lp ℝ 2 m} (hu : ∀ n : ℕ, u n ∈ E.domain)
    (hw : w ∈ E.domain)
    (h : Tendsto (fun n => E.energyNormSq (u n - w)) atTop (𝓝 0)) :
    Tendsto (fun n => E.form (u n) (u n)) atTop (𝓝 (E.form w w)) := by
  have hsub : ∀ n : ℕ, u n - w ∈ E.domain := fun n => E.domain.sub_mem (hu n) hw
  -- the `L²` norms converge
  have hnsq : Tendsto (fun n => ‖u n - w‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => E.sq_norm_le_energyNormSq (hsub n)) h
  have hn : Tendsto (fun n => ‖u n - w‖) atTop (𝓝 0) := by
    have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by simpa using Real.continuous_sqrt.tendsto 0
    refine (hc.comp hnsq).congr fun n => ?_
    simp [Real.sqrt_sq (norm_nonneg _)]
  have hnorm : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 (‖w‖ ^ 2)) := by
    have : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖w‖) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hn
      simpa [Real.dist_eq] using abs_norm_sub_norm_le (u n) w
    exact this.pow 2
  -- the energy norms converge
  have hsqrt : Tendsto (fun n => Real.sqrt (E.energyNormSq (u n))) atTop
      (𝓝 (Real.sqrt (E.energyNormSq w))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hc : Tendsto (fun n => Real.sqrt (E.energyNormSq (u n - w))) atTop (𝓝 0) := by
      have hc0 : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
        simpa using Real.continuous_sqrt.tendsto 0
      simpa using! hc0.comp h
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hc
    have h1 : Real.sqrt (E.energyNormSq (u n)) ≤
        Real.sqrt (E.energyNormSq w) + Real.sqrt (E.energyNormSq (u n - w)) := by
      have := E.sqrt_energyNormSq_add_le hw (hsub n)
      simpa using this
    have h2 : Real.sqrt (E.energyNormSq w) ≤
        Real.sqrt (E.energyNormSq (u n)) + Real.sqrt (E.energyNormSq (w - u n)) := by
      have := E.sqrt_energyNormSq_add_le (hu n) (E.domain.sub_mem hw (hu n))
      simpa using this
    have h3 : E.energyNormSq (w - u n) = E.energyNormSq (u n - w) :=
      E.energyNormSq_sub_comm hw (hu n)
    rw [h3] at h2
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hE1 : Tendsto (fun n => E.energyNormSq (u n)) atTop (𝓝 (E.energyNormSq w)) := by
    have hp := hsqrt.pow 2
    rw [Real.sq_sqrt (E.energyNormSq_nonneg hw)] at hp
    exact hp.congr fun n => Real.sq_sqrt (E.energyNormSq_nonneg (hu n))
  have hfin := hE1.sub hnorm
  simp only [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq] at hfin
  simpa using hfin

/-- **Closedness in the form the truncation argument uses.**  A sequence in the
domain that is Cauchy for the form and converges in `L²` has its limit in the
domain, and converges to it in the energy norm.

This is the step at `mfd:lem-truncation` ("by closedness,
`v_q ∈ D(E^Q)` and `w_ε → v_q` in form norm"): the `L²` convergence upgrades the
form-Cauchy property to an energy-norm Cauchy property, `ClosedForm.complete`
produces a limit, and uniqueness of `L²` limits identifies it. -/
theorem mem_domain_of_tendsto_of_formCauchy (E : ClosedForm m) (w : ℕ → Lp ℝ 2 m)
    (hw : ∀ n : ℕ, w n ∈ E.domain) (z : Lp ℝ 2 m) (hL2 : Tendsto w atTop (𝓝 z))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
      E.form (w p - w r) (w p - w r) < ε) :
    z ∈ E.domain ∧ Tendsto (fun n => E.energyNormSq (w n - z)) atTop (𝓝 0) := by
  have hL2cauchy : CauchySeq w := hL2.cauchySeq
  have hE1 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
      E.form (w p - w r) (w p - w r) + ‖w p - w r‖ ^ 2 < ε := by
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hcauchy (ε / 2) (by positivity)
    obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.mp hL2cauchy (Real.sqrt (ε / 2))
      (Real.sqrt_pos.mpr (by positivity))
    refine ⟨max N₁ N₂, fun p hp r hr => ?_⟩
    have h1 := hN₁ p (le_of_max_le_left hp) r (le_of_max_le_left hr)
    have h2 := hN₂ p (le_of_max_le_right hp) r (le_of_max_le_right hr)
    rw [dist_eq_norm] at h2
    have h3 : ‖w p - w r‖ ^ 2 < ε / 2 := by
      have hnn : (0 : ℝ) ≤ ‖w p - w r‖ := norm_nonneg _
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ ε / 2), h2, hnn,
        Real.sqrt_nonneg (ε / 2)]
    linarith
  obtain ⟨z', hz'mem, hz'⟩ := E.complete w hw hE1
  have hnormsq : Tendsto (fun n => ‖w n - z'‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hz'
    have := E.form_nonneg _ (E.domain.sub_mem (hw n) hz'mem)
    linarith
  have hnorm : Tendsto (fun n => ‖w n - z'‖) atTop (𝓝 0) := by
    have hcont : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0)
    have := hcont.comp hnormsq
    refine this.congr fun n => ?_
    simp [Real.sqrt_sq (norm_nonneg _)]
  have hzz' : z = z' := tendsto_nhds_unique hL2 (by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mpr hnorm))
  rw [hzz']
  exact ⟨hz'mem, hz'⟩

end ClosedForm

/-- Weak convergence in `L²(X, m)`. -/
def TendstoWeakly (u : ℕ → Lp ℝ 2 m) (w : Lp ℝ 2 m) : Prop :=
  ∀ f : Lp ℝ 2 m, Tendsto (fun n => (inner ℝ f (u n) : ℝ)) atTop (𝓝 (inner ℝ f w))

theorem TendstoWeakly.of_tendsto {u : ℕ → Lp ℝ 2 m} {w : Lp ℝ 2 m}
    (h : Tendsto u atTop (𝓝 w)) : TendstoWeakly u w := by
  intro f
  exact ((innerSL ℝ f).continuous.tendsto w).comp h

/-- **Mosco convergence** of a sequence of closed forms `F n` to `E`:
the weak liminf inequality and the existence of a strong recovery sequence.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroMoscoConverges`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure MoscoConverges (F : ℕ → ClosedForm m) (E : ClosedForm m) : Prop where
  /-- Mosco (i): if `u n ⇀ w` weakly in `L²` then `E(w) ≤ liminf F n (u n)`. -/
  liminf_le : ∀ (u : ℕ → Lp ℝ 2 m) (w : Lp ℝ 2 m), TendstoWeakly u w →
    E.energy w ≤ liminf (fun n => (F n).energy (u n)) atTop
  /-- Mosco (ii): every `w` admits a strongly convergent recovery sequence. -/
  exists_recovery : ∀ w : Lp ℝ 2 m, ∃ u : ℕ → Lp ℝ 2 m,
    Tendsto u atTop (𝓝 w) ∧ limsup (fun n => (F n).energy (u n)) atTop ≤ E.energy w

/-- A recovery sequence has energies converging to the limit energy. -/
theorem MoscoConverges.tendsto_energy_of_recovery {F : ℕ → ClosedForm m} {E : ClosedForm m}
    (h : MoscoConverges F E) {u : ℕ → Lp ℝ 2 m} {w : Lp ℝ 2 m}
    (hconv : Tendsto u atTop (𝓝 w))
    (hlim : limsup (fun n => (F n).energy (u n)) atTop ≤ E.energy w) :
    Tendsto (fun n => (F n).energy (u n)) atTop (𝓝 (E.energy w)) := by
  have hle : E.energy w ≤ liminf (fun n => (F n).energy (u n)) atTop :=
    h.liminf_le u w (_root_.SubdiffusiveProcess.DirichletForm.TendstoWeakly.of_tendsto hconv)
  have hlb : liminf (fun n => (F n).energy (u n)) atTop ≤
      limsup (fun n => (F n).energy (u n)) atTop := liminf_le_limsup
  have h1 : liminf (fun n => (F n).energy (u n)) atTop = E.energy w := le_antisymm
    (hlim.trans' hlb) hle
  have h2 : limsup (fun n => (F n).energy (u n)) atTop = E.energy w :=
    le_antisymm hlim (h1 ▸ hlb)
  exact tendsto_of_liminf_eq_limsup h1 h2

end SubdiffusiveProcess.DirichletForm
