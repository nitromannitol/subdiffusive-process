import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusLocal
import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusDomination

open MeasureTheory Filter Set Topology
open scoped NNReal ContDiff

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

/-- The quadratic energy of a scalar multiple. -/
theorem EnergyFamily.toReal_measure_smul {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    (a : ℝ) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure (a • u) B).toReal = a ^ 2 * (Γ.measure u B).toReal := by
  rw [← Γ.cross_self _ (F.domain.smul_mem a hu) B hB,
    Γ.cross_smul_left a hu (F.domain.smul_mem a hu), Γ.cross_smul_right a u hu u hu,
    VectorMeasure.smul_apply, VectorMeasure.smul_apply, smul_eq_mul, smul_eq_mul,
    Γ.cross_self u hu B hB]
  ring

/-- A small local energy error controls the error in the quadratic energy. -/
theorem EnergyFamily.affine_energy_error {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u w : Lp ℝ 2 m} (hu : u ∈ F.domain) (hw : w ∈ F.domain)
    {a ε : ℝ} (hε : 0 ≤ ε) {B : Set X} (hB : MeasurableSet B)
    (hd : (Γ.measure (w - a • u) B).toReal ≤ ε ^ 2 * (Γ.measure u B).toReal) :
    |(Γ.measure w B).toReal - a ^ 2 * (Γ.measure u B).toReal| ≤
      (2 * |a| * ε + ε ^ 2) * (Γ.measure u B).toReal := by
  let d := w - a • u
  have hdmem : d ∈ F.domain := F.domain.sub_mem hw (F.domain.smul_mem a hu)
  have hsqrt : Real.sqrt (Γ.measure d B).toReal ≤ ε * Real.sqrt (Γ.measure u B).toReal := by
    have hleft := Real.sq_sqrt (ENNReal.toReal_nonneg (a := Γ.measure d B))
    have hright := Real.sq_sqrt (ENNReal.toReal_nonneg (a := Γ.measure u B))
    have hrnonneg := mul_nonneg hε (Real.sqrt_nonneg (Γ.measure u B).toReal)
    nlinarith only [hd, hleft, hright, hrnonneg, Real.sqrt_nonneg (Γ.measure d B).toReal]
  have hcross : |Γ.cross u d B| ≤ ε * (Γ.measure u B).toReal := by
    calc
      |Γ.cross u d B| ≤ Real.sqrt (Γ.measure u B).toReal *
          Real.sqrt (Γ.measure d B).toReal := Γ.cross_le u hu d hdmem B hB
      _ ≤ Real.sqrt (Γ.measure u B).toReal *
          (ε * Real.sqrt (Γ.measure u B).toReal) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
      _ = ε * (Γ.measure u B).toReal := by
        rw [show Real.sqrt (Γ.measure u B).toReal *
          (ε * Real.sqrt (Γ.measure u B).toReal) =
            ε * (Real.sqrt (Γ.measure u B).toReal) ^ 2 by ring,
          Real.sq_sqrt ENNReal.toReal_nonneg]
  have hdecomp : w = a • u + d := by dsimp [d]; module
  have hexp : (Γ.measure w B).toReal = a ^ 2 * (Γ.measure u B).toReal +
      2 * a * Γ.cross u d B + (Γ.measure d B).toReal := by
    rw [hdecomp, ← Γ.cross_self _ (F.domain.add_mem (F.domain.smul_mem a hu) hdmem) B hB,
      Γ.cross_add_self_apply (F.domain.smul_mem a hu) hdmem B,
      Γ.cross_self _ (F.domain.smul_mem a hu) B hB,
      Γ.toReal_measure_smul hu a hB, Γ.cross_smul_left a hu hdmem,
      VectorMeasure.smul_apply, smul_eq_mul, Γ.cross_self d hdmem B hB]
    ring
  rw [hexp, show a ^ 2 * (Γ.measure u B).toReal + 2 * a * Γ.cross u d B +
      (Γ.measure d B).toReal - a ^ 2 * (Γ.measure u B).toReal =
        2 * a * Γ.cross u d B + (Γ.measure d B).toReal by ring]
  calc
    _ ≤ |2 * a * Γ.cross u d B| + |(Γ.measure d B).toReal| := abs_add_le _ _
    _ = 2 * |a| * |Γ.cross u d B| + (Γ.measure d B).toReal := by
      rw [abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      norm_num
    _ ≤ 2 * |a| * (ε * (Γ.measure u B).toReal) +
        ε ^ 2 * (Γ.measure u B).toReal :=
      add_le_add (mul_le_mul_of_nonneg_left hcross (by positivity)) hd
    _ = _ := by ring

/-- A prescribed domain composition is still in the relative continuous core. -/
theorem core_composition {F : _root_.DirichletForm m} {U : Set X}
    {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    {uc : X → ℝ} (huae : ⇑u =ᵐ[m] uc) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (hΦ0 : Φ 0 = 0) {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (uc x)) : F.toClosedForm.MemCoreOn U w := by
  obtain ⟨f, hf, hfc, hfU, hfae⟩ := hu.2
  refine ⟨hw, Φ ∘ f, hΦ.comp hf, hfc.comp_left hΦ0,
    (tsupport_comp_subset hΦ0 f).trans hfU, ?_⟩
  exact hwae.trans ((huae.symm.trans hfae).fun_comp Φ)

/-- A `C¹` function has a globally Lipschitz, zero-preserving affine remainder locally. -/
theorem exists_small_lipschitz_remainder {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (T : ℝ → ℝ) (b : ℝ), 0 < r ∧ LipschitzWith ⟨ε, hε.le⟩ T ∧
      T 0 = 0 ∧ ∀ t : ℝ, |t - c| < r →
        T t = Φ t - deriv Φ c * t - b ∧ |deriv Φ t - deriv Φ c| ≤ ε := by
  obtain ⟨δ, hδ, hderiv⟩ := Metric.continuousAt_iff.mp
    (hΦ.continuous_deriv le_rfl).continuousAt ε hε
  let r := δ / 2
  have hr : 0 < r := half_pos hδ
  let a := deriv Φ c
  let P : ℝ → ℝ := fun t => Φ t - a * t
  let cl : ℝ → ℝ := fun t => max (c - r) (min t (c + r))
  have hclmem : ∀ t, cl t ∈ Icc (c - r) (c + r) := fun t =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hcl : LipschitzWith 1 cl := by
    simpa [cl] using
      (LipschitzWith.const (c - r)).max (LipschitzWith.id.min (LipschitzWith.const (c + r)))
  have hd : ∀ t ∈ Icc (c - r) (c + r), |deriv Φ t - a| ≤ ε := by
    intro t ht
    have habs : |t - c| ≤ r := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hlt : dist t c < δ := by rw [Real.dist_eq]; exact habs.trans_lt (by dsimp [r]; linarith)
    simpa only [Real.dist_eq, a] using (hderiv hlt).le
  have hPdiff : Differentiable ℝ P := (hΦ.differentiable le_rfl).sub
    ((differentiable_const a).mul differentiable_id)
  have hPderiv : ∀ t, deriv P t = deriv Φ t - a := by
    intro t
    have h := ((hΦ.differentiable le_rfl t).hasDerivAt.sub
      ((hasDerivAt_id t).const_mul a)).deriv
    simpa only [mul_one] using h
  have hbound : ∀ t ∈ Icc (c - r) (c + r), ‖deriv P t‖ ≤ ε := by
    intro t ht
    rw [hPderiv, Real.norm_eq_abs]
    exact hd t ht
  let T : ℝ → ℝ := fun t => P (cl t) - P (cl 0)
  have hT : LipschitzWith ⟨ε, hε.le⟩ T := by
    refine LipschitzWith.of_dist_le_mul fun t s => ?_
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
      (fun x _ => hPdiff x) hbound (convex_Icc (c - r) (c + r)) (hclmem s) (hclmem t)
    have hc := hcl.dist_le_mul t s
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
    change |T t - T s| ≤ ε * |t - s|
    rw [show T t - T s = P (cl t) - P (cl s) by dsimp [T]; ring]
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    exact hmv.trans (mul_le_mul_of_nonneg_left hc hε.le)
  refine ⟨r, T, P (cl 0), hr, hT, sub_self _, ?_⟩
  intro t ht
  have htc : t ∈ Icc (c - r) (c + r) := by
    have hh := abs_lt.mp ht
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hcleq : cl t = t := by
    dsimp only [cl]
    rw [min_eq_left htc.2, max_eq_right htc.1]
  constructor
  · change P (cl t) - P (cl 0) = _
    simp only [hcleq, P, a]
  · exact hd t htc

/-- Subtraction preserves the relative continuous core. -/
theorem core_sub {F : _root_.DirichletForm m} {U : Set X} {u v : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) (hv : F.toClosedForm.MemCoreOn U v) :
    F.toClosedForm.MemCoreOn U (u - v) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hu.add (hv.smul (-1))

/-- On a sufficiently small neighborhood, composition is affine up to arbitrarily small energy. -/
theorem EnergyFamily.local_affine_chain_bound {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) {uc : X → ℝ}
    (huc : Continuous uc) (huae : ⇑u =ᵐ[m] uc)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain) (hwae : ⇑w =ᵐ[m] fun x => Φ (uc x))
    (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧
      (∀ y ∈ O, |deriv Φ (uc y) - deriv Φ (uc x)| ≤ ε) ∧
      ∀ B : Set X, MeasurableSet B → B ⊆ O →
        |(Γ.measure w B).toReal - (deriv Φ (uc x)) ^ 2 * (Γ.measure u B).toReal| ≤
          (2 * |deriv Φ (uc x)| * ε + ε ^ 2) * (Γ.measure u B).toReal := by
  obtain ⟨r, T, b, hr, hT, hT0, happrox⟩ := exists_small_lipschitz_remainder hΦ (uc x) hε
  let O : Set X := {y | |uc y - uc x| < r}
  let a := deriv Φ (uc x)
  let τ := hT.compLp hT0 u
  let d := w - a • u
  let z := d - τ
  have hwcore := core_composition hu huae hΦ.continuous hΦ0 hw hwae
  have hτcore := memCoreOn_compLp F hu hT hT0
  have hdcore := core_sub hwcore (hu.smul a)
  have hzcore := core_sub hdcore hτcore
  have hτae : ⇑τ =ᵐ[m] fun y => T (u y) := hT.coeFn_compLp hT0 u
  have hzae : ⇑z =ᵐ[m] fun y => Φ (uc y) - a * uc y - T (uc y) := by
    filter_upwards [Lp.coeFn_sub d τ, Lp.coeFn_sub w (a • u), Lp.coeFn_smul a u,
      hwae, huae, hτae] with y h1 h2 h3 h4 h5 h6
    simp only [z, d, h1, h2, h3, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h4, h5, h6]
  have hO : IsOpen O := isOpen_lt ((huc.sub continuous_const).abs) continuous_const
  have hxO : x ∈ O := by simpa only [O, mem_setOf_eq, sub_self, abs_zero] using hr
  have hzc : Continuous (fun y => Φ (uc y) - a * uc y - T (uc y)) :=
    ((hΦ.continuous.comp huc).sub (continuous_const.mul huc)).sub (hT.continuous.comp huc)
  have hzO : Γ.measure z O = 0 := Γ.measure_eq_zero_of_core_constant h hzcore hzc hzae hO
    (c := b) (fun y hy => by
      have heq := (happrox (uc y) hy).1
      dsimp only [a]
      linarith only [heq])
  refine ⟨O, hO, hxO, fun y hy => (happrox (uc y) hy).2, ?_⟩
  intro B hB hBO
  have hzB : Γ.measure z B = 0 := (measure_mono hBO).trans_eq hzO |>.antisymm bot_le
  have heq := Γ.toReal_measure_eq_of_difference_zero hdcore.1 hτcore.1 hB hzB
  have hτle := Γ.core_lipschitz_measure_le h hu hτcore hT hT0 hτae
  have hboundENN := Measure.le_iff'.mp hτle B
  have hbound : (Γ.measure τ B).toReal ≤ ε ^ 2 * (Γ.measure u B).toReal := by
    rw [Measure.smul_apply, smul_eq_mul] at hboundENN
    have hb := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Γ.measure_ne_top hu.1 B)) hboundENN
    simpa only [NNReal.coe_mk, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg ε)] using hb
  apply Γ.affine_energy_error hu.1 hw hε.le hB
  change (Γ.measure d B).toReal ≤ _
  rw [heq]
  exact hbound

end DirichletForm.FOTConstruction
