module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusChain
public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusSigned

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal ContDiff

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

theorem sqrt_le_of_energy_bound {p q ε : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hε : 0 ≤ ε) (h : p ≤ ε ^ 2 * q) : Real.sqrt p ≤ ε * Real.sqrt q := by
  have ha := Real.sq_sqrt hp
  have hb := Real.sq_sqrt hq
  have hc := mul_nonneg hε (Real.sqrt_nonneg q)
  nlinarith only [ha, hb, hc, Real.sqrt_nonneg p, h]

theorem sqrt_mul_le_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.sqrt p * Real.sqrt q ≤ p + q := by
  nlinarith only [Real.sq_sqrt hp, Real.sq_sqrt hq, hp, hq,
    sq_nonneg (Real.sqrt p - Real.sqrt q)]

theorem product_error_bound {p q a b ε : ℝ} (hε : 0 ≤ ε)
    (hp : |p - a| ≤ ε) (hq : |q - b| ≤ ε) :
    |p * q - a * b| ≤ ε * (|a| + |b| + ε) := by
  have hqabs : |q| ≤ |b| + ε := by
    calc
      |q| = |b + (q - b)| := by congr 1; ring
      _ ≤ |b| + |q - b| := abs_add_le _ _
      _ ≤ _ := add_le_add (le_refl _) hq
  calc
    |p * q - a * b| = |a * (q - b) + (p - a) * q| := by congr 1; ring
    _ ≤ |a * (q - b)| + |(p - a) * q| := abs_add_le _ _
    _ = |a| * |q - b| + |p - a| * |q| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * ε + ε * (|b| + ε) :=
      add_le_add (mul_le_mul_of_nonneg_left hq (abs_nonneg _))
        (mul_le_mul hp hqabs (abs_nonneg _) hε)
    _ = _ := by ring

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
/-- Simultaneously small affine errors give a small cross-energy error. -/
theorem EnergyFamily.cross_affine_error {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [_t2 : T2Space X] [_lc : LocallyCompactSpace X] [_borel : BorelSpace X] {m : Measure X}
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u v w z : Lp ℝ 2 m}
    (hu : u ∈ F.domain) (hv : v ∈ F.domain) (hw : w ∈ F.domain) (hz : z ∈ F.domain)
    {a b ε : ℝ} (hε : 0 ≤ ε) {B : Set X} (hB : MeasurableSet B)
    (hd : (Γ.measure (w - a • u) B).toReal ≤ ε ^ 2 * (Γ.measure u B).toReal)
    (he : (Γ.measure (z - b • v) B).toReal ≤ ε ^ 2 * (Γ.measure v B).toReal) :
    |Γ.cross w z B - a * b * Γ.cross u v B| ≤
      ε * (|a| + |b| + ε) * ((Γ.measure u B).toReal + (Γ.measure v B).toReal) := by
  let d := w - a • u
  let e := z - b • v
  have hdm := F.domain.sub_mem hw (F.domain.smul_mem a hu)
  have hem := F.domain.sub_mem hz (F.domain.smul_mem b hv)
  have hds : Real.sqrt (Γ.measure d B).toReal ≤ ε * Real.sqrt (Γ.measure u B).toReal :=
    sqrt_le_of_energy_bound ENNReal.toReal_nonneg ENNReal.toReal_nonneg hε hd
  have hes : Real.sqrt (Γ.measure e B).toReal ≤ ε * Real.sqrt (Γ.measure v B).toReal :=
    sqrt_le_of_energy_bound ENNReal.toReal_nonneg ENNReal.toReal_nonneg hε he
  let S := Real.sqrt (Γ.measure u B).toReal * Real.sqrt (Γ.measure v B).toReal
  have h1 : |Γ.cross u e B| ≤ ε * S := by
    apply (Γ.cross_le u hu e hem B hB).trans
    calc
      _ ≤ Real.sqrt (Γ.measure u B).toReal * (ε * Real.sqrt (Γ.measure v B).toReal) :=
        mul_le_mul_of_nonneg_left hes (Real.sqrt_nonneg _)
      _ = _ := by dsimp [S]; ring
  have h2 : |Γ.cross d v B| ≤ ε * S := by
    apply (Γ.cross_le d hdm v hv B hB).trans
    calc
      _ ≤ (ε * Real.sqrt (Γ.measure u B).toReal) * Real.sqrt (Γ.measure v B).toReal :=
        mul_le_mul_of_nonneg_right hds (Real.sqrt_nonneg _)
      _ = _ := by dsimp [S]; ring
  have h3 : |Γ.cross d e B| ≤ ε ^ 2 * S := by
    apply (Γ.cross_le d hdm e hem B hB).trans
    calc
      _ ≤ (ε * Real.sqrt (Γ.measure u B).toReal) * (ε * Real.sqrt (Γ.measure v B).toReal) :=
        mul_le_mul hds hes (Real.sqrt_nonneg _) (mul_nonneg hε (Real.sqrt_nonneg _))
      _ = _ := by dsimp [S]; ring
  have hwdec : w = a • u + d := by dsimp [d]; module
  have hzdec : z = b • v + e := by dsimp [e]; module
  have hexp : Γ.cross w z B - a * b * Γ.cross u v B =
      a * Γ.cross u e B + b * Γ.cross d v B + Γ.cross d e B := by
    rw [hwdec, hzdec, Γ.cross_add_left (F.domain.smul_mem a hu) hdm
      (F.domain.add_mem (F.domain.smul_mem b hv) hem),
      Γ.cross_add_right _ (F.domain.smul_mem a hu) _ (F.domain.smul_mem b hv) _ hem,
      Γ.cross_add_right _ hdm _ (F.domain.smul_mem b hv) _ hem,
      Γ.cross_smul_left a hu (F.domain.smul_mem b hv), Γ.cross_smul_right b u hu v hv,
      Γ.cross_smul_left a hu hem, Γ.cross_smul_right b d hdm v hv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hexp]
  calc
    _ ≤ |a * Γ.cross u e B| + |b * Γ.cross d v B| + |Γ.cross d e B| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |a| * |Γ.cross u e B| + |b| * |Γ.cross d v B| + |Γ.cross d e B| := by
      rw [abs_mul, abs_mul]
    _ ≤ |a| * (ε * S) + |b| * (ε * S) + ε ^ 2 * S :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))) h3
    _ = ε * (|a| + |b| + ε) * S := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sqrt_mul_le_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (mul_nonneg hε (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hε))

/-- The chain rule also controls an affine remainder on an arbitrary measurable set. -/
theorem EnergyFamily.composition_difference_bound {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) {uc : X → ℝ}
    (huc : Continuous uc) (huae : ⇑u =ᵐ[m] uc)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain) (hwae : ⇑w =ᵐ[m] fun x => Φ (uc x))
    (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {B : Set X} (hB : MeasurableSet B)
    (hbound : ∀ x ∈ B, |deriv Φ (uc x) - a| ≤ ε) :
    (Γ.measure (w - a • u) B).toReal ≤ ε ^ 2 * (Γ.measure u B).toReal := by
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu.1⟩
  let Ψ : ℝ → ℝ := fun t => Φ t - a * t
  have hΨ : ContDiff ℝ 1 Ψ := hΦ.sub (contDiff_const.mul contDiff_id)
  have hΨ0 : Ψ 0 = 0 := by simp only [Ψ, hΦ0, mul_zero, sub_self]
  have hΨae : ⇑(w - a • u) =ᵐ[m] fun x => Ψ (uc x) := by
    filter_upwards [Lp.coeFn_sub w (a • u), Lp.coeFn_smul a u, hwae, huae] with x h1 h2 h3 h4
    simp only [h1, h2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h3, h4, Ψ]
  rw [Γ.core_chain_formula h hu huc huae Ψ hΨ hΨ0
    (F.domain.sub_mem hw (F.domain.smul_mem a hu.1)) hΨae hB]
  have hderiv : ∀ t, deriv Ψ t = deriv Φ t - a := by
    intro t
    simpa only [Ψ, mul_one] using! ((hΦ.differentiable one_ne_zero t).hasDerivAt.sub
      ((hasDerivAt_id t).const_mul a)).deriv
  have hbd : ∀ᵐ x ∂(Γ.measure u).restrict B, (deriv Ψ (uc x)) ^ 2 ≤ ε ^ 2 := by
    filter_upwards [ae_restrict_mem hB] with x hx
    rw [hderiv]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε).mpr (hbound x hx)
  have hi := integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
    (integrable_const (μ := (Γ.measure u).restrict B) (ε ^ 2)) hbd
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ,
    smul_eq_mul, mul_comm] using hi

end SubdiffusiveProcess.DirichletForm.FOTConstruction
