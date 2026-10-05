module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicClockLower
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicInterior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicScaledContrast
public import SubdiffusiveProcess.Frozen.Section8.LocalResolventExitUpper
public import SubdiffusiveProcess.Frozen.Section8.LocalResolventIteration
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.MaxPrinciple
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothSolution

@[expose] public section

/-!
# Sub-unit estimates for the divergence-form diffusion and Sobolev normalization

Coefficient and energy estimates for sub-unit cubes, with a scaling
counterexample to the unnormalized Sobolev inequality.

## The normalization layer

The printed proof begins by dividing `a` by `a(z_U)` and rescaling `U` to the unit cube.
`coefficient_sandwich_of_logCoefficientControlOn` is the first half of that step, read off
`abs_log_sub_le_of_logCoefficientControlOn`: on the concentric double of a cube
carrying `LogCoefficientControlOn a H U`, the coefficient normalized at the centre satisfies

    exp (-(√d √H)) * a z_U ≤ a x ≤ exp (√d √H) * a z_U,

which is the printed `e^{−C√H} ≤ b̃ ≤ e^{C√H}` with `C = √d`, and it holds for **every**
cube side, not only below one — the gradient clause alone carries it, since the control is
already scaled by `ℓ²`.  `energy_le_of_logCoefficientControlOn` is the consequence every
rescaled display uses: the Dirichlet energy of a test function with a gradient bound is at
most `exp (√d √H) · a z_U · K · ℓ^d`.

## Why the Sobolev estimate needs the volume factor

`not_subunitSobolevDisplay` refutes the unnormalized inequality

    lpSq 1 U p0 f ≤ ofReal (C e^{CH} F_U) * ofReal (energy a U f)

for every constant `C`.  The printed display is

    (⨏_U |f|^{p0})^{2/p0} ≤ C e^{CH} F_U ⨏_U a |∇f|²,

with **averages on both sides**; `lpSq` and `energy` are the unnormalized
`‖f‖²_{L^{p0}(U)}` and `∫_U a|∇f|²`, so the printed display is

    lpSq ≤ C e^{CH} F_U · |U|^{2/p0 − 1} · energy,

Omitting the factor `|U|^{2/p0−1}`.  Below scale one that factor exceeds
one (`|U| = ℓ^d < 1` and `2/p0 − 1 < 0`), so the inequality without that factor is **strictly stronger** than
the averaged one, and it is false: the scaled cutoff of
`Section9Support.exists_cutoff_h10Function` has
`lpSq ≍ ℓ^{2d/p0}` and `F_U · energy ≍ ℓ^d`, and `ℓ^{2d/p0}/ℓ^d → ∞` as `ℓ → 0`.

The corresponding large-cube estimate permits the unnormalized inequality because `size U = 3^n ≥ 1`, so `|U|^{2/p0−1} ≤ 1` and the
unnormalized form is the weaker one.  The `ℓ < 1` hypothesis that defines the sub-unit lemma
is exactly what makes the unnormalized inequality false.

The witness is the constant coefficient, for which
`logCoefficientControlOn_const` discharges the control hypothesis at `H = 1` on every cube;
only `LocalDiffusionData` is left, as in
`Section9Support.WeightedSubunitLowerRefutation`.

## The normalized estimate

`(volume (cubeSet U)).toReal ^ (-(1 - 2 / p0))` on the right, which is how
`Section9SupportInput.SobolevAssumption` and the `sobolev` field of
`Section9SupportInput.LocalTorsionEstimates` both
write it.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
open SubdiffusiveProcess.CoarseGrainingVocab (HolderSeminormBoundOn)
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11

variable {d : ℕ}

/-! ## The normalization step of the printed proof -/

theorem centre_mem_cubeSet' {U : Cube d} (hU : 0 < U.2) : U.1 ∈ cubeSet U := by
  intro i _
  simp only [Set.mem_Ioo]
  constructor <;> linarith

/-- **The coefficient normalized at the centre of the cube.**  The control at `H` sandwiches
`a` between `e^{∓√d√H} a(z_U)` on the cube; This is the printed `e^{-C√H} ≤ b̃ ≤ e^{C√H}`
with `C = √d`, and it holds at every side length, the control being already scaled by `ℓ²`. -/
theorem coefficient_sandwich_of_logCoefficientControlOn {a : Vec d → ℝ} {H : ℝ}
    {U : Cube d} (hU : 0 < U.2) (hctrl : LogCoefficientControlOn a H U)
    {x : Vec d} (hx : x ∈ cubeSet U) :
    Real.exp (-(Real.sqrt d * Real.sqrt H)) * a U.1 ≤ a x ∧
      a x ≤ Real.exp (Real.sqrt d * Real.sqrt H) * a U.1 := by
  have hsub := cubeSet_subset_double (d := d) (B := U) hU.le
  have hcentre : U.1 ∈ cubeSet U := centre_mem_cubeSet' hU
  have hposx : 0 < a x := hctrl.1 x (hsub hx)
  have hposc : 0 < a U.1 := hctrl.1 U.1 (hsub hcentre)
  have hlog := abs_log_sub_le_of_logCoefficientControlOn hU hctrl (hsub hcentre) (hsub hx)
  have hnorm : ‖x - U.1‖ ≤ U.2 := norm_sub_le_side (B := U) hU.le hx hcentre
  have hbound : |Real.log (a x) - Real.log (a U.1)| ≤ Real.sqrt d * Real.sqrt H := by
    refine hlog.trans ?_
    have hcoef : 0 ≤ Real.sqrt d * (Real.sqrt H / U.2) := by positivity
    calc Real.sqrt d * (Real.sqrt H / U.2) * ‖x - U.1‖
        ≤ Real.sqrt d * (Real.sqrt H / U.2) * U.2 :=
          mul_le_mul_of_nonneg_left hnorm hcoef
      _ = Real.sqrt d * Real.sqrt H := by field_simp
  have habs := abs_le.mp hbound
  constructor
  · have h1 : Real.log (a U.1) - Real.sqrt d * Real.sqrt H ≤ Real.log (a x) := by
      linarith [habs.1]
    have hx2 := Real.exp_le_exp.mpr h1
    rw [Real.exp_sub, Real.exp_log hposc, Real.exp_log hposx] at hx2
    rw [Real.exp_neg, inv_mul_eq_div]
    exact hx2
  · have h2 : Real.log (a x) ≤ Real.log (a U.1) + Real.sqrt d * Real.sqrt H := by
      linarith [habs.2]
    have hx2 := Real.exp_le_exp.mpr h2
    rw [Real.exp_log hposx, Real.exp_add, Real.exp_log hposc, mul_comm] at hx2
    exact hx2

/-- **The rescaled Dirichlet energy.**  With the coefficient normalized at the centre, the
energy of a test function with a pointwise gradient bound is at most
`e^{√d√H} a(z_U) K ℓ^d`. -/
theorem energy_le_of_logCoefficientControlOn {a : Vec d → ℝ} {H K : ℝ}
    {U : Cube d} (hU : 0 < U.2) (hctrl : LogCoefficientControlOn a H U)
    (hameas : AEStronglyMeasurable a (volume.restrict (cubeSet U)))
    (f : H10Function (cubeSet U))
    (hgrad : ∀ x, vecDot (f.toH1Function.grad x) (f.toH1Function.grad x) ≤ K) :
    energy a (cubeSet U) f.toH1Function
      ≤ Real.exp (Real.sqrt d * Real.sqrt H) * a U.1 * K * U.2 ^ d := by
  have hsub := cubeSet_subset_double (d := d) (B := U) hU.le
  exact energy_le_of_bounds (a := a) (Q := U) (K := K)
    (hi := Real.exp (Real.sqrt d * Real.sqrt H) * a U.1) hU
    (fun x hx => (coefficient_sandwich_of_logCoefficientControlOn hU hctrl hx).2)
    (fun x hx => hctrl.1 x (hsub hx)) hameas f hgrad

/-! ## The constant coefficient satisfies the control -/

/-- For a constant coefficient the logarithm has vanishing Euclidean gradient. -/
theorem euclideanGradient_log_const' (k : ℝ) (x : Vec d) :
    euclideanGradient (fun _ : Vec d => Real.log k) x = 0 := by
  funext i
  simp [euclideanGradient, euclideanCoordDeriv]

/-- The constant coefficient `k > 0` satisfies `LogCoefficientControlOn` at `H = 1` on every
cube, with `G = K = 0`. -/
theorem logCoefficientControlOn_const {k : ℝ} (hk : 0 < k) (U : Cube d) :
    LogCoefficientControlOn (fun _ : Vec d => k) 1 U := by
  refine ⟨fun _ _ => hk, 0, 0, le_rfl, le_rfl, ?_, ?_, ?_, by simp⟩
  · intro x _
    simp
  · intro x _
    simp [euclideanGradient_log_const']
  · intro x _ y _
    simp [euclideanGradient_log_const']

theorem weightedMeasure_one : weightedMeasure (fun _ : Vec d => (1 : ℝ)) = volume := by
  have h : (fun _ : Vec d => ENNReal.ofReal (1 : ℝ)) = 1 := by
    funext x; simp
  rw [weightedMeasure, h, withDensity_one]

/-! ## The Sobolev display of the frozen anchor, isolated -/

/-- The Sobolev clause of **version 1** of
`SubdiffusiveProcess.Frozen.Section11.divergence_subunit_estimates`, with the model coefficient
`aCutoff M 0 omega` replaced by a general coefficient carrying the same control.  The v1
clause was this `Prop` at `a := aCutoff M 0 omega`, verbatim; v2 carries the volume
normalization and is not an instance of it. -/
def SubunitSobolevDisplay (d : ℕ) (a : Vec d → ℝ) (p0 C : ℝ) : Prop :=
  ∀ (U : Cube d) (H : ℝ), 0 < U.2 → U.2 < 1 → 1 ≤ H →
    LogCoefficientControlOn a H U →
    ∀ FU : ℝ, FU = U.2 ^ 2 / a U.1 → 0 < FU →
      ∀ f : H10Function (cubeSet U),
        lpSq (fun _ => (1 : ℝ)) (cubeSet U) p0 f.toH1Function.toFun ≤
          ENNReal.ofReal (C * Real.exp (C * H) * FU) *
            ENNReal.ofReal (energy a (cubeSet U) f.toH1Function)

/-- The scaling inequality the display forces on every cube below scale one. -/
theorem subunitSobolev_scaling [NeZero d] {p0 C : ℝ} (hp0 : 2 < p0) (hC : 0 ≤ C)
    (hdisp : SubunitSobolevDisplay d (fun _ => (1 : ℝ)) p0 C)
    {ell : ℝ} (hell : 0 < ell) (hell1 : ell < 1) :
    ((volume (smallContrastUnitBall d)).toReal / 8 ^ d) ^ (2 / p0) * (ell ^ d) ^ (2 / p0)
      ≤ C * Real.exp (C * 1) * cutoffGradSq d * ell ^ d := by
  have hcg : 0 ≤ cutoffGradSq d := cutoffGradSq_nonneg d
  set kap : ℝ := (volume (smallContrastUnitBall d)).toReal with hkap
  have hkappos : 0 < kap := volume_smallContrastUnitBall_toReal_pos d
  set U : Cube d := ((0 : Vec d), ell) with hUdef
  have hU2 : (0 : ℝ) < U.2 := hell
  obtain ⟨f, hone, _hnn, hgrad⟩ := exists_cutoff_h10Function (Q := U) hU2
  have hctrl : LogCoefficientControlOn (fun _ : Vec d => (1 : ℝ)) 1 U :=
    logCoefficientControlOn_const one_pos U
  have hdd := hdisp U 1 hU2 hell1 le_rfl hctrl (ell ^ 2)
    (by simp [hUdef]) (by positivity) f
  have hballsub : euclideanBall U.1 (U.2 / 8) ⊆ cubeSet U :=
    euclideanBall_subset_cubeSet (by positivity) (by linarith)
  have hballmeas : MeasurableSet (euclideanBall U.1 (U.2 / 8)) :=
    (Homogenization.isOpen_euclideanBall _ _).measurableSet
  have hlow := weightedMeasure_rpow_le_lpSq (a := fun _ : Vec d => (1 : ℝ)) (Q := U)
    (p0 := p0) (by linarith) hballmeas hballsub f hone
  rw [weightedMeasure_one] at hlow
  have hen : energy (fun _ : Vec d => (1 : ℝ)) (cubeSet U) f.toH1Function
      ≤ 1 * (cutoffGradSq d / U.2 ^ 2) * U.2 ^ d :=
    energy_le_of_bounds hU2 (fun _ _ => le_rfl) (fun _ _ => one_pos)
      aestronglyMeasurable_const f hgrad
  have hvol : volume (euclideanBall U.1 (U.2 / 8))
      = ENNReal.ofReal (kap / 8 ^ d * ell ^ d) := by
    have hpos : (0 : ℝ) < U.2 / 8 := by positivity
    have hval := volume_euclideanBall_toReal_eq_unit_mul_pow (d := d) U.1 hpos
    have hne : volume (euclideanBall U.1 (U.2 / 8)) ≠ ⊤ :=
      Homogenization.Book.Ch01.volume_euclideanBall_ne_top _ _
    rw [← ENNReal.ofReal_toReal hne, hval, ← hkap]
    congr 1
    simp only [hUdef]
    rw [div_pow]
    ring
  have hnnB : (0 : ℝ) ≤ C * Real.exp (C * 1) * cutoffGradSq d * ell ^ d := by
    have h1 : (0 : ℝ) ≤ C * Real.exp (C * 1) := by positivity
    have h2 : (0 : ℝ) ≤ ell ^ d := by positivity
    exact mul_nonneg (mul_nonneg h1 hcg) h2
  have hchain : ENNReal.ofReal (kap / 8 ^ d * ell ^ d) ^ (2 / p0)
      ≤ ENNReal.ofReal (C * Real.exp (C * 1) * cutoffGradSq d * ell ^ d) := by
    rw [← hvol]
    refine hlow.trans (hdd.trans ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcancel : C * Real.exp (C * 1) * ell ^ 2 *
          (1 * (cutoffGradSq d / ell ^ 2) * ell ^ d)
        = C * Real.exp (C * 1) * cutoffGradSq d * ell ^ d := by
      field_simp
    calc C * Real.exp (C * 1) * ell ^ 2 *
          energy (fun _ : Vec d => (1 : ℝ)) (cubeSet U) f.toH1Function
        ≤ C * Real.exp (C * 1) * ell ^ 2 * (1 * (cutoffGradSq d / ell ^ 2) * ell ^ d) := by
          refine mul_le_mul_of_nonneg_left (by simpa [hUdef] using! hen) (by positivity)
      _ = C * Real.exp (C * 1) * cutoffGradSq d * ell ^ d := hcancel
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff hnnB] at hchain
  calc (kap / 8 ^ d) ^ (2 / p0) * (ell ^ d) ^ (2 / p0)
      = (kap / 8 ^ d * ell ^ d) ^ (2 / p0) :=
        (Real.mul_rpow (by positivity) (by positivity)).symm
    _ ≤ C * Real.exp (C * 1) * cutoffGradSq d * ell ^ d := hchain

/-- **The v1 Sobolev display is false below scale one.**  The printed display carries
averages on both sides; `lpSq` and `energy` are unnormalized, so the printed form is
`lpSq ≤ C e^{CH} F_U |U|^{2/p0−1} energy`, and the frozen clause drops `|U|^{2/p0−1}`, which
exceeds one when `|U| < 1`. -/
theorem not_subunitSobolevDisplay [NeZero d] {p0 C : ℝ} (hp0 : 2 < p0) (hC : 0 ≤ C) :
    ¬ SubunitSobolevDisplay d (fun _ => (1 : ℝ)) p0 C := by
  intro hdisp
  set kap : ℝ := (volume (smallContrastUnitBall d)).toReal with hkap
  have hkappos : 0 < kap := volume_smallContrastUnitBall_toReal_pos d
  set A : ℝ := (kap / 8 ^ d) ^ (2 / p0) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  set B : ℝ := C * Real.exp (C * 1) * cutoffGradSq d with hB
  set beta : ℝ := 1 - 2 / p0 with hbeta
  have hbetapos : 0 < beta := by
    have : 2 / p0 < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    rw [hbeta]
    linarith
  have hkey : ∀ ell : ℝ, 0 < ell → ell < 1 → A ≤ B * (ell ^ d) ^ beta := by
    intro ell hell hell1
    have hsc := subunitSobolev_scaling hp0 hC hdisp hell hell1
    have hvpos : (0 : ℝ) < ell ^ d := by positivity
    have hvq : (0 : ℝ) < (ell ^ d) ^ (2 / p0) := Real.rpow_pos_of_pos hvpos _
    have hdiv : A ≤ B * ell ^ d / (ell ^ d) ^ (2 / p0) := by
      rw [le_div_iff₀ hvq]
      exact hsc
    have hsplit : B * ell ^ d / (ell ^ d) ^ (2 / p0) = B * (ell ^ d) ^ beta := by
      rw [hbeta, Real.rpow_sub hvpos, Real.rpow_one]
      ring
    rwa [hsplit] at hdiv
  have hstep : ∀ n : ℕ, A ≤ B * ((((n : ℝ) + 2)⁻¹) ^ d) ^ beta := by
    intro n
    refine hkey _ (by positivity) ?_
    rw [inv_lt_one_iff₀]
    right
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hto0 : Tendsto (fun n : ℕ => (((n : ℝ) + 2)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hpow : Tendsto (fun n : ℕ => (((n : ℝ) + 2)⁻¹) ^ d) atTop (𝓝 0) := by
    have h := ((continuous_pow d).continuousAt (x := (0 : ℝ))).tendsto.comp hto0
    rw [zero_pow (NeZero.ne d)] at h
    exact h
  have hrpow : Tendsto (fun n : ℕ => B * ((((n : ℝ) + 2)⁻¹) ^ d) ^ beta) atTop (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ beta) 0 :=
      Real.continuousAt_rpow_const 0 beta (Or.inr hbetapos.le)
    have h1 : Tendsto (fun n : ℕ => ((((n : ℝ) + 2)⁻¹) ^ d) ^ beta) atTop (𝓝 0) := by
      have h := hc.tendsto.comp hpow
      rw [Real.zero_rpow hbetapos.ne'] at h
      exact h
    simpa using! h1.const_mul B
  have hle : A ≤ 0 := ge_of_tendsto hrpow (Filter.Eventually.of_forall hstep)
  linarith

/-! ## The v2 Sobolev display, and the two displays it unlocks

`SubunitSobolevHypothesis a U p0 F` is the **v2** Sobolev clause with the constant abstracted:
the frozen clause is this at `F := C e^{CH} F_U`, since
`ofReal (C e^{CH} F_U * vol^{-(1-2/p0)}) * ofReal energy` is `ofReal (F * vol^{-(1-2/p0)}) *
ofReal energy` at that `F`.  It is exactly the hypothesis the PROVED local-resolvent exit-time
estimate converts into `SobolevAssumption ∧ PoincareAssumption` — which
is independent confirmation that the volume normalization of v2 is the form the tree expects.
-/

/-- The v2 Sobolev clause with the constant abstracted. -/
def SubunitSobolevHypothesis (a : Vec d → ℝ) (U : Cube d) (p0 F : ℝ) : Prop :=
  ∀ f : H10Function (cubeSet U),
    lpSq (fun _ => (1 : ℝ)) (cubeSet U) p0 f.toH1Function.toFun ≤
      ENNReal.ofReal (F * (volume (cubeSet U)).toReal ^ (-(1 - 2 / p0))) *
        ENNReal.ofReal (energy a (cubeSet U) f.toH1Function)

/-- The v2 Sobolev clause is the Sobolev/Poincaré package of the local-resolvent exit-time estimate. -/
theorem sobolevAssumption_of_subunitSobolevHypothesis {p0 : ℝ} (hp0 : 2 < p0)
    (_hd : 2 ≤ d) {a : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hLD : LocalDiffusion a (fun _ => (1 : ℝ)) law) {U : Cube d} {F : ℝ}
    (hU : 0 < U.2) (hF : 0 < F) (hsob : SubunitSobolevHypothesis a U p0 F) :
    SobolevAssumption a (fun _ => (1 : ℝ)) (cubeSet U) p0 1 F ∧
      PoincareAssumption a (fun _ => (1 : ℝ)) (cubeSet U) 1 F := by
  obtain ⟨c0, C, hc0, hC, h⟩ := SubdiffusiveProcess.Frozen.Section8.local_resolvent_exit_upper p0 hp0
  refine (h d _hd a (fun _ => (1 : ℝ)) law hLD (fun i => U.1 i - U.2 / 2) U.2 hU 1 F
    le_rfl hF).2 ?_
  intro f
  refine (hsob f).trans_eq ?_
  have hEq : F * (volume (cubeSet U)).toReal ^ (-(1 - 2 / p0)) *
        energy a (cubeSet U) f.toH1Function
      = 1 * ((weightedMeasure (fun _ : Vec d => (1 : ℝ)) (cubeSet U)).toReal) ^
          (-(1 - 2 / p0)) * F * energy a (cubeSet U) f.toH1Function := by
    rw [weightedMeasure_one]
    ring
  rw [← ENNReal.ofReal_mul (by positivity), hEq]
  rfl

/-- **The torsion upper display** of the subunit divergence estimates v2, from the v2 Sobolev
display through the PROVED local-resolvent exit-time estimate.  At `F = C e^{CH} F_U` this is
`sup_{z ∈ U} E_z σ_U ≤ C' e^{CH} F_U`. -/
theorem meanExit_le_of_subunitSobolev {p0 : ℝ} (hp0 : 2 < p0) :
    ∃ Ctor : ℝ, 0 < Ctor ∧
      ∀ (_hd : 2 ≤ d) (a : Vec d → ℝ) (law : Kernel (Vec d) (Path d)),
        LocalDiffusion a (fun _ => (1 : ℝ)) law →
        ∀ (U : Cube d) (F : ℝ), 0 < U.2 → 0 < F →
          SubunitSobolevHypothesis a U p0 F →
          ∀ q : ℝ → Vec d → Vec d → ℝ,
            IsKilledDensity law (fun _ => (1 : ℝ)) (cubeSet U) q →
            ContinuousOn (fun z : ℝ × Vec d × Vec d => q z.1 z.2.1 z.2.2)
              (Ioi 0 ×ˢ cubeSet U ×ˢ cubeSet U) →
            ∀ x ∈ cubeSet U, meanExit law (cubeSet U) x ≤ ENNReal.ofReal (Ctor * F) := by
  obtain ⟨c0, C, hc0, hC, h⟩ := SubdiffusiveProcess.Frozen.Section8.local_resolvent_exit_upper p0 hp0
  refine ⟨C, hC, ?_⟩
  intro _hd a law hLD U F hU hF hsob q hq hqc x hx
  have hassum := sobolevAssumption_of_subunitSobolevHypothesis hp0 _hd hLD hU hF hsob
  have hexit := ((h d _hd a (fun _ => (1 : ℝ)) law hLD (fun i => U.1 i - U.2 / 2) U.2 hU 1 F
    le_rfl hF).1 hassum) q hq hqc
  have hval := hexit.2 x hx
  rwa [Real.one_rpow, mul_one] at hval

/-- **The killed-kernel upper display** of the subunit divergence estimates v2, from the v2
Sobolev display through the PROVED local resolvent iteration lemma.  The continuity clause that
v2 adds is exactly the one that anchor's pointwise diagonal bound requires. -/
theorem killedDiagonal_le_of_subunitSobolev {p0 : ℝ} (hp0 : 2 < p0) :
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (_hd : 2 ≤ d) (a : Vec d → ℝ) (law : Kernel (Vec d) (Path d)),
        LocalDiffusion a (fun _ => (1 : ℝ)) law →
        ∀ (U : Cube d) (F : ℝ), 0 < U.2 → 0 < F →
          SubunitSobolevHypothesis a U p0 F →
          ∀ q : ℝ → Vec d → Vec d → ℝ,
            IsKilledDensity law (fun _ => (1 : ℝ)) (cubeSet U) q →
            ContinuousOn (fun z : ℝ × Vec d × Vec d => q z.1 z.2.1 z.2.2)
              (Ioi 0 ×ˢ cubeSet U ×ˢ cubeSet U) →
            ∀ t : ℝ, 0 < t → ∀ x ∈ cubeSet U,
              q t x x ≤ Cq / (volume (cubeSet U)).toReal *
                (1 + F / t) ^ ((1 - 2 / p0)⁻¹) := by
  obtain ⟨N0, C, hN0, hC, h⟩ := SubdiffusiveProcess.Frozen.Section8.local_resolvent_iteration p0 hp0
  refine ⟨C, hC, ?_⟩
  intro _hd a law hLD U F hU hF hsob q hq hqc t ht x hx
  have hassum := (sobolevAssumption_of_subunitSobolevHypothesis hp0 _hd hLD hU hF hsob).1
  have hmain := h d _hd a (fun _ => (1 : ℝ)) law hLD (fun i => U.1 i - U.2 / 2) U.2 hU 1 F
    le_rfl hF hassum
  have hval := ((hmain.2 q hq).2 hqc) t ht x hx
  rw [Real.one_rpow, mul_one, weightedMeasure_one] at hval
  exact hval


/-! ## The torsion lower display, reduced to one barrier bound

Everything the printed proof needs for `ce^{-CH}F_U ≤ E_z σ_U` on the middle quarter is in
the tree except the barrier step itself:

* the mean-exit **upper** bound is `meanExit_le_of_subunitSobolev` above;
* `Section9Support.goodCube_exists_h10_meanExit` turns it into a zero-trace torsion carrier
  `v ∈ H¹₀(U)` with `ofReal (v x) = E_x σ_U` almost everywhere, `0 ≤ v ≤ E`, and
  `IsMassiveWeakSolutionOn a 1 0 U v 1` — that is, `−∇·(a∇v) = 1` weakly;
* `Section9Support.goodCube_meanExit_lower_of_h10` reads an almost-everywhere lower bound for
  `v` on an open interior set back as a pointwise lower bound for the mean exit time.

`meanExit_lower_of_barrier` chains the three.  The single remaining input is `hbarrier`: the
comparison-principle step, that a nonnegative `H¹₀` solution of `−∇·(a∇v) = 1` on the cube is
at least `k` on the middle quarter.  The printed route is the quadratic barrier
`φ(x) = (r² − |x − z|²)/(2dΛ)` on `B_r(z)` for `z` in the middle quarter, which sits inside the
cube for `r ≤ ℓ/4` in every dimension.  Note `−∇·(a∇φ) = −aΔφ − ∇a·∇φ`, so for a
non-constant coefficient the first-order term must be absorbed: with
`‖∇ log a‖_{L^∞(2U)} ≤ √H/ℓ` from `LogCoefficientControlOn`, taking `r ≍ ℓ/√H` makes it a
fraction of the zeroth-order term and gives `k ≍ ℓ²/(HΛ)`, which is of the printed form
`c e^{−CH} F_U` since `H⁻¹ ≥ e^{−H}` for `H ≥ 1`.
-/

/-- The middle quarter sits inside the cube. -/
theorem middleQuarter_subset_cubeSet {U : Cube d} (hU : 0 < U.2) :
    middleQuarter U ⊆ cubeSet U := by
  intro y hy i _
  have h := hy i (Set.mem_univ i)
  simp only [Set.mem_Ioo] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem isOpen_middleQuarter {U : Cube d} : IsOpen (middleQuarter U) :=
  isOpen_axisCube _ _

/-- **The torsion lower display, reduced to the barrier bound.**  Every step but the
comparison principle is discharged from the tree. -/
theorem meanExit_lower_of_barrier [NeZero d] {p0 : ℝ} (hp0 : 2 < p0) (hd : 2 ≤ d)
    {a : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData a (fun _ => (1 : ℝ)) law)
    {U : Cube d} (hU : 0 < U.2) {F : ℝ} (hF : 0 < F)
    (hsob : SubunitSobolevHypothesis a U p0 F)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet U) (scalarCoeffField a))
    {k : ℝ} (hk : 0 ≤ k)
    (hbarrier : ∀ v : H10Function (cubeSet U),
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
        a (fun _ => (1 : ℝ)) 0 (cubeSet U) v.toH1Function (fun _ => (1 : ℝ)) →
      (∀ᵐ x ∂volume.restrict (cubeSet U), 0 ≤ v.toH1Function.toFun x) →
      ∀ᵐ x ∂volume.restrict (cubeSet U),
        x ∈ middleQuarter U → k ≤ v.toH1Function.toFun x) :
    ∀ x ∈ middleQuarter U, ENNReal.ofReal k ≤ meanExit law (cubeSet U) x := by
  classical
  have hconv : IsOpenBoundedConvexDomain (cubeSet U) :=
    isOpenBoundedConvexDomain_axisCube (fun i => U.1 i - U.2 / 2) U.2
  have hopen : IsOpen (cubeSet U) := hconv.isOpen
  have hbdd : Bornology.IsBounded (cubeSet U) := hconv.isBoundedDomain.isBounded
  -- the mean-exit upper bound, from the Sobolev display
  obtain ⟨q, hq, hqc⟩ := hD.2 (cubeSet U) hopen hbdd
  obtain ⟨Ctor, hCtor, hupper⟩ := meanExit_le_of_subunitSobolev (d := d) hp0
  have hmean : ∀ x ∈ cubeSet U, meanExit law (cubeSet U) x ≤ ENNReal.ofReal (Ctor * F) :=
    hupper hd a law hD.1 U F hU hF hsob q hq hqc
  -- the torsion carrier
  obtain ⟨v, hv, hvb, hvsol⟩ :=
    goodCube_exists_h10_meanExit hD.1 hopen hbdd hconv hlam hEll
      (E := Ctor * F) (by positivity) hmean
  -- the barrier bound, then the readout
  refine goodCube_meanExit_lower_of_h10 hD hopen hbdd isOpen_middleQuarter
    (middleQuarter_subset_cubeSet hU) v hv hk ?_
  exact hbarrier v hvsol (by filter_upwards [hvb] with x hx using hx.1)


/-! ## The comparison principle at zero mass

The torsion carrier of `goodCube_exists_h10_meanExit` solves the massive equation at mass
`mu = 0`, while every Stampacchia and barrier lemma in the tree
(`Section8Resolvent.ae_nonpos_of_isMassiveWeakSolutionOn_of_memH10_posPart`,
`ae_le_barrier_of_isMassiveWeakSolutionOn`,
`Section8Resolvent.ae_le_of_massiveWeakSolutions_of_nonneg_comparison`,
`ae_le_of_massiveWeakSolutionsOn_nestedDomains`) carries `0 < mu` — the mass term is what
their final step uses.  At `mu = 0` the Poincaré inequality replaces it.  These three
declarations are that replacement: the coefficient-free Poincaré tail, the weak maximum
principle for subsolutions, and the lower-barrier comparison, which is the shape
`hbarrier` of `meanExit_lower_of_barrier` needs.
-/


/-- The Poincaré tail: a zero-trace function with vanishing weak gradient vanishes. -/
theorem ae_le_of_truncation_grad_zero [NeZero d] {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) {u : H1Function W} {M : ℝ}
    {psi : H10Function W}
    (hval : ∀ x, psi.toH1Function.toFun x = max (u.toFun x - M) 0)
    (hgrad : psi.toH1Function.grad =ᵐ[volume.restrict W] 0) :
    ∀ᵐ x ∂(volume.restrict W), u.toFun x ≤ M := by
  have hVL2 : psi.toH1Function.gradToVectorL2 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [psi.toH1Function.coeFn_gradToVectorL2, hgrad] with y h1 h2
    rw [h1, h2]
  have hS :=
    Homogenization.H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
      (Homogenization.H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hW)
      psi hVL2
  have hzero : psi.toH1Function.toFun =ᵐ[volume.restrict W] 0 := by
    have hc := psi.toH1Function.coeFn_toScalarL2
    rw [hS] at hc
    filter_upwards [hc, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict W)]
      with y h1 h2
    rw [← h1, h2]
  filter_upwards [hzero] with y hy
  have hmax : max (u.toFun y - M) 0 = 0 := by rw [← hval y]; simpa using! hy
  linarith only [max_eq_right_iff.1 hmax]



theorem vecDot_smul_left' (c : ℝ) (v w : Vec d) :
    vecDot (c • v) w = c * vecDot v w := by
  simp [vecDot, Finset.mul_sum, mul_assoc]

/-- A weak subsolution of the divergence-form operator at zero mass. -/
def IsWeakSubSolutionOn (a : Vec d → ℝ) (W : Set (Vec d)) (u : H1Function W) : Prop :=
  ∀ psi : H10Function W, (∀ x, 0 ≤ psi.toH1Function.toFun x) →
    ∫ x in W, vecDot (a x • u.grad x) (psi.toH1Function.grad x) ∂volume ≤ 0

/-- **The weak maximum principle for subsolutions at zero mass.** -/
theorem ae_nonpos_of_isWeakSubSolutionOn [NeZero d] {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) {a : Vec d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ y ∂(volume.restrict W), lam ≤ a y ∧ a y ≤ Lam)
    {u : H1Function W} (hu : IsWeakSubSolutionOn a W u)
    (hmem : MemH10 W fun x => max (u.toFun x) 0) :
    ∀ᵐ x ∂(volume.restrict W), u.toFun x ≤ 0 := by
  classical
  obtain ⟨psi, hpsif, hpsig⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.exists_h10_positivePart_of_memH10 hW u hmem
  have hpsinn : ∀ x, 0 ≤ psi.toH1Function.toFun x := fun x => by
    rw [hpsif x]; exact le_max_right _ _
  -- the tested integrand collapses to `a |∇ψ|²`
  have hae : ∀ᵐ y ∂(volume.restrict W),
      vecDot (a y • u.grad y) (psi.toH1Function.grad y) =
        a y * vecNormSq (psi.toH1Function.grad y) := by
    filter_upwards [hpsig] with y hy
    by_cases hmem' : y ∈ {p | (0 : ℝ) < u.toFun p}
    · rw [hy, Set.indicator_of_mem hmem',
        vecDot_smul_left', vecNormSq]
    · rw [hy, Set.indicator_of_notMem hmem', vecDot_smul_left']
      simp [vecDot, vecNormSq]
  have hgint : Integrable (fun y => vecNormSq (psi.toH1Function.grad y))
      (volume.restrict W) := by
    have h := SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.integrableOn_vecDot_grad
      psi.toH1Function psi.toH1Function
    simpa [IntegrableOn, vecNormSq] using! h
  have hint : Integrable (fun y => a y * vecNormSq (psi.toH1Function.grad y))
      (volume.restrict W) := by
    refine Integrable.mono' (hgint.const_mul |Lam|)
      (hameas.mul hgint.aestronglyMeasurable) ?_
    filter_upwards [hbounds] with y hy
    have hpos : 0 < a y := lt_of_lt_of_le hlam hy.1
    have hnn : 0 ≤ vecNormSq (psi.toH1Function.grad y) := Homogenization.vecNormSq_nonneg _
    have habs : |a y| ≤ |Lam| := by
      rw [abs_of_pos hpos]; exact le_trans hy.2 (le_abs_self Lam)
    calc ‖a y * vecNormSq (psi.toH1Function.grad y)‖
        = |a y| * vecNormSq (psi.toH1Function.grad y) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      _ ≤ |Lam| * vecNormSq (psi.toH1Function.grad y) :=
          mul_le_mul_of_nonneg_right habs hnn
  have hnonneg : ∀ᵐ y ∂(volume.restrict W),
      0 ≤ a y * vecNormSq (psi.toH1Function.grad y) := by
    filter_upwards [hbounds] with y hy
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le hlam hy.1)) (Homogenization.vecNormSq_nonneg _)
  have hzero : ∫ y in W, a y * vecNormSq (psi.toH1Function.grad y) ∂volume = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae hnonneg)
    rw [← integral_congr_ae hae]
    exact hu psi hpsinn
  have hgradzero : psi.toH1Function.grad =ᵐ[volume.restrict W] 0 := by
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
    filter_upwards [hae0, hbounds] with y hy hb
    have hpos : 0 < a y := lt_of_lt_of_le hlam hb.1
    have : vecNormSq (psi.toH1Function.grad y) = 0 := by
      rcases mul_eq_zero.mp hy with h | h
      · exact absurd h hpos.ne'
      · exact h
    exact Homogenization.vecNormSq_eq_zero this
  exact ae_le_of_truncation_grad_zero (M := 0) hW
    (by intro x; rw [hpsif x]; simp) hgradzero


/-- **The lower-barrier comparison at zero mass.** -/
theorem ae_barrier_le_of_isWeakSubSolutionOn [NeZero d] {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) {a : Vec d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ y ∂(volume.restrict W), lam ≤ a y ∧ a y ≤ Lam)
    {B : H10Function W} {v : H1Function W} (hvnn : ∀ x, 0 ≤ v.toFun x)
    (hsub : IsWeakSubSolutionOn a W (B.toH1Function - v)) :
    ∀ᵐ x ∂(volume.restrict W), B.toH1Function.toFun x ≤ v.toFun x := by
  have hmem : MemH10 W fun x => max ((B.toH1Function - v).toFun x) 0 := by
    obtain ⟨w, hwf, _⟩ :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.exists_h10_positivePart_sub_of_nonneg hW B v hvnn
    exact ⟨w, by funext x; rw [hwf x, H1Function.sub_toFun]⟩
  have := ae_nonpos_of_isWeakSubSolutionOn hW hlam hameas hbounds hsub hmem
  filter_upwards [this] with x hx
  have : B.toH1Function.toFun x - v.toFun x ≤ 0 := by
    simpa [H1Function.sub_toFun] using! hx
  linarith


/-! ## The quadratic barrier and its subsolution bound

The printed barrier for the torsion lower bound, in the form that needs neither a cutoff nor
a Hessian.  `quadBarrier kap rho z x = kap (rho² − ‖x − z‖²)` is a **polynomial**, so it is
`ContDiff ⊤` globally and `isMassiveWeakSolutionOn_ofContDiffOnBounded` applies to it with no
smoothness bookkeeping; and it is **nonpositive off the ball** `B_rho(z)`, which is what makes
the comparison work without the barrier itself having zero trace: for `v ≥ 0` the positive
part `(quadBarrier − v)₊` is supported in `B_rho(z)`, compactly inside the cube, so
`memH10_of_compactSupport` supplies the zero trace that
`ae_barrier_le_of_isWeakSubSolutionOn` needs.

`coeffFluxDiv_quadBarrier` is the classical forcing, computed exactly:

    −∇·(a ∇(quadBarrier kap rho z)) = 2 kap (∑_i ∂_i a (x_i − z_i) + d · a),

which uses only **first** derivatives of `a` — the `∇a·∇φ` term the constant-coefficient
barrier misses.  `neg_coeffFluxDiv_quadBarrier_le` bounds it by
`2 kap (d G R + d Λ)`, so the subsolution inequality `−∇·(a∇B) ≤ 1` holds as soon as

    kap ≤ (2 (d G R + d Λ))⁻¹.

With `LogCoefficientControlOn a H U` on a cube of side `ℓ`: `|∂_i a| ≤ a |∂_i log a| ≤ Λ √H/ℓ`,
`R = ℓ`, `Λ = e^{√d√H} a(z_U)`, so `kap = (2 d Λ (√H + 1))⁻¹`, and at `rho = ℓ/4` the barrier
is at least `(3/4) kap rho²` on `B_{rho/2}(z)`.  That is the constant of the torsion lower
display:

    k = 3 ℓ² / (128 d e^{√d√H} a(z_U) (√H + 1)) = 3 F_U / (128 d e^{√d√H} (√H + 1)),

which is the printed `c e^{−CH} F_U` with **c = 3/(256 d)** and **C = √d + 1**, using
`√H + 1 ≤ 2 e^H` and `e^{√d√H} ≤ e^{√d H}` for `H ≥ 1`.
-/


/-- The quadratic barrier: a polynomial, positive on the ball of radius `rho` about `z`
and nonpositive outside it. -/
def quadBarrier (kap rho : ℝ) (z : Vec d) : Vec d → ℝ :=
  fun x => kap * (rho ^ 2 - ∑ i : Fin d, (x i - z i) ^ 2)

theorem contDiff_quadBarrier (kap rho : ℝ) (z : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (quadBarrier kap rho z) := by
  unfold quadBarrier
  fun_prop

theorem hasFDerivAt_quadBarrier (kap rho : ℝ) (z x : Vec d) :
    HasFDerivAt (quadBarrier kap rho z)
      (kap • ((0 : Vec d →L[ℝ] ℝ) -
        ∑ i : Fin d, (2 * (x i - z i)) •
          (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))) x := by
  have hcoord : ∀ j : Fin d, HasFDerivAt (fun y : Vec d => (y j - z j) ^ 2)
      ((2 * (x j - z j)) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) x := by
    intro j
    have h1 : HasFDerivAt (fun y : Vec d => y j - z j)
        (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) x :=
      ((ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).hasFDerivAt).sub_const _
    simpa using! h1.pow 2
  have hsum : HasFDerivAt (fun y : Vec d => ∑ i : Fin d, (y i - z i) ^ 2)
      (∑ i : Fin d, (2 * (x i - z i)) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) x :=
    HasFDerivAt.fun_sum fun i _ => hcoord i
  exact ((hasFDerivAt_const (rho ^ 2) x).sub hsum).const_mul kap

theorem euclideanCoordDeriv_quadBarrier (kap rho : ℝ) (z : Vec d) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (quadBarrier kap rho z) x = -(2 * kap) * (x i - z i) := by
  rw [euclideanCoordDeriv, (hasFDerivAt_quadBarrier kap rho z x).fderiv]
  simp [ContinuousLinearMap.proj, basisVec, Pi.single_apply, Finset.sum_ite_eq']
  ring

theorem hasFDerivAt_coordAffine (kap : ℝ) (z : Vec d) (i : Fin d) (x : Vec d) :
    HasFDerivAt (fun y : Vec d => -(2 * kap) * (y i - z i))
      (-((2 * kap) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))) x := by
  have h1 : HasFDerivAt (fun y : Vec d => y i - z i)
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) x :=
    ((ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).hasFDerivAt).sub_const _
  simpa using! h1.const_mul (-(2 * kap))

theorem coeffFluxDiv_quadBarrier {a : Vec d → ℝ} (ha : ContDiff ℝ 1 a)
    (kap rho : ℝ) (z x : Vec d) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.coeffFluxDiv a (quadBarrier kap rho z) x
      = -(2 * kap) * ((∑ i : Fin d, euclideanCoordDeriv i a x * (x i - z i)) + d * a x) := by
  have hA : HasFDerivAt a (fderiv ℝ a x) x :=
    ((ha.differentiable (by decide)) x).hasFDerivAt
  have hstep : ∀ i : Fin d,
      euclideanCoordDeriv i (fun y => a y * euclideanCoordDeriv i (quadBarrier kap rho z) y) x
        = euclideanCoordDeriv i a x * (-(2 * kap) * (x i - z i)) + a x * -(2 * kap) := by
    intro i
    have hrw : (fun y => a y * euclideanCoordDeriv i (quadBarrier kap rho z) y)
        = fun y => a y * (-(2 * kap) * (y i - z i)) := by
      funext y
      rw [euclideanCoordDeriv_quadBarrier]
    have hmul : HasFDerivAt (fun y : Vec d => a y * (-(2 * kap) * (y i - z i)))
        (a x • (-((2 * kap) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))) +
          (-(2 * kap) * (x i - z i)) • fderiv ℝ a x) x :=
      hA.mul (hasFDerivAt_coordAffine kap z i x)
    rw [hrw, euclideanCoordDeriv, hmul.fderiv]
    simp [euclideanCoordDeriv, ContinuousLinearMap.proj, basisVec]
    ring
  have hfold : ∀ i : Fin d,
      euclideanCoordDeriv i a x * (-(2 * kap) * (x i - z i)) + a x * -(2 * kap)
        = -(2 * kap) * (euclideanCoordDeriv i a x * (x i - z i) + a x) := by
    intro i; ring
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.coeffFluxDiv]
  simp only [hstep, hfold]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem neg_coeffFluxDiv_quadBarrier_le {a : Vec d → ℝ} (ha : ContDiff ℝ 1 a)
    {kap rho G Lam R : ℝ} (hkap : 0 ≤ kap) (z x : Vec d)
    (hG : ∀ i : Fin d, |euclideanCoordDeriv i a x| ≤ G)
    (hxz : ∀ i : Fin d, |x i - z i| ≤ R)
    (hLam : a x ≤ Lam) :
    -(SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.coeffFluxDiv a (quadBarrier kap rho z) x) ≤ 2 * kap * ((d : ℝ) * (G * R) + d * Lam) := by
  rw [coeffFluxDiv_quadBarrier ha]
  have hbound : (∑ i : Fin d, euclideanCoordDeriv i a x * (x i - z i)) ≤ (d : ℝ) * (G * R) := by
    calc (∑ i : Fin d, euclideanCoordDeriv i a x * (x i - z i))
        ≤ ∑ _i : Fin d, G * R := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc euclideanCoordDeriv i a x * (x i - z i)
              ≤ |euclideanCoordDeriv i a x * (x i - z i)| := le_abs_self _
            _ = |euclideanCoordDeriv i a x| * |x i - z i| := abs_mul _ _
            _ ≤ G * R := by
                refine mul_le_mul (hG i) (hxz i) (abs_nonneg _) ?_
                exact le_trans (abs_nonneg _) (hG i)
      _ = (d : ℝ) * (G * R) := by simp [Finset.sum_const, mul_comm]
  have : -(-(2 * kap) * ((∑ i : Fin d, euclideanCoordDeriv i a x * (x i - z i)) + d * a x))
      = 2 * kap * ((∑ i : Fin d, euclideanCoordDeriv i a x * (x i - z i)) + d * a x) := by ring
  rw [this]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hda : (d : ℝ) * a x ≤ d * Lam := by
    refine mul_le_mul_of_nonneg_left hLam (by positivity)
  linarith


/-! ## The barrier is a subsolution, and the comparison it feeds

Step (i) of the torsion lower route: the polynomial barrier, viewed as an `H1Function`
through `H1Function.ofContDiffOnIsOpenBoundedConvexDomain`, solves the massive equation at
`rho ≡ 1`, `mu = 0` with the classical forcing, by `isMassiveWeakSolutionOn_ofContDiffOnBounded`
— which carries no `0 < mu` hypothesis.  It does require `ContDiff ℝ 1 a` **globally**, which
`LogCoefficientControlOn` does not give (that is `ContDiffOn` on the concentric double), so it
is carried as a hypothesis here and discharged by the consumer; `aCutoff M n omega` and
`aAnchored M omega` are both globally `C^{1,1}`.

Step (ii): subtracting the two weak-solution identities gives the subsolution property, with
the integrability done honestly — `integrableOn_coeff_vecDot` dominates the tested integrand
by the bounded coefficient times `integrableOn_vecDot_grad`, and the two forcing integrals are
compared by `setIntegral_mono_on` with both sides integrable (the barrier's forcing is
continuous, hence bounded on the bounded cube), so no Bochner integral is silently junk-`0`.

`ae_le_of_isWeakSubSolutionOn_compactSupport` is the comparison in the form the polynomial
barrier needs: the barrier is **not** in `H¹₀`, and it does not have to be — it lies below `v`
off a compact subset, which is what `memH10_of_compactSupport` needs to give the difference's
positive part a zero trace.
-/


theorem vecDot_smul_sub (c : ℝ) (p q w : Vec d) :
    vecDot (c • (p - q)) w = vecDot (c • p) w - vecDot (c • q) w := by
  simp only [vecDot, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, sub_mul]
  rw [← Finset.sum_sub_distrib]

theorem integrableOn_coeff_vecDot {a : Vec d → ℝ} (hameas : Measurable a)
    {W : Set (Vec d)} {Lam : ℝ} (habdd : ∀ᵐ x ∂(volume.restrict W), |a x| ≤ Lam)
    (u psi : H1Function W) :
    IntegrableOn (fun x => vecDot (a x • u.grad x) (psi.grad x)) W volume := by
  have h0 := SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.integrableOn_vecDot_grad u psi
  have hmeas : AEStronglyMeasurable
      (fun x => vecDot (a x • u.grad x) (psi.grad x)) (volume.restrict W) := by
    have : (fun x => vecDot (a x • u.grad x) (psi.grad x))
        = fun x => a x * vecDot (u.grad x) (psi.grad x) := by
      funext x; exact vecDot_smul_left' _ _ _
    rw [this]
    exact hameas.aestronglyMeasurable.mul h0.aestronglyMeasurable
  refine Integrable.mono' (h0.abs.const_mul |Lam|) hmeas ?_
  filter_upwards [habdd] with x hx
  rw [vecDot_smul_left', Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hx.trans (le_abs_self Lam)) (le_refl _) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hx.trans (le_abs_self Lam)))



theorem isWeakSubSolutionOn_quadBarrier_sub [NeZero d] {a : Vec d → ℝ}
    (ha : ContDiff ℝ 1 a)
    {U : Cube d} (hUconv : IsOpenBoundedConvexDomain (cubeSet U))
    {Lam : ℝ} (habdd : ∀ᵐ x ∂(volume.restrict (cubeSet U)), |a x| ≤ Lam)
    {v : H1Function (cubeSet U)}
    (hvsol : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn a (fun _ => (1 : ℝ)) 0 (cubeSet U) v (fun _ => (1 : ℝ)))
    {kap rho : ℝ} (z : Vec d)
    (hsub : ∀ x ∈ cubeSet U,
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.smoothMassiveForcing a (fun _ => (1 : ℝ)) 0 (quadBarrier kap rho z) x ≤ 1) :
    IsWeakSubSolutionOn a (cubeSet U)
      ((H1Function.ofContDiffOnIsOpenBoundedConvexDomain hUconv
        ((contDiff_quadBarrier kap rho z).of_le (by simp))) - v) := by
  classical
  have : IsFiniteMeasure (volume.restrict (cubeSet U)) :=
    hUconv.isSobolevRegularDomain.isFiniteMeasure_restrict_volume
  set B := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hUconv
    ((contDiff_quadBarrier kap rho z).of_le (by simp)) with hBdef
  set g := SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.smoothMassiveForcing a (fun _ => (1 : ℝ)) 0 (quadBarrier kap rho z) with hgdef
  have hBsol : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn a (fun _ => (1 : ℝ)) 0 (cubeSet U) B g :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.isMassiveWeakSolutionOn_ofContDiffOnBounded ha (contDiff_quadBarrier kap rho z) hUconv
      (rho := fun _ => (1 : ℝ)) (rhoMax := 1) aestronglyMeasurable_const
      (by filter_upwards with x; simp) (by simp)
  intro psi hpsinn
  have hBpsi := hBsol psi
  have hvpsi := hvsol psi
  simp only [zero_mul, zero_add, one_mul] at hBpsi hvpsi
  have hXint := integrableOn_coeff_vecDot ha.continuous.measurable habdd B psi.toH1Function
  have hYint := integrableOn_coeff_vecDot ha.continuous.measurable habdd v psi.toH1Function
  have hsplit : ∫ x in cubeSet U,
        vecDot (a x • (B - v).grad x) (psi.toH1Function.grad x) ∂volume
      = (∫ x in cubeSet U, vecDot (a x • B.grad x) (psi.toH1Function.grad x) ∂volume)
        - ∫ x in cubeSet U, vecDot (a x • v.grad x) (psi.toH1Function.grad x) ∂volume := by
    rw [← integral_sub hXint hYint]
    refine setIntegral_congr_fun hUconv.isOpen.measurableSet fun x _ => ?_
    rw [H1Function.sub_grad, vecDot_smul_sub]
  rw [hsplit, hBpsi, hvpsi]
  -- the two forcing integrals
  have hpsiint : IntegrableOn psi.toH1Function.toFun (cubeSet U) volume :=
    (psi.toH1Function.memL2).integrable (by norm_num)
  have hgcont : Continuous g := by
    have : g = fun x => 0 * quadBarrier kap rho z x -
        SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.coeffFluxDiv a (quadBarrier kap rho z) x / 1 := rfl
    rw [this]
    exact (continuous_const.mul (contDiff_quadBarrier kap rho z).continuous).sub
      ((SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.continuous_coeffFluxDiv ha (contDiff_quadBarrier kap rho z)).div_const _)
  have hgint : IntegrableOn (fun x => g x * psi.toH1Function.toFun x) (cubeSet U) volume := by
    obtain ⟨C, hC⟩ := (hUconv.isSobolevRegularDomain.isBoundedDomain.isBounded.isCompact_closure).exists_bound_of_continuousOn
      hgcont.continuousOn
    refine Integrable.mono' (hpsiint.abs.const_mul C) ?_ ?_
    · exact hgcont.measurable.aestronglyMeasurable.mul psi.toH1Function.memL2.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hUconv.isOpen.measurableSet] with x hx
      have hgx : |g x| ≤ C := by simpa [Real.norm_eq_abs] using! hC x (subset_closure hx)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hgx (le_refl _) (abs_nonneg _) (le_trans (abs_nonneg _) hgx)
  have hmono : ∫ x in cubeSet U, g x * psi.toH1Function.toFun x ∂volume
      ≤ ∫ x in cubeSet U, psi.toH1Function.toFun x ∂volume := by
    refine setIntegral_mono_on hgint hpsiint hUconv.isOpen.measurableSet fun x hx => ?_
    have := hsub x hx
    nlinarith [hpsinn x]
  linarith



/-- **The comparison when only the difference has compact support.**  The barrier itself need
not have zero trace: it is enough that it lies below `v` off a compact subset. -/
theorem ae_le_of_isWeakSubSolutionOn_compactSupport [NeZero d] {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) {a : Vec d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ y ∂(volume.restrict W), lam ≤ a y ∧ a y ≤ Lam)
    {B v : H1Function W} (hsub : IsWeakSubSolutionOn a W (B - v))
    {K : Set (Vec d)} (hK : IsCompact K) (hKW : K ⊆ W)
    (hout : ∀ x, x ∉ K → B.toFun x ≤ v.toFun x) :
    ∀ᵐ x ∂(volume.restrict W), B.toFun x ≤ v.toFun x := by
  classical
  obtain ⟨w, hwf, _hwg⟩ :=
    Homogenization.exists_h1_max_sub_const hW (B - v) 0
  have hmem : MemH10 W fun x => max ((B - v).toFun x) 0 := by
    have hz : ∀ x, x ∉ K → w.toFun x = 0 := by
      intro x hx
      rw [congrFun hwf x, sub_zero, H1Function.sub_toFun]
      exact max_eq_right (by linarith [hout x hx])
    have h := Homogenization.memH10_of_compactSupport hW w hK hKW hz
    simpa [hwf, sub_zero] using! h
  have hnp := ae_nonpos_of_isWeakSubSolutionOn hW hlam hameas hbounds hsub hmem
  filter_upwards [hnp] with x hx
  have : B.toFun x - v.toFun x ≤ 0 := by simpa [H1Function.sub_toFun] using! hx
  linarith


/-! ## Step (iii): the barrier bound on the middle quarter

`quadBarrier_nonpos_of_notMem` is what makes the compact-support comparison apply — off the
closed ball the polynomial is nonpositive, hence below the nonnegative torsion carrier.
`le_quadBarrier_of_close` is its value near the centre.

`barrier_bound_of_torsion` assembles the three steps and is exactly the `hbarrier` hypothesis
of `meanExit_lower_of_barrier`, at

    k = (3/4) · kap · rho².

The torsion carrier is first replaced by its **pointwise** positive part
(`exists_h1_max_sub_const` and `IsMassiveWeakSolutionOn.congr`), since
`goodCube_exists_h10_meanExit` gives nonnegativity only almost everywhere while the
comparison needs it at every point.  The centre `z` then ranges over a **countable dense**
subset of the ambient space (`TopologicalSpace.exists_countable_dense` and `ae_ball_iff`):
one barrier per centre gives an almost-everywhere bound, countably many of them intersect to
a single almost-everywhere statement, and every point of the middle quarter lies within
`rho/2` of an admissible centre because the middle quarter is open — the moving centre is
needed because a single barrier at the cube's centre covers only the inscribed euclidean ball,
which misses the middle quarter once `√d ℓ/8 ≥ ℓ/2`, i.e. from `d = 16` on.

With `rho = ℓ/4` and `kap = (2 d Λ (√H + 1))⁻¹` from `neg_coeffFluxDiv_quadBarrier_le`:

    k = 3 ℓ² / (128 d Λ (√H + 1)) = 3 F_U / (128 d e^{√d√H} (√H + 1)),

the printed `c e^{−CH} F_U` with **c = 3/(256 d)**, **C = √d + 1**.
-/


theorem quadBarrier_nonpos_of_notMem {kap rho : ℝ} (hkap : 0 ≤ kap) (hrho : 0 ≤ rho)
    (z x : Vec d) (hx : x ∉ Metric.closedBall z rho) : quadBarrier kap rho z x ≤ 0 := by
  have hlt : rho < ‖x - z‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using! hx
  obtain ⟨i, hi⟩ : ∃ i : Fin d, rho < |x i - z i| := by
    by_contra hcon
    push Not at hcon
    have : ‖x - z‖ ≤ rho := by
      refine (pi_norm_le_iff_of_nonneg hrho).mpr fun i => ?_
      simpa [Real.norm_eq_abs] using! hcon i
    exact absurd this (not_le.mpr hlt)
  have hsq : rho ^ 2 ≤ ∑ j : Fin d, (x j - z j) ^ 2 := by
    have hterm : rho ^ 2 ≤ (x i - z i) ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg (x i - z i)] : -(|x i - z i|) ≤ rho)
        (le_of_lt hi)
      nlinarith [abs_nonneg (x i - z i), sq_abs (x i - z i)]
    refine hterm.trans ?_
    refine Finset.single_le_sum (f := fun j : Fin d => (x j - z j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have : rho ^ 2 - ∑ j : Fin d, (x j - z j) ^ 2 ≤ 0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos hkap this

theorem le_quadBarrier_of_close {kap rho : ℝ} (hkap : 0 ≤ kap) (z x : Vec d)
    (hx : ∑ j : Fin d, (x j - z j) ^ 2 ≤ rho ^ 2 / 4) :
    3 / 4 * kap * rho ^ 2 ≤ quadBarrier kap rho z x := by
  have : rho ^ 2 - ∑ j : Fin d, (x j - z j) ^ 2 ≥ 3 / 4 * rho ^ 2 := by linarith
  calc 3 / 4 * kap * rho ^ 2 = kap * (3 / 4 * rho ^ 2) := by ring
    _ ≤ kap * (rho ^ 2 - ∑ j : Fin d, (x j - z j) ^ 2) :=
        mul_le_mul_of_nonneg_left this hkap
    _ = quadBarrier kap rho z x := rfl



theorem barrier_bound_of_torsion [NeZero d] {a : Vec d → ℝ} (ha : ContDiff ℝ 1 a)
    {U : Cube d} (hUconv : IsOpenBoundedConvexDomain (cubeSet U))
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hbounds : ∀ᵐ y ∂(volume.restrict (cubeSet U)), lam ≤ a y ∧ a y ≤ Lam)
    (habdd : ∀ᵐ x ∂(volume.restrict (cubeSet U)), |a x| ≤ Lam)
    {kap rho : ℝ} (hkap : 0 ≤ kap) (hrho : 0 < rho)
    (hforcing : ∀ z ∈ middleQuarter U, ∀ x ∈ cubeSet U,
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.smoothMassiveForcing a (fun _ => (1 : ℝ)) 0 (quadBarrier kap rho z) x ≤ 1)
    (hball : ∀ z ∈ middleQuarter U, Metric.closedBall z rho ⊆ cubeSet U)
    {v : H1Function (cubeSet U)}
    (hvsol : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn a (fun _ => (1 : ℝ)) 0 (cubeSet U) v (fun _ => (1 : ℝ)))
    (hvnn : ∀ᵐ x ∂(volume.restrict (cubeSet U)), 0 ≤ v.toFun x) :
    ∀ᵐ x ∂(volume.restrict (cubeSet U)), x ∈ middleQuarter U →
      3 / 4 * kap * rho ^ 2 ≤ v.toFun x := by
  classical
  have hameas : AEStronglyMeasurable a (volume.restrict (cubeSet U)) :=
    ha.continuous.measurable.aestronglyMeasurable
  obtain ⟨vp, hvpf, hvpg⟩ := Homogenization.exists_h1_max_sub_const hUconv v 0
  have hvpnn : ∀ x, 0 ≤ vp.toFun x := by
    intro x; rw [congrFun hvpf x]; exact le_max_right _ _
  have hvpeq : vp.toFun =ᵐ[volume.restrict (cubeSet U)] v.toFun := by
    filter_upwards [hvnn] with x hx
    rw [congrFun hvpf x, sub_zero]
    exact max_eq_left hx
  have hvpgrad : vp.grad =ᵐ[volume.restrict (cubeSet U)] v.grad :=
    Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hUconv.isOpen hvpeq
  have hvpsol : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn a (fun _ => (1 : ℝ)) 0 (cubeSet U) vp
      (fun _ => (1 : ℝ)) := hvsol.congr hvpeq.symm hvpgrad.symm
  have hcmp : ∀ z ∈ middleQuarter U, ∀ᵐ x ∂(volume.restrict (cubeSet U)),
      quadBarrier kap rho z x ≤ vp.toFun x := by
    intro z hz
    have hsub := isWeakSubSolutionOn_quadBarrier_sub ha hUconv habdd hvpsol z (hforcing z hz)
    exact ae_le_of_isWeakSubSolutionOn_compactSupport hUconv hlam hameas hbounds hsub
      (isCompact_closedBall z rho) (hball z hz)
      (fun x hx => le_trans (quadBarrier_nonpos_of_notMem hkap hrho.le z x hx) (hvpnn x))
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hall : ∀ᵐ x ∂(volume.restrict (cubeSet U)), ∀ z ∈ D,
      z ∈ middleQuarter U → quadBarrier kap rho z x ≤ vp.toFun x := by
    rw [ae_ball_iff hDcount]
    intro z _
    by_cases hz : z ∈ middleQuarter U
    · filter_upwards [hcmp z hz] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall fun x hzmem => absurd hzmem hz
  filter_upwards [hall, hvpeq] with x hx hxeq
  intro hxMQ
  obtain ⟨delta, hdelta, hdsub⟩ := Metric.isOpen_iff.mp isOpen_middleQuarter x hxMQ
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  set r : ℝ := min delta (rho / (2 * Real.sqrt d)) with hrdef
  have hr : 0 < r := lt_min hdelta (by positivity)
  obtain ⟨z, hzD, hzdist⟩ := Metric.mem_closure_iff.mp (hDdense.closure_eq ▸ Set.mem_univ x) r hr
  have hzMQ : z ∈ middleQuarter U := hdsub (by
    simpa [Metric.mem_ball, dist_comm] using! lt_of_lt_of_le hzdist (min_le_left _ _))
  have hclose : ∑ j : Fin d, (x j - z j) ^ 2 ≤ rho ^ 2 / 4 := by
    have h1 : euclideanNorm (x - z) ≤ Real.sqrt d * ‖x - z‖ :=
      euclideanNorm_le_sqrt_card_mul_norm _
    have h2 : ‖x - z‖ < rho / (2 * Real.sqrt d) := by
      have := lt_of_lt_of_le hzdist (min_le_right _ _)
      rwa [dist_eq_norm] at this
    have h3 : euclideanNorm (x - z) ≤ rho / 2 := by
      have : Real.sqrt d * ‖x - z‖ ≤ Real.sqrt d * (rho / (2 * Real.sqrt d)) :=
        mul_le_mul_of_nonneg_left h2.le (Real.sqrt_nonneg _)
      have heq : Real.sqrt d * (rho / (2 * Real.sqrt d)) = rho / 2 := by
        field_simp
      linarith [h1, this, heq ▸ this]
    have h4 : euclideanNorm (x - z) ^ 2 ≤ (rho / 2) ^ 2 := by
      have hnn : 0 ≤ euclideanNorm (x - z) := euclideanNorm_nonneg _
      nlinarith
    have h5 : ∑ j : Fin d, (x j - z j) ^ 2 = euclideanNorm (x - z) ^ 2 := by
      rw [euclideanNorm_sq (x - z)]
      simp [vecNormSq, vecDot, Pi.sub_apply, sq]
    rw [h5]
    nlinarith
  have hb := hx z hzD hzMQ
  have := le_quadBarrier_of_close hkap z x hclose
  rw [← hxeq]
  linarith


/-! ## The same refutation at the model's own coefficient -/

theorem aestronglyMeasurable_of_logCoefficientControlOn {a : Vec d → ℝ} {H : ℝ} {U : Cube d}
    (hU : 0 < U.2) (hctrl : LogCoefficientControlOn a H U) :
    AEStronglyMeasurable a (volume.restrict (cubeSet U)) := by
  have hcont : ContinuousOn a (cubeSet U) :=
    ((contDiffOn_of_logCoefficientControlOn hctrl).continuousOn).mono
      (cubeSet_subset_double hU.le)
  exact hcont.aestronglyMeasurable (isOpen_cubeSet).measurableSet

/-- The scaling inequality at a coefficient carrying the control at `H`.  The value `a z_U`
cancels between `F_U` and the energy, so the bound is the same as for a constant
coefficient, with one extra factor `e^{√d√H}` from the normalization. -/
theorem subunitSobolev_scaling_of_control [NeZero d] {p0 C H : ℝ} (hp0 : 2 < p0) (hC : 0 ≤ C)
    (hH : 1 ≤ H) {a : Vec d → ℝ} (hdisp : SubunitSobolevDisplay d a p0 C)
    {z0 : Vec d} {ell : ℝ} (hell : 0 < ell) (hell1 : ell < 1)
    (hctrl : LogCoefficientControlOn a H (z0, ell)) :
    ((volume (smallContrastUnitBall d)).toReal / 8 ^ d) ^ (2 / p0) * (ell ^ d) ^ (2 / p0)
      ≤ C * Real.exp (C * H) * Real.exp (Real.sqrt d * Real.sqrt H) *
          cutoffGradSq d * ell ^ d := by
  have hcg : 0 ≤ cutoffGradSq d := cutoffGradSq_nonneg d
  set kap : ℝ := (volume (smallContrastUnitBall d)).toReal with hkap
  have hkappos : 0 < kap := volume_smallContrastUnitBall_toReal_pos d
  set U : Cube d := (z0, ell) with hUdef
  have hU2 : (0 : ℝ) < U.2 := hell
  have hapos : 0 < a U.1 :=
    hctrl.1 U.1 (cubeSet_subset_double hU2.le (centre_mem_cubeSet' hU2))
  obtain ⟨f, hone, _hnn, hgrad⟩ := exists_cutoff_h10Function (Q := U) hU2
  have hdd := hdisp U H hU2 hell1 hH hctrl (ell ^ 2 / a z0) rfl (by positivity) f
  have hballsub : euclideanBall U.1 (U.2 / 8) ⊆ cubeSet U :=
    euclideanBall_subset_cubeSet (by positivity) (by linarith)
  have hballmeas : MeasurableSet (euclideanBall U.1 (U.2 / 8)) :=
    (Homogenization.isOpen_euclideanBall _ _).measurableSet
  have hlow := weightedMeasure_rpow_le_lpSq (a := fun _ : Vec d => (1 : ℝ)) (Q := U)
    (p0 := p0) (by linarith) hballmeas hballsub f hone
  rw [weightedMeasure_one] at hlow
  have hen : energy a (cubeSet U) f.toH1Function
      ≤ Real.exp (Real.sqrt d * Real.sqrt H) * a U.1 * (cutoffGradSq d / U.2 ^ 2) * U.2 ^ d :=
    energy_le_of_logCoefficientControlOn hU2 hctrl
      (aestronglyMeasurable_of_logCoefficientControlOn hU2 hctrl) f hgrad
  have hvol : volume (euclideanBall U.1 (U.2 / 8))
      = ENNReal.ofReal (kap / 8 ^ d * ell ^ d) := by
    have hpos : (0 : ℝ) < U.2 / 8 := by positivity
    have hval := volume_euclideanBall_toReal_eq_unit_mul_pow (d := d) U.1 hpos
    have hne : volume (euclideanBall U.1 (U.2 / 8)) ≠ ⊤ :=
      Homogenization.Book.Ch01.volume_euclideanBall_ne_top _ _
    rw [← ENNReal.ofReal_toReal hne, hval, ← hkap]
    congr 1
    simp only [hUdef]
    rw [div_pow]
    ring
  have hnnB : (0 : ℝ) ≤ C * Real.exp (C * H) * Real.exp (Real.sqrt d * Real.sqrt H) *
      cutoffGradSq d * ell ^ d := by
    have h1 : (0 : ℝ) ≤ C * Real.exp (C * H) * Real.exp (Real.sqrt d * Real.sqrt H) := by
      positivity
    exact mul_nonneg (mul_nonneg h1 hcg) (by positivity)
  have hchain : ENNReal.ofReal (kap / 8 ^ d * ell ^ d) ^ (2 / p0)
      ≤ ENNReal.ofReal (C * Real.exp (C * H) * Real.exp (Real.sqrt d * Real.sqrt H) *
          cutoffGradSq d * ell ^ d) := by
    rw [← hvol]
    refine hlow.trans (hdd.trans ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hstep : C * Real.exp (C * H) * (ell ^ 2 / a z0) *
          energy a (cubeSet U) f.toH1Function
        ≤ C * Real.exp (C * H) * (ell ^ 2 / a z0) *
          (Real.exp (Real.sqrt d * Real.sqrt H) * a U.1 *
            (cutoffGradSq d / U.2 ^ 2) * U.2 ^ d) :=
      mul_le_mul_of_nonneg_left hen (by positivity)
    refine hstep.trans (le_of_eq ?_)
    have hU1 : a U.1 = a z0 := rfl
    have hU2' : U.2 = ell := rfl
    have haz : a z0 ≠ 0 := ne_of_gt hapos
    have hez : ell ≠ 0 := ne_of_gt hell
    rw [hU1, hU2']
    field_simp
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff hnnB] at hchain
  calc (kap / 8 ^ d) ^ (2 / p0) * (ell ^ d) ^ (2 / p0)
      = (kap / 8 ^ d * ell ^ d) ^ (2 / p0) :=
        (Real.mul_rpow (by positivity) (by positivity)).symm
    _ ≤ _ := hchain

/-- **The v1 Sobolev display is false at any coefficient carrying the control at a fixed `H`
on arbitrarily small cubes about one point** — in particular at `aCutoff M 0 omega`,
which is positive and `C^{1,1}`, so the control holds at a bounded `H` once the side is small
enough. -/
theorem not_subunitSobolevDisplay_of_control [NeZero d] {p0 C H : ℝ} (hp0 : 2 < p0)
    (hC : 0 ≤ C) (hH : 1 ≤ H) {a : Vec d → ℝ} {z0 : Vec d} {ell0 : ℝ} (hell0 : 0 < ell0)
    (hell0' : ell0 ≤ 1)
    (hctrl : ∀ ell : ℝ, 0 < ell → ell < ell0 → LogCoefficientControlOn a H (z0, ell)) :
    ¬ SubunitSobolevDisplay d a p0 C := by
  intro hdisp
  set kap : ℝ := (volume (smallContrastUnitBall d)).toReal with hkap
  have hkappos : 0 < kap := volume_smallContrastUnitBall_toReal_pos d
  set A : ℝ := (kap / 8 ^ d) ^ (2 / p0) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  set B : ℝ := C * Real.exp (C * H) * Real.exp (Real.sqrt d * Real.sqrt H) *
    cutoffGradSq d with hB
  set beta : ℝ := 1 - 2 / p0 with hbeta
  have hbetapos : 0 < beta := by
    have : 2 / p0 < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    rw [hbeta]
    linarith
  have hkey : ∀ ell : ℝ, 0 < ell → ell < ell0 → A ≤ B * (ell ^ d) ^ beta := by
    intro ell hell hellsmall
    have hell1 : ell < 1 := lt_of_lt_of_le hellsmall hell0'
    have hsc := subunitSobolev_scaling_of_control hp0 hC hH hdisp hell hell1
      (hctrl ell hell hellsmall)
    have hvpos : (0 : ℝ) < ell ^ d := by positivity
    have hvq : (0 : ℝ) < (ell ^ d) ^ (2 / p0) := Real.rpow_pos_of_pos hvpos _
    have hdiv : A ≤ B * ell ^ d / (ell ^ d) ^ (2 / p0) := by
      rw [le_div_iff₀ hvq]
      exact hsc
    have hsplit : B * ell ^ d / (ell ^ d) ^ (2 / p0) = B * (ell ^ d) ^ beta := by
      rw [hbeta, Real.rpow_sub hvpos, Real.rpow_one]
      ring
    rwa [hsplit] at hdiv
  have hto0 : Tendsto (fun n : ℕ => (((n : ℝ) + 2)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hstep : ∀ᶠ n : ℕ in atTop, A ≤ B * ((((n : ℝ) + 2)⁻¹) ^ d) ^ beta := by
    filter_upwards [hto0.eventually_lt_const hell0] with n hn
    exact hkey _ (by positivity) hn
  have hpow : Tendsto (fun n : ℕ => (((n : ℝ) + 2)⁻¹) ^ d) atTop (𝓝 0) := by
    have h := ((continuous_pow d).continuousAt (x := (0 : ℝ))).tendsto.comp hto0
    rw [zero_pow (NeZero.ne d)] at h
    exact h
  have hrpow : Tendsto (fun n : ℕ => B * ((((n : ℝ) + 2)⁻¹) ^ d) ^ beta) atTop (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ beta) 0 :=
      Real.continuousAt_rpow_const 0 beta (Or.inr hbetapos.le)
    have h1 : Tendsto (fun n : ℕ => ((((n : ℝ) + 2)⁻¹) ^ d) ^ beta) atTop (𝓝 0) := by
      have h := hc.tendsto.comp hpow
      rw [Real.zero_rpow hbetapos.ne'] at h
      exact h
    simpa using! h1.const_mul B
  have hle : A ≤ 0 := ge_of_tendsto hrpow hstep
  linarith


end SubdiffusiveProcess.CoarseGrainingVocab.Section11

end
