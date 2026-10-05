module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.RandomFactor

@[expose] public section

/-!
# Moment bound for the parameter-balanced Dirichlet random factor

This file completes `e.Dirichlet.random.factor.moment`.  One enlarged fixed
moment controls both response errors and the coefficient-only energy envelope.
Exponent monotonicity on the probability space and Hölder at
`(2q, 2q, q)` then control the two products in the normalized polynomial.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Hölder's inequality in the symmetric exponent form used by the random
factor. -/
private theorem eLpNorm_mul_le_two_mul_exponent
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {q : ℝ} (hq : 0 < q) {X Y : Omega → ℝ}
    (hX : AEStronglyMeasurable X mu) (hY : AEStronglyMeasurable Y mu) :
    eLpNorm (fun omega ↦ X omega * Y omega) (ENNReal.ofReal q) mu ≤
      eLpNorm X (ENNReal.ofReal (2 * q)) mu *
        eLpNorm Y (ENNReal.ofReal (2 * q)) mu := by
  have hholderReal : Real.HolderTriple (2 * q) (2 * q) q := by
    constructor
    · field_simp
      ring
    · positivity
    · positivity
  let : ENNReal.HolderTriple (2 * ENNReal.ofReal q)
      (2 * ENNReal.ofReal q) (ENNReal.ofReal q) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat] using hholderReal.ennrealOfReal
  simpa using
    (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (fun x y : ℝ ↦ x * y) 1 (by fun_prop) hX hY
      (Filter.Eventually.of_forall fun _ ↦ by simp))

/-- The manuscript random factor is bounded below by one whenever all three
random inputs and the deterministic prefactor are nonnegative. -/
theorem one_le_dirichletRandomFactor
    {Omega : Type*} {C delta vartheta s1 s2 : ℝ} {k : ℕ}
    {E1 E2 Y : Omega → ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hE1 : ∀ omega, 0 ≤ E1 omega) (hY : ∀ omega, 0 ≤ Y omega)
    (omega : Omega) :
    1 ≤ dirichletRandomFactor C delta vartheta s1 s2 k E1 E2 Y omega := by
  unfold dirichletRandomFactor
  have hbalanced : 0 ≤ Real.rpow 3 (s1 * (k : ℝ)) * E1 omega * Y omega +
      Real.rpow 3 (-s2 * (k : ℝ)) *
        (1 + Real.rpow 3 (s1 * (k : ℝ)) * E2 omega ^ (2 : ℕ)) := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hE1 omega))
        (hY omega))
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (add_nonneg zero_le_one
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _))))
  have hfirst : 0 ≤ C * Real.rpow delta (-vartheta) *
      (Real.rpow 3 (s1 * (k : ℝ)) * E1 omega * Y omega +
        Real.rpow 3 (-s2 * (k : ℝ)) *
          (1 + Real.rpow 3 (s1 * (k : ℝ)) * E2 omega ^ (2 : ℕ))) :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hdelta.le _)) hbalanced
  have hsecond : 0 ≤ C * Real.rpow delta (-1) * E1 omega * Y omega := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg hdelta.le _)) (hE1 omega))
      (hY omega)
  linarith

/-- Uniform fixed-moment bound for the literal common random factor, with the
optimizing integer and the two response errors chosen exactly as in the
manuscript. -/
theorem exists_dirichletRandomFactor_moment_bound
    (d : ℕ) [NeZero d] {vartheta q C : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1)
    (hq : 1 ≤ q) (hC : 0 ≤ C) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 < B ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
        ∀ L N : ℕ, L ≤ N →
          eLpNorm
              (dirichletRandomFactor C M.delta vartheta
                (dirichletS1 vartheta) (dirichletS2 vartheta)
                (dirichletBalanceScale vartheta M.delta)
                (dirichletFullResponseOne M L N (dirichletS1 vartheta))
                (dirichletFullResponseTwo M L N (dirichletS1 vartheta))
                (dirichletEllipticityEnvelope M L N (dirichletS1 vartheta)))
              (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B := by
  let s := dirichletS1 vartheta
  let xi := 2 * q + 4 * (d : ℝ) * (s / 2)⁻¹
  have hs : 0 < s := by
    dsimp only [s, dirichletS1]
    linarith
  have hsOne : s ≤ 1 := by
    dsimp only [s, dirichletS1]
    linarith
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hxiOne : 1 ≤ xi := by
    dsimp only [xi]
    have hdim0 : 0 ≤ 4 * (d : ℝ) * (s / 2)⁻¹ := by positivity
    linarith
  have hdim : 4 * (d : ℝ) * (s / 2)⁻¹ ≤ xi := by
    dsimp only [xi]
    have : 0 ≤ 2 * q := by positivity
    linarith
  obtain ⟨delta0, R, hdelta0, hR, hmoments⟩ :=
    exists_dirichletResponseAndEllipticity_moment_bound
      hs hsOne hxiOne hdim
  let G := Real.rpow 3 s
  let B := 1 + C + C * (G + 1) * R ^ (2 : ℕ) + C * G * R ^ (2 : ℕ)
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact Real.rpow_nonneg (by norm_num) _
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨delta0, B, hdelta0, hB, ?_⟩
  intro M hM L N hLN
  let E1 := dirichletFullResponseOne M L N s
  let E2 := dirichletFullResponseTwo M L N s
  let Y := dirichletEllipticityEnvelope M L N s
  let X1 : Sample d → ℝ := fun omega ↦ M.delta⁻¹ * E1 omega
  let X2 : Sample d → ℝ := fun omega ↦ M.delta⁻¹ * E2 omega
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaOne : M.delta ≤ 1 :=
    M.shellPrefix.delta_le_half.trans (by norm_num)
  obtain ⟨hE1xi, hE2xi, hYxi⟩ := hmoments M hM L N hLN
  have hE1Meas : AEStronglyMeasurable E1 M.P.toMeasure := by
    exact (measurable_dirichletFullResponseOne M L N s).aestronglyMeasurable
  have hE2Meas : AEStronglyMeasurable E2 M.P.toMeasure := by
    exact (measurable_dirichletFullResponseTwo M L N s).aestronglyMeasurable
  have hYMeas : AEStronglyMeasurable Y M.P.toMeasure := by
    exact ((measurable_const.add
      (measurable_const.mul (measurable_dirichletFullResponseTwo M L N s))) :
        Measurable Y).aestronglyMeasurable
  have hX1Meas : AEStronglyMeasurable X1 M.P.toMeasure := by
    exact hE1Meas.const_mul M.delta⁻¹
  have hX2Meas : AEStronglyMeasurable X2 M.P.toMeasure := by
    exact hE2Meas.const_mul M.delta⁻¹
  have hX1xi : eLpNorm X1 (ENNReal.ofReal xi) M.P.toMeasure ≤
      ENNReal.ofReal R := by
    calc
      eLpNorm X1 (ENNReal.ofReal xi) M.P.toMeasure =
          ENNReal.ofReal M.delta⁻¹ *
            eLpNorm E1 (ENNReal.ofReal xi) M.P.toMeasure := by
        change eLpNorm (M.delta⁻¹ • E1) (ENNReal.ofReal xi) M.P.toMeasure = _
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr hdelta.le)]
      _ ≤ ENNReal.ofReal M.delta⁻¹ * ENNReal.ofReal (R * M.delta) := by
        gcongr
      _ = ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hdelta.le)]
        congr 1
        field_simp
  have hX2xi : eLpNorm X2 (ENNReal.ofReal xi) M.P.toMeasure ≤
      ENNReal.ofReal R := by
    calc
      eLpNorm X2 (ENNReal.ofReal xi) M.P.toMeasure =
          ENNReal.ofReal M.delta⁻¹ *
            eLpNorm E2 (ENNReal.ofReal xi) M.P.toMeasure := by
        change eLpNorm (M.delta⁻¹ • E2) (ENNReal.ofReal xi) M.P.toMeasure = _
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr hdelta.le)]
      _ ≤ ENNReal.ofReal M.delta⁻¹ * ENNReal.ofReal (R * M.delta) := by
        gcongr
      _ = ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hdelta.le)]
        congr 1
        field_simp
  have htwoqXi : ENNReal.ofReal (2 * q) ≤ ENNReal.ofReal xi :=
    ENNReal.ofReal_le_ofReal (by
      dsimp only [xi]
      have : 0 ≤ 4 * (d : ℝ) * (s / 2)⁻¹ := by positivity
      linarith)
  have hX1two : eLpNorm X1 (ENNReal.ofReal (2 * q)) M.P.toMeasure ≤
      ENNReal.ofReal R :=
    (eLpNorm_le_eLpNorm_of_exponent_le htwoqXi).trans hX1xi
  have hX2two : eLpNorm X2 (ENNReal.ofReal (2 * q)) M.P.toMeasure ≤
      ENNReal.ofReal R :=
    (eLpNorm_le_eLpNorm_of_exponent_le htwoqXi).trans hX2xi
  have hYtwo : eLpNorm Y (ENNReal.ofReal (2 * q)) M.P.toMeasure ≤
      ENNReal.ofReal R :=
    (eLpNorm_le_eLpNorm_of_exponent_le htwoqXi).trans hYxi
  let XY : Sample d → ℝ := fun omega ↦ X1 omega * Y omega
  let X2sq : Sample d → ℝ := fun omega ↦ X2 omega ^ (2 : ℕ)
  have hXYMeas : AEStronglyMeasurable XY M.P.toMeasure := hX1Meas.mul hYMeas
  have hX2sqMeas : AEStronglyMeasurable X2sq M.P.toMeasure := hX2Meas.pow 2
  have hXYNorm : eLpNorm XY (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (R ^ (2 : ℕ)) := by
    calc
      eLpNorm XY (ENNReal.ofReal q) M.P.toMeasure ≤
          eLpNorm X1 (ENNReal.ofReal (2 * q)) M.P.toMeasure *
            eLpNorm Y (ENNReal.ofReal (2 * q)) M.P.toMeasure :=
        eLpNorm_mul_le_two_mul_exponent hq0 hX1Meas hYMeas
      _ ≤ ENNReal.ofReal R * ENNReal.ofReal R := mul_le_mul' hX1two hYtwo
      _ = ENNReal.ofReal (R ^ (2 : ℕ)) := by
        rw [pow_two, ENNReal.ofReal_mul hR.le]
  have hX2sqNorm : eLpNorm X2sq (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (R ^ (2 : ℕ)) := by
    calc
      eLpNorm X2sq (ENNReal.ofReal q) M.P.toMeasure ≤
          eLpNorm X2 (ENNReal.ofReal (2 * q)) M.P.toMeasure *
            eLpNorm X2 (ENNReal.ofReal (2 * q)) M.P.toMeasure := by
        simpa [X2sq, pow_two] using
          eLpNorm_mul_le_two_mul_exponent hq0 hX2Meas hX2Meas
      _ ≤ ENNReal.ofReal R * ENNReal.ofReal R := mul_le_mul' hX2two hX2two
      _ = ENNReal.ofReal (R ^ (2 : ℕ)) := by
        rw [pow_two, ENNReal.ofReal_mul hR.le]
  let P : Sample d → ℝ := fun omega ↦
    (1 + C) + (C * (G + 1)) * XY omega + (C * G) * X2sq omega
  have hqENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  have hPNorm : eLpNorm P (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B := by
    have hConstMeas : AEStronglyMeasurable
        (fun _ : Sample d ↦ (1 + C : ℝ)) M.P.toMeasure :=
      aestronglyMeasurable_const
    have hXYScaledMeas : AEStronglyMeasurable
        (fun omega ↦ (C * (G + 1)) * XY omega) M.P.toMeasure :=
      hXYMeas.const_mul _
    have hX2ScaledMeas : AEStronglyMeasurable
        (fun omega ↦ (C * G) * X2sq omega) M.P.toMeasure :=
      hX2sqMeas.const_mul _
    have htriangleOne := eLpNorm_add_le
      (f := fun _ : Sample d => (1 + C : ℝ))
      (g := fun omega => (C * (G + 1)) * XY omega)
      (μ := M.P.toMeasure) hqENN
    have htriangleTwo := eLpNorm_add_le
      (f := (fun _ : Sample d => (1 + C : ℝ)) +
        (fun omega => (C * (G + 1)) * XY omega))
      (g := fun omega => (C * G) * X2sq omega)
      (μ := M.P.toMeasure) hqENN
    have hconstNorm : eLpNorm (fun _ : Sample d ↦ (1 + C : ℝ))
        (ENNReal.ofReal q) M.P.toMeasure = ENNReal.ofReal (1 + C) := by
      rw [eLpNorm_const (1 + C) (ENNReal.ofReal_pos.mpr hq0).ne'
        (NeZero.ne M.P.toMeasure)]
      rw [Real.enorm_eq_ofReal (by linarith)]
      simp
    have hXYScaledNorm : eLpNorm (fun omega ↦ (C * (G + 1)) * XY omega)
        (ENNReal.ofReal q) M.P.toMeasure =
          ENNReal.ofReal (C * (G + 1)) *
            eLpNorm XY (ENNReal.ofReal q) M.P.toMeasure := by
      change eLpNorm ((C * (G + 1)) • XY) (ENNReal.ofReal q) M.P.toMeasure = _
      rw [eLpNorm_const_smul,
        Real.enorm_eq_ofReal (mul_nonneg hC (add_nonneg hG zero_le_one))]
    have hX2ScaledNorm : eLpNorm (fun omega ↦ (C * G) * X2sq omega)
        (ENNReal.ofReal q) M.P.toMeasure =
          ENNReal.ofReal (C * G) *
            eLpNorm X2sq (ENNReal.ofReal q) M.P.toMeasure := by
      change eLpNorm ((C * G) • X2sq) (ENNReal.ofReal q) M.P.toMeasure = _
      rw [eLpNorm_const_smul,
        Real.enorm_eq_ofReal (mul_nonneg hC hG)]
    calc
      eLpNorm P (ENNReal.ofReal q) M.P.toMeasure ≤
          eLpNorm (fun omega ↦ (1 + C : ℝ) +
            (C * (G + 1)) * XY omega) (ENNReal.ofReal q) M.P.toMeasure +
          eLpNorm (fun omega ↦ (C * G) * X2sq omega)
            (ENNReal.ofReal q) M.P.toMeasure := htriangleTwo
      _ ≤ (eLpNorm (fun _ : Sample d ↦ (1 + C : ℝ))
            (ENNReal.ofReal q) M.P.toMeasure +
          eLpNorm (fun omega ↦ (C * (G + 1)) * XY omega)
            (ENNReal.ofReal q) M.P.toMeasure) +
          eLpNorm (fun omega ↦ (C * G) * X2sq omega)
            (ENNReal.ofReal q) M.P.toMeasure :=
        add_le_add htriangleOne le_rfl
      _ ≤ ENNReal.ofReal (1 + C) +
          ENNReal.ofReal (C * (G + 1)) * ENNReal.ofReal (R ^ (2 : ℕ)) +
          ENNReal.ofReal (C * G) * ENNReal.ofReal (R ^ (2 : ℕ)) := by
        rw [hconstNorm, hXYScaledNorm, hX2ScaledNorm]
        gcongr
      _ = ENNReal.ofReal B := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hC (add_nonneg hG zero_le_one)),
          ← ENNReal.ofReal_mul (mul_nonneg hC hG),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hfactorNonneg : ∀ omega,
      0 ≤ dirichletRandomFactor C M.delta vartheta s
        (dirichletS2 vartheta) (dirichletBalanceScale vartheta M.delta)
        E1 E2 Y omega := fun omega ↦
    zero_le_one.trans (one_le_dirichletRandomFactor hC hdelta
      (fun x ↦ dirichletFullResponseOne_nonneg M L N s x)
      (fun x ↦ zero_le_one.trans
        (one_le_dirichletEllipticityEnvelope M L N s x)) omega)
  have hPNonneg : ∀ omega, 0 ≤ P omega := by
    intro omega
    have hX1 : 0 ≤ X1 omega := mul_nonneg (inv_nonneg.mpr hdelta.le)
      (dirichletFullResponseOne_nonneg M L N s omega)
    have hX2sq : 0 ≤ X2sq omega := by
      dsimp only [X2sq]
      exact sq_nonneg _
    have hXY : 0 ≤ XY omega := mul_nonneg hX1
      (zero_le_one.trans (one_le_dirichletEllipticityEnvelope M L N s omega))
    dsimp only [P]
    exact add_nonneg
      (add_nonneg (add_nonneg zero_le_one hC)
        (mul_nonneg (mul_nonneg hC (add_nonneg hG zero_le_one)) hXY))
      (mul_nonneg (mul_nonneg hC hG) hX2sq)
  have hpoint : ∀ omega,
      dirichletRandomFactor C M.delta vartheta s
          (dirichletS2 vartheta) (dirichletBalanceScale vartheta M.delta)
          E1 E2 Y omega ≤ P omega := by
    intro omega
    have hmain := dirichletRandomFactor_le_normalized
      hvartheta hvarthetaOne hdelta hdeltaOne hC
      (mul_nonneg (inv_nonneg.mpr hdelta.le)
        (dirichletFullResponseOne_nonneg M L N s omega))
      (mul_nonneg (inv_nonneg.mpr hdelta.le)
        (dirichletFullResponseTwo_nonneg M L N s omega))
      (zero_le_one.trans (one_le_dirichletEllipticityEnvelope M L N s omega))
      (X1 := X1 omega) (X2 := X2 omega) (Y := Y omega)
    have hE1eq : M.delta * X1 omega = E1 omega := by
      dsimp only [X1]
      field_simp
    have hE2eq : M.delta * X2 omega = E2 omega := by
      dsimp only [X2]
      field_simp
    have hleft :
        dirichletRandomFactor C M.delta vartheta s
            (dirichletS2 vartheta) (dirichletBalanceScale vartheta M.delta)
            (fun _ : Unit ↦ M.delta * X1 omega)
            (fun _ : Unit ↦ M.delta * X2 omega) (fun _ : Unit ↦ Y omega) () =
          dirichletRandomFactor C M.delta vartheta s
            (dirichletS2 vartheta) (dirichletBalanceScale vartheta M.delta)
            E1 E2 Y omega := by
      unfold dirichletRandomFactor
      rw [hE1eq, hE2eq]
    rw [hleft] at hmain
    calc
      dirichletRandomFactor C M.delta vartheta s
          (dirichletS2 vartheta) (dirichletBalanceScale vartheta M.delta)
          E1 E2 Y omega ≤
        1 + C * (G * X1 omega * Y omega + 1 + G * X2 omega ^ (2 : ℕ)) +
          C * (X1 omega * Y omega) := by simpa [s, G] using hmain
      _ = P omega := by
        dsimp only [P, XY, X2sq]
        ring
  change eLpNorm
      (dirichletRandomFactor C M.delta vartheta s
        (dirichletS2 vartheta) (dirichletBalanceScale vartheta M.delta)
        E1 E2 Y) (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B
  have hfactorMeas : AEStronglyMeasurable
      (dirichletRandomFactor C M.delta vartheta s
        (dirichletS2 vartheta) (dirichletBalanceScale vartheta M.delta)
        E1 E2 Y) M.P.toMeasure := by
    unfold dirichletRandomFactor
    fun_prop
  exact (eLpNorm_mono_enorm_ae hfactorMeas (Filter.Eventually.of_forall fun omega ↦ by
    rw [Real.enorm_eq_ofReal (hfactorNonneg omega),
      Real.enorm_eq_ofReal (hPNonneg omega)]
    exact ENNReal.ofReal_le_ofReal (hpoint omega))).trans hPNorm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
