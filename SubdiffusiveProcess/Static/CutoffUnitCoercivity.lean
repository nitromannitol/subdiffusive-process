module

public import SubdiffusiveProcess.Static.KilledReadout
public import SubdiffusiveProcess.Static.CutoffUnitEnergy
public import SubdiffusiveProcess.Static.CutoffMassMomentBound

@[expose] public section

/-! # Uniform finite-cutoff coercivity in unit coordinates

The cutoff may lie below the physical domain scale. The random factor is
measurable, at least one everywhere, and has every fixed moment uniformly
in the cutoff, scale and arbitrary real translation at small disorder.
-/

open MeasureTheory Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Static
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

private theorem readout_of_coarse_bound {S E : ℝ≥0∞} {C N R t : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hS : S ≤ ENNReal.ofReal (C * N)) (hN : N ≤ R * t)
    (ht : ENNReal.ofReal t ≤ E) : S ≤ ENNReal.ofReal (C * R) * E := by
  refine (hS.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hN hC))).trans ?_
  rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hC hR)]
  exact mul_le_mul_right ht _

/-- Both coercivity clauses use one measurable ellipticity multiplier. -/
theorem exists_cutoff_unit_coercivity_constant (d : ℕ) [NeZero d] :
    ∃ D : ℝ, 0 < D ∧ ∀ (M : GMCModel d) (L m : ℕ) (z : Vec d),
      ∀ᵐ ω ∂M.P.toMeasure,
        (∀ H : H1Function (openCubeSet (originCube d 0)),
          fractionalSqNorm (openCubeSet (originCube d 0)) H.toFun ≤
            ENNReal.ofReal (1 + D * cutoffLowerInv M L m z ω) *
              (energy (openCubeSet (originCube d 0))
                (fun x => (ahom M L)⁻¹ * aCutoff M L (translatePotentialSample z ω)
                  ((3 : ℝ) ^ m • x)) H.grad +
                ∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (H.toFun x ^ 2))) ∧
        (∀ H : H10Function (openCubeSet (originCube d 0)),
          fractionalSqNorm (openCubeSet (originCube d 0)) H.toFun ≤
            ENNReal.ofReal (1 + D * cutoffLowerInv M L m z ω) *
              energy (openCubeSet (originCube d 0))
                (fun x => (ahom M L)⁻¹ * aCutoff M L (translatePotentialSample z ω)
                  ((3 : ℝ) ^ m • x)) H.grad) := by
  obtain ⟨Cf, hCf, hf⟩ := exists_unit_fractional_kernel_readout d
  obtain ⟨Ck, hCk, hk⟩ := exists_unit_killed_readout d
  let G : ℝ := paperPoincareGeometricFactor (1 / 16) (.finite 1) ^ 2
  have hG : 0 ≤ G := sq_nonneg _
  let D : ℝ := 1 + (Cf + Ck) * G
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro M L m z
  filter_upwards [cutoff_rescaledCoarsePoincare_ae M L m z] with ω hω
  let X := cutoffLowerInv M L m z ω
  have hX : 0 ≤ X := cutoffLowerInv_nonneg M L m z ω
  have hRX : 0 ≤ G * X := mul_nonneg hG hX
  have hDsum : (Cf + Ck) * G ≤ D := by dsimp only [D]; linarith
  have hDf : Cf * G ≤ D := by
    have := mul_nonneg hCk.le hG
    dsimp only [D]
    nlinarith
  have hAone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + D * X) := by
    exact ENNReal.one_le_ofReal.mpr (by nlinarith only [hD.le, hX])
  have hAf : ENNReal.ofReal (Cf * (G * X)) ≤ ENNReal.ofReal (1 + D * X) := by
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right hDf hX
    nlinarith only [h]
  constructor
  · intro H
    have hfrac := readout_of_coarse_bound hCf.le hRX (hf H) (hω H)
      (cutoffUnitEnergy_le_energy M L m (translatePotentialSample z ω) H.grad)
    change fractionalSeminormSq (openCubeSet (originCube d 0)) H.toFun +
      (∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (H.toFun x ^ 2)) ≤ _
    rw [mul_add]
    apply add_le_add (hfrac.trans (mul_le_mul_left hAf _))
    simpa only [one_mul] using! mul_le_mul_left hAone
      (∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (H.toFun x ^ 2))
  · intro H
    have henergy := cutoffUnitEnergy_le_energy M L m (translatePotentialSample z ω) H.grad
    have hfrac := readout_of_coarse_bound hCf.le hRX (hf H.toH1Function)
      (hω H.toH1Function) henergy
    have hl2 := readout_of_coarse_bound hCk.le hRX (hk H) (hω H.toH1Function) henergy
    change fractionalSeminormSq (openCubeSet (originCube d 0)) H.toFun +
      (∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (H.toFun x ^ 2)) ≤ _
    refine (add_le_add hfrac hl2).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hCf.le hRX) (mul_nonneg hCk.le hRX)]
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right hDsum hX
    nlinarith only [h]

/-- The finite-cutoff coercivity supplier with all scale and moment premises
closed. In particular, it covers the physical regime `m > L`. -/
theorem exists_uniform_cutoff_unit_coercivity (d : ℕ) [NeZero d] (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 → ∀ L m : ℕ, L ≤ m → ∀ z : Vec d,
        ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂M.P.toMeasure) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ω ∂M.P.toMeasure,
            (∀ H : H1Function (openCubeSet (originCube d 0)),
              fractionalSqNorm (openCubeSet (originCube d 0)) H.toFun ≤
                ENNReal.ofReal (K ω) *
                  (energy (openCubeSet (originCube d 0))
                    (fun x => (ahom M L)⁻¹ * aCutoff M L (translatePotentialSample z ω)
                      ((3 : ℝ) ^ m • x)) H.grad +
                    ∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (H.toFun x ^ 2))) ∧
            (∀ H : H10Function (openCubeSet (originCube d 0)),
              fractionalSqNorm (openCubeSet (originCube d 0)) H.toFun ≤
                ENNReal.ofReal (K ω) *
                  energy (openCubeSet (originCube d 0))
                    (fun x => (ahom M L)⁻¹ * aCutoff M L (translatePotentialSample z ω)
                      ((3 : ℝ) ^ m • x)) H.grad) := by
  obtain ⟨D, hD, hcoer⟩ := exists_cutoff_unit_coercivity_constant d
  let r := max q (64 * (d : ℝ))
  have hr : 1 ≤ r := hq.trans (le_max_left _ _)
  have hdr : 64 * (d : ℝ) ≤ r := le_max_right _ _
  obtain ⟨δ0, B, hδ0, hB, hnorm⟩ := exists_uniform_cutoffLowerInv_moment_bound (d := d) r hr hdr
  let C : ℝ := (1 + D * B) ^ q
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨δ0, C, hδ0, hC, ?_⟩
  intro M hM L m hLm z
  let X := cutoffLowerInv M L m z
  let K : PotentialSample d → ℝ := fun ω => 1 + D * X ω
  have hXmeas : Measurable X := measurable_cutoffLowerInv M L m z
  have hKmeas : Measurable K := measurable_const.add (measurable_const.mul hXmeas)
  have hKone : ∀ ω, 1 ≤ K ω := fun ω =>
    le_add_of_nonneg_right (mul_nonneg hD.le (cutoffLowerInv_nonneg M L m z ω))
  have hXnorm : eLpNorm X (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (le_max_left _ _))).trans (hnorm M hM L m hLm z)
  have hKn : eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal (1 + D * B) := by
    have hDX : AEStronglyMeasurable (fun ω => D * X ω) M.P.toMeasure :=
      (measurable_const.mul hXmeas).aestronglyMeasurable
    refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
    have hconst : eLpNorm (fun _ : PotentialSample d => (1 : ℝ)) (ENNReal.ofReal q)
        M.P.toMeasure = 1 := by
      rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hq)).ne' (NeZero.ne M.P.toMeasure)]
      simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
    have hscale : eLpNorm (fun ω => D * X ω) (ENNReal.ofReal q) M.P.toMeasure =
        ENNReal.ofReal D * eLpNorm X (ENNReal.ofReal q) M.P.toMeasure := by
      simpa only [Pi.smul_apply, smul_eq_mul, Real.enorm_eq_ofReal hD.le] using!
        eLpNorm_const_smul D X (ENNReal.ofReal q) M.P.toMeasure
    rw [hconst, hscale, ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_mul hD.le]
    exact add_le_add le_rfl (mul_le_mul_right hXnorm _)
  have hmoment : (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂M.P.toMeasure) ≤ ENNReal.ofReal C := by
    rw [lintegral_rpow_eq_eLpNorm_rpow_of_aestronglyMeasurable M.P.toMeasure K
      (fun ω => zero_le_one.trans (hKone ω)) (zero_lt_one.trans_le hq) hKmeas.aestronglyMeasurable]
    change _ ≤ ENNReal.ofReal ((1 + D * B) ^ q)
    exact (ENNReal.rpow_le_rpow hKn (zero_le_one.trans hq)).trans_eq
      (ENNReal.ofReal_rpow_of_nonneg (by positivity) (zero_le_one.trans hq))
  exact ⟨K, hKmeas, hKone, hmoment, hcoer M L m z⟩

end SubdiffusiveProcess.Static
