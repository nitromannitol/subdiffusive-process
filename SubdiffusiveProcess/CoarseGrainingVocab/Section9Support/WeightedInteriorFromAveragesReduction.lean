module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedInteriorFromAveragesUnit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedInteriorFromAveragesGridRepair
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import Homogenization.Sobolev.Foundations.EuclideanL2CZ

@[expose] public section

/-!
# The frozen interior estimate contains De Giorgi–Nash–Moser local boundedness

`SubdiffusiveProcess/Section9/WeightedInteriorFromAverages.lean` (the weighted
interior-from-averages anchor, v2) quantifies over **every** `L > 0`.  Its
third quantitative input — the averaged oscillation decay — is guarded by `1 ≤ r`, `r ≤ L` and
`centeredAxisCube y (2 * r) ⊆ centeredAxisCube zQ L`, so at `L = 1` it has no
instances at all: `IsGridCube` forces `r = 3 ^ m`, and `1 ≤ r ≤ 1` forces
`r = 1`, at which the extra scale guard
`C0 * (1 + log A + log (L / r)) < ⌊logb 3 r⌋` reads `C0 * (1 + log A) < 0`.

At `rho = b = 1` the two remaining inputs (mass and `∇ log b`) are satisfied by
every multiplier.  What is left of the first conclusion is exactly the
De Giorgi–Nash–Moser local boundedness estimate for a divergence-form operator
whose coefficient is an arbitrary Lebesgue-measurable multiplier with values in
`[1/2, 2]`, i.e. of ellipticity ratio `4`, with a constant depending on nothing
but `d`.

`localBoundedness_of_weighted_interior_from_averages` is the machine-checked
reduction.  It is a statement *about* the frozen type, transcribed into the
`hanchor` binder without applying the source wrapper, in the style of
`WeightedInteriorFromAveragesRefutation.lean`.  The
statement is true and non-vacuous.  It records that no proof of it can
avoid a local-boundedness theorem at bounded ellipticity ratio.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The De Giorgi–Nash–Moser local boundedness estimate at ellipticity ratio `4`:
a constant depending on the dimension alone bounds a weak solution of
`∇ · (theta ∇ h) = 0` pointwise on the middle quarter of a unit cube by its
`L ^ 2` norm on the cube, for **every** measurable multiplier `theta` with
values in `[1/2, 2]`.  The cube has unit volume, so no normalisation appears. -/
def LocalBoundednessAtRatioFour (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (theta : Vec d → ℝ) (zQ : Vec d),
      (∀ x, 1 / 2 ≤ theta x ∧ theta x ≤ 2) →
      AEStronglyMeasurable theta (volume.restrict (centeredAxisCube zQ 1)) →
      ∀ h : Vec d → ℝ, WeakHarmonic theta (centeredAxisCube zQ 1) h →
        ∀ x ∈ centeredAxisCube zQ (1 / 4),
          ENNReal.ofReal |h x| ≤
            ENNReal.ofReal C * eLpNorm h 2 (volume.restrict (centeredAxisCube zQ 1))

/-- Volume of an axis cube, in `ℝ≥0∞`. -/
theorem volume_centeredAxisCube_eq {d : ℕ} (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    volume (centeredAxisCube x L) = ENNReal.ofReal (L ^ d) := by
  have htop : volume (centeredAxisCube x L) ≠ ⊤ := volume_axisCube_ne_top _ _
  rw [← ENNReal.ofReal_toReal htop, SubdiffusiveProcess.Section9.volume_centeredAxisCube_toReal x hL]

/-- The unit cube has unit volume. -/
theorem volume_centeredAxisCube_one {d : ℕ} (x : Vec d) :
    volume (centeredAxisCube x (1 : ℝ)) = 1 := by
  rw [volume_centeredAxisCube_eq x (by norm_num : (0:ℝ) ≤ 1), one_pow, ENNReal.ofReal_one]

/-- The mass input of the frozen block at `rho = 1`, `L = 1`, `A = 2`, `C0 = 1`,
`D = d`. -/
theorem unit_mass_bound' {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) (zQ : Vec d) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(1 : ℝ)) * (r / 1) ^ ((d : ℕ) : ℝ)) *
      weightedMeasure (fun _ : Vec d => (1 : ℝ)) (centeredAxisCube zQ 1) ≤
      weightedMeasure (fun _ : Vec d => (1 : ℝ)) (centeredAxisCube y r) := by
  rw [weightedMeasure_one, volume_centeredAxisCube_one zQ,
    volume_centeredAxisCube_eq y hr.le, mul_one]
  apply ENNReal.ofReal_le_ofReal
  have hpow : (r / 1 : ℝ) ^ ((d : ℕ) : ℝ) = r ^ d := by
    rw [div_one, Real.rpow_natCast]
  rw [hpow, Real.rpow_neg_one]
  have : (0 : ℝ) ≤ r ^ d := pow_nonneg hr.le d
  nlinarith

/-- The `∇ log b` input of the frozen block at `b = 1`, in every dimension. -/
theorem unit_derivative_bound' {d : ℕ} (y : Vec d) :
    supNormOn (centeredAxisCube y 2)
        (fun x => euclideanNorm (euclideanGradient
          (fun _ : Vec d => Real.log (1 : ℝ)) x)) ^ 2 ≤
      (1 : ℝ) * (Real.log 2 + Real.log (2 + 1)) := by
  have hy : y ∈ centeredAxisCube y 2 := by
    intro i _
    change y i - 2 / 2 < y i ∧ y i < y i - 2 / 2 + 2
    constructor <;> linarith
  have hg (x : Vec d) : euclideanGradient (fun _ : Vec d => Real.log (1 : ℝ)) x = 0 := by
    funext i
    simp [euclideanGradient, euclideanCoordDeriv]
  have hsup : supNormOn (centeredAxisCube y 2)
      (fun x => euclideanNorm (euclideanGradient
        (fun _ : Vec d => Real.log (1 : ℝ)) x)) = 0 := by
    simp only [hg, euclideanNorm_zero, supNormOn, abs_zero]
    have hs : {t : ℝ | ∃ x ∈ centeredAxisCube y 2, t = 0} = {0} := by
      ext t
      exact ⟨fun ⟨_, _, ht⟩ => ht, fun ht => ⟨y, hy, ht⟩⟩
    rw [hs, csSup_singleton]
  rw [hsup]
  have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, one_mul]
  exact add_nonneg h2 h3

/-- **The frozen interior estimate implies De Giorgi–Nash–Moser local
boundedness at ellipticity ratio `4`.**  `hanchor` is the exact frozen type of
`SubdiffusiveProcess.Section9.weighted_interior_from_averages`, transcribed verbatim. -/
theorem localBoundedness_of_weighted_interior_from_averages
    (d : ℕ) (hd : 2 ≤ d)
    (hanchor :
∀ (d : ℕ) (_hd : 2 ≤ d) (alpha D C0 p0 lam : ℝ)
    (_halpha0 : 0 < alpha) (_halpha1 : alpha < 1) (_hD : 0 ≤ D) (_hC0 : 1 ≤ C0)
    (_hp0 : 2 < p0) (grid : Finset (Vec d))
    (_hgrid : HasMiddleSixteenthCover grid lam),
    ∃ (C : ℝ) (J : ℕ), 0 < C ∧
      ∀ (rho b theta : Vec d → ℝ) (zQ : Vec d) (L A : ℝ),
        0 < L → 2 ≤ A →
        (∀ K : Set (Vec d), IsCompact K →
          CoefficientOn K rho ∧ CoefficientOn K (fun x => (rho x)⁻¹)) →
        (∀ x, 0 < b x) → ContDiff ℝ 1 b →
        (∀ x, 1 / 2 ≤ theta x ∧ theta x ≤ 2) →
        AEStronglyMeasurable theta (volume.restrict (centeredAxisCube zQ L)) →
        (∀ (y : Vec d) (r : ℝ), IsGridCube grid y r → 0 < r → r ≤ L →
          centeredAxisCube y (2 * r) ⊆ centeredAxisCube zQ L →
          ENNReal.ofReal (A ^ (-C0) * (r / L) ^ D) *
              weightedMeasure rho (centeredAxisCube zQ L) ≤
            weightedMeasure rho (centeredAxisCube y r)) →
        (∀ y : Vec d, (centeredAxisCube y 1 ∩ centeredAxisCube zQ L).Nonempty →
          supNormOn (centeredAxisCube y 2)
              (fun x => euclideanNorm (euclideanGradient (fun w => Real.log (b w)) x)) ^ 2 ≤
            C0 * (Real.log A + Real.log (2 + L))) →
        (∀ (y : Vec d) (r : ℝ), IsGridCube grid y r → 1 ≤ r → r ≤ L →
          centeredAxisCube y (2 * r) ⊆ centeredAxisCube zQ L →
          C0 * (1 + Real.log A + Real.log (L / r)) < (⌊Real.logb 3 r⌋ : ℝ) →
          ∀ h : Vec d → ℝ,
            WeakHarmonic (fun x => b x * theta x) (centeredAxisCube y r) h →
            (∃ K : ℝ, ∀ x ∈ centeredAxisCube y r, |h x| ≤ K) →
            ∀ (z : Vec d) (varrho : ℝ), IsGridCube grid z varrho →
              1 ≤ varrho → varrho ≤ r / C0 →
              centeredAxisCube z varrho ⊆ centeredAxisCube y (r / 4) →
              normalizedL2On (centeredAxisCube z varrho)
                  (fun x => h x - averageOn (centeredAxisCube z varrho) h) ≤
                A ^ C0 * (L / r) ^ C0 * (varrho / r) ^ alpha *
                  oscillationOn (centeredAxisCube y r) h) →
        (∀ h : Vec d → ℝ,
          WeakHarmonic (fun x => b x * theta x) (centeredAxisCube zQ L) h →
          ∀ x ∈ centeredAxisCube zQ (L / 4),
          ENNReal.ofReal |h x| ≤
            ENNReal.ofReal (C * A ^ C) *
              weightedMeasure rho (centeredAxisCube zQ L) ^ (-(1 / 2) : ℝ) *
              eLpNorm h 2
                ((weightedMeasure rho).restrict (centeredAxisCube zQ L))) ∧
        (∀ F : ℝ, 0 < F →
          (∀ (y : Vec d) (r : ℝ), IsGridCube grid y r →
            centeredAxisCube y r ⊆ centeredAxisCube zQ L →
            SobolevAssumption (fun x => b x * theta x) rho
                (centeredAxisCube y r) p0 (A ^ C0) F ∧
              PoincareAssumption (fun x => b x * theta x) rho
                (centeredAxisCube y r) (A ^ C0) F) →
          ∀ s : ℝ, 0 < s → ∀ u : H1Function (centeredAxisCube zQ L),
            SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
              (fun x => b x * theta x) rho s⁻¹ (centeredAxisCube zQ L) u
              (fun _ => (0 : ℝ)) →
            ∀ uc : Vec d → ℝ, ContinuousOn uc (centeredAxisCube zQ L) →
              (∀ᵐ x ∂(volume.restrict (centeredAxisCube zQ L)), uc x = u.toFun x) →
              ∀ x ∈ centeredAxisCube zQ (L / 4),
              ENNReal.ofReal |uc x| ≤
                ENNReal.ofReal (C * A ^ C * (1 + F / s) ^ J) *
                  weightedMeasure rho (centeredAxisCube zQ L) ^ (-(1 / 2) : ℝ) *
                  eLpNorm u.toFun 2
                    ((weightedMeasure rho).restrict (centeredAxisCube zQ L)))) :
    LocalBoundednessAtRatioFour d := by
  obtain ⟨grid, hgrid⟩ := exists_hasMiddleSixteenthCover d
  obtain ⟨C, J, hC, hmain⟩ :=
    hanchor d hd (1 / 2) ((d : ℕ) : ℝ) 1 3 192 (by norm_num) (by norm_num)
      (by positivity) le_rfl (by norm_num) grid hgrid
  refine ⟨C * (2 : ℝ) ^ C, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) C), ?_⟩
  intro theta zQ hthetaB hthetaM h hharm x hx
  have hb1 : (fun x : Vec d => (1 : ℝ) * theta x) = theta := by funext y; ring
  have hspec := hmain (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) theta zQ 1 2
      (by norm_num) le_rfl
      (fun K _ => ⟨coefficientOn_one K, by simpa using coefficientOn_one (d := d) K⟩)
      (fun _ => one_pos) contDiff_const hthetaB hthetaM
      (fun y r _ hr _ _ => unit_mass_bound' y hr zQ)
      (fun y _ => unit_derivative_bound' y)
      (fun y r _ hr hr1 _ hguard =>
        (unit_scale_threshold_impossible (C0 := 1) (A := 2) (r := r)
          le_rfl (by norm_num) hr hr1 hguard).elim)
  have hfirst := hspec.1 h (by rw [hb1]; exact hharm) x (by norm_num at hx ⊢; exact hx)
  rw [weightedMeasure_one, volume_centeredAxisCube_one zQ, ENNReal.one_rpow, mul_one] at hfirst
  exact hfirst

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
