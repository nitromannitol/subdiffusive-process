module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepProjectedEnergyBound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepThermodynamicAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepVariationalPatching

@[expose] public section

/-!
# Finite-volume assembly for the Section 5 one-step estimates

This module is the literal assembly layer for Steps 2--3.

The first theorem inserts the already constructed finite cell patch into the
public Dirichlet minimum defining `aMatrix`.  The remaining theorems perform
the exact scalar aggregation of the principal, mixed, and oscillatory cell
energies and insert the sharp stationary projected-energy estimate.  They
leave no hidden numerical absorption: the output has precisely the
penultimate shape consumed by `one_step_upper_of_penultimate` and
`one_step_lower_of_penultimate`.

The variational carrier is connected to the coarse matrix before the scalar one-step estimate is applied.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-! ## The patched Dirichlet competitor enters the coarse matrix -/

/-- Any finite fold of zero-trace cell corrections is an admissible competitor
for the Dirichlet minimum defining the finite-volume coarse matrix.  This is
the formal content of the competitor insertion; partitioning its energy into cells is a separate
identity. -/
theorem vecDot_aMatrix_le_patchedCompetitorEnergy {d : ℕ}
    {a : Vec d → ℝ} {U : Homogenization.Book.Ch02.Domain d}
    (ha : ScalarCoeffOnData U a) (ha0 : ∀ x, 0 ≤ a x)
    (p : Vec d) (w : H10Function (U : Set (Vec d)))
    (patches : List (H10Function (U : Set (Vec d)))) :
    vecDot p (matVecMul (aMatrix U ha.toCoeffOn) p) ≤
      (volume (U : Set (Vec d))).toReal⁻¹ *
        dirichletEnergyOn' a (U : Set (Vec d)) p
          (oneStepPatchedCompetitor w patches).toH1Function.grad := by
  rw [vecDot_aMatrix_eq_dirichletInfOn ha ha0 p]
  exact mul_le_mul_of_nonneg_left
    (dirichletInfOn_le U.measurableSet ha0
      (oneStepPatchedCompetitor w patches))
    (inv_nonneg.mpr (volume_toReal_pos U).le)

/-! ## The sharp stationary principal factors -/

/-- The primal stationary correction contributes the printed negative drift
`-2 tauSq h / d`, up to the fourth-order remainder. -/
theorem oneStep_primalProjectedFactor_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    1 - oneStepProjectedEnergy M n h p hh ≤
      1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
        oneStepProjectedEnergyErrorConst * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  have h := abs_oneStepProjectedEnergy_sub_two_tauSq_mul_div_dimension_le
    M n h p hh hp hscale
  rw [abs_le] at h
  linarith

/-- The dual stationary correction contributes the printed positive drift
`+2 tauSq h / d`, up to the same fourth-order remainder. -/
theorem oneStep_dualProjectedFactor_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    1 + oneStepProjectedEnergy M n h p hh ≤
      1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
        oneStepProjectedEnergyErrorConst * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  have h := abs_oneStepProjectedEnergy_sub_two_tauSq_mul_div_dimension_le
    M n h p hh hp hscale
  rw [abs_le] at h
  linarith

/-! ## Scalar Step 2--3 aggregation -/

private theorem pow_thirty_le_pow_fifteen {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    delta ^ 30 ≤ delta ^ 15 := by
  have hpow0 : 0 ≤ delta ^ 15 := pow_nonneg hdelta0 15
  have hpow1 : delta ^ 15 ≤ 1 := pow_le_one₀ hdelta0 hdelta1
  calc
    delta ^ 30 = (delta ^ 15) ^ 2 := by ring
    _ ≤ delta ^ 15 := by nlinarith

/-- Assemble the primal penultimate inequality from the four literal pieces
of Steps 2--3: the principal cell energy, the mixed term, the oscillatory
energy, and competitor insertion.  The loose factor `4` is a single common
constant and absorbs the source's smaller `delta^30` term into `delta^15`.
-/
theorem one_step_upper_penultimate_of_component_bounds
    {delta tau h d A next cell previous principal mixed oscillatory : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hA : 0 ≤ A) (hcell0 : 0 ≤ cell) (hprevious0 : 0 ≤ previous)
    (hprincipal :
      principal ≤
        (1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cell +
          A * delta ^ 15 * previous)
    (hmixed : |mixed| ≤ A * delta ^ 15 * previous)
    (hoscillatory : oscillatory ≤ A * delta ^ 30 * previous)
    (hvariational :
      (1 / 2 : ℝ) * next ≤
        (1 / 2 : ℝ) * principal + mixed +
          (1 / 2 : ℝ) * oscillatory) :
    (1 / 2 : ℝ) * next ≤
      (1 / 2 - tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) * cell +
        (4 * A) * delta ^ 15 * previous := by
  have hpow := pow_thirty_le_pow_fifteen hdelta0 hdelta1
  have hmixed' : mixed ≤ A * delta ^ 15 * previous :=
    (le_abs_self mixed).trans hmixed
  have hoscillatory' : A * delta ^ 30 * previous ≤
      A * delta ^ 15 * previous := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hA) hprevious0
  have hleading :
      (1 / 2 : ℝ) *
          (1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cell ≤
        (1 / 2 - tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) * cell := by
    apply mul_le_mul_of_nonneg_right _ hcell0
    have herror0 : 0 ≤ A * delta ^ 4 * h ^ 2 := by positivity
    calc
      (1 / 2 : ℝ) *
          (1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) =
          1 / 2 - tau * h / d + (1 / 2) *
            (A * delta ^ 4 * h ^ 2) := by ring
      _ ≤ 1 / 2 - tau * h / d + (4 * A) * delta ^ 4 * h ^ 2 := by
        nlinarith
  calc
    (1 / 2 : ℝ) * next ≤
        (1 / 2 : ℝ) * principal + mixed +
          (1 / 2 : ℝ) * oscillatory := hvariational
    _ ≤ (1 / 2 : ℝ) *
          ((1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cell +
            A * delta ^ 15 * previous) +
        (A * delta ^ 15 * previous) +
          (1 / 2 : ℝ) * (A * delta ^ 30 * previous) := by
      gcongr
    _ ≤ (1 / 2 : ℝ) *
          ((1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cell +
            A * delta ^ 15 * previous) +
        (A * delta ^ 15 * previous) +
          (1 / 2 : ℝ) * (A * delta ^ 15 * previous) := by
      gcongr
    _ ≤ (1 / 2 - tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) * cell +
          (4 * A) * delta ^ 15 * previous := by
      have htail0 : 0 ≤ A * delta ^ 15 * previous := by positivity
      nlinarith

/-- Dual copy of `one_step_upper_penultimate_of_component_bounds`.  Its only
difference is the positive stationary drift. -/
theorem one_step_lower_penultimate_of_component_bounds
    {delta tau h d A nextStarInv cellStarInv previousInv
      principal mixed oscillatory : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hA : 0 ≤ A) (hcell0 : 0 ≤ cellStarInv)
    (hprevious0 : 0 ≤ previousInv)
    (hprincipal :
      principal ≤
        (1 + 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cellStarInv +
          A * delta ^ 15 * previousInv)
    (hmixed : |mixed| ≤ A * delta ^ 15 * previousInv)
    (hoscillatory : oscillatory ≤ A * delta ^ 30 * previousInv)
    (hvariational :
      (1 / 2 : ℝ) * nextStarInv ≤
        (1 / 2 : ℝ) * principal + mixed +
          (1 / 2 : ℝ) * oscillatory) :
    (1 / 2 : ℝ) * nextStarInv ≤
      (1 / 2 + tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) * cellStarInv +
        (4 * A) * delta ^ 15 * previousInv := by
  have hpow := pow_thirty_le_pow_fifteen hdelta0 hdelta1
  have hmixed' : mixed ≤ A * delta ^ 15 * previousInv :=
    (le_abs_self mixed).trans hmixed
  have hoscillatory' : A * delta ^ 30 * previousInv ≤
      A * delta ^ 15 * previousInv := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hA) hprevious0
  have hleading :
      (1 / 2 : ℝ) *
          (1 + 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cellStarInv ≤
        (1 / 2 + tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) *
          cellStarInv := by
    apply mul_le_mul_of_nonneg_right _ hcell0
    have herror0 : 0 ≤ A * delta ^ 4 * h ^ 2 := by positivity
    calc
      (1 / 2 : ℝ) *
          (1 + 2 * tau * h / d + A * delta ^ 4 * h ^ 2) =
          1 / 2 + tau * h / d + (1 / 2) *
            (A * delta ^ 4 * h ^ 2) := by ring
      _ ≤ 1 / 2 + tau * h / d + (4 * A) * delta ^ 4 * h ^ 2 := by
        nlinarith
  calc
    (1 / 2 : ℝ) * nextStarInv ≤
        (1 / 2 : ℝ) * principal + mixed +
          (1 / 2 : ℝ) * oscillatory := hvariational
    _ ≤ (1 / 2 : ℝ) *
          ((1 + 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cellStarInv +
            A * delta ^ 15 * previousInv) +
        (A * delta ^ 15 * previousInv) +
          (1 / 2 : ℝ) * (A * delta ^ 30 * previousInv) := by
      gcongr
    _ ≤ (1 / 2 : ℝ) *
          ((1 + 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cellStarInv +
            A * delta ^ 15 * previousInv) +
        (A * delta ^ 15 * previousInv) +
          (1 / 2 : ℝ) * (A * delta ^ 15 * previousInv) := by
      gcongr
    _ ≤ (1 / 2 + tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) *
          cellStarInv + (4 * A) * delta ^ 15 * previousInv := by
      have htail0 : 0 ≤ A * delta ^ 15 * previousInv := by positivity
      nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
