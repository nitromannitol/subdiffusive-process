module

public import SubdiffusiveProcess.Lane1.ChaosBasic

@[expose] public section

/-!
# Splitting off a finite block of layers

The cutoff density factors as the density of the first `k+1` layers times the
density of the layers beyond them, the latter being the SAME cutoff density at
the shifted environment.  That is what makes a finite block of layers unable to
create or destroy a null mass, and hence what makes the event that a cube
carries no mass a tail event.
-/

open MeasureTheory

noncomputable section
namespace SubdiffusiveProcess

/-- The layers the chaos beyond generation `m` reads: the fine potential only
ever evaluates the environment at nonpositive indices, so shifting by `m` reads
only indices `≤ -m`. -/
def tailIndices (m : ℕ) : Set ℤ := {j : ℤ | j ≤ -(m : ℤ)}

/-- Reindex the layers by shifting the index by `m`, and zero out the indices
the shifted chaos never reads.  The zeroing is what makes the shifted
environment a function of the tail block alone. -/
def layerShift {d : ℕ} (m : ℕ) (omega : BilateralField d) : BilateralField d :=
  fun j => if j ≤ 0 then omega (j - (m : ℤ)) else 0



def layerFill {d : ℕ} (m : ℕ)
    (y : (i : tailIndices m) → C(SpatialCoordinates d, ℝ)) : BilateralField d :=
  fun j => if h : j ≤ 0 then y ⟨j - (m : ℤ), by
      simp only [tailIndices, Set.mem_setOf_eq]; omega⟩ else 0

theorem layerFill_restrict {d : ℕ} (m : ℕ) (omega : BilateralField d) :
    layerFill m ((tailIndices m).restrict omega) = layerShift m omega := rfl

theorem measurable_layerFill {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] (m : ℕ) :
    Measurable (layerFill (d := d) m) := by
  refine measurable_pi_iff.mpr fun j => ?_
  by_cases h : j ≤ 0
  · simpa only [layerFill, dif_pos h] using measurable_pi_apply _
  · simpa only [layerFill, dif_neg h] using measurable_const

theorem finePotential_split {d : ℕ} (k m : ℕ) (omega : BilateralField d)
    (x : SpatialCoordinates d) :
    finePotential (k + 1 + m) omega x
      = finePotential k omega x
        + finePotential m (layerShift (k + 1) omega) x := by
  classical
  have hsplit : k + 1 + m + 1 = (k + 1) + (m + 1) := by omega
  rw [finePotential, finePotential, finePotential, hsplit,
    Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hnonpos : (-(Int.ofNat j) : ℤ) ≤ 0 := by
    have : (0 : ℤ) ≤ Int.ofNat j := Int.natCast_nonneg j
    omega
  have hidx : (-(Int.ofNat (k + 1 + j)) : ℤ)
      = -(Int.ofNat j) - ((k + 1 : ℕ) : ℤ) := by
    have hcast : ∀ n : ℕ, (Int.ofNat n : ℤ) = (n : ℤ) := fun _ => rfl
    simp only [hcast]
    push_cast
    ring
  unfold layerShift
  rw [if_pos hnonpos, hidx]

/-- The cutoff density factors through the shift. -/
theorem fineDensity_split {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (k m : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d) :
    fineDensity M (k + 1 + m) omega x
      = fineDensity M k omega x
        * fineDensity M m (layerShift (k + 1) omega) x := by
  rw [fineDensity, fineDensity, fineDensity, finePotential_split k m omega x,
    ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The cutoff MEASURE factors: the first `k+1` layers contribute a continuous
strictly positive density, and the rest is the unweighted cutoff chaos at the
shifted environment. -/
theorem weightedChaosCutoff_split {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k m : ℕ) (omega : BilateralField d) :
    weightedChaosCutoff M H (k + 1 + m) omega
      = (chaosCutoff M m (layerShift (k + 1) omega)).withDensity
        (fun x => ENNReal.ofReal
          (Real.exp (H omega x) * fineDensity M k omega x)) := by
  classical
  have hmeas_tail : Measurable fun x : SpatialCoordinates d =>
      ENNReal.ofReal (fineDensity M m (layerShift (k + 1) omega) x) :=
    (continuous_fineDensity M m _).measurable.ennreal_ofReal
  have hmeas_head : Measurable fun x : SpatialCoordinates d =>
      ENNReal.ofReal (Real.exp (H omega x) * fineDensity M k omega x) :=
    ((Real.continuous_exp.comp (H omega).continuous).mul
      (continuous_fineDensity M k omega)).measurable.ennreal_ofReal
  rw [weightedChaosCutoff, chaosCutoff]
  simp only [Function.comp_def]
  rw [← withDensity_mul _ hmeas_tail hmeas_head]
  congr 1
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (le_of_lt (fineDensity_pos M m _ x)),
    fineDensity_split M k m omega x]
  congr 1
  ring

end SubdiffusiveProcess
