import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMeasurableCorrectors
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Measurable local `L²` observables of one-step correctors

A fixed measurable spatial window defines a one-Lipschitz seminorm on the
ambient Hilbert `L²` class.  Together with the continuous set-integral maps
from `Homogenization.Sobolev.L2Ambient`, this gives a Borel centered-cell
variance without selecting a jointly measurable pointwise representative of
the Sobolev solution.

This is the GMC counterpart of the observable layer in
`Algsuperdiff/.../Corrector/CorrectorMeasurableGradient.lean` and
`CorrectorMeasurableQuartic.lean`.  The important difference is that the GMC
cell calculation needs a proper subwindow of the finite-volume solution, so
the restriction seminorm is made explicit.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The unnormalized `L²` norm of an ambient Hilbert class on a fixed
measurable window. -/
def oneStepWindowL2Norm {d : ℕ} (U S : Set (Vec d))
    (f : HilbertVectorL2 U) : ℝ :=
  (eLpNorm (S.indicator fun x => f x) 2 (volumeMeasureOn U)).toReal

theorem oneStepWindowL2Norm_nonneg {d : ℕ} (U S : Set (Vec d))
    (f : HilbertVectorL2 U) :
    0 ≤ oneStepWindowL2Norm U S f := by
  exact ENNReal.toReal_nonneg

/-- Restriction to a measurable window is contractive in the ambient `L²`
distance. -/
theorem oneStepWindowL2Norm_le_add_dist {d : ℕ} (U S : Set (Vec d))
    (hS : MeasurableSet S) (f g : HilbertVectorL2 U) :
    oneStepWindowL2Norm U S f ≤ oneStepWindowL2Norm U S g + ‖f - g‖ := by
  have htri := eLpNorm_add_le
    ((Lp.aestronglyMeasurable g).indicator hS)
    ((Lp.aestronglyMeasurable (f - g)).indicator hS)
    (show 1 ≤ (2 : ℝ≥0∞) by norm_num)
  have hae : S.indicator (fun x => f x) =ᵐ[volumeMeasureOn U]
      S.indicator (fun x => g x) +
        S.indicator (fun x => (f - g) x) := by
    filter_upwards [Lp.coeFn_sub f g] with x hx
    by_cases hxs : x ∈ S
    · simp only [Set.indicator_of_mem hxs, Pi.add_apply]
      rw [hx]
      simp
    · simp [Set.indicator_of_notMem hxs]
  have htop1 : eLpNorm (S.indicator fun x => g x) 2
      (volumeMeasureOn U) ≠ ∞ :=
    (((Lp.memLp g).indicator hS).2.ne)
  have htop2 : eLpNorm (S.indicator fun x => (f - g) x) 2
      (volumeMeasureOn U) ≠ ∞ :=
    (((Lp.memLp (f - g)).indicator hS).2.ne)
  have hmain : eLpNorm (S.indicator fun x => f x) 2
      (volumeMeasureOn U) ≤
      eLpNorm (S.indicator fun x => g x) 2 (volumeMeasureOn U) +
        eLpNorm (S.indicator fun x => (f - g) x) 2
          (volumeMeasureOn U) := by
    rw [eLpNorm_congr_ae hae]
    exact htri
  rw [oneStepWindowL2Norm, oneStepWindowL2Norm]
  calc
    _ ≤ (eLpNorm (S.indicator fun x => g x) 2 (volumeMeasureOn U) +
        eLpNorm (S.indicator fun x => (f - g) x) 2
          (volumeMeasureOn U)).toReal :=
      ENNReal.toReal_mono (by finiteness) hmain
    _ = (eLpNorm (S.indicator fun x => g x) 2
          (volumeMeasureOn U)).toReal +
        (eLpNorm (S.indicator fun x => (f - g) x) 2
          (volumeMeasureOn U)).toReal := by
      rw [ENNReal.toReal_add htop1 htop2]
    _ ≤ _ := by
      gcongr
      rw [Lp.norm_def]
      exact ENNReal.toReal_mono (by finiteness)
        (eLpNorm_indicator_le (fun x => (f - g) x))

theorem lipschitzWith_oneStepWindowL2Norm {d : ℕ} (U S : Set (Vec d))
    (hS : MeasurableSet S) :
    LipschitzWith 1 (oneStepWindowL2Norm U S) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hfg := oneStepWindowL2Norm_le_add_dist U S hS f g
  have hgf := oneStepWindowL2Norm_le_add_dist U S hS g f
  rw [Real.dist_eq]
  simp only [NNReal.coe_one, one_mul]
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    simpa only [dist_eq_norm, add_comm] using hfg
  · rw [sub_le_iff_le_add]
    simpa only [dist_eq_norm, norm_sub_rev, add_comm] using hgf

theorem continuous_oneStepWindowL2Norm {d : ℕ} (U S : Set (Vec d))
    (hS : MeasurableSet S) :
    Continuous (oneStepWindowL2Norm U S) :=
  (lipschitzWith_oneStepWindowL2Norm U S hS).continuous

section Cube

variable {d : ℕ}

/-- The normalized squared fluctuation of an ambient vector `L²` class on a
triadic subcube.  The `max` makes the definition total; the variance identity
shows that its first argument is nonnegative on genuine `L²` classes. -/
def oneStepCellCenteredL2Sq (Q R : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) : ℝ :=
  by
    letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
      isFiniteMeasure_volumeMeasureOn_openCubeSet Q
    exact max
      ((cubeVolume R)⁻¹ * oneStepWindowL2Norm
          (openCubeSet Q) (openCubeSet R) f ^ 2 -
        ∑ i : Fin d,
          ((cubeVolume R)⁻¹ *
            hilbertVectorL2CoordSetIntegralCLM
              (U := openCubeSet Q) (openCubeSet R)
                (measurableSet_openCubeSet R) i f) ^ 2)
      0

/-- The source's `A_z` carrier: the square root of the normalized centered
cell variance. -/
def oneStepCellCenteredL2 (Q R : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) : ℝ :=
  Real.sqrt (oneStepCellCenteredL2Sq Q R f)

theorem continuous_oneStepCellCenteredL2Sq (Q R : TriadicCube d) :
    Continuous (oneStepCellCenteredL2Sq Q R) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  change Continuous (fun f : HilbertVectorL2 (openCubeSet Q) =>
    max
      ((cubeVolume R)⁻¹ * oneStepWindowL2Norm
          (openCubeSet Q) (openCubeSet R) f ^ 2 -
        ∑ i : Fin d,
          ((cubeVolume R)⁻¹ *
            hilbertVectorL2CoordSetIntegralCLM
              (U := openCubeSet Q) (openCubeSet R)
                (measurableSet_openCubeSet R) i f) ^ 2)
      0)
  apply Continuous.max _ continuous_const
  exact ((continuous_const.mul
      ((continuous_oneStepWindowL2Norm (openCubeSet Q) (openCubeSet R)
        (measurableSet_openCubeSet R)).pow 2)).sub
      (continuous_finset_sum _ fun i _ =>
        (continuous_const.mul
          (hilbertVectorL2CoordSetIntegralCLM
            (U := openCubeSet Q) (openCubeSet R)
              (measurableSet_openCubeSet R) i).continuous).pow 2))

theorem continuous_oneStepCellCenteredL2 (Q R : TriadicCube d) :
    Continuous (oneStepCellCenteredL2 Q R) :=
  Real.continuous_sqrt.comp (continuous_oneStepCellCenteredL2Sq Q R)

theorem measurable_oneStepCellCenteredL2_comp {Omega : Type*}
    [MeasurableSpace Omega] (Q R : TriadicCube d)
    {F : Omega → HilbertVectorL2 (openCubeSet Q)} (hF : Measurable F) :
    Measurable fun omega => oneStepCellCenteredL2 Q R (F omega) :=
  (continuous_oneStepCellCenteredL2 Q R).measurable.comp hF

/-- Every centered-cell `A_z` observable formed from a zero-Dirichlet
one-step corrector is measurable. -/
theorem measurable_oneStepShellDirichlet_cellCenteredL2 [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h)
    (uD : Sample d → H10Function (openCubeSet Q))
    (huD : ∀ omega,
      CubeDirichletDivergenceProblem Q (uD omega)
        (oneStepShellForcingH1 M n h omega p Q hh).toField) :
    Measurable fun omega =>
      oneStepCellCenteredL2 Q R
        (uD omega).toH1Function.gradToHilbertVectorL2 := by
  apply measurable_oneStepCellCenteredL2_comp
  exact measurable_oneStepShellDirichletGradL2 M n h p Q hh uD huD

/-- The dual `A_z` observable formed from a centered Neumann corrector is
measurable as well. -/
theorem measurable_oneStepShellNeumann_cellCenteredL2
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h)
    (uN : Sample d → H1MeanZeroFunction (openCubeSet Q))
    (huN : ∀ omega,
      IsMeanZeroNeumannRhsWeakSolution
        (identityCoeffField d) (openCubeSet Q) (uN omega)
        (fun x =>
          -(oneStepShellForcingH1 M n h omega p Q hh).toField x)) :
    Measurable fun omega =>
      oneStepCellCenteredL2 Q R (uN omega).gradToHilbertVectorL2 := by
  apply measurable_oneStepCellCenteredL2_comp
  exact measurable_oneStepShellNeumannGradL2 M n h p Q hh uN huN

end Cube

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
