module

public import SubdiffusiveProcess.Processes.ResolventSolutionUniqueness
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffPotential
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

@[expose] public section

/-!
# The finite-cutoff resolvent datum is unique

The pair `(A_N, μ_N) = (cutoffCoefficient M H ω N, cutoffSpeedDensity M H ω N)` of paper
`eq:mfd-normalization` is continuous and positive, so two `C₀` resolvent data that are weak elliptic
resolvents for it have the same solutions (`solution_eq_of_isWeakEllipticResolvent`).
-/

open MarkovProcess
open scoped ZeroAtInfty

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

theorem continuous_cutoffSpeedDensity (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    Continuous (cutoffSpeedDensity M H omega N) := by
  have hpot : Continuous (cutoffPotential H omega N) := by
    unfold cutoffPotential
    fun_prop
  unfold cutoffSpeedDensity
  exact Real.continuous_exp.comp (hpot.sub continuous_const)

theorem cutoffSpeedDensity_pos' (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) : 0 < cutoffSpeedDensity M H omega N x := by
  unfold cutoffSpeedDensity
  exact Real.exp_pos _

theorem continuous_cutoffCoefficient (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    Continuous (cutoffCoefficient M H omega N) := by
  have hpot : Continuous (cutoffPotential H omega N) := by
    unfold cutoffPotential
    fun_prop
  unfold cutoffCoefficient
  exact continuous_const.mul (Real.continuous_exp.comp (hpot.sub continuous_const))

theorem cutoffCoefficient_pos' (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) : 0 < cutoffCoefficient M H omega N x := by
  unfold cutoffCoefficient
  exact mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

/-- **Uniqueness of the finite-cutoff resolvent datum.** -/
theorem cutoff_solution_eq_of_isWeakEllipticResolvent (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    {D D' : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (SpatialCoordinates d)}
    (hD : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D)
    (hD' : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D')
    (mu : Semigroup.PositiveShift) (f : C₀(SpatialCoordinates d, ℝ))
    (x : SpatialCoordinates d) :
    D.solution mu f x = D'.solution mu f x := by
  obtain ⟨B⟩ := nonempty_massiveCubeBounds_of_continuous_pos
    (continuous_cutoffCoefficient M H omega N) (continuous_cutoffSpeedDensity M H omega N)
    (cutoffCoefficient_pos' M H omega N) (cutoffSpeedDensity_pos' M H omega N)
  exact solution_eq_of_isWeakEllipticResolvent B hD hD' mu f x

end SubdiffusiveProcess
