import SubdiffusiveProcess.CoarseGrainingVocab.DirichletScalarForcing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CutoffDirichletExistence
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSymmetry

/-!
# A variational Green inverse from locally bounded coefficient data

The scalar forcing is represented on the closed space of zero-trace
gradients, and the existing coercive Dirichlet solver constructs the inverse.
An almost everywhere measurable coefficient is replaced by a measurable
bounded representative only inside that construction. The exported equation
uses the original coefficient. No diffusion law is an input.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A coefficient in the frozen vocabulary has a measurable, uniformly
elliptic representative on the domain, equal to the original almost everywhere. -/
theorem exists_interior_elliptic_representative {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {c : Vec d → ℝ} (hc : CoefficientOn U c) :
    ∃ (a : Vec d → ℝ) (lam Lam : ℝ),
      IsEllipticFieldOn lam Lam U (scalarCoeffField a) ∧
      c =ᵐ[volume.restrict U] a := by
  classical
  obtain ⟨hc, lam, Lam, hlam, hb⟩ := hc
  let a : Vec d → ℝ := fun x => max lam (min (max lam Lam) (hc.mk c x))
  have ha : Measurable a := measurable_const.max
    (measurable_const.min hc.stronglyMeasurable_mk.measurable)
  refine ⟨a, lam, max lam Lam, ?_, ?_⟩
  · apply Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds hlam
      (ha.ite hU measurable_const)
    · intro x _
      exact le_max_left _ _
    · intro x _
      exact max_le (le_max_left _ _) (min_le_left _ _)
  · filter_upwards [hc.ae_eq_mk, hb] with x hx hbx
    dsimp only [a]
    rw [← hx, min_eq_right (hbx.2.trans (le_max_right _ _)), max_eq_right hbx.1]



theorem exists_interior_variational_green {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {c rho : Vec d → ℝ} (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {f : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    ∃ g : H10Function U, IsMassiveWeakSolutionOn c rho 0 U g.toH1Function f := by
  letI : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hfvol := memLp_volume_restrict_of_weighted hU.isOpen.measurableSet hr hf
  obtain ⟨lo, hi, hlo, hrb⟩ := hr.2
  have hrabs : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ hi := by
    filter_upwards [hrb] with x hx
    rw [abs_of_nonneg (hlo.le.trans hx.1)]
    exact hx.2
  have hforce : MemScalarL2 U (fun x => rho x * f x) :=
    memL2On_mul_of_bounded hr.1 hrabs hfvol
  obtain ⟨a, lam, Lam, hEll, hca⟩ := exists_interior_elliptic_representative hU.isOpen.measurableSet hc
  obtain ⟨F, hF, hFpair⟩ := exists_memVectorL2_integral_mul_eq_integral_vecDot hU hforce
  have hRealize :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain hU
  obtain ⟨g, hg⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      hF hRealize hne hEll
  refine ⟨g, ?_⟩
  intro phi
  have heq := hg phi
  rw [← hFpair phi] at heq
  simp only [scalarCoeffField, matVecMul_scalarMatrix] at heq
  simp only [zero_mul, zero_add]
  refine (integral_congr_ae ?_).trans heq
  filter_upwards [hca] with x hx
  rw [hx]

/-- A chosen variational Green inverse. Its construction uses only the
coefficient data and the zero-trace Dirichlet problem. -/
def interiorGreen {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {c rho : Vec d → ℝ} (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {f : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) : H10Function U :=
  Classical.choose (exists_interior_variational_green hU hne hc hr hf)

/-- The chosen inverse solves the original weak equation. -/
theorem interiorGreen_spec {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {c rho : Vec d → ℝ} (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {f : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    IsMassiveWeakSolutionOn c rho 0 U (interiorGreen hU hne hc hr hf).toH1Function f :=
  Classical.choose_spec (exists_interior_variational_green hU hne hc hr hf)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
