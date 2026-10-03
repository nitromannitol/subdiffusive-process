module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerOccupationEllipticity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKMassiveHolder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRegularity
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
variable {d : ℕ}

/-- A continuous Poisson correction inherits the occupation maximum principle and leaves a harmonic remainder. -/
theorem exists_harmonic_correction_of_bounded_forcing
    (hd : 2 ≤ d) {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) {W : Set (Vec d)}
    (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hc : ContinuousOn c W)
    {lam Lam : ℝ} (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    {q h : Vec d → ℝ} (hq : Measurable q) (hcont : ContinuousOn h W)
    {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hqb : ∀ x ∈ W, |q x| ≤ K)
    (hmean : ∀ z ∈ W, meanExit law W z ≤ ENNReal.ofReal E)
    {P : H1Function W} (hPae : ∀ᵐ x ∂(volume.restrict W), P.toFun x = h x)
    (hPsol : IsMassiveWeakSolutionOn c rho 0 W P q) :
    ∃ v : Vec d → ℝ, (∀ x ∈ W, |v x| ≤ K * E) ∧
      WeakHarmonic c W (fun y => h y - v y) := by
  classical
  haveI hne : NeZero d := ⟨by omega⟩
  haveI hmarkov : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  have hWmeas : MeasurableSet W := hW.measurableSet
  have hcoeffc : CoefficientOn W c :=
    coefficientOn_mono subset_closure (hD.2.1 (closure W) hWb.isCompact_closure).1
  have hcpos : ∀ x ∈ W, 0 < c x :=
    RRKHolderRegularity.pos_of_continuousOn_of_coefficientOn hW hc hcoeffc
  have hrhoW : CoefficientOn W rho :=
    coefficientOn_mono subset_closure (hD.2.1 (closure W) hWb.isCompact_closure).2
  obtain ⟨hrhoMeas, lo, hi, hlo, hbnd⟩ := hrhoW
  have hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ hi := by
    filter_upwards [hbnd] with x hx
    rw [abs_of_nonneg (le_trans hlo.le hx.1)]
    exact hx.2
  have hqbound : ∀ᵐ x ∂(volume.restrict W), ‖q x‖ ≤ K := by
    filter_upwards [ae_restrict_mem hWmeas] with x hx
    simpa only [Real.norm_eq_abs] using hqb x hx
  haveI : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono subset_closure) hWb.isCompact_closure.measure_lt_top
  have hqL2 : MemL2On W q := MemLp.of_bound hq.aestronglyMeasurable K hqbound
  obtain ⟨V, Vae, Vsol⟩ :=
    exists_isMassiveWeakSolutionOn_zero_occupationPotential hD hW hWb hlam hEll hq
      hK hE hqb hmean
  have hVbound : ∀ᵐ x ∂(volume.restrict W), |V.toFun x| ≤ K * E := by
    filter_upwards [Vae, ae_restrict_mem hWmeas] with x hx hxW
    rw [hx]
    exact abs_occupationPotential_le law hW hK hE hqb (hmean x hxW)
  obtain ⟨vcont, vae, -⟩ :=
    holder_euclideanBallAverageRepresentative_of_bounded_massiveWeakSolution
      hd hW hc hcpos hrhoMeas hrhoBdd hqL2
      (by filter_upwards [hqbound] with x hx; simpa only [Real.norm_eq_abs] using hx)
      (M := K * E) hVbound Vsol
  have hvbound : ∀ z ∈ W, |euclideanBallAverageRepresentative V.toFun z| ≤ K * E :=
    abs_le_of_continuousOn_of_ae_le hW vcont vae hVbound
  refine ⟨euclideanBallAverageRepresentative V.toFun, hvbound, ?_⟩
  exact weakHarmonic_sub_of_isMassiveWeakSolutionOn_zero hEll hrhoMeas hrhoBdd hqL2
    (hcont.sub vcont) hW hPae vae.symm hPsol Vsol

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
