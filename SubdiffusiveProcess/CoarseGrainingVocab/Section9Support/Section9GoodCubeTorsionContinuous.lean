import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeOccupationTorsion
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerCorrection
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationMeasure
set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The zero-trace mean-exit carrier has a bounded continuous representative. -/
theorem goodCube_exists_continuous_h10_meanExit
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} (hD : LocalDiffusion c rho law)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    (hWconv : IsOpenBoundedConvexDomain W) (hc : ContinuousOn c W)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    {E : ℝ} (hE : 0 ≤ E)
    (hmean : ∀ x ∈ W, meanExit law W x ≤ ENNReal.ofReal E) :
    ∃ u : H10Function W, ∃ h : Vec d → ℝ,
      ContinuousOn h W ∧
      (∀ x ∈ W, 0 ≤ h x ∧ h x ≤ E) ∧
      u.toH1Function.toFun =ᵐ[volume.restrict W] h ∧
      (∀ᵐ x ∂volume.restrict W, ENNReal.ofReal (h x) = meanExit law W x) ∧
      IsMassiveWeakSolutionOn c rho 0 W u.toH1Function (fun _ => 1) := by
  obtain ⟨u, hurep, hub, husol⟩ :=
    goodCube_exists_h10_meanExit hD hW hWb hWconv hlam hEll hE hmean
  have hcoeffc : CoefficientOn W c :=
    coefficientOn_mono subset_closure (hD.2.1 (closure W) hWb.isCompact_closure).1
  have hcpos := SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRegularity.pos_of_continuousOn_of_coefficientOn hW hc hcoeffc
  have hcoeffrho : CoefficientOn W rho :=
    coefficientOn_mono subset_closure (hD.2.1 (closure W) hWb.isCompact_closure).2
  obtain ⟨hrhoMeas, lo, hi, hlo, hrhob⟩ := hcoeffrho
  have hrhob' : ∀ᵐ x ∂volume.restrict W, |rho x| ≤ hi := by
    filter_upwards [hrhob] with x hx
    rw [abs_of_nonneg (hlo.le.trans hx.1)]
    exact hx.2
  haveI : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hWb.isCompact_closure.measure_lt_top
  have h1 : MemL2On W (fun _ : Vec d => (1 : ℝ)) := memLp_const 1
  have h1b : ∀ᵐ x ∂volume.restrict W, |(1 : ℝ)| ≤ 1 := by simp
  have huabs : ∀ᵐ x ∂volume.restrict W, |u.toH1Function.toFun x| ≤ E := by
    filter_upwards [hub] with x hx
    rw [abs_of_nonneg hx.1]
    exact hx.2
  obtain ⟨hcont, hae, -⟩ :=
    holder_euclideanBallAverageRepresentative_of_bounded_massiveWeakSolution hd hW hc hcpos
      hrhoMeas hrhob' h1 h1b huabs husol
  let h := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.euclideanBallAverageRepresentative u.toH1Function.toFun
  have hhb : ∀ᵐ x ∂volume.restrict W, 0 ≤ h x ∧ h x ≤ E := by
    filter_upwards [hae, hub] with x hx hb
    simpa only [h, hx] using hb
  have hupper : ∀ x ∈ W, h x ≤ E :=
    continuousOn_le_of_ae_restrict volume W hW h hcont E (hhb.mono fun _ hx => hx.2)
  have hlower : ∀ x ∈ W, -h x ≤ 0 :=
    continuousOn_le_of_ae_restrict volume W hW (fun x => -h x) hcont.neg 0
      (hhb.mono fun _ hx => by linarith only [hx.1])
  refine ⟨u, h, hcont, fun x hx => ⟨by linarith only [hlower x hx], hupper x hx⟩,
    hae.symm, ?_, husol⟩
  filter_upwards [hae, hurep] with x hx heq
  simpa only [h, hx] using heq

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
