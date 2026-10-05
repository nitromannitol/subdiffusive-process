module

public import SubdiffusiveProcess.Probability.Diffusion.HuntContinuityJoint
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph

@[expose] public section

/-!
# The full witness scope and a boundary-free approximation step

The common part forms are defined on arbitrary open sets. The first two results check the precise
remaining input of the existing Brownian witness. The last two expose the
global Sobolev approximation already available and its pathwise exit value.
They do not assert the missing Brownian maximal estimate or identification.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.ScopeChecks

/-- The actual local diffusion predicate requires variational identification
on every bounded open set, including nonsmooth and disconnected sets. -/
theorem variationalIdentification_of_localDiffusion {d : ℕ}
    (hD : LocalDiffusion (fun _ => 1) (fun _ => 1) (laplacianLaw d)) :
    BrownianVariationalIdentification d := by
  intro U hU hUb s hs f hf
  have hfw : MemLp f 2 ((weightedMeasure (fun _ => (1 : ℝ))).restrict U) := by
    simpa only [weightedMeasure, ENNReal.ofReal_one, withDensity_const, one_smul] using hf
  obtain ⟨u, hae, hsol⟩ := hD.2.2 U hU hUb s hs f hfw
  have hae' : u.toH1Function.toFun =ᵐ[volume.restrict U]
      killedResolvent (laplacianLaw d) U s f := by
    simpa only [weightedMeasure, ENNReal.ofReal_one, withDensity_const, one_smul] using! hae
  exact (variationalResolvent_unique hU hs hf u hsol).1.symm.trans hae'

/-- With the proved Hunt continuity theorem, the exact full Brownian witness
is equivalent to the remaining arbitrary-domain variational identification. -/
theorem localDiffusionData_laplacianLaw_iff {d : ℕ} :
    LocalDiffusionData (fun _ => 1) (fun _ => 1) (laplacianLaw d) ↔
      BrownianVariationalIdentification d :=
  ⟨fun h => variationalIdentification_of_localDiffusion h.1,
    localDiffusionData_laplacianLaw_of_variational d⟩

/-- The given zero-boundary approximation converges in the global Sobolev
norm after zero extension, without any regularity assumption on the boundary. -/
theorem global_sobolev_approximation {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (u : H10Function U) :
    ∃ phi : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (phi n)) ∧
      (∀ n, HasCompactSupport (phi n)) ∧ (∀ n, tsupport (phi n) ⊆ U) ∧
      Tendsto (fun n => eLpNorm (fun x => phi n x - u.zeroExtension x) 2 volume)
        atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto
        (fun n => eLpNorm (fun x => fderiv ℝ (phi n) x (Pi.single i 1) -
          u.zeroExtensionGrad x i) 2 volume) atTop (𝓝 0) := by
  let v := u.extendByZeroToOpenSuperset hU.measurableSet isOpen_univ (subset_univ U)
  refine ⟨u.approx, u.approx_smooth, u.approx_hasCompactSupport, u.approx_support_subset,
    ?_, ?_⟩
  · simpa only [v, H10Function.extendByZeroToOpenSuperset, Measure.restrict_univ]
      using! v.tendsto_approx
  · intro i
    simpa only [v, H10Function.extendByZeroToOpenSuperset, Measure.restrict_univ]
      using! v.tendsto_approx_grad i

/-- Uniform pathwise limits of functions supported inside an open set vanish
at its finite exit time. No regularity of that set's frontier is used. -/
theorem zero_at_exit_of_tendstoUniformlyOn {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (omega : ContinuousPath (Vec d)) (h0 : omega 0 ∈ U)
    (hfin : ContinuousPath.exitTime U omega ≠ ⊤) (T : ℝ≥0)
    (hT : (ContinuousPath.exitTime U omega).toNNReal ≤ T)
    (phi : ℕ → Vec d → ℝ) (hphi : ∀ n, tsupport (phi n) ⊆ U)
    (Z : ℝ≥0 → ℝ)
    (hlim : TendstoUniformlyOn (fun n t => phi n (omega t)) Z atTop (Icc 0 T)) :
    Z ((ContinuousPath.exitTime U omega).toNNReal) = 0 := by
  have hx : omega ((ContinuousPath.exitTime U omega).toNNReal) ∉ U := by
    have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU omega h0 hfin
    rw [hU.frontier_eq] at hfront
    exact hfront.2
  have hz (n : ℕ) : phi n (omega ((ContinuousPath.exitTime U omega).toNNReal)) = 0 := by
    by_contra h
    exact hx (hphi n (subset_tsupport (phi n) h))
  have hpoint := hlim.tendsto_at (show (ContinuousPath.exitTime U omega).toNNReal ∈ Icc 0 T
    from ⟨bot_le, hT⟩)
  have hzero : Tendsto
      (fun n => phi n (omega ((ContinuousPath.exitTime U omega).toNNReal))) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hpoint hzero

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.ScopeChecks
