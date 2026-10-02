import SubdiffusiveProcess.Probability.Diffusion.BrownianWitnessInputs
import SubdiffusiveProcess.Probability.Diffusion.HuntContinuityStart
import MarkovProcess.Killed.Semigroup
import Mathlib.Topology.UniformSpace.UniformConvergence




set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.Model.LifetimeProcess
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.Packet445Checks

variable {d : ℕ}



theorem variationalResolvent_energy {U : Set (Vec d)} (hU : IsOpen U)
    {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    let u := variationalResolvent hU hs hf
    (∫ x in U, u.toH1Function.toFun x * u.toH1Function.toFun x) +
      s * (∫ x in U, vecDot (u.toH1Function.grad x) (u.toH1Function.grad x)) =
        ∫ x in U, f x * u.toH1Function.toFun x := by
  dsimp only
  let u := variationalResolvent hU hs hf
  have he := variationalResolvent_spec hU hs hf u
  change s⁻¹ * (∫ x in U, 1 * u.toH1Function.toFun x * u.toH1Function.toFun x) +
    (∫ x in U, vecDot (1 • u.toH1Function.grad x) (u.toH1Function.grad x)) =
      ∫ x in U, 1 * (s⁻¹ * f x) * u.toH1Function.toFun x at he
  simp only [one_mul, one_smul] at he
  have hr : (∫ x in U, s⁻¹ * f x * u.toH1Function.toFun x) =
      s⁻¹ * ∫ x in U, f x * u.toH1Function.toFun x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hr] at he
  have hm := congrArg (fun a : ℝ => s * a) he
  simpa only [mul_add, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] using hm

/-- Chapman--Kolmogorov for the actual lifetime-path killed Brownian kernel. -/
theorem killedKernel_laplacianLaw_add (U : Set (Vec d)) (hU : IsOpen U)
    (s t : NNReal) :
    killedKernel (laplacianLaw d) U hU (s + t) =
      (killedKernel (laplacianLaw d) U hU t).comp
        (killedKernel (laplacianLaw d) U hU s) := by
  simp only [laplacianLaw, killedKernel_lifetimeProcess]
  exact SubMarkovKernelSemigroup.IsConservative.killedKernel_add
    (laplacianSemigroup d) isConservative_laplacianSemigroup U hU
    isFeller_laplacianSemigroup kolmogorovRegular_laplacianSemigroup s t

/-- The fixed-start density is continuous in time and the terminal point. -/
theorem continuousOn_huntDensity_time_end {U : Set (Vec d)} (hU : IsOpen U)
    {x : Vec d} (hx : x ∈ U) :
    ContinuousOn (fun z : ℝ × Vec d => huntDensity U z.1 x z.2) (Ioi 0 ×ˢ U) := by
  intro z hz
  have hg : ContinuousAt (fun v : ℝ × Vec d => laplacianDensity v.1 x v.2) z := by
    unfold laplacianDensity
    apply tendsto_finset_prod
    intro i _
    change ContinuousAt (fun v : ℝ × Vec d =>
      gaussianPDFReal (x i) (2 * Real.toNNReal v.1) (v.2 i)) z
    have hv : (0 : ℝ) < (2 * Real.toNNReal z.1 : NNReal) := by
      exact_mod_cast mul_pos (by norm_num : (0 : NNReal) < 2)
        (Real.toNNReal_pos.mpr hz.1)
    unfold gaussianPDFReal
    fun_prop (disch := positivity)
  have hh := continuousAt_huntCorrection_start hU hx hz.1 hz.2
  have hm : ContinuousAt (fun v : ℝ × Vec d =>
      max (laplacianDensity v.1 x v.2 - huntCorrection U v.1 x v.2) 0) z :=
    continuous_max.continuousAt.comp ((hg.sub hh).prodMk continuousAt_const)
  exact hm.continuousWithinAt

/-- Gaussian domination is pointwise and independent of any Sobolev witness. -/
theorem huntDensity_le_laplacianDensity (U : Set (Vec d)) (t : ℝ) (x y : Vec d) :
    huntDensity U t x y ≤ laplacianDensity t x y := by
  exact max_le (sub_le_self _ (huntCorrection_nonneg U t x y))
    (laplacianDensity_nonneg t x y)

/-- Continuous Hilbert-space rows and a half-time factorization imply joint
continuity; the row continuity remains a substantive input. -/
theorem continuous_inner_rows {A : Type*} [TopologicalSpace A]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : A → E) (hv : Continuous v) :
    Continuous (fun z : A × A => inner ℝ (v z.1) (v z.2)) :=
  (hv.comp continuous_fst).inner (hv.comp continuous_snd)

end SubdiffusiveProcess.Probability.Diffusion.Packet445Checks
