module

public import SubdiffusiveProcess.Nash.Fatou
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import MarkovProcess.Kernel.LpConsistency

@[expose] public section

open MeasureTheory MarkovProcess ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- A kernel estimate on L1 ∩ L2 extends to all L1 inputs. -/
theorem kernel_bound_of_L1_L2 {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (κ : ProbabilityTheory.Kernel X X) (hκ : IsSubMarkovKernel κ) (hsub : κ ∘ₘ mu ≤ mu)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ f : X → ℝ, MemLp f 2 mu → Integrable f mu →
      eLpNorm (kernelIntegral κ f) ∞ mu ≤ ENNReal.ofReal A * eLpNorm f 1 mu)
    (f : X → ℝ) (hf : Integrable f mu) :
    eLpNorm (kernelIntegral κ f) ∞ mu ≤ ENNReal.ofReal A * eLpNorm f 1 mu := by
  let : Fact ((1 : ℝ≥0) ≤ 1) := ⟨le_rfl⟩
  let : Fact ((1 : ℝ≥0∞) ≤ ((1 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  let f1 : Lp ℝ 1 mu := (memLp_one_iff_integrable.mpr hf).toLp f
  let T := kernelLpFinite mu κ hκ hsub 1
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp
    ((Lp.simpleFunc.dense (E := ℝ) (μ := mu) (p := 1) ENNReal.one_ne_top) f1)
  have hconv := tendstoInMeasure_of_tendsto_Lp ((T.continuous.tendsto f1).comp hlim)
  have hvbound (n : ℕ) : eLpNorm (T (v n) : X → ℝ) ∞ mu ≤ ENNReal.ofReal (A * ‖v n‖) := by
    let g : Lp.simpleFunc ℝ 1 mu := ⟨v n, hv n⟩
    let sg := Lp.simpleFunc.toSimpleFunc g
    have hg1 : MemLp sg 1 mu := Lp.simpleFunc.memLp g
    have hgI : Integrable sg mu := memLp_one_iff_integrable.mp hg1
    have hg2 : MemLp sg 2 mu := (SimpleFunc.memLp_iff_integrable (by norm_num) (by norm_num)).mpr hgI
    have hsg : (v n : X → ℝ) =ᵐ[mu] sg := (Lp.simpleFunc.toSimpleFunc_eq_toFun g).symm
    have hrep : (T (v n) : X → ℝ) =ᵐ[mu] kernelIntegral κ sg :=
      (coeFn_kernelLpFinite mu κ hκ hsub 1 (v n)).trans (kernelIntegral_congr_ae hsub hsg)
    calc
      _ = eLpNorm (kernelIntegral κ sg) ∞ mu := eLpNorm_congr_ae hrep
      _ ≤ ENNReal.ofReal A * eLpNorm sg 1 mu := hbound sg hg2 hgI
      _ = ENNReal.ofReal (A * ‖v n‖) := by
        rw [← eLpNorm_congr_ae hsg, ← Lp.enorm_def, ← ofReal_norm,
          ENNReal.ofReal_mul hA]
  have hAlim : Tendsto (fun n => ENNReal.ofReal (A * ‖v n‖)) atTop
      (𝓝 (ENNReal.ofReal (A * ‖f1‖))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul hlim.norm)
  have hfinal := eLpNorm_le_of_tendstoInMeasure_bounds ∞ (fun n => Lp.aestronglyMeasurable (T (v n)))
    hconv (fun n => ENNReal.ofReal (A * ‖v n‖)) _ hAlim (Eventually.of_forall hvbound)
  have hrep : (T f1 : X → ℝ) =ᵐ[mu] kernelIntegral κ f :=
    (coeFn_kernelLpFinite mu κ hκ hsub 1 f1).trans
      (kernelIntegral_congr_ae hsub (MemLp.coeFn_toLp _))
  rw [eLpNorm_congr_ae hrep, ENNReal.ofReal_mul hA, ofReal_norm, Lp.enorm_def,
    eLpNorm_congr_ae (MemLp.coeFn_toLp _)] at hfinal
  exact hfinal

end SubdiffusiveProcess.Nash
