module

public import SubdiffusiveProcess.Probability.BrownianProduct.OperatorInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLowerSobolevPair
public import Homogenization.Sobolev.W1p.ZeroTraceClosure
public import Homogenization.Sobolev.Truncation.Basic

@[expose] public section

/-!
# Closure of the explicit Dirichlet Sobolev graph

The graph is closed under coordinatewise `L²` convergence and under changes
of representatives. Compactly supported `C¹` functions in a bounded open
convex domain belong to it; infinite smoothness is not required of the
function itself. Smooth approximants are supplied by the zero-trace library.
-/

set_option autoImplicit false

open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Probability.BrownianProduct
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower

/-- The explicit graph respects almost-everywhere equality of value and gradient. -/
theorem sobolevGraph_congr {d : ℕ} {W : Set (Vec d)}
    {u v : Vec d → ℝ} {g h : Vec d → Vec d} (hu : SobolevGraph W u g)
    (hv : u =ᵐ[volume.restrict W] v)
    (hh : ∀ i, (fun x => g x i) =ᵐ[volume.restrict W] fun x => h x i) : SobolevGraph W v h := by
  obtain ⟨hum, hgm, f, hf, hc, hs, hlim, hglim⟩ := hu
  refine ⟨(memLp_congr_ae hv).mp hum, fun i => (memLp_congr_ae (hh i)).mp (hgm i),
    f, hf, hc, hs, ?_, ?_⟩
  · have he (n : ℕ) : eLpNorm (fun x => f n x - v x) 2 (volume.restrict W) =
        eLpNorm (fun x => f n x - u x) 2 (volume.restrict W) := by
      apply eLpNorm_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    simpa only [he] using hlim
  · intro i
    have he (n : ℕ) :
        eLpNorm (fun x => fderiv ℝ (f n) x (Pi.single i 1) - h x i) 2 (volume.restrict W) =
          eLpNorm (fun x => fderiv ℝ (f n) x (Pi.single i 1) - g x i) 2 (volume.restrict W) := by
      apply eLpNorm_congr_ae
      filter_upwards [hh i] with x hx
      rw [hx]
    simpa only [he] using hglim i

/-- Coordinatewise `L²` convergence preserves the explicit zero-boundary graph. -/
theorem sobolevGraph_of_tendsto {d : ℕ} {W : Set (Vec d)}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict W)) (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict W))
    (f : ℕ → Vec d → ℝ) (h : ℕ → Vec d → Vec d)
    (hf : ∀ n, SobolevGraph W (f n) (h n))
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 (volume.restrict W)) atTop (𝓝 0))
    (hglim : ∀ i, Tendsto (fun n => eLpNorm (fun x => h n x i - g x i) 2 (volume.restrict W))
      atTop (𝓝 0)) : SobolevGraph W u g := by
  have hex : ∀ n, ∃ v : H10Function W, v.toH1Function.toFun = f n ∧ v.toH1Function.grad = h n :=
    fun n => (show DirichletSobolevPair W (f n) (h n) from hf n).exists_h10
  choose v hv hvg using hex
  let w (n : ℕ) : W10pFunction W 2 :=
    { toFun := (v n).toH1Function.toFun
      grad := (v n).toH1Function.grad
      memLp := (v n).memL2
      gradMemLp := (v n).gradMemL2
      hasWeakGradient := (v n).toH1Function.hasWeakGradient
      approx := (v n).approx
      approx_smooth := (v n).approx_smooth
      approx_hasCompactSupport := (v n).approx_hasCompactSupport
      approx_support_subset := (v n).approx_support_subset
      tendsto_approx := (v n).tendsto_approx
      tendsto_approx_grad := (v n).tendsto_approx_grad }
  let z := W10pFunction.ofTendstoELpNorm FiniteLpExponent.two hu hg w
    (by simpa only [w, hv, FiniteLpExponent.two_exponent] using hlim)
    (by simpa only [w, hvg, FiniteLpExponent.two_exponent] using hglim)
  exact ⟨hu, hg, z.approx, z.approx_smooth, z.approx_hasCompactSupport,
    z.approx_support_subset, z.tendsto_approx, z.tendsto_approx_grad⟩

/-- A compactly supported `C¹` function in the domain has the explicit smooth
zero-trace approximation, with its classical first derivative as gradient. -/
theorem sobolevGraph_of_contDiff_one {d : ℕ} {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ W) :
    SobolevGraph W f (fun x i => fderiv ℝ f x (Pi.single i 1)) := by
  let u := H1Function.ofContDiff hW.isOpen hf hc
  have hm : MemH10 W f := memH10_of_compactSupport hW u hc hs
    (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  obtain ⟨v, hv⟩ := hm
  have hvgraph : SobolevGraph W v.toH1Function.toFun v.toH1Function.grad :=
    dirichletSobolevPair_of_h10 v
  apply sobolevGraph_congr hvgraph (Eventually.of_forall (fun x => congrFun hv x))
  intro i
  have hlocv : LocallyIntegrableOn (fun x => v.toH1Function.grad x i) W volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((v.gradMemL2 i).locallyIntegrable (by norm_num))
  have hlocu : LocallyIntegrableOn (fun x => u.grad x i) W volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((u.gradMemL2 i).locallyIntegrable (by norm_num))
  have hw := v.toH1Function.hasWeakGradient i
  rw [hv] at hw
  exact HasWeakPartialDerivOn.ae_eq hW.isOpen hlocv hlocu hw (u.hasWeakGradient i)




end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower
