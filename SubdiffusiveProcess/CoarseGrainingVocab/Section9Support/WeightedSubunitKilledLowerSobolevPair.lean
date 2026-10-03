module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLowerAnalyticInput
public import Homogenization.Sobolev.Truncation.WeakGradientLimit

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower



theorem dirichletSobolevPair_of_h10 {d : ℕ} {W : Set (Vec d)} (u : H10Function W) :
    DirichletSobolevPair W u.toH1Function.toFun u.toH1Function.grad :=
  ⟨u.memL2, u.gradMemL2, u.approx, u.approx_smooth, u.approx_hasCompactSupport,
    u.approx_support_subset, u.tendsto_approx, u.tendsto_approx_grad⟩

/-- Smooth graph approximation constructs an actual `H10Function`, including
its weak derivative identity. The constructed value and gradient are exact. -/
theorem DirichletSobolevPair.exists_h10 {d : ℕ} {W : Set (Vec d)}
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : DirichletSobolevPair W u g) :
    ∃ v : H10Function W, v.toH1Function.toFun = u ∧ v.toH1Function.grad = g := by
  obtain ⟨hu, hg, f, hf, hc, hs, hlim, hglim⟩ := h
  have hfm : ∀ n, MemLp (f n) 2 (volume.restrict W) := fun n =>
    ((hf n).continuous.memLp_of_hasCompactSupport (hc n)).restrict W
  have hfgm : ∀ n, GradMemL2On W (fun x i => fderiv ℝ (f n) x (basisVec i)) := by
    intro n i
    exact (((hf n).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.memLp_of_hasCompactSupport ((hc n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict W
  have hweak : HasWeakGradientOn W u g := HasWeakGradientOn.of_tendsto_eLpNorm_two
    hu hg hfm hfgm (fun n => HasWeakGradientOn.of_contDiff ((hf n).of_le (by simp))) hlim hglim
  exact ⟨{
    toFun := u
    grad := g
    memL2 := hu
    gradMemL2 := hg
    hasWeakGradient := hweak
    approx := f
    approx_smooth := hf
    approx_hasCompactSupport := hc
    approx_support_subset := hs
    tendsto_approx := hlim
    tendsto_approx_grad := hglim }, rfl, rfl⟩



theorem dirichletSobolevPair_iff_exists_h10 {d : ℕ} {W : Set (Vec d)}
    {u : Vec d → ℝ} {g : Vec d → Vec d} :
    DirichletSobolevPair W u g ↔
      ∃ v : H10Function W, v.toH1Function.toFun = u ∧ v.toH1Function.grad = g := by
  refine ⟨DirichletSobolevPair.exists_h10, ?_⟩
  rintro ⟨v, rfl, rfl⟩
  exact dirichletSobolevPair_of_h10 v




end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower
