module

public import Mathlib
public import Homogenization.Sobolev.H1.Definitions
public import Homogenization.Sobolev.Truncation.WeakGradientLimit
public import Homogenization.Sobolev.Truncation.ChainRule
public import SubdiffusiveProcess.Sobolev.KilledGraph
public import SubdiffusiveProcess.Stampacchia.Mollify

@[expose] public section

/-!
# Stampacchia: the chain rule for a smooth `1`-Lipschitz `S` with `S 0 = 0` in the killed graph

If `u` is an `H¹₀` function and `S` is smooth, `1`-Lipschitz, `S 0 = 0`, then the pair
`(S ∘ u, S'(u) ∇u)` is an element of the killed Sobolev graph: it is the `L²`-limit of the classical
data of `S ∘ φ_n` for the smooth compactly supported approximants `φ_n → u`, along a subsequence
converging almost everywhere.
-/

open MeasureTheory Set Filter Topology Homogenization SubdiffusiveProcess
open scoped ContDiff Distributions ENNReal
noncomputable section
namespace SubdiffusiveProcess.Stampacchia

variable {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}

/-- `L²` convergence of the values and partial derivatives of test functions gives convergence
of their Sobolev data. -/
theorem tendsto_smoothSobolevData_of (Ψ : ℕ → 𝓓(Ω, ℝ)) (z1 : DomainL2 Ω)
    (z2 : Fin d → DomainL2 Ω)
    (h1 : Tendsto (fun n => eLpNorm (fun x => (Ψ n : SpatialCoordinates d → ℝ) x - z1 x) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d)))) atTop (𝓝 0))
    (h2 : ∀ i : Fin d, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (Ψ n : SpatialCoordinates d → ℝ) x (Pi.single i 1) - z2 i x) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d)))) atTop (𝓝 0)) :
    Tendsto (fun n => smoothSobolevData (Ψ n)) atTop (𝓝 (z1, z2)) := by
  have e1 : ∀ n, eLpNorm (fun x => (Ψ n : SpatialCoordinates d → ℝ) x - z1 x) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d))) = edist (testL2 (Ψ n)) z1 := by
    intro n
    rw [MeasureTheory.Lp.edist_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [testL2_coeFn (Ψ n)] with x hx
    simp only [Pi.sub_apply, hx]
  have e2 : ∀ (i : Fin d) (n : ℕ), eLpNorm
      (fun x => fderiv ℝ (Ψ n : SpatialCoordinates d → ℝ) x (Pi.single i 1) - z2 i x) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d))) =
      edist (testPartialL2 (Ψ n) i) (z2 i) := by
    intro i n
    rw [MeasureTheory.Lp.edist_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [testPartialL2_coeFn (Ψ n) i] with x hx
    simp only [Pi.sub_apply, hx]
  have t1 : Tendsto (fun n => testL2 (Ψ n)) atTop (𝓝 z1) := by
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [← e1] using h1
  have t2 : ∀ i : Fin d, Tendsto (fun n => testPartialL2 (Ψ n) i) atTop (𝓝 (z2 i)) := by
    intro i
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [← e2 i] using h2 i
  exact t1.prodMk_nhds (tendsto_pi_nhds.mpr t2)

/-- Convergence of `S'(φ_k) ∂φ_k` to `S'(f₀) g`. -/
theorem tendsto_deriv_comp_mul {μ : Measure (SpatialCoordinates d)} {S : ℝ → ℝ}
    (hdSc : Continuous (deriv S)) (hdS1 : ∀ t, |deriv S t| ≤ 1)
    {φ dφ : ℕ → SpatialCoordinates d → ℝ} {f0 g : SpatialCoordinates d → ℝ}
    (hφ : ∀ k, AEStronglyMeasurable (φ k) μ)
    (hdφ : ∀ k, AEStronglyMeasurable (dφ k) μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun k => φ k x) atTop (𝓝 (f0 x)))
    (hf0 : AEStronglyMeasurable f0 μ) (hg : MemLp g 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (fun x => dφ k x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => deriv S (φ k x) * dφ k x - deriv S (f0 x) * g x) 2 μ)
      atTop (𝓝 0) := by
  have hθm : ∀ k, AEStronglyMeasurable (fun x => deriv S (φ k x)) μ := fun k =>
    hdSc.comp_aestronglyMeasurable (hφ k)
  have hθ0m : AEStronglyMeasurable (fun x => deriv S (f0 x)) μ := hdSc.comp_aestronglyMeasurable hf0
  -- the dominated part
  have hdom : Tendsto (fun k => eLpNorm (fun x => deriv S (φ k x) * g x - deriv S (f0 x) * g x) 2 μ)
      atTop (𝓝 0) := by
    refine tendsto_eLpNorm_two_of_tendsto_ae_of_dominated (f := fun k x => deriv S (φ k x) * g x)
      (g := fun x => deriv S (f0 x) * g x) (h := fun x => ‖g x‖) (fun k => (hθm k).mul hg.aestronglyMeasurable)
      (hg.mono (hθ0m.mul hg.aestronglyMeasurable) (Eventually.of_forall fun x => by
        rw [norm_mul]
        calc ‖deriv S (f0 x)‖ * ‖g x‖ ≤ 1 * ‖g x‖ :=
              mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hdS1 (f0 x))
                (norm_nonneg _)
          _ = ‖g x‖ := one_mul _)) hg.norm (fun k => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_mul]
      calc ‖deriv S (φ k x)‖ * ‖g x‖ ≤ 1 * ‖g x‖ :=
            mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hdS1 (φ k x))
              (norm_nonneg _)
        _ = ‖g x‖ := one_mul _
    · filter_upwards [hae] with x hx
      exact ((hdSc.tendsto (f0 x)).comp hx).mul_const (g x)
  -- the part controlled by the gradient convergence
  have hlin : ∀ k, eLpNorm (fun x => deriv S (φ k x) * dφ k x - deriv S (φ k x) * g x) 2 μ ≤
      eLpNorm (fun x => dφ k x - g x) 2 μ := by
    intro k
    refine eLpNorm_mono_ae (((hθm k).mul (hdφ k)).sub ((hθm k).mul hg.aestronglyMeasurable)) (Eventually.of_forall fun x => ?_)
    rw [← mul_sub, norm_mul]
    calc ‖deriv S (φ k x)‖ * ‖dφ k x - g x‖ ≤ 1 * ‖dφ k x - g x‖ :=
          mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hdS1 (φ k x))
            (norm_nonneg _)
      _ = ‖dφ k x - g x‖ := one_mul _
  have hsum : ∀ k, eLpNorm (fun x => deriv S (φ k x) * dφ k x - deriv S (f0 x) * g x) 2 μ ≤
      eLpNorm (fun x => dφ k x - g x) 2 μ +
        eLpNorm (fun x => deriv S (φ k x) * g x - deriv S (f0 x) * g x) 2 μ := by
    intro k
    calc eLpNorm (fun x => deriv S (φ k x) * dφ k x - deriv S (f0 x) * g x) 2 μ
        = eLpNorm ((fun x => deriv S (φ k x) * dφ k x - deriv S (φ k x) * g x) +
            (fun x => deriv S (φ k x) * g x - deriv S (f0 x) * g x)) 2 μ := by
          congr 1; funext x; simp only [Pi.add_apply]; ring
      _ ≤ eLpNorm (fun x => deriv S (φ k x) * dφ k x - deriv S (φ k x) * g x) 2 μ +
            eLpNorm (fun x => deriv S (φ k x) * g x - deriv S (f0 x) * g x) 2 μ :=
          eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add (hlin k) le_rfl
  have hlim : Tendsto (fun k => eLpNorm (fun x => dφ k x - g x) 2 μ +
      eLpNorm (fun x => deriv S (φ k x) * g x - deriv S (f0 x) * g x) 2 μ) atTop (𝓝 0) := by
    simpa using hconv.add hdom
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => bot_le) hsum

/-- **Chain rule in the killed graph.**  For `u ∈ H¹₀(U)` and a smooth `1`-Lipschitz `S` with
`S 0 = 0`, the pair `(S ∘ u, S'(u) ∇u)` belongs to the killed Sobolev graph of `U`. -/
theorem chain_smooth_mem_killed {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    (u : H10Function U) {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S) (hS0 : S 0 = 0)
    (hS1 : ∀ s t, |S s - S t| ≤ |s - t|) :
    ∃ z : SobolevData (⟨U, hU⟩ : TopologicalSpace.Opens (SpatialCoordinates d)),
      z ∈ killedSobolevGraph (⟨U, hU⟩ : TopologicalSpace.Opens (SpatialCoordinates d)) ∧
      ((z.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict U] fun x => S (u.toH1Function.toFun x)) ∧
      ∀ i : Fin d, ((z.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict U]
          fun x => deriv S (u.toH1Function.toFun x) * u.toH1Function.grad x i) := by
  classical
  set Ω : TopologicalSpace.Opens (SpatialCoordinates d) := ⟨U, hU⟩ with hΩ
  set μ : Measure (SpatialCoordinates d) := volume.restrict U with hμ
  have hSc : Continuous S := hS.continuous
  have hdSc : Continuous (deriv S) := (contDiff_infty_iff_deriv.1 hS).2.continuous
  have hdS1 : ∀ t, |deriv S t| ≤ 1 := abs_deriv_le_one hS1
  have hSabs : ∀ t, |S t| ≤ |t| := fun t => by simpa [hS0] using hS1 t 0
  set f0 : SpatialCoordinates d → ℝ := u.toH1Function.toFun with hf0def
  set gr : Fin d → SpatialCoordinates d → ℝ := fun i x => u.toH1Function.grad x i with hgrdef
  have hf0 : MemLp f0 2 μ := u.toH1Function.memL2
  have hgr : ∀ i, MemLp (gr i) 2 μ := u.toH1Function.gradMemL2
  have hSf0 : MemLp (fun x => S (f0 x)) 2 μ :=
    hf0.mono (hSc.comp_aestronglyMeasurable hf0.aestronglyMeasurable) (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hSabs (f0 x))
  have hθg : ∀ i, MemLp (fun x => deriv S (f0 x) * gr i x) 2 μ := fun i =>
    (hgr i).mono ((hdSc.comp_aestronglyMeasurable hf0.aestronglyMeasurable).mul (hgr i).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul]
        calc ‖deriv S (f0 x)‖ * ‖gr i x‖ ≤ 1 * ‖gr i x‖ :=
              mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hdS1 (f0 x))
                (norm_nonneg _)
          _ = ‖gr i x‖ := one_mul _)
  -- an almost everywhere convergent subsequence of the approximants
  have hmeas : TendstoInMeasure μ (fun n x => u.approx n x) atTop f0 :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      u.tendsto_approx
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  -- the test functions `S ∘ φ_{n_k}`
  let Ψ : ℕ → 𝓓(Ω, ℝ) := fun k =>
    ⟨fun x => S (u.approx (ns k) x), hS.comp (u.approx_smooth (ns k)),
      (u.approx_hasCompactSupport (ns k)).comp_left hS0,
      (tsupport_comp_subset hS0 _).trans (u.approx_support_subset (ns k))⟩
  have hΨ : ∀ k, (Ψ k : SpatialCoordinates d → ℝ) = fun x => S (u.approx (ns k) x) := fun k => rfl
  refine ⟨(hSf0.toLp _, fun i => (hθg i).toLp _), ?_, hSf0.coeFn_toLp, fun i => (hθg i).coeFn_toLp⟩
  -- convergence of the classical data
  have h1a : ∀ k, eLpNorm (fun x => (Ψ k : SpatialCoordinates d → ℝ) x - (hSf0.toLp _) x) 2 μ =
      eLpNorm (fun x => S (u.approx (ns k) x) - S (f0 x)) 2 μ := by
    intro k
    refine eLpNorm_congr_ae ?_
    filter_upwards [hSf0.coeFn_toLp] with x hx
    simp only [hΨ, hx]
  have h1b : ∀ k, eLpNorm (fun x => S (u.approx (ns k) x) - S (f0 x)) 2 μ ≤
      eLpNorm (fun x => u.approx (ns k) x - f0 x) 2 μ := fun k =>
    eLpNorm_mono_ae ((hSc.comp_aestronglyMeasurable (u.approx_smooth (ns k)).continuous.aestronglyMeasurable).sub (hSc.comp_aestronglyMeasurable hf0.aestronglyMeasurable)) (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hS1 (u.approx (ns k) x) (f0 x))
  have h1c : Tendsto (fun k => eLpNorm (fun x => u.approx (ns k) x - f0 x) 2 μ) atTop (𝓝 0) :=
    u.tendsto_approx.comp hns.tendsto_atTop
  have h1 : Tendsto (fun k => eLpNorm (fun x => (Ψ k : SpatialCoordinates d → ℝ) x -
      (hSf0.toLp _) x) 2 μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1c (fun k => bot_le)
      (fun k => by rw [h1a]; exact h1b k)
  have h2 : ∀ i : Fin d, Tendsto (fun k => eLpNorm
      (fun x => fderiv ℝ (Ψ k : SpatialCoordinates d → ℝ) x (Pi.single i 1) -
        (hθg i).toLp _ x) 2 μ) atTop (𝓝 0) := by
    intro i
    have hchain : ∀ k x, fderiv ℝ (Ψ k : SpatialCoordinates d → ℝ) x (Pi.single i 1) =
        deriv S (u.approx (ns k) x) * fderiv ℝ (u.approx (ns k)) x (Pi.single i 1) := by
      intro k x
      rw [hΨ]
      exact fderiv_comp_basisVec (i := i) ((hS.differentiable (by simp)) _)
        (((u.approx_smooth (ns k)).differentiable (by simp)) x)
    have hconv : Tendsto (fun k => eLpNorm (fun x => fderiv ℝ (u.approx (ns k)) x (Pi.single i 1) -
        gr i x) 2 μ) atTop (𝓝 0) := (u.tendsto_approx_grad i).comp hns.tendsto_atTop
    have hG := tendsto_deriv_comp_mul (μ := μ) (S := S) hdSc hdS1
      (φ := fun k => u.approx (ns k))
      (dφ := fun k x => fderiv ℝ (u.approx (ns k)) x (Pi.single i 1)) (f0 := f0) (g := gr i)
      (fun k => (u.approx_smooth (ns k)).continuous.aestronglyMeasurable)
      (fun k => (((u.approx_smooth (ns k)).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable) hae hf0.aestronglyMeasurable (hgr i) hconv
    refine hG.congr (fun k => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hθg i).coeFn_toLp] with x hx
    simp only [hchain, hx]
  have htend := tendsto_smoothSobolevData_of Ψ (hSf0.toLp _) (fun i => (hθg i).toLp _) h1 h2
  have hmem_closure : ((hSf0.toLp _), fun i => (hθg i).toLp _) ∈
      closure ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) : Set (SobolevData Ω)) :=
    mem_closure_of_tendsto htend (Eventually.of_forall fun k => ⟨Ψ k, rfl⟩)
  simpa [killedSobolevGraph, Submodule.topologicalClosure_coe] using! hmem_closure

end SubdiffusiveProcess.Stampacchia
