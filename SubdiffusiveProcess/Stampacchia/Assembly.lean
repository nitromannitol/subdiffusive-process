module

public import Mathlib
public import Homogenization.Sobolev.H1.Definitions
public import Homogenization.Sobolev.Truncation.WeakGradientLimit
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Stampacchia.Mollify
public import SubdiffusiveProcess.Stampacchia.ChainSmooth
public import SubdiffusiveProcess.Stampacchia.TailLimit
public import SubdiffusiveProcess.Stampacchia.AeSeq
public import SubdiffusiveProcess.Stampacchia.Pointwise

@[expose] public section

/-!
# Stampacchia composition with a normal contraction, on an arbitrary open set

For `u ∈ H¹₀(U)` and a normal contraction `T` (`T 0 = 0`, `1`-Lipschitz) there are `v ∈ H¹₀(U)` and
`θ` with `|θ| ≤ 1` such that `v = T ∘ u` and `∇v = θ ∇u` almost everywhere.

Proof: mollify `T` to smooth `1`-Lipschitz `S_n` (`S_n 0 = 0`); `(S_n ∘ u, S_n'(u) ∇u)` lies in the
killed graph (chain rule for smooth data).  Convex combinations of tails of this bounded sequence
converge in the Hilbert space of Sobolev data (Mazur's argument via the parallelogram law); the
limit is in the killed graph, its value component is `T ∘ u`, and its gradient components are
limits of `θ_m ∇u`, `|θ_m| ≤ 1`, hence of the form `θ ∇u`.
-/

open MeasureTheory Set Filter Topology Homogenization SubdiffusiveProcess
open scoped ContDiff ENNReal
noncomputable section
namespace SubdiffusiveProcess.Stampacchia

variable {d : ℕ}

theorem stampacchia_general {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    (u : H10Function U) (T : ℝ → ℝ) (h0 : T 0 = 0) (hlip : ∀ s t, |T s - T t| ≤ |s - t|) :
    ∃ (v : H10Function U) (theta : SpatialCoordinates d → ℝ),
      (∀ x, |theta x| ≤ 1) ∧
      (v.toH1Function.toFun =ᵐ[volume.restrict U] fun x => T (u.toH1Function.toFun x)) ∧
      (v.toH1Function.grad =ᵐ[volume.restrict U] fun x => theta x • u.toH1Function.grad x) := by
  classical
  set Ω : TopologicalSpace.Opens (SpatialCoordinates d) := ⟨U, hU⟩ with hΩ
  set μ : Measure (SpatialCoordinates d) := volume.restrict U with hμ
  have hTc : Continuous T := by
    have : LipschitzWith 1 T := LipschitzWith.of_dist_le_mul fun s t => by
      simpa [Real.dist_eq] using hlip s t
    exact this.continuous
  have hTabs : ∀ t, |T t| ≤ |t| := fun t => by simpa [h0] using hlip t 0
  set f0 : SpatialCoordinates d → ℝ := u.toH1Function.toFun with hf0def
  set gr : Fin d → SpatialCoordinates d → ℝ := fun i x => u.toH1Function.grad x i with hgrdef
  have hf0 : MemLp f0 2 μ := u.toH1Function.memL2
  have hgr : ∀ i, MemLp (gr i) 2 μ := u.toH1Function.gradMemL2
  have hTf0 : MemLp (fun x => T (f0 x)) 2 μ :=
    hf0.mono (hTc.comp_aestronglyMeasurable hf0.aestronglyMeasurable) (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hTabs (f0 x))
  obtain ⟨S, hSc, hS0, hS1, hST⟩ := exists_smooth_approx T h0 hlip
  have hz := fun n => chain_smooth_mem_killed hU u (hSc n) (hS0 n) (hS1 n)
  choose z hzmem hz1 hz2 using hz
  set a : DomainL2 Ω := hTf0.toLp _ with ha
  have hc : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    rw [mul_zero] at this
    exact this.congr fun n => by ring
  -- (1) the value components converge to `a`
  have hz1conv : Tendsto (fun n => (z n).1) atTop (𝓝 a) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hdom := tendsto_eLpNorm_two_of_tendsto_ae_of_dominated (μ := μ)
      (f := fun n x => S n (f0 x) - T (f0 x)) (g := fun _ => 0)
      (h := fun x => 2 * ‖f0 x‖)
      (fun n => ((hSc n).continuous.comp_aestronglyMeasurable hf0.aestronglyMeasurable).sub
        (hTc.comp_aestronglyMeasurable hf0.aestronglyMeasurable))
      (MemLp.zero) (hf0.norm.const_mul 2)
      (fun n => Eventually.of_forall fun x => by
        have h1 := hS1 n (f0 x) 0
        rw [hS0 n, sub_zero, sub_zero] at h1
        have h2 := hTabs (f0 x)
        rw [Real.norm_eq_abs]
        calc |S n (f0 x) - T (f0 x)| ≤ |S n (f0 x)| + |T (f0 x)| := abs_sub _ _
          _ ≤ 2 * ‖f0 x‖ := by rw [Real.norm_eq_abs]; linarith)
      (Eventually.of_forall fun x => by
        show Tendsto (fun n => S n (f0 x) - T (f0 x)) atTop (𝓝 0)
        exact squeeze_zero_norm (fun n => by
          rw [Real.norm_eq_abs]; exact hST n (f0 x)) hc)
    refine hdom.congr fun n => ?_
    rw [Lp.edist_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hz1 n, hTf0.coeFn_toLp] with x h1 h2
    have h2' : ((a : DomainL2 Ω) : SpatialCoordinates d → ℝ) x = T (f0 x) := h2
    show S n (f0 x) - T (f0 x) - 0 = _
    simp only [Pi.sub_apply, h1, h2', sub_zero]
    rfl
  -- (2) a bound for the quadratic form
  set M : ℝ := ‖hf0.toLp f0‖ ^ 2 + ∑ i, ‖(hgr i).toLp (gr i)‖ ^ 2 with hM
  have hzN : ∀ n, N2 (z n) ≤ M := by
    intro n
    have h1 : ‖(z n).1‖ ≤ ‖hf0.toLp f0‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [hz1 n, hf0.coeFn_toLp] with x hx hx0
      rw [hx, hx0, Real.norm_eq_abs, Real.norm_eq_abs]
      have := hS1 n (f0 x) 0
      rwa [hS0 n, sub_zero, sub_zero] at this
    have h2 : ∀ i, ‖(z n).2 i‖ ≤ ‖(hgr i).toLp (gr i)‖ := by
      intro i
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [hz2 n i, (hgr i).coeFn_toLp] with x hx hx0
      rw [hx, hx0, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      calc |deriv (S n) (f0 x)| * |gr i x| ≤ 1 * |gr i x| :=
            mul_le_mul_of_nonneg_right (abs_deriv_le_one (hS1 n) _) (abs_nonneg _)
        _ = |gr i x| := one_mul _
    unfold N2
    rw [hM]
    gcongr with i
    all_goals first | exact h1 | exact h2 i
  obtain ⟨y, yL, hyhull, hylim⟩ := exists_tail_limit z M hzN
  -- (3) the class of "scalar multiples of the gradient" is convex and contains the `z n`
  set Cset : Set (SobolevData Ω) := {w | ∃ θ : SpatialCoordinates d → ℝ, (∀ x, |θ x| ≤ 1) ∧
    ∀ i, ((w.2 i : DomainL2 Ω) : SpatialCoordinates d → ℝ) =ᵐ[μ] fun x => θ x * gr i x} with hC
  have hCcvx : Convex ℝ Cset := by
    intro w hw w' hw' p q hp hq hpq
    obtain ⟨θ, hθ, hwθ⟩ := hw
    obtain ⟨θ', hθ', hwθ'⟩ := hw'
    refine ⟨fun x => p * θ x + q * θ' x, fun x => ?_, fun i => ?_⟩
    · calc |p * θ x + q * θ' x| ≤ |p * θ x| + |q * θ' x| := abs_add_le _ _
        _ = p * |θ x| + q * |θ' x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
        _ ≤ p * 1 + q * 1 := add_le_add (mul_le_mul_of_nonneg_left (hθ x) hp)
          (mul_le_mul_of_nonneg_left (hθ' x) hq)
        _ = 1 := by rw [mul_one, mul_one, hpq]
    · have e1 := Lp.coeFn_add (p • w.2 i) (q • w'.2 i)
      have e2 := Lp.coeFn_smul p (w.2 i)
      have e3 := Lp.coeFn_smul q (w'.2 i)
      filter_upwards [e1, e2, e3, hwθ i, hwθ' i] with x h1 h2 h3 h4 h5
      change ((p • w.2 i + q • w'.2 i : DomainL2 Ω) : SpatialCoordinates d → ℝ) x = _
      rw [h1]
      simp only [Pi.add_apply]
      rw [h2, h3]
      simp only [Pi.smul_apply, smul_eq_mul, h4, h5]
      ring
  have hzC : ∀ n, z n ∈ Cset := by
    intro n
    exact ⟨fun x => deriv (S n) (f0 x), fun x => abs_deriv_le_one (hS1 n) _, hz2 n⟩
  have hyC : ∀ m, y m ∈ Cset := fun m =>
    convexHull_min (by rintro w ⟨n, _, rfl⟩; exact hzC n) hCcvx (hyhull m)
  -- (4) the limit lies in the killed graph
  have hkill_cvx : Convex ℝ (killedSobolevGraph Ω : Set (SobolevData Ω)) :=
    (killedSobolevGraph Ω).convex
  have hykill : ∀ m, y m ∈ killedSobolevGraph Ω := fun m =>
    convexHull_min (by rintro w ⟨n, _, rfl⟩; exact hzmem n) hkill_cvx (hyhull m)
  have hyLkill : yL ∈ killedSobolevGraph Ω :=
    isClosed_killedSobolevGraph.mem_of_tendsto hylim (Eventually.of_forall hykill)
  -- (5) the value component of the limit is `a`
  have hy1conv : Tendsto (fun m => (y m).1) atTop (𝓝 a) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hz1conv (ε / 2) (by positivity)
    refine ⟨N, fun m hm => ?_⟩
    have hcvx : Convex ℝ {w : SobolevData Ω | ‖w.1 - a‖ ≤ ε / 2} := by
      have := (convex_closedBall a (ε / 2)).linear_preimage
        (LinearMap.fst ℝ (DomainL2 Ω) (Fin d → DomainL2 Ω))
      convert this using 1
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall,
        LinearMap.fst_apply, dist_eq_norm]
    have hsub : z '' Ici m ⊆ {w : SobolevData Ω | ‖w.1 - a‖ ≤ ε / 2} := by
      rintro _ ⟨n, hn, rfl⟩
      have := hN n (hm.trans hn)
      rw [dist_eq_norm] at this
      exact this.le
    have := convexHull_min hsub hcvx (hyhull m)
    rw [dist_eq_norm]
    exact lt_of_le_of_lt this (by linarith)
  have hyL1 : yL.1 = a :=
    tendsto_nhds_unique ((continuous_fst.tendsto yL).comp hylim) hy1conv
  -- (6) an almost everywhere convergent subsequence of the gradient components
  choose θm hθm hyθ using fun m => hyC m
  have hycomp : ∀ i, Tendsto (fun m => (y m).2 i) atTop (𝓝 (yL.2 i)) := fun i =>
    ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto yL).comp hylim)
  obtain ⟨ns, hns, hae⟩ := exists_seq_tendsto_ae_pi (μ := μ)
    (F := fun i m x => ((y m).2 i : DomainL2 Ω) x) (G := fun i x => (yL.2 i : DomainL2 Ω) x)
    (fun i m => (Lp.stronglyMeasurable _).aestronglyMeasurable)
    (fun i => (Lp.stronglyMeasurable _).aestronglyMeasurable)
    (fun i => by
      have := (tendsto_iff_edist_tendsto_0.1 (hycomp i))
      refine this.congr fun m => ?_
      rw [Lp.edist_def]
      rfl)
  have hall : ∀ᵐ x ∂μ, ∀ m i, ((y m).2 i : DomainL2 Ω) x = θm m x * gr i x := by
    rw [ae_all_iff]; intro m
    rw [ae_all_iff]; intro i
    exact hyθ m i
  -- (7) the scalar factor
  set theta0 : SpatialCoordinates d → ℝ := fun x =>
    if ∑ i, gr i x ^ 2 = 0 then 0 else (∑ i, (yL.2 i : DomainL2 Ω) x * gr i x) / (∑ i, gr i x ^ 2)
    with htheta0
  set theta : SpatialCoordinates d → ℝ := fun x => if |theta0 x| ≤ 1 then theta0 x else 0
    with htheta
  have hgood : ∀ᵐ x ∂μ, |theta0 x| ≤ 1 ∧ ∀ i, (yL.2 i : DomainL2 Ω) x = theta0 x * gr i x := by
    filter_upwards [hae, hall] with x hx1 hx2
    exact pointwise_theta (fun i => gr i x) (fun i => (yL.2 i : DomainL2 Ω) x)
      (fun j => θm (ns j) x) (fun j => hθm _ x) (fun i => by
        refine (hx1 i).congr fun j => ?_
        exact (hx2 (ns j) i))
  -- (8) the killed function
  obtain ⟨v, hv1, hv2⟩ := exists_nativeH10Function_of_killedSobolevGraph
    (⟨yL, hyLkill⟩ : killedSobolevGraph Ω)
  refine ⟨v, theta, fun x => ?_, ?_, ?_⟩
  · by_cases h : |theta0 x| ≤ 1
    · simp only [htheta, if_pos h]; exact h
    · simp only [htheta, if_neg h]; simp
  · have : v.toH1Function.toFun = fun x => (yL.1 : DomainL2 Ω) x := hv1
    rw [this, hyL1]
    exact hTf0.coeFn_toLp
  · have hgr' : v.toH1Function.grad = fun x i => (yL.2 i : DomainL2 Ω) x := hv2
    rw [hgr']
    filter_upwards [hgood] with x hx
    funext i
    have hth : theta x = theta0 x := by
      simp only [htheta, if_pos hx.1]
    simp only [Pi.smul_apply, smul_eq_mul, hth, hx.2 i]
    rfl

end SubdiffusiveProcess.Stampacchia
