module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-! Classical Arzela--Ascoli compactness with a finite closed Holder cover.
The statement is about a general compact metric space and contains no forms,
coefficients, random fields, or energy estimates.
Proof: bounded by the sum of the piece bounds; uniform equicontinuity from the Holder bounds on pieces:
if `x_k in A_i`, `y_k in A_j`, `dist x_k y_k -> 0` then a subsequence converges to a common limit in `A_i cap A_j`
and the Holder bounds on both pieces at that limit give `|F_n x_k - F_n y_k| -> 0` uniformly in `n`;
then Arzela--Ascoli for bounded continuous functions on a compact space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_pa_bound {X : Type*} {ι : Type*} [Fintype ι] (A : ι → Set X)
    (hcover : ∀ x, ∃ i, x ∈ A i) (F : ℕ → X → ℝ) (alpha : ℝ) [MetricSpace X]
    (hlocal : ∀ i, ∃ B : ℝ, 0 ≤ B ∧
      (∀ n x, x ∈ A i → |F n x| ≤ B) ∧
      (∀ n x, x ∈ A i → ∀ y, y ∈ A i → |F n x - F n y| ≤ B * dist x y ^ alpha)) :
    ∃ B : ℝ, ∀ n x, |F n x| ≤ B := by
  classical
  choose B hB0 hBd _ using hlocal
  refine ⟨∑ i, B i, ?_⟩
  intro n x
  obtain ⟨i, hi⟩ := hcover x
  exact le_trans (hBd i n x hi) (Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ i))

theorem aux_pa_holder_tendsto {X : Type*} [MetricSpace X] (u : ℕ → X) (z : X)
    (hu : Tendsto u atTop (𝓝 z)) (B alpha : ℝ) (halpha : 0 < alpha) :
    Tendsto (fun k => B * dist (u k) z ^ alpha) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => dist (u k) z) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 hu
  have h2 : Tendsto (fun k => dist (u k) z ^ alpha) atTop (𝓝 (0 ^ alpha)) :=
    h1.rpow_const (Or.inr halpha.le)
  rw [Real.zero_rpow halpha.ne'] at h2
  have h3 := h2.const_mul B
  simpa using h3

theorem aux_pa_pair_tendsto {X : Type*} [MetricSpace X] (Ai Aj : Set X) (F : ℕ → X → ℝ)
    (alpha : ℝ) (halpha : 0 < alpha) (Bi Bj : ℝ)
    (hBi : ∀ n x, x ∈ Ai → ∀ y, y ∈ Ai → |F n x - F n y| ≤ Bi * dist x y ^ alpha)
    (hBj : ∀ n x, x ∈ Aj → ∀ y, y ∈ Aj → |F n x - F n y| ≤ Bj * dist x y ^ alpha)
    (z : X) (hzi : z ∈ Ai) (hzj : z ∈ Aj) (n : ℕ → ℕ) (u v : ℕ → X)
    (hu : ∀ k, u k ∈ Ai) (hv : ∀ k, v k ∈ Aj)
    (hu' : Tendsto u atTop (𝓝 z)) (hv' : Tendsto v atTop (𝓝 z)) :
    Tendsto (fun k => |F (n k) (u k) - F (n k) (v k)|) atTop (𝓝 0) := by
  have hBiu : Tendsto (fun k => Bi * dist (u k) z ^ alpha) atTop (𝓝 0) :=
    aux_pa_holder_tendsto u z hu' Bi alpha halpha
  have hBjv : Tendsto (fun k => Bj * dist (v k) z ^ alpha) atTop (𝓝 0) :=
    aux_pa_holder_tendsto v z hv' Bj alpha halpha
  have hg : Tendsto (fun k => Bi * dist (u k) z ^ alpha + Bj * dist (v k) z ^ alpha) atTop (𝓝 0) := by
    simpa using hBiu.add hBjv
  refine squeeze_zero (fun k => abs_nonneg _) (fun k => ?_) hg
  calc |F (n k) (u k) - F (n k) (v k)|
      ≤ |F (n k) (u k) - F (n k) z| + |F (n k) z - F (n k) (v k)| := abs_sub_le _ _ _
    _ ≤ Bi * dist (u k) z ^ alpha + Bj * dist z (v k) ^ alpha :=
        add_le_add (hBi (n k) (u k) (hu k) z hzi) (hBj (n k) z hzj (v k) (hv k))
    _ = Bi * dist (u k) z ^ alpha + Bj * dist (v k) z ^ alpha := by rw [dist_comm z (v k)]

theorem aux_pa_pair_subseq {X : Type*} [MetricSpace X] [CompactSpace X] (Ai Aj : Set X)
    (hi : IsClosed Ai) (hj : IsClosed Aj) (x y : ℕ → X)
    (hx : ∀ k, x k ∈ Ai) (hy : ∀ k, y k ∈ Aj)
    (hd : ∀ k, dist (x k) (y k) < 1 / ((k : ℝ) + 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z, z ∈ Ai ∧ z ∈ Aj ∧
      Tendsto (fun k => x (φ k)) atTop (𝓝 z) ∧ Tendsto (fun k => y (φ k)) atTop (𝓝 z) := by
  obtain ⟨z, φ, hφ, hxlim⟩ := CompactSpace.tendsto_subseq x
  have hφle : ∀ k, k ≤ φ k := fun k => hφ.id_le k
  have h1 : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => by positivity)
    · intro k
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hkφ : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφle k
      exact one_div_le_one_div_of_le hk (by linarith)
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hx0 : Tendsto (fun k => dist (x (φ k)) z) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hxlim
  have hsum : Tendsto (fun k => 1 / ((φ k : ℝ) + 1) + dist (x (φ k)) z) atTop (𝓝 0) := by
    have := h1.add hx0
    simpa using this
  have hy0 : Tendsto (fun k => dist (y (φ k)) z) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => dist_nonneg)
    · intro k
      calc dist (y (φ k)) z ≤ dist (y (φ k)) (x (φ k)) + dist (x (φ k)) z := dist_triangle _ _ _
        _ = dist (x (φ k)) (y (φ k)) + dist (x (φ k)) z := by rw [dist_comm]
        _ ≤ 1 / ((φ k : ℝ) + 1) + dist (x (φ k)) z := by
            have := (hd (φ k)).le
            linarith
    · exact hsum
  have hylim : Tendsto (fun k => y (φ k)) atTop (𝓝 z) :=
    tendsto_iff_dist_tendsto_zero.mpr hy0
  exact ⟨φ, hφ, z, hi.mem_of_tendsto hxlim (Eventually.of_forall fun k => hx (φ k)),
    hj.mem_of_tendsto hylim (Eventually.of_forall fun k => hy (φ k)), hxlim, hylim⟩

theorem aux_pa_pair {X : Type*} [MetricSpace X] [CompactSpace X] (Ai Aj : Set X)
    (hi : IsClosed Ai) (hj : IsClosed Aj) (F : ℕ → X → ℝ)
    (alpha : ℝ) (halpha : 0 < alpha) (Bi Bj : ℝ)
    (hBi : ∀ n x, x ∈ Ai → ∀ y, y ∈ Ai → |F n x - F n y| ≤ Bi * dist x y ^ alpha)
    (hBj : ∀ n x, x ∈ Aj → ∀ y, y ∈ Aj → |F n x - F n y| ≤ Bj * dist x y ^ alpha) :
    ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ Ai, ∀ y ∈ Aj, dist x y < δ → |F n x - F n y| < ε := by
  intro ε hε
  by_contra h
  push Not at h
  have h' : ∀ k : ℕ, ∃ n : ℕ, ∃ x ∈ Ai, ∃ y ∈ Aj,
      dist x y < 1 / ((k : ℝ) + 1) ∧ ε ≤ |F n x - F n y| := by
    intro k
    exact h _ (by positivity)
  choose n x hx y hy hdd hineq using h'
  obtain ⟨φ, hφ, z, hzi, hzj, hxt, hyt⟩ := aux_pa_pair_subseq Ai Aj hi hj x y hx hy hdd
  have hlim := aux_pa_pair_tendsto Ai Aj F alpha halpha Bi Bj hBi hBj z hzi hzj
    (fun k => n (φ k)) (fun k => x (φ k)) (fun k => y (φ k))
    (fun k => hx (φ k)) (fun k => hy (φ k)) hxt hyt
  have hle := ge_of_tendsto' hlim (fun k => hineq (φ k))
  linarith

theorem aux_pa_equicont {X : Type*} {ι : Type*} [MetricSpace X] [Fintype ι] (A : ι → Set X)
    (hcover : ∀ x, ∃ i, x ∈ A i) (F : ℕ → X → ℝ)
    (hpair : ∀ i j, ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ A i, ∀ y ∈ A j, dist x y < δ →
      |F n x - F n y| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ n x y, dist x y < δ → |F n x - F n y| < ε := by
  intro ε hε
  by_cases hι : Nonempty ι
  · obtain ⟨i0⟩ := hι
    choose δ hδ using fun i j => hpair i j ε hε
    let s : Finset ℝ := Finset.univ.image (fun p : ι × ι => δ p.1 p.2)
    have hsne : s.Nonempty := ⟨δ i0 i0, Finset.mem_image.mpr ⟨(i0, i0), Finset.mem_univ _, rfl⟩⟩
    refine ⟨s.min' hsne, ?_, ?_⟩
    · have hmem := Finset.min'_mem s hsne
      rw [Finset.mem_image] at hmem
      obtain ⟨p, _, hp⟩ := hmem
      rw [← hp]
      exact (hδ p.1 p.2).1
    · intro n x y hxy
      obtain ⟨i, hi⟩ := hcover x
      obtain ⟨j, hj⟩ := hcover y
      have hle : s.min' hsne ≤ δ i j :=
        Finset.min'_le s (δ i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
      exact (hδ i j).2 n x hi y hj (lt_of_lt_of_le hxy hle)
  · refine ⟨1, one_pos, ?_⟩
    intro n x y _
    exact (hι ⟨(hcover x).choose⟩).elim

theorem aux_pa_equicont_range {X : Type*} [MetricSpace X] [CompactSpace X] (F : ℕ → X → ℝ)
    (hcont : ∀ n, Continuous (F n))
    (hE : ∀ ε > 0, ∃ δ > 0, ∀ n x y, dist x y < δ → |F n x - F n y| < ε) :
    Equicontinuous ((↑) : Set.range (fun n => BoundedContinuousFunction.mkOfCompact
      (⟨F n, hcont n⟩ : ContinuousMap X ℝ)) → X → ℝ) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := hE ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro x hx i
  obtain ⟨n, hn⟩ := i.2
  have hgi : i.1 = BoundedContinuousFunction.mkOfCompact (⟨F n, hcont n⟩ : ContinuousMap X ℝ) := hn.symm
  rw [Real.dist_eq, hgi]
  rw [BoundedContinuousFunction.mkOfCompact_apply, BoundedContinuousFunction.mkOfCompact_apply]
  exact hδ n x₀ x (by rw [dist_comm]; exact hx)

theorem aux_pa_ascoli {X : Type*} [MetricSpace X] [CompactSpace X] (F : ℕ → X → ℝ)
    (hcont : ∀ n, Continuous (F n)) (B : ℝ) (hB : ∀ n x, |F n x| ≤ B)
    (hE : ∀ ε > 0, ∃ δ > 0, ∀ n x y, dist x y < δ → |F n x - F n y| < ε) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ f : X → ℝ, Continuous f ∧ TendstoUniformly (fun n => F (seq n)) f atTop := by
  let Fb : ℕ → BoundedContinuousFunction X ℝ := fun n => BoundedContinuousFunction.mkOfCompact (⟨F n, hcont n⟩ : C(X, ℝ))
  have hin : ∀ (f : BoundedContinuousFunction X ℝ) (x : X), f ∈ Set.range Fb → f x ∈ Set.Icc (-B) B := by
    rintro f x ⟨n, rfl⟩
    simpa only [Fb, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk, Set.mem_Icc] using abs_le.1 (hB n x)
  have heq : Equicontinuous (fun x : Set.range Fb => ⇑(↑x : BoundedContinuousFunction X ℝ) : Set.range Fb → X → ℝ) :=
    aux_pa_equicont_range F hcont hE
  have hcomp : IsCompact (closure (Set.range Fb)) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc (-B) B) isCompact_Icc (Set.range Fb) hin heq
  obtain ⟨g, _hg, φ, hφ_mono, hφ_tendsto⟩ :=
    hcomp.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨φ, hφ_mono, ⇑g, g.continuous, ?_⟩
  have htu : TendstoUniformly (fun n => ⇑(Fb (φ n))) (⇑g) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hφ_tendsto
  exact htu

/-- A continuous family bounded and uniformly Holder on a finite closed cover has a uniformly convergent subsequence. -/
theorem inputs_classical_piecewise_ascoli
    {X : Type*} [MetricSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] (A : ι → Set X)
    (_hclosed : ∀ i, IsClosed (A i)) (_hcover : ∀ x, ∃ i, x ∈ A i)
    (F : ℕ → X → ℝ) (_hcont : ∀ n, Continuous (F n))
    (alpha : ℝ) (_halpha : 0 < alpha)
    (_hlocal : ∀ i, ∃ B : ℝ, 0 ≤ B ∧
      (∀ n x, x ∈ A i → |F n x| ≤ B) ∧
      (∀ n x, x ∈ A i → ∀ y, y ∈ A i →
        |F n x - F n y| ≤ B * dist x y ^ alpha)) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ f : X → ℝ, Continuous f ∧ TendstoUniformly (fun n => F (seq n)) f atTop := by
  obtain ⟨B, hB⟩ := aux_pa_bound A _hcover F alpha _hlocal
  refine aux_pa_ascoli F _hcont B hB (aux_pa_equicont A _hcover F fun i j => ?_)
  obtain ⟨Bi, -, -, hBi⟩ := _hlocal i
  obtain ⟨Bj, -, -, hBj⟩ := _hlocal j
  exact aux_pa_pair (A i) (A j) (_hclosed i) (_hclosed j) F alpha _halpha Bi Bj hBi hBj

end SubdiffusiveProcess.Paper
