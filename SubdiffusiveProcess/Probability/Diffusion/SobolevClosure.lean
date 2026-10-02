import Homogenization.Sobolev.Foundations.H10Graph




set_option autoImplicit false

open Homogenization MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ} {U : Set (Vec d)}

/-- The `L²` distance between scalar representatives of two `H¹` functions is
the scalar `L²` distance between their `toScalarL2` realisations. -/
private theorem eLpNorm_toFun_sub_eq_edist_toScalarL2
    (u v : H1Function U) :
    MeasureTheory.eLpNorm (fun x => u.toFun x - v.toFun x) 2 (volumeMeasureOn U)
      = edist u.toScalarL2 v.toScalarL2 := by
  rw [MeasureTheory.Lp.edist_def]
  refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
  filter_upwards [u.coeFn_toScalarL2, v.coeFn_toScalarL2] with x hu hv
  simp [Pi.sub_apply, hu, hv]

/-- The coordinate-wise `L²` distance between weak gradients equals the
`ScalarL2` distance between `gradCoordToScalarL2` realisations. -/
private theorem eLpNorm_grad_coord_sub_eq_edist_gradCoordToScalarL2
    (u v : H1Function U) (i : Fin d) :
    MeasureTheory.eLpNorm (fun x => u.grad x i - v.grad x i) 2 (volumeMeasureOn U)
      = edist (u.gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i) := by
  rw [MeasureTheory.Lp.edist_def]
  refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
  filter_upwards [u.coeFn_gradCoordToScalarL2 i, v.coeFn_gradCoordToScalarL2 i]
    with x hu hv
  simp [Pi.sub_apply, hu, hv]

/-- Coordinate-wise `L²` distance of two weak gradients is controlled by the
`HilbertVectorL2` distance of their gradient realisations. -/
private theorem eLpNorm_grad_coord_sub_le_edist_gradToHilbertVectorL2
    (u v : H1Function U) (i : Fin d) :
    MeasureTheory.eLpNorm (fun x => u.grad x i - v.grad x i) 2 (volumeMeasureOn U)
      ≤ edist u.gradToHilbertVectorL2 v.gradToHilbertVectorL2 := by
  have hrhs :
      edist u.gradToHilbertVectorL2 v.gradToHilbertVectorL2
        = MeasureTheory.eLpNorm
            (fun x => HilbertVec.ofVec (u.grad x - v.grad x)) 2
            (volumeMeasureOn U) := by
    rw [MeasureTheory.Lp.edist_def]
    refine MeasureTheory.eLpNorm_congr_ae ?_
    filter_upwards
        [u.coeFn_gradToHilbertVectorL2, v.coeFn_gradToHilbertVectorL2] with x hu hv
    simp [Pi.sub_apply, hu, hv, hilbertifyVecField]
  rw [hrhs]
  refine MeasureTheory.eLpNorm_mono_ae (Filter.Eventually.of_forall ?_)
  intro x
  have hcoord : ‖u.grad x i - v.grad x i‖ ≤ ‖u.grad x - v.grad x‖ := by
    simpa [Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (u.grad x - v.grad x) i
  have hVec_le_Hilbert :
      ‖u.grad x - v.grad x‖ ≤ ‖HilbertVec.ofVec (u.grad x - v.grad x)‖ :=
    HilbertVec.norm_le_norm_ofVec (u.grad x - v.grad x)
  exact hcoord.trans hVec_le_Hilbert

/-- `ScalarL2` distance on `gradCoordToScalarL2` is controlled by the
`HilbertVectorL2` distance on `gradToHilbertVectorL2`. -/
private theorem edist_gradCoordToScalarL2_le_edist_gradToHilbertVectorL2
    (u v : H1Function U) (i : Fin d) :
    edist (u.gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i)
      ≤ edist u.gradToHilbertVectorL2 v.gradToHilbertVectorL2 := by
  rw [← eLpNorm_grad_coord_sub_eq_edist_gradCoordToScalarL2]
  exact eLpNorm_grad_coord_sub_le_edist_gradToHilbertVectorL2 u v i

/-- Every point of the closed `H¹₀` graph is realized by an honest `H¹₀`
function on every open domain. The witness is obtained by
diagonalising closure approximations against each graph approximant's internal
smooth compactly supported approximation data. -/
theorem exists_h10Function_of_mem_h10GraphClosedSubmodule_of_isOpen
    (hU : IsOpen U)
    {z : ScalarL2 U × HilbertVectorL2 U}
    (hz : z ∈ (h10GraphClosedSubmodule U).toSubmodule) :
    ∃ u : H10Function U,
      u.toH1Function.toScalarL2 = z.1
        ∧ u.toH1Function.gradToHilbertVectorL2 = z.2 := by
  classical
  have hUopen : IsOpen U := hU
  have hzH1 : z ∈ h1GraphClosedSubmodule (U := U) :=
    h10GraphClosedSubmodule_le_h1GraphClosedSubmodule (U := U) hz
  set v : H1Function U := toH1FunctionOfMemH1Graph (U := U) z hzH1 with v_def
  have hv_val : v.toScalarL2 = z.1 :=
    toH1FunctionOfMemH1Graph_toScalarL2 (U := U) z hzH1
  have hv_grad : v.gradToHilbertVectorL2 = z.2 :=
    toH1FunctionOfMemH1Graph_gradToHilbertVectorL2 (U := U) z hzH1
  have hz_closure :
      z ∈ closure ((h10GraphSubmodule U : Submodule ℝ
        (ScalarL2 U × HilbertVectorL2 U)) : Set (ScalarL2 U × HilbertVectorL2 U)) := by
    have hzSub : z ∈ (h10GraphSubmodule U).topologicalClosure := hz
    simpa [Submodule.topologicalClosure_coe] using hzSub
  obtain ⟨ψ, hψ_mem, hψ_tendsto⟩ := mem_closure_iff_seq_limit.mp hz_closure
  choose φ hφ_val hφ_grad using hψ_mem
  have hval_tendsto :
      Filter.Tendsto (fun n => (φ n).toH1Function.toScalarL2) Filter.atTop
        (nhds v.toScalarL2) := by
    rw [hv_val]
    exact hψ_tendsto.fst_nhds.congr'
      (Filter.Eventually.of_forall fun n => (hφ_val n).symm)
  have hgrad_tendsto :
      Filter.Tendsto (fun n => (φ n).toH1Function.gradToHilbertVectorL2) Filter.atTop
        (nhds v.gradToHilbertVectorL2) := by
    rw [hv_grad]
    exact hψ_tendsto.snd_nhds.congr'
      (Filter.Eventually.of_forall fun n => (hφ_grad n).symm)
  have hgrad_edist_zero :
      Filter.Tendsto
        (fun n => edist (φ n).toH1Function.gradToHilbertVectorL2 v.gradToHilbertVectorL2)
        Filter.atTop (nhds 0) := by
    rw [← edist_self v.gradToHilbertVectorL2]
    exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp hgrad_tendsto
  have hgradcoord_edist_zero :
      ∀ i : Fin d, Filter.Tendsto
        (fun n => edist ((φ n).toH1Function.gradCoordToScalarL2 i)
          (v.gradCoordToScalarL2 i))
        Filter.atTop (nhds 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ => (0 : ENNReal))
      (h := fun n =>
        edist (φ n).toH1Function.gradToHilbertVectorL2 v.gradToHilbertVectorL2)
      tendsto_const_nhds hgrad_edist_zero (fun _ => bot_le) ?_
    intro n
    exact edist_gradCoordToScalarL2_le_edist_gradToHilbertVectorL2
      (φ n).toH1Function v i
  have hgradcoord_tendsto :
      ∀ i : Fin d, Filter.Tendsto
        (fun n => (φ n).toH1Function.gradCoordToScalarL2 i) Filter.atTop
        (nhds (v.gradCoordToScalarL2 i)) := by
    intro i
    refine (EMetric.tendsto_nhds).mpr ?_
    intro ε hε
    exact (hgradcoord_edist_zero i).eventually (gt_mem_nhds hε)
  have happroxH1_val :
      ∀ n : ℕ, Filter.Tendsto
        (fun m => (H10Function.approxH1 hUopen (φ n) m).toScalarL2)
        Filter.atTop (nhds (φ n).toH1Function.toScalarL2) :=
    fun n => H10Function.tendsto_approxH1_toScalarL2 hUopen (φ n)
  have happroxH1_gradcoord :
      ∀ n : ℕ, ∀ i : Fin d, Filter.Tendsto
        (fun m => (H10Function.approxH1 hUopen (φ n) m).gradCoordToScalarL2 i)
        Filter.atTop (nhds ((φ n).toH1Function.gradCoordToScalarL2 i)) :=
    fun n i =>
      H10Function.tendsto_approxH1_gradCoordToScalarL2 hUopen (φ n) i
  have diagonal :
      ∀ n : ℕ, ∃ m : ℕ,
        dist (H10Function.approxH1 hUopen (φ n) m).toScalarL2
            (φ n).toH1Function.toScalarL2 ≤ ((n : ℝ) + 1)⁻¹ ∧
        (∀ i : Fin d,
          dist ((H10Function.approxH1 hUopen (φ n) m).gradCoordToScalarL2 i)
            ((φ n).toH1Function.gradCoordToScalarL2 i) ≤ ((n : ℝ) + 1)⁻¹) := by
    intro n
    have hε_pos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by
      refine inv_pos.mpr ?_
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hscalar := (Metric.tendsto_atTop.mp (happroxH1_val n)) _ hε_pos
    have hcoords : ∀ i : Fin d, ∃ N : ℕ, ∀ m ≥ N,
        dist ((H10Function.approxH1 hUopen (φ n) m).gradCoordToScalarL2 i)
          ((φ n).toH1Function.gradCoordToScalarL2 i) < ((n : ℝ) + 1)⁻¹ := fun i =>
      (Metric.tendsto_atTop.mp (happroxH1_gradcoord n i)) _ hε_pos
    choose Nc hNc using hcoords
    obtain ⟨Nv, hNv⟩ := hscalar
    let M : ℕ := max Nv ((Finset.univ : Finset (Fin d)).sup Nc)
    have hMv : Nv ≤ M := le_max_left _ _
    have hMc : ∀ i : Fin d, Nc i ≤ M := by
      intro i
      refine le_max_of_le_right ?_
      exact Finset.le_sup (f := Nc) (Finset.mem_univ i)
    refine ⟨M, (hNv M hMv).le, ?_⟩
    intro i
    exact (hNc i M (hMc i)).le
  choose m hm_val hm_grad using diagonal
  let a : ℕ → H1Function U := fun n => H10Function.approxH1 hUopen (φ n) (m n)
  have hinv_small : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ((n : ℝ) + 1)⁻¹ < ε := by
    intro ε hε
    have htend_one_div :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have heq : (fun n : ℕ => 1 / ((n : ℝ) + 1)) =
        fun n : ℕ => ((n : ℝ) + 1)⁻¹ := by
      funext n; rw [one_div]
    rw [heq] at htend_one_div
    have hev := Metric.tendsto_atTop.mp htend_one_div ε hε
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn => ?_⟩
    have hnn := hN n hn
    have hpos : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by
      refine inv_nonneg.mpr ?_
      have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc ((n : ℝ) + 1)⁻¹ = |((n : ℝ) + 1)⁻¹| := (abs_of_nonneg hpos).symm
      _ = dist (((n : ℝ) + 1)⁻¹) 0 := by rw [Real.dist_eq, sub_zero]
      _ < ε := hnn
  have ha_val :
      Filter.Tendsto (fun n => (a n).toScalarL2) Filter.atTop (nhds v.toScalarL2) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨N₁, hN₁⟩ := hinv_small (ε / 2) hε2
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hval_tendsto (ε / 2) hε2
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn1 : N₁ ≤ n := le_of_max_le_left hn
    have hn2 : N₂ ≤ n := le_of_max_le_right hn
    have htri : dist (a n).toScalarL2 v.toScalarL2 ≤
        dist (a n).toScalarL2 (φ n).toH1Function.toScalarL2
          + dist (φ n).toH1Function.toScalarL2 v.toScalarL2 := dist_triangle _ _ _
    have hm_val_n : dist (a n).toScalarL2 (φ n).toH1Function.toScalarL2
        ≤ ((n : ℝ) + 1)⁻¹ := hm_val n
    have hN₂_n : dist (φ n).toH1Function.toScalarL2 v.toScalarL2 < ε / 2 := hN₂ n hn2
    have hN₁_n : ((n : ℝ) + 1)⁻¹ < ε / 2 := hN₁ n hn1
    linarith
  have ha_gradcoord :
      ∀ i : Fin d, Filter.Tendsto (fun n => (a n).gradCoordToScalarL2 i)
        Filter.atTop (nhds (v.gradCoordToScalarL2 i)) := by
    intro i
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨N₁, hN₁⟩ := hinv_small (ε / 2) hε2
    obtain ⟨N₂, hN₂⟩ :=
      Metric.tendsto_atTop.mp (hgradcoord_tendsto i) (ε / 2) hε2
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn1 : N₁ ≤ n := le_of_max_le_left hn
    have hn2 : N₂ ≤ n := le_of_max_le_right hn
    have htri : dist ((a n).gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i) ≤
        dist ((a n).gradCoordToScalarL2 i) ((φ n).toH1Function.gradCoordToScalarL2 i)
          + dist ((φ n).toH1Function.gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i) :=
      dist_triangle _ _ _
    have hm_grad_n :
        dist ((a n).gradCoordToScalarL2 i) ((φ n).toH1Function.gradCoordToScalarL2 i)
          ≤ ((n : ℝ) + 1)⁻¹ := hm_grad n i
    have hN₂_n : dist ((φ n).toH1Function.gradCoordToScalarL2 i)
        (v.gradCoordToScalarL2 i) < ε / 2 := hN₂ n hn2
    have hN₁_n : ((n : ℝ) + 1)⁻¹ < ε / 2 := hN₁ n hn1
    linarith
  have htendsto_val_eLpNorm :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x => (φ n).approx (m n) x - v.toFun x) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    have hedist :
        Filter.Tendsto (fun n => edist (a n).toScalarL2 v.toScalarL2) Filter.atTop
          (nhds 0) := by
      rw [← edist_self v.toScalarL2]
      exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp ha_val
    refine hedist.congr ?_
    intro n
    rw [← eLpNorm_toFun_sub_eq_edist_toScalarL2]
    rfl
  have htendsto_grad_eLpNorm :
      ∀ i : Fin d, Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ ((φ n).approx (m n)) x) (basisVec i) -
                v.grad x i) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    intro i
    have hedist :
        Filter.Tendsto
          (fun n => edist ((a n).gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i))
          Filter.atTop (nhds 0) := by
      rw [← edist_self (v.gradCoordToScalarL2 i)]
      exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp
        (ha_gradcoord i)
    refine hedist.congr ?_
    intro n
    rw [← eLpNorm_grad_coord_sub_eq_edist_gradCoordToScalarL2]
    rfl
  let u : H10Function U :=
    { toH1Function := v
      approx := fun n => (φ n).approx (m n)
      approx_smooth := fun n => (φ n).approx_smooth (m n)
      approx_hasCompactSupport := fun n => (φ n).approx_hasCompactSupport (m n)
      approx_support_subset := fun n => (φ n).approx_support_subset (m n)
      tendsto_approx := htendsto_val_eLpNorm
      tendsto_approx_grad := htendsto_grad_eLpNorm }
  exact ⟨u, hv_val, hv_grad⟩

end SubdiffusiveProcess.Probability.Diffusion
