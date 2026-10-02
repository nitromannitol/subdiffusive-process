import Mathlib
import Homogenization.Sobolev.H1.Definitions
import Homogenization.Geometry.ConvexDomain
import SubdiffusiveProcess.Gluing.Truncation
import SubdiffusiveProcess.Gluing.Weak

/-!
# Gluing continuous `H¹` cell functions over a cubical partition

`h1_glue`: finitely many pairwise disjoint open cubes `Q_i = ball c_i (r_i/2)` inside the cube
`Ω = ball z (R/2)` whose closures cover `closure Ω`; `u_i ∈ H¹(Q_i)` continuous on `closure Q_i`
with `u_i = g` on `frontier Q_i` and `g = 0` on `frontier Ω`.  Then there is an `H¹₀(Ω)` function
`w`, continuous on `closure Ω`, equal to `u_i` on `closure Q_i`, whose gradient is `∇u_i` a.e. on
each `Q_i`.
-/

open MeasureTheory Set Filter Topology Homogenization
open scoped ContDiff
noncomputable section
namespace SubdiffusiveProcess.Gluing

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem h1_glue [NeZero d] (z : Fin d → ℝ) (R : ℝ) (hR : 0 < R)
    (cent : ι → Fin d → ℝ) (rad : ι → ℝ) (hrad : ∀ i, 0 < rad i)
    (hsub : ∀ i, Metric.ball (cent i) (rad i / 2) ⊆ Metric.ball z (R / 2))
    (hdisj : Pairwise fun i k => Disjoint (Metric.ball (cent i) (rad i / 2))
      (Metric.ball (cent k) (rad k / 2)))
    (hcover : (⋃ i, closure (Metric.ball (cent i) (rad i / 2))) = closure (Metric.ball z (R / 2)))
    (g : (Fin d → ℝ) → ℝ) (hg0 : ∀ x ∈ frontier (Metric.ball z (R / 2)), g x = 0)
    (uc : ∀ i, H1Function (Metric.ball (cent i) (rad i / 2)))
    (hcont : ∀ i, ContinuousOn (uc i).toFun (closure (Metric.ball (cent i) (rad i / 2))))
    (htrace : ∀ i, ∀ x ∈ frontier (Metric.ball (cent i) (rad i / 2)), (uc i).toFun x = g x) :
    ∃ w : H10Function (Metric.ball z (R / 2)),
      ContinuousOn w.toH1Function.toFun (closure (Metric.ball z (R / 2))) ∧
      (∀ i, EqOn w.toH1Function.toFun (uc i).toFun (closure (Metric.ball (cent i) (rad i / 2)))) ∧
      ∀ i j, (fun x => w.toH1Function.grad x j) =ᵐ[volume.restrict
        (Metric.ball (cent i) (rad i / 2))] (fun x => (uc i).grad x j) := by
  classical
  set Ω : Set (Fin d → ℝ) := Metric.ball z (R / 2) with hΩ
  set Q : ι → Set (Fin d → ℝ) := fun i => Metric.ball (cent i) (rad i / 2) with hQ
  have hh : ∀ i, 0 < rad i / 2 := fun i => by have := hrad i; positivity
  have hΩcvx : IsOpenBoundedConvexDomain Ω := isOpenBoundedConvexDomain_ball z (by positivity)
  -- the cells are open and contained in `Ω`
  have hQopen : ∀ i, IsOpen (Q i) := fun i => Metric.isOpen_ball
  -- a point of two closed cells lies on both frontiers
  have hfront : ∀ i x, x ∈ closure (Q i) → (∃ k, k ≠ i ∧ x ∈ closure (Q k)) → x ∈ frontier (Q i) := by
    intro i x hxc ⟨k, hki, hxk⟩
    refine ⟨hxc, ?_⟩
    rw [(hQopen i).interior_eq]
    intro hxi
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hxk (Q i) (hQopen i) hxi
    exact (Set.disjoint_left.1 (hdisj hki.symm)) hy1 hy2
  -- the glued function
  let W : (Fin d → ℝ) → ℝ := fun x =>
    if hx : ∃ i, x ∈ closure (Q i) then (uc (Classical.choose hx)).toFun x else 0
  have hWeq : ∀ i, ∀ x ∈ closure (Q i), W x = (uc i).toFun x := by
    intro i x hxi
    have hx : ∃ i, x ∈ closure (Q i) := ⟨i, hxi⟩
    simp only [W, dif_pos hx]
    set k := Classical.choose hx with hk
    have hxk : x ∈ closure (Q k) := Classical.choose_spec hx
    by_cases hki : k = i
    · subst hki; rfl
    · have h1 : x ∈ frontier (Q k) := hfront k x hxk ⟨i, fun h => hki h.symm, hxi⟩
      have h2 : x ∈ frontier (Q i) := hfront i x hxi ⟨k, hki, hxk⟩
      rw [htrace k x h1, htrace i x h2]
  have hWout : ∀ x, (∀ i, x ∉ closure (Q i)) → W x = 0 := by
    intro x hx
    have : ¬ ∃ i, x ∈ closure (Q i) := by push_neg; exact hx
    simp only [W, dif_neg this]
  have hcl_sub : ∀ i, closure (Q i) ⊆ closure Ω := fun i => closure_mono (hsub i)
  -- continuity of `W`
  have hWcontOn : ContinuousOn W (closure Ω) := by
    rw [← hcover]
    refine LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite _) (fun i => isClosed_closure)
      fun i => ?_
    exact (hcont i).congr fun x hx => hWeq i x hx
  have hWzero : ∀ x, x ∉ Ω → W x = 0 := by
    intro x hx
    by_cases hxc : ∃ i, x ∈ closure (Q i)
    · obtain ⟨i, hi⟩ := hxc
      have hxΩ : x ∈ frontier Ω := ⟨hcl_sub i hi, by rwa [hΩ, Metric.isOpen_ball.interior_eq]⟩
      have hxQ : x ∈ frontier (Q i) := ⟨hi, by rw [(hQopen i).interior_eq]; exact fun h => hx (hsub i h)⟩
      rw [hWeq i x hi, htrace i x hxQ, hg0 x hxΩ]
    · push_neg at hxc
      exact hWout x hxc
  have hWcont : Continuous W := by
    refine continuousOn_univ.1 ?_
    have hu : (Set.univ : Set (Fin d → ℝ)) = closure Ω ∪ Ωᶜ := by
      ext x; simp only [mem_univ, mem_union, mem_compl_iff, true_iff]
      by_cases hx : x ∈ Ω
      · exact Or.inl (subset_closure hx)
      · exact Or.inr hx
    rw [hu]
    refine hWcontOn.union_of_isClosed (continuousOn_const.congr fun x hx => hWzero x hx)
      isClosed_closure Metric.isOpen_ball.isClosed_compl
  have hWcs : HasCompactSupport W := by
    refine HasCompactSupport.intro (K := closure Ω) (Metric.isBounded_ball.isCompact_closure) ?_
    intro x hx
    exact hWout x fun i hi => hx (hcl_sub i hi)
  -- null complement
  have hnull : volume (Ω \ ⋃ i, gcCell cent (fun i => rad i / 2) i) = 0 := by
    refine measure_mono_null (t := ⋃ i, Metric.sphere (cent i) (rad i / 2)) ?_
      (measure_iUnion_null fun i => Measure.addHaar_sphere volume _ _)
    intro x ⟨hxΩ, hxU⟩
    have hxc : x ∈ closure Ω := subset_closure hxΩ
    rw [← hcover] at hxc
    obtain ⟨i, hi⟩ := mem_iUnion.1 hxc
    refine mem_iUnion.2 ⟨i, ?_⟩
    have hxnot : x ∉ Q i := fun h => hxU (mem_iUnion.2 ⟨i, h⟩)
    have hcb : x ∈ Metric.closedBall (cent i) (rad i / 2) :=
      Metric.closure_ball_subset_closedBall hi
    rw [Metric.mem_closedBall] at hcb
    rw [Metric.mem_sphere]
    refine le_antisymm hcb ?_
    by_contra hlt
    exact hxnot (Metric.mem_ball.2 (not_le.1 hlt))
  -- the `H¹` function
  have hweak : ∀ j, HasWeakPartialDerivOn Ω j W (gluedGrad cent (fun i => rad i / 2) uc j) :=
    fun j => hasWeakPartialDerivOn_glue Metric.isOpen_ball hh (fun i => hsub i) hdisj hnull uc hWcont
      (fun i x hx => hWeq i x (subset_closure hx)) j
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hgradL2 : ∀ j, MemLp (gluedGrad cent (fun i => rad i / 2) uc j) 2 (volume.restrict Ω) := by
    intro j
    unfold gluedGrad
    refine memLp_finset_sum _ fun i _ => ?_
    rw [memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet,
      Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
      Set.inter_eq_left.2 (hsub i)]
    exact (uc i).gradMemL2 j
  let Wh : H1Function Ω :=
    { toFun := W
      grad := fun x j => gluedGrad cent (fun i => rad i / 2) uc j x
      memL2 := (hWcont.memLp_of_hasCompactSupport hWcs).restrict Ω
      gradMemL2 := hgradL2
      hasWeakGradient := hweak }
  have hmem : MemH10 Ω Wh.toFun := by
    refine memH10_of_continuousOn_zero_frontier hΩcvx Wh hWcontOn ?_ ?_
    · intro x hx
      exact hWzero x (by
        have : x ∉ interior Ω := hx.2
        rwa [Metric.isOpen_ball.interior_eq] at this)
    · intro x hx
      exact hWout x fun i hi => hx (hcl_sub i hi)
  obtain ⟨w, hw⟩ := hmem
  have hwW : w.toH1Function.toFun = W := hw
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [hwW]; exact hWcontOn
  · intro i x hx
    rw [hwW]; exact hWeq i x hx
  · intro i j
    have hloc : ∀ (z : H1Function Ω) (k : Fin d),
        LocallyIntegrableOn (fun x => z.grad x k) Ω volume := fun z k =>
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((z.gradMemL2 k).locallyIntegrable (by norm_num))
    have hw' := w.toH1Function.hasWeakGradient j
    rw [hwW] at hw'
    have hae : (fun x => w.toH1Function.grad x j) =ᵐ[volume.restrict Ω]
        gluedGrad cent (fun i => rad i / 2) uc j :=
      HasWeakPartialDerivOn.ae_eq Metric.isOpen_ball (hloc _ j) (hloc Wh j) hw' (hweak j)
    have hae' := ae_restrict_of_ae_restrict_of_subset (hsub i) hae
    refine Filter.EventuallyEq.trans hae' ?_
    exact ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun x hx =>
      gluedGrad_eq_of_mem hdisj uc j hx

end SubdiffusiveProcess.Gluing
