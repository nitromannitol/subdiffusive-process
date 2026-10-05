module

public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.in_represented_enum
public import SubdiffusiveProcess.ResponseMoments.Subdivision

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **The covering half of `cor_32`'s `hcatalogue`.** Given only that
the represented family contains, at every scale `k`, the cube of side `3^k` centered at the origin
(`thm_c1`'s own `qidx`/`hq` binders, `thm_c1`), EVERY cube of the
ambient space is eventually engulfed by one of these — no rationality, no triadic side, no prior
containment needed on the target cube. This is the general-position half of `cor_32`'s `hcatalogue`
(`cor_32`); it does not need `hCat`/`conv_represented_estimates` at
all. Independent, standalone: does not depend on `in_represented_bounds`/`in_represented_mosco`. -/
theorem aux_in_represented_catalogue_hcatalogue
    (d : ℕ) (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (qidx : ℕ → ℕ) (hq : ∀ k, z (qidx k) = 0 ∧ r (qidx k) = (3 : ℝ) ^ k) :
    ∀ (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0),
      ∃ i : ℕ, closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) := by
  intro z0 r0 hr0
  have htend : Tendsto (fun k : ℕ => (3 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨k, hk⟩ := (htend.eventually_gt_atTop (2 * ‖z0‖ + r0)).exists
  obtain ⟨hzk, hrk⟩ := hq k
  refine ⟨qidx k, ?_⟩
  have hsub : closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ⊆
      Metric.closedBall z0 (r0 / 2) := by
    have heq : (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) = Metric.ball z0 (r0 / 2) :=
      rfl
    rw [heq]
    exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
  have htarget : (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
      Set (SpatialCoordinates d)) = Metric.ball (z (qidx k)) (r (qidx k) / 2) := rfl
  rw [htarget, hzk, hrk]
  refine hsub.trans ?_
  intro x hx
  have hx' : dist x z0 ≤ r0 / 2 := hx
  have htri : dist x (0 : SpatialCoordinates d) ≤ dist x z0 + dist z0 0 := dist_triangle _ _ _
  have hz0 : dist z0 (0 : SpatialCoordinates d) = ‖z0‖ := by
    rw [dist_eq_norm, sub_zero]
  rw [hz0] at htri
  have hfinal : dist x (0 : SpatialCoordinates d) < (3 : ℝ) ^ k / 2 := by linarith
  exact Metric.mem_ball.mpr hfinal

/-- Rationality of `oddGridCenter` is preserved: a rational centre and a rational side give a
rational-coordinate child centre. Pure field algebra on the affine formula, no geometry. -/
theorem aux_in_represented_catalogue_ratCoord_oddGridCenter
    (d m : ℕ) (c : SpatialCoordinates d) (s : ℝ) (k : OddGridIndex d m)
    (hc : ∀ i : Fin d, ∃ q : ℚ, c i = (q : ℝ)) (hs : ∃ q : ℚ, s = (q : ℝ)) :
    ∀ i : Fin d, ∃ q : ℚ, oddGridCenter c s m k i = (q : ℝ) := by
  intro i
  obtain ⟨qc, hqc⟩ := hc i
  obtain ⟨qs, hqs⟩ := hs
  refine ⟨qc + (((k i).val : ℚ) - (m : ℚ)) * (qs / (2 * (m : ℚ) + 1)), ?_⟩
  show c i + (((k i).val : ℝ) - (m : ℝ)) * (s / (2 * (m : ℝ) + 1)) = _
  rw [hqc, hqs]
  push_cast
  ring

/-- `descendantSide` stays a triadic power under a triadic-power root side. -/
theorem aux_in_represented_catalogue_triadic_descendantSide
    (H1 : ℕ) (r0 : ℝ) (h0 : ∃ k0 : ℤ, r0 = (3 : ℝ) ^ k0) :
    ∀ n : ℕ, ∃ k : ℤ, descendantSide (subdivisionHalfWidth H1) n r0 = (3 : ℝ) ^ k := by
  intro n
  induction n with
  | zero => rw [descendantSide_zero]; exact h0
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k - (H1 : ℤ), ?_⟩
    have hcast : (2 * (subdivisionHalfWidth H1 : ℝ) + 1) = (3 : ℝ) ^ H1 := by
      exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
    rw [descendantSide_succ, hk, hcast]
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num

/-- `descendantCenter` stays rational-coordinate under a rational-coordinate root centre and a
triadic-power root side, by induction on depth (Lemma 3, DEV note section C1 step 3). -/
theorem aux_in_represented_catalogue_ratCoord_descendantCenter
    (d H1 : ℕ) (rootCenter : SpatialCoordinates d) (r0 : ℝ)
    (hRootRat : ∀ i : Fin d, ∃ q : ℚ, rootCenter i = (q : ℝ))
    (hRootTriadic : ∃ k0 : ℤ, r0 = (3 : ℝ) ^ k0) :
    ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      ∀ i : Fin d, ∃ q : ℚ,
        descendantCenter (subdivisionHalfWidth H1) rootCenter r0 n w i = (q : ℝ) := by
  intro n
  induction n with
  | zero => intro _ i; exact hRootRat i
  | succ n ih =>
    intro w
    have hprev := ih (fun i => w i.castSucc)
    have hside := aux_in_represented_catalogue_triadic_descendantSide H1 r0 hRootTriadic n
    have hsideRat : ∃ q : ℚ, descendantSide (subdivisionHalfWidth H1) n r0 = (q : ℝ) := by
      obtain ⟨k, hk⟩ := hside
      exact ⟨(3 : ℚ) ^ k, by rw [hk]; push_cast [zpow_natCast, zpow_negSucc]; norm_cast⟩
    show ∀ i : Fin d, ∃ q : ℚ,
        oddGridCenter (descendantCenter (subdivisionHalfWidth H1) rootCenter r0 n
          (fun i => w i.castSucc)) (descendantSide (subdivisionHalfWidth H1) n r0)
          (subdivisionHalfWidth H1) (w (Fin.last n)) i = (q : ℝ)
    exact aux_in_represented_catalogue_ratCoord_oddGridCenter d (subdivisionHalfWidth H1)
      (descendantCenter (subdivisionHalfWidth H1) rootCenter r0 n (fun i => w i.castSucc))
      (descendantSide (subdivisionHalfWidth H1) n r0) (w (Fin.last n)) hprev hsideRat

/-- Every descendant cell is contained in the root cube (Lemma 4, DEV note section C1 step 4). -/
theorem aux_in_represented_catalogue_descendantCell_subset_root
    (d H1 : ℕ) (rootCenter : SpatialCoordinates d) {r0 : ℝ} (hr0 : 0 < r0) :
    ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      (descendantCell (subdivisionHalfWidth H1) rootCenter hr0 n w :
        Set (SpatialCoordinates d)) ⊆ (centeredCube rootCenter r0 hr0 : Set (SpatialCoordinates d)) := by
  intro n
  induction n with
  | zero =>
    intro w
    have : (descendantCell (subdivisionHalfWidth H1) rootCenter hr0 0 w :
        Set (SpatialCoordinates d)) = (centeredCube rootCenter r0 hr0 : Set (SpatialCoordinates d)) := by
      simp only [descendantCell, descendantCenter, descendantSide_zero]
    rw [this]
  | succ n ih =>
    intro w
    exact (descendantCell_succ_subset (subdivisionHalfWidth H1) rootCenter hr0 n w).trans
      (ih (fun i => w i.castSucc))



theorem in_represented_catalogue
    (d H1 : ℕ) (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hEnum : in_represented_enum d z r hr) :
    ∃ (rootCenter : SpatialCoordinates d) (r0 : ℝ) (_hr0 : 0 < r0)
      (idx : ∀ n : ℕ, (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℕ),
      ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
        z (idx n w) = descendantCenter (subdivisionHalfWidth H1) rootCenter r0 n w ∧
        r (idx n w) = descendantSide (subdivisionHalfWidth H1) n r0 := by
  obtain ⟨rootCenter, r0, hr0, hRootRat, hRootTriadic, hComplete⟩ := hEnum
  refine ⟨rootCenter, r0, hr0, ?_⟩
  have hchoice : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      ∃ i : ℕ, z i = descendantCenter (subdivisionHalfWidth H1) rootCenter r0 n w ∧
        r i = descendantSide (subdivisionHalfWidth H1) n r0 := by
    intro n w
    have hrat := aux_in_represented_catalogue_ratCoord_descendantCenter d H1 rootCenter r0
      hRootRat hRootTriadic n w
    have htri := aux_in_represented_catalogue_triadic_descendantSide H1 r0 hRootTriadic n
    have hsub := aux_in_represented_catalogue_descendantCell_subset_root d H1 rootCenter hr0 n w
    have hpos := descendantSide_pos (subdivisionHalfWidth H1) n hr0
    have hcell : (descendantCell (subdivisionHalfWidth H1) rootCenter hr0 n w :
        Set (SpatialCoordinates d)) =
        (centeredCube (descendantCenter (subdivisionHalfWidth H1) rootCenter r0 n w)
          (descendantSide (subdivisionHalfWidth H1) n r0) hpos : Set (SpatialCoordinates d)) := rfl
    rw [hcell] at hsub
    exact hComplete _ _ hpos hrat htri hsub
  choose idx hidx using hchoice
  exact ⟨idx, hidx⟩

end SubdiffusiveProcess.Paper
