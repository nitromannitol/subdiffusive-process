module

public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family
public import SubdiffusiveProcess.Sobolev.GoodextHolderLimit
public import SubdiffusiveProcess.Geometry.TriadicApproximation

@[expose] public section

/-! Continuous bounded harmonic meshes for an arbitrary controlled coefficient sequence.
The meshes approximate smooth compactly supported data uniformly; taking a
limit in a candidate form is a separate step.
-/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Controlled cell bounds give an actual finite harmonic mesh bank uniformly approximating a smooth datum. -/
theorem goodext_controlled_mesh_bank
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ a n x ∧ a n x ≤ Lam)
    (t alpha : ℝ)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr a t alpha)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hcompact : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (J : ℕ) (w : ℕ → H10Function (centeredCube z r hr : Set (SpatialCoordinates d)))
      (Ebound : ℝ) (Hbound : OddGridIndex d (triadicHalf J) → ℝ),
      (∀ k, 0 ≤ Hbound k) ∧
      (∀ n, energy (a n) (centeredCube z r hr : Set (SpatialCoordinates d))
        (w n).toH1Function ≤ Ebound) ∧
      (∀ n, ContinuousOn (w n).toH1Function.toFun
        (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) ∧
      (∀ k n, IsHolderOn alpha
          (closure (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)))
          (w n).toH1Function.toFun ∧
        cAlphaNorm alpha
          (closure (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)))
          (w n).toH1Function.toFun ≤ Hbound k) ∧
      ∀ n x, x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) →
        |(w n).toH1Function.toFun x - phi x| ≤ eps := by
  classical
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨Cmesh, _hCmesh, hmesh⟩ := mesh_interpolator hd
  let gradBound := sSup ((fun x => ‖fderiv ℝ phi x‖) ''
    closure (centeredCube z r hr : Set (SpatialCoordinates d)))
  obtain ⟨J, hside, herr⟩ := exists_triadic_side_error_lt r (Cmesh * gradBound) eps heps
  let beta : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z r hr).isOpen (hphi.of_le (by norm_num)) hcompact
  choose lam Lam hlam hb using hell
  choose w hwcont hwcell hwsum hwerr using fun n =>
    hmesh z r hr J (a n) (lam n) (Lam n) (hlam n) (ha n) (hb n)
      beta hphi hcompact hsupp
  have hclose : ∀ n x, x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) →
      |(w n).toH1Function.toFun x - phi x| ≤ eps := by
    intro n x hx
    have h := le_on_closure (hwerr n) (((hwcont n).sub hphi.continuous.continuousOn).abs)
      continuousOn_const hx
    exact h.trans (by change Cmesh * (r / (3 : ℝ) ^ J) * gradBound ≤ eps; nlinarith only [herr])
  choose E Gr Ho hE hGr hHo hBounds using hcell J hside phi hphi beta rfl
  obtain ⟨Bphi, hBphi⟩ := (lane2_isCompact_closure_centeredCube z hr).exists_bound_of_continuousOn
    hphi.continuous.continuousOn
  let K : OddGridIndex d (triadicHalf J) → ℝ := fun k => max (Ho k) (Bphi + eps)
  have hK : ∀ k, 0 ≤ K k := fun k => (hHo k).trans (le_max_left _ _)
  have hBound (k : OddGridIndex d (triadicHalf J)) (n : ℕ) :=
    hBounds k n
      ((w n).toH1Function.restrict (oddGridCell z r hr (triadicHalf J) k).isOpen
        (oddGridCell_subset z hr (triadicHalf J) k))
      (hwcell n k).1 (hwcell n k).2.1
      ((hwcont n).mono (lane2_closure_oddGridCell_subset z hr (triadicHalf J) k))
  refine ⟨J, w, ∑ k, E k, fun k => 2 * K k,
    (fun k => mul_nonneg (by norm_num) (hK k)), ?_, hwcont, ?_, hclose⟩
  · intro n
    rw [hwsum n]
    apply Finset.sum_le_sum
    intro k _
    rw [← (hwcell n k).2.2]
    exact (hBound k n).1
  · intro k n
    apply aux_lem_goodext_cAlpha_of_pointwise alpha (K k) (hK k)
    · intro x hx
      have hxQ := lane2_closure_oddGridCell_subset z hr (triadicHalf J) k hx
      have hphiB : |phi x| ≤ Bphi := by
        simpa only [Real.norm_eq_abs] using hBphi x hxQ
      have htri : |(w n).toH1Function.toFun x| ≤
          |(w n).toH1Function.toFun x - phi x| + |phi x| := by
        simpa only [sub_add_cancel] using
          abs_add_le ((w n).toH1Function.toFun x - phi x) (phi x)
      exact (htri.trans ((add_le_add (hclose n x hxQ) hphiB).trans_eq
        (add_comm eps Bphi))).trans (le_max_right _ _)
    · intro x hx y hy
      exact ((hBound k n).2.2 x hx y hy).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (Real.sqrt_nonneg _) _))

end SubdiffusiveProcess.Paper
