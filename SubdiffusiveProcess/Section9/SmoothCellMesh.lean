import SubdiffusiveProcess.Lane2.MeshGluing

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section9

/-- Construct the actual smooth cell-harmonic interpolants, including their concrete
continuous frontier values. No estimate or solution limit is required. -/
theorem exists_smooth_cell_mesh
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hell : ∀ n, ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        lo ≤ a n x ∧ a n x ≤ hi)
    (Phi : SpatialCoordinates d → ℝ) (hPhi : ContDiff ℝ ∞ Phi)
    (hPhis : HasCompactSupport Phi)
    (hPhiQ : tsupport Phi ⊆ (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ (PhiH : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
      (UN : ℕ → H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
      (UNS : ℕ → S.space),
      PhiH.toFun = Phi ∧ ∀ n,
        (UNS n).val = sobolevDataOfH1 (UN n) ∧
        ContinuousOn (UN n).toFun (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)), (UN n).toFun x = 0) ∧
        ∀ k : OddGridIndex d (triadicHalf 1),
          let W := oddGridCell z R hR (triadicHalf 1) k
          let hsub := oddGridCell_subset z hR (triadicHalf 1) k
          IsWeaklyHarmonicOn (a n) (W : Set (SpatialCoordinates d))
            ((UN n).restrict W.isOpen hsub) ∧
          HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d))
            ((UN n).restrict W.isOpen hsub) (PhiH.restrict W.isOpen hsub) ∧
          ContinuousOn (UN n).toFun (closure (W : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ frontier (W : Set (SpatialCoordinates d)), (UN n).toFun x = Phi x) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  let Q := centeredCube z R hR
  let PhiH := H1Function.ofContDiff Q.isOpen (hPhi.of_le (by simp)) hPhis
  obtain ⟨_, _, hmesh⟩ := lane2_meshInterpolator (d := d) hd
  have hex : ∀ n, ∃ w : H10Function (Q : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun (closure (Q : Set (SpatialCoordinates d))) ∧
      ∀ k : OddGridIndex d (triadicHalf 1),
        let W := oddGridCell z R hR (triadicHalf 1) k
        let hsub := oddGridCell_subset z hR (triadicHalf 1) k
        IsWeaklyHarmonicOn (a n) (W : Set (SpatialCoordinates d))
          (w.toH1Function.restrict W.isOpen hsub) ∧
        HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d))
          (w.toH1Function.restrict W.isOpen hsub) (PhiH.restrict W.isOpen hsub) := by
    intro n
    obtain ⟨lo, hi, hlo, hab⟩ := hell n
    obtain ⟨w, hwc, hw, -, -⟩ := hmesh z R hR 1 (a n) lo hi hlo (ha n)
      (fun x hx => hab x (subset_closure hx)) PhiH hPhi hPhis hPhiQ
    exact ⟨w, hwc, fun k => ⟨(hw k).1, (hw k).2.1⟩⟩
  choose w hwc hw using hex
  let UN := fun n => (w n).toH1Function
  let UNS : ℕ → S.space := fun n => ⟨sobolevDataOfH1 (UN n), by
    rw [hS]
    exact sobolevDataOfH1_mem_killed (w n)⟩
  have hcell : ∀ n k, ∀ x ∈ frontier
      (oddGridCell z R hR (triadicHalf 1) k : Set (SpatialCoordinates d)),
      (UN n).toFun x = Phi x := by
    intro n k
    let W := oddGridCell z R hR (triadicHalf 1) k
    have hsub := oddGridCell_subset z hR (triadicHalf 1) k
    obtain ⟨lo, hi, hlo, hab⟩ := hell n
    have hsubc := closure_mono hsub
    have hucont : ContinuousOn (UN n).toFun (closure (W : Set (SpatialCoordinates d))) :=
      (hwc n).mono hsubc
    obtain ⟨vc, hvc, hvae, hvb⟩ :=
      (lane2_cellDirichletBoundaryContinuity hd).continuous_up_to_boundary
        (oddGridCenter z R (triadicHalf 1) k)
        (R / (2 * (triadicHalf 1 : ℝ) + 1)) (div_pos hR (by positivity))
        (a n) lo hi hlo (ha n) (fun x hx => hab x (subset_closure (hsub hx)))
        (PhiH.restrict W.isOpen hsub) ((UN n).restrict W.isOpen hsub)
        hPhi (hw n k).1 (hw n k).2
    have hEqOpen : EqOn (UN n).toFun vc (W : Set (SpatialCoordinates d)) := by
      intro x hx
      exact lane2_eqOn_of_ae_eq_of_continuousOn W.isOpen
        (hucont.mono subset_closure) (hvc.mono subset_closure) hvae.symm x hx
    have hEq := hEqOpen.of_subset_closure hucont hvc subset_closure (subset_refl _)
    intro x hx
    exact (hEq (frontier_subset_closure hx)).trans (hvb x hx)
  refine ⟨PhiH, UN, UNS, rfl, ?_⟩
  intro n
  refine ⟨rfl, hwc n, ?_, fun k => ⟨(hw n k).1, (hw n k).2,
    (hwc n).mono (closure_mono (oddGridCell_subset z hR (triadicHalf 1) k)), hcell n k⟩⟩
  intro x hx
  have hxc : x ∈ closure (Q : Set (SpatialCoordinates d)) := frontier_subset_closure hx
  rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (triadicHalf 1)] at hxc
  obtain ⟨k, hxk⟩ := mem_iUnion.mp hxc
  have hxnot : x ∉ (Q : Set (SpatialCoordinates d)) := by
    rw [frontier, Q.isOpen.interior_eq] at hx
    exact hx.2
  have hxface : x ∈ frontier (oddGridCell z R hR (triadicHalf 1) k : Set (SpatialCoordinates d)) :=
    ⟨hxk, fun hi => hxnot (oddGridCell_subset z hR (triadicHalf 1) k (interior_subset hi))⟩
  exact (hcell n k x hxface).trans
    (image_eq_zero_of_notMem_tsupport (fun h => hxnot (hPhiQ h)))

end SubdiffusiveProcess.Section9
