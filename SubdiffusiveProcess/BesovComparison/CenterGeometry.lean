import SubdiffusiveProcess.BesovComparison.RawNorms
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilityCap

/-! Identifying the paper's real centres with the finite overlap cubes. -/
open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube

noncomputable section
namespace SubdiffusiveProcess.BesovComparison
variable {d : ℕ}

theorem translatedCube_eq_translateSet (n : ℤ) (z : Vec d) :
    translatedCube d n z = translateSet z (openCubeSet (originCube d n)) := by
  unfold translatedCube cube
  rw [← image_addRight_eq_translateSet]
  congr 1
  funext x
  exact add_comm z x

theorem mem_translatedCube_iff (n : ℤ) (z y : Vec d) :
    y ∈ translatedCube d n z ↔
      ∀ i, -(1 / 2 : ℝ) * (3 : ℝ) ^ n < y i - z i ∧
        y i - z i < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  rw [translatedCube_eq_translateSet, mem_translateSet_iff_sub_mem,
    mem_openCubeSet_originCube_iff]
  rfl

theorem overlap_openCube_eq_translatedCube (S : TriadicCube d) :
    ScalarOverlap.openCubeSet S = translatedCube d (S.scale + 1) (cubeCenter S) := by
  have hp : (3 : ℝ) ^ (S.scale + 1) = 3 * cubeScaleFactor S := by
    rw [zpow_add₀ (by norm_num), zpow_one]
    unfold cubeScaleFactor
    ring
  ext y
  rw [mem_translatedCube_iff]
  change (∀ i, ((S.index i : ℝ) - 3 / 2) * cubeScaleFactor S < y i ∧
      y i < ((S.index i : ℝ) + 3 / 2) * cubeScaleFactor S) ↔ _
  rw [hp]
  simp only [cubeCenter]
  constructor <;> intro h i <;> have hi := h i <;> constructor <;> linarith

/-- Inclusion of open coordinate boxes also includes their half-open versions. -/
theorem overlap_halfOpen_subset_of_open_subset {S Q : TriadicCube d}
    (h : ScalarOverlap.openCubeSet S ⊆ openCubeSet Q) :
    ScalarOverlap.cubeSet S ⊆ cubeSet Q := by
  classical
  have hbounds : ∀ i,
      ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q ≤
        ((S.index i : ℝ) - 3 / 2) * cubeScaleFactor S ∧
      ((S.index i : ℝ) + 3 / 2) * cubeScaleFactor S ≤
        ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q := by
    intro i
    have hpos : 0 < cubeScaleFactor S := zpow_pos (by norm_num) _
    apply (Set.Ioo_subset_Ioo_iff (by nlinarith :
      ((S.index i : ℝ) - 3 / 2) * cubeScaleFactor S <
        ((S.index i : ℝ) + 3 / 2) * cubeScaleFactor S)).1
    intro t ht
    let y : Vec d := fun j => if j = i then t else (S.index j : ℝ) * cubeScaleFactor S
    have hy : y ∈ ScalarOverlap.openCubeSet S := by
      intro j
      dsimp [y]
      split_ifs with hj
      · subst j
        exact ht
      · constructor <;> nlinarith
    have hi := h hy i
    simpa only [y, if_pos rfl] using hi
  intro y hy i
  have hi := hy i
  exact ⟨(hbounds i).1.trans hi.1, hi.2.trans_le (hbounds i).2⟩

theorem cubeCenter_injective_on_centers (Q : TriadicCube d) (j : ℕ) :
    Set.InjOn cubeCenter (ScalarOverlap.centersAtDepth Q j : Set (TriadicCube d)) := by
  intro S hS T hT hST
  have hs := scale_eq_sub_of_mem_descendantsAtDepth
    (ScalarOverlap.mem_descendantsAtDepth_of_mem_centersAtDepth hS)
  have ht := scale_eq_sub_of_mem_descendantsAtDepth
    (ScalarOverlap.mem_descendantsAtDepth_of_mem_centersAtDepth hT)
  have hscale : S.scale = T.scale := hs.trans ht.symm
  have hi : S.index = T.index := by
    funext i
    have hcoord := congrFun hST i
    change (S.index i : ℝ) * cubeScaleFactor S = (T.index i : ℝ) * cubeScaleFactor T at hcoord
    have hfac : cubeScaleFactor S = cubeScaleFactor T := by unfold cubeScaleFactor; rw [hscale]
    rw [hfac] at hcoord
    have heq := mul_right_cancel₀ (zpow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)) hcoord
    exact_mod_cast heq
  cases S
  cases T
  simp_all

theorem positiveCenters_eq_image (m : ℤ) (j : ℕ) :
    positiveCenters d m (m - (j : ℤ)) =
      cubeCenter '' (ScalarOverlap.centersAtDepth (originCube d m) j : Set (TriadicCube d)) := by
  classical
  ext z
  constructor
  · rintro ⟨hgrid, hz, hsub⟩
    choose k hk using hgrid
    let S : TriadicCube d := ⟨m - (j : ℤ) - 1, k⟩
    have hcenter : cubeCenter S = z := by
      funext i
      dsimp [cubeCenter, cubeScaleFactor, S]
      exact (mul_comm _ _).trans (hk i).symm
    have hopen : ScalarOverlap.openCubeSet S ⊆ openCubeSet (originCube d m) := by
      rw [overlap_openCube_eq_translatedCube, hcenter]
      have hn : S.scale + 1 = m - (j : ℤ) := by dsimp [S]; omega
      rw [hn]
      exact hsub
    have hhalf := overlap_halfOpen_subset_of_open_subset hopen
    have hsmall : cubeSet S ⊆ cubeSet (originCube d m) := by
      intro y hy
      apply hhalf
      intro i
      have hi := hy i
      have hc : 0 ≤ cubeScaleFactor S := (zpow_pos (by norm_num) _).le
      constructor <;> nlinarith
    have hdesc := SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.mem_descendantsAtScale_of_cubeSet_subset hsmall
      (by dsimp [S, originCube]; omega : S.scale ≤ (originCube d m).scale)
    have hD : S ∈ descendantsAtDepth (originCube d m) (j + 1) := by
      rw [descendantsAtScale_eq_descendantsAtDepth _ (by dsimp [S, originCube]; omega)] at hdesc
      have hj : ((originCube d m).scale - S.scale).toNat = j + 1 := by dsimp [S, originCube]; omega
      rw [hj] at hdesc
      exact hdesc
    exact ⟨S, ScalarOverlap.mem_centersAtDepth_iff.2 ⟨hD, hhalf⟩, hcenter⟩
  · rintro ⟨S, hS, rfl⟩
    have hscale := scale_eq_sub_of_mem_descendantsAtDepth
      (ScalarOverlap.mem_descendantsAtDepth_of_mem_centersAtDepth hS)
    have hn : S.scale + 1 = m - (j : ℤ) := by dsimp [originCube] at hscale; omega
    have hopen := ScalarOverlap.openCubeSet_subset_openCubeSet_of_mem_centersAtDepth hS
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine ⟨S.index i, ?_⟩
      change (S.index i : ℝ) * (3 : ℝ) ^ S.scale = _
      rw [show S.scale = m - (j : ℤ) - 1 by omega]
      ring
    · apply hopen
      intro i
      change ((S.index i : ℝ) - 3 / 2) * cubeScaleFactor S <
        (S.index i : ℝ) * cubeScaleFactor S ∧ _
      have hc : 0 < cubeScaleFactor S := zpow_pos (by norm_num) _
      dsimp only [cubeCenter]
      constructor <;> nlinarith
    · rw [← hn, ← overlap_openCube_eq_translatedCube]
      exact hopen

end SubdiffusiveProcess.BesovComparison
