module

public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.Geometry.TriadicResidual

@[expose] public section




open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.EllipticRegularity

/-- `2 m_J + 1 = 3^J` forces `m_{J+1} = 3 m_J + 1`. -/
theorem triadicHalf_succ (J : ℕ) : triadicHalf (J + 1) = 3 * triadicHalf J + 1 := by
  have h1 := two_mul_triadicHalf_add_one J
  have h2 := two_mul_triadicHalf_add_one (J + 1)
  have h3 : (3 : ℕ) ^ (J + 1) = 3 * 3 ^ J := by ring
  omega

/-- Every depth-`J` descendant of the origin cube has scale `n − J` and all indices of
modulus at most `triadicHalf J`. -/
theorem scale_and_index_of_mem_descendantsAtDepth_originCube
    {d : ℕ} (n : ℕ) : ∀ (J : ℕ) (R : Homogenization.TriadicCube d),
    R ∈ Homogenization.descendantsAtDepth (Homogenization.originCube d n) J →
      R.scale = (n : ℤ) - J ∧ ∀ i, |R.index i| ≤ (triadicHalf J : ℤ) := by
  intro J
  induction J with
  | zero =>
      intro R hR
      simp only [Homogenization.descendantsAtDepth_zero, Finset.mem_singleton] at hR
      subst hR
      refine ⟨by simp [Homogenization.originCube], fun i => ?_⟩
      simp [Homogenization.originCube, triadicHalf]
  | succ J ih =>
      intro R hR
      obtain ⟨S, hS, hRS⟩ := Homogenization.mem_descendantsAtDepth_succ_iff.1 hR
      obtain ⟨hSscale, hSindex⟩ := ih S hS
      simp only [Homogenization.childCubes, Finset.mem_image, Finset.mem_univ, true_and]
        at hRS
      obtain ⟨digits, hdig⟩ := hRS
      subst hdig
      refine ⟨by simp [hSscale]; ring, fun i => ?_⟩
      have hd0 : (0 : ℤ) ≤ (digits i : ℤ) := Int.natCast_nonneg _
      have hd2 : ((digits i : ℕ) : ℤ) ≤ 2 := by
        have := (digits i).isLt
        omega
      have hSi := hSindex i
      have hsucc : ((triadicHalf (J + 1) : ℕ) : ℤ) = 3 * (triadicHalf J : ℤ) + 1 := by
        rw [triadicHalf_succ]; push_cast; ring
      simp only [hsucc]
      have habs := abs_le.1 hSi
      rw [abs_le]
      constructor <;> omega

/-- The explicit index map from the project's odd-grid labels to upstream triadic cubes. -/
def descendantCube {d : ℕ} (n J : ℕ) (k : OddGridIndex d (triadicHalf J)) :
    Homogenization.TriadicCube d :=
  { scale := (n : ℤ) - J, index := fun i => ((k i).val : ℤ) - triadicHalf J }

theorem descendantCube_injective {d n J : ℕ} :
    Function.Injective (descendantCube (d := d) n J) := by
  intro k k' hkk'
  funext i
  have h := congrArg (fun Q => Homogenization.TriadicCube.index Q i) hkk'
  simp only [descendantCube] at h
  exact Fin.ext (by omega)

theorem descendantsAtDepth_originCube_eq_image {d : ℕ} (n J : ℕ) :
    Homogenization.descendantsAtDepth (Homogenization.originCube d n) J =
      Finset.image (descendantCube (d := d) n J) Finset.univ := by
  classical
  have hsub : Homogenization.descendantsAtDepth (Homogenization.originCube d n) J ⊆
      Finset.image (descendantCube (d := d) n J) Finset.univ := by
    intro R hR
    obtain ⟨hscale, hindex⟩ :=
      scale_and_index_of_mem_descendantsAtDepth_originCube n J R hR
    obtain ⟨sc, idx⟩ := R
    simp only at hscale hindex
    refine Finset.mem_image.2 ⟨fun i => ⟨(idx i + (triadicHalf J : ℤ)).toNat, ?_⟩,
      Finset.mem_univ _, ?_⟩
    · have := abs_le.1 (hindex i); omega
    · simp only [descendantCube, Homogenization.TriadicCube.mk.injEq]
      refine ⟨hscale.symm, ?_⟩
      funext i
      have habs := abs_le.1 (hindex i)
      omega
  refine Finset.eq_of_subset_of_card_le hsub (le_of_eq ?_)
  rw [Finset.card_image_of_injective _ descendantCube_injective,
    Homogenization.descendantsAtDepth_card]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [two_mul_triadicHalf_add_one, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem oddGridCell_eq_openCubeSet_descendantCube {d : ℕ} (n J : ℕ)
    (hr : (0 : ℝ) < 3 ^ n) (k : OddGridIndex d (triadicHalf J)) :
    (oddGridCell (0 : SpatialCoordinates d) ((3 : ℝ) ^ n) hr (triadicHalf J) k :
        Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet (descendantCube (d := d) n J k) := by
  have hden : (2 * (triadicHalf J : ℝ) + 1) = (3 : ℝ) ^ J := by
    have h := two_mul_triadicHalf_add_one J
    have h' : ((2 * triadicHalf J + 1 : ℕ) : ℝ) = ((3 ^ J : ℕ) : ℝ) := by rw [h]
    push_cast at h'
    linarith
  have hz : (3 : ℝ) ^ ((n : ℤ) - (J : ℤ)) = (3 : ℝ) ^ n / (3 : ℝ) ^ J := by
    rw [zpow_sub₀ (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  rw [oddGridCell, centeredCube_eq_pi]
  ext x
  simp only [Set.mem_univ_pi, Set.mem_Ioo, Homogenization.openCubeSet, mem_ofPred_eq,
    oddGridCenter, descendantCube, Homogenization.cubeScaleFactor, hden, hz,
    Pi.zero_apply, zero_add]
  push_cast
  constructor
  · intro hx i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith
  · intro hx i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith

end SubdiffusiveProcess.EllipticRegularity
