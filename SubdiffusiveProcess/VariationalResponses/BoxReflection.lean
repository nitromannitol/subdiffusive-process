module

public import SubdiffusiveProcess.VariationalResponses.OddExtension

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology Distributions ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- The open coordinate box with lower corner `lo` and upper corner `hi`.  After
one reflection a cube becomes a box, so the multi-face induction runs on boxes. -/
def openBox (lo hi : SpatialCoordinates d) : Opens (SpatialCoordinates d) :=
  ⟨Set.pi Set.univ (fun j => Set.Ioo (lo j) (hi j)),
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)⟩

theorem mem_openBox_iff (lo hi x : SpatialCoordinates d) :
    x ∈ openBox lo hi ↔ ∀ j : Fin d, lo j < x j ∧ x j < hi j := by
  show x ∈ Set.pi Set.univ (fun j => Set.Ioo (lo j) (hi j)) ↔ _
  simp only [Set.mem_univ_pi, Set.mem_Ioo]

/-- A centred cube is the box with the corresponding corners. -/
theorem centeredCube_eq_openBox (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    centeredCube z r hr = openBox (fun j => z j - r / 2) (fun j => z j + r / 2) := by
  apply Opens.ext
  rw [centeredCube_eq_pi]
  rfl

/-- The upper corner of the box doubled across its upper `i`-face. -/
def doubledCorner (lo hi : SpatialCoordinates d) (i : Fin d) : SpatialCoordinates d :=
  Function.update hi i (2 * hi i - lo i)

/-- A point of the upper `i`-face plane of the box. -/
def upperFacePoint (lo hi : SpatialCoordinates d) (i : Fin d) : SpatialCoordinates d :=
  Function.update lo i (hi i)

theorem upperFacePoint_apply_self (lo hi : SpatialCoordinates d) (i : Fin d) :
    upperFacePoint lo hi i i = hi i := by
  simp [upperFacePoint]

theorem doubledCorner_apply_self (lo hi : SpatialCoordinates d) (i : Fin d) :
    doubledCorner lo hi i i = 2 * hi i - lo i := by
  simp [doubledCorner]

theorem doubledCorner_apply_of_ne (lo hi : SpatialCoordinates d) {i j : Fin d}
    (hj : j ≠ i) : doubledCorner lo hi i j = hi j := by
  simp [doubledCorner, Function.update_of_ne hj]

theorem boxEvenReflection_mem_iff (lo hi : SpatialCoordinates d) (i : Fin d)
    (x : SpatialCoordinates d) :
    x ∈ openBox lo hi ↔
      x ∈ openBox lo (doubledCorner lo hi i) ∧ x i < upperFacePoint lo hi i i := by
  rw [mem_openBox_iff, mem_openBox_iff, upperFacePoint_apply_self]
  constructor
  · intro h
    refine ⟨fun j => ⟨(h j).1, ?_⟩, (h i).2⟩
    by_cases hj : j = i
    · subst hj
      rw [doubledCorner_apply_self]
      have h1 := (h j).1
      have h2 := (h j).2
      linarith
    · rw [doubledCorner_apply_of_ne lo hi hj]
      exact (h j).2
  · rintro ⟨h, hii⟩ j
    refine ⟨(h j).1, ?_⟩
    by_cases hj : j = i
    · subst hj; exact hii
    · have hjj := (h j).2
      rwa [doubledCorner_apply_of_ne lo hi hj] at hjj

theorem boxEvenReflection_symm (lo hi : SpatialCoordinates d) (i : Fin d) :
    coordinateReflection (upperFacePoint lo hi i) {i} ⁻¹'
        (openBox lo (doubledCorner lo hi i) : Set (SpatialCoordinates d)) =
      (openBox lo (doubledCorner lo hi i) : Set (SpatialCoordinates d)) := by
  ext x
  simp only [Set.mem_preimage]
  rw [show ((openBox lo (doubledCorner lo hi i) : Set (SpatialCoordinates d))) =
      {y : SpatialCoordinates d | ∀ j : Fin d, lo j < y j ∧ y j < doubledCorner lo hi i j} from
    Set.ext (fun y => mem_openBox_iff lo _ y)]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h j
    by_cases hj : j = i
    · subst hj
      have hji := h j
      rw [coordinateReflection_single_apply_self, upperFacePoint_apply_self,
        doubledCorner_apply_self] at hji
      rw [doubledCorner_apply_self]
      constructor <;> linarith [hji.1, hji.2]
    · have hjj := h j
      rwa [coordinateReflection_single_apply_of_ne _ hj] at hjj
  · intro h j
    by_cases hj : j = i
    · subst hj
      have hji := h j
      rw [doubledCorner_apply_self] at hji
      rw [coordinateReflection_single_apply_self, upperFacePoint_apply_self,
        doubledCorner_apply_self]
      constructor <;> linarith [hji.1, hji.2]
    · rw [coordinateReflection_single_apply_of_ne _ hj]
      exact h j

/-- **The box reflection domain**: the box `openBox lo hi` inside the box doubled
across its upper `i`-face, with the reflection plane `{x i = hi i}`.  This is the
box analogue of `cubeEvenReflectionDomain` and is what the multi-face induction
iterates. -/
def boxEvenReflectionDomain (lo hi : SpatialCoordinates d) (i : Fin d) :
    EvenReflectionDomain d where
  z := upperFacePoint lo hi i
  i := i
  Ω := openBox lo hi
  U := openBox lo (doubledCorner lo hi i)
  mem_iff := boxEvenReflection_mem_iff lo hi i
  symm := boxEvenReflection_symm lo hi i

/-- The preimage of a box under a single-coordinate reflection is again a box:
only the `i`-th interval is reflected. -/
theorem coordinateReflection_preimage_openBox (z : SpatialCoordinates d) (i : Fin d)
    (lo hi : SpatialCoordinates d) :
    coordinateReflection z {i} ⁻¹' (openBox lo hi : Set (SpatialCoordinates d)) =
      (openBox (Function.update lo i (2 * z i - hi i))
        (Function.update hi i (2 * z i - lo i)) : Set (SpatialCoordinates d)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe]
  rw [mem_openBox_iff, mem_openBox_iff]
  constructor
  · intro h j
    by_cases hj : j = i
    · subst hj
      have hji := h j
      rw [coordinateReflection_single_apply_self] at hji
      rw [Function.update_self, Function.update_self]
      constructor <;> linarith [hji.1, hji.2]
    · have hjj := h j
      rw [coordinateReflection_single_apply_of_ne _ hj] at hjj
      rw [Function.update_of_ne hj, Function.update_of_ne hj]
      exact hjj
  · intro h j
    by_cases hj : j = i
    · subst hj
      have hji := h j
      rw [Function.update_self, Function.update_self] at hji
      rw [coordinateReflection_single_apply_self]
      constructor <;> linarith [hji.1, hji.2]
    · have hjj := h j
      rw [Function.update_of_ne hj, Function.update_of_ne hj] at hjj
      rwa [coordinateReflection_single_apply_of_ne _ hj]

/-- The lower corner of the box doubled DOWNWARD across its lower `i`-face. -/
def lowerDoubledCorner (lo hi : SpatialCoordinates d) (i : Fin d) :
    SpatialCoordinates d :=
  Function.update lo i (2 * lo i - hi i)

/-- The mirror box below the lower `i`-face. -/
def mirrorBoxLower (lo hi : SpatialCoordinates d) (i : Fin d) :
    Opens (SpatialCoordinates d) :=
  openBox (lowerDoubledCorner lo hi i) (Function.update hi i (lo i))

/-- Doubling the mirror box upward reproduces the downward-doubled box: the
upper-face constructor applied to `mirrorBoxLower` has `U` equal to
`openBox (lowerDoubledCorner lo hi i) hi`. -/
theorem boxEvenReflectionDomain_mirror_U (lo hi : SpatialCoordinates d) (i : Fin d) :
    (boxEvenReflectionDomain (lowerDoubledCorner lo hi i)
      (Function.update hi i (lo i)) i).U = openBox (lowerDoubledCorner lo hi i) hi := by
  show openBox (lowerDoubledCorner lo hi i)
      (doubledCorner (lowerDoubledCorner lo hi i) (Function.update hi i (lo i)) i) =
    openBox (lowerDoubledCorner lo hi i) hi
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    rw [doubledCorner_apply_self, Function.update_self, lowerDoubledCorner,
      Function.update_self]
    ring
  · rw [doubledCorner_apply_of_ne _ _ hj, Function.update_of_ne hj]

/-- The reflected half of the mirror-box domain is the original box. -/
theorem boxEvenReflectionDomain_mirror_reflected (lo hi : SpatialCoordinates d)
    (i : Fin d) :
    (boxEvenReflectionDomain (lowerDoubledCorner lo hi i)
      (Function.update hi i (lo i)) i).reflected = openBox lo hi := by
  apply Opens.ext
  show coordinateReflection
      (upperFacePoint (lowerDoubledCorner lo hi i) (Function.update hi i (lo i)) i) {i} ⁻¹'
      (openBox (lowerDoubledCorner lo hi i) (Function.update hi i (lo i)) :
        Set (SpatialCoordinates d)) = _
  rw [coordinateReflection_preimage_openBox]
  have hz : upperFacePoint (lowerDoubledCorner lo hi i)
      (Function.update hi i (lo i)) i i = lo i := by
    rw [upperFacePoint_apply_self, Function.update_self]
  have h1 : Function.update (lowerDoubledCorner lo hi i) i
      (2 * upperFacePoint (lowerDoubledCorner lo hi i)
        (Function.update hi i (lo i)) i i - Function.update hi i (lo i) i) = lo := by
    funext j
    rw [hz, Function.update_self]
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      ring
    · rw [Function.update_of_ne hj, lowerDoubledCorner, Function.update_of_ne hj]
  have h2 : Function.update (Function.update hi i (lo i)) i
      (2 * upperFacePoint (lowerDoubledCorner lo hi i)
        (Function.update hi i (lo i)) i i - lowerDoubledCorner lo hi i i) = hi := by
    funext j
    rw [hz, lowerDoubledCorner, Function.update_self]
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      ring
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  rw [h1, h2]

/-- **The downward induction step, in general form.**  A killed datum on the
UPPER half `D.reflected` of a reflection domain is pulled back to the lower half
by the reflection (which preserves the killed space) and then extended oddly, so
it too produces a killed datum on the doubled domain.  Combined with
`boxEvenReflectionDomain_mirror_reflected` this doubles a box DOWNWARD across its
lower `i`-face, which is what a boundary point with `x₀ i = lo i` needs. -/
theorem oddExtension_reflected_mem_killed (D : EvenReflectionDomain d)
    {u : SobolevData D.reflected} (hu : u ∈ killedSobolevGraph D.reflected) :
    D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected u)
      ∈ killedSobolevGraph D.U :=
  _root_.SubdiffusiveProcess.EvenReflectionDomain.oddExtension_mem_killed D
    (reflectionSobolevData_mem_killed D.z {D.i} D.preimage_reflected hu)

end SubdiffusiveProcess
