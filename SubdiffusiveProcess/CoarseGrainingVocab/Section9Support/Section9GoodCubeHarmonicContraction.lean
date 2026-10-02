import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReducedResidual
import SubdiffusiveProcess.CoarseGrainingVocab.Section6DerivedSupport




set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (translatedCube IsMiddleHalfSubcube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-! ## The depth choice of 13188-13190 -/

/-- **The manuscript's choice of the inner depth.**  For every contraction
target `eps0 > 0` there is a depth `j ≥ 2` with `C·3^{-c j} ≤ eps0`; this is
the sentence "then choose `j₂` so that `C3^{-cj₂} ≤ ε₀`" at 13188-13190. -/
theorem exists_depth_of_contraction (C c eps0 : ℝ) (hc : 0 < c) (heps0 : 0 < eps0) :
    ∃ j : ℕ, 2 ≤ j ∧ C * (3 : ℝ) ^ (-c * (j : ℝ)) ≤ eps0 := by
  set t : ℝ := (3 : ℝ) ^ (-c) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have ht1 : t < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K : ℝ := max C 1 with hK
  have hK0 : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos heps0 hK0) ht1
  refine ⟨max 2 n, le_max_left _ _, ?_⟩
  have hpow : t ^ (max 2 n) ≤ t ^ n :=
    pow_le_pow_of_le_one ht0.le ht1.le (le_max_right _ _)
  have hrw : (3 : ℝ) ^ (-c * ((max 2 n : ℕ) : ℝ)) = t ^ (max 2 n) := by
    rw [ht, ← Real.rpow_natCast ((3 : ℝ) ^ (-c)) (max 2 n),
      ← Real.rpow_mul (by norm_num)]
  rw [hrw]
  calc C * t ^ (max 2 n) ≤ K * t ^ (max 2 n) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ K * t ^ n := mul_le_mul_of_nonneg_left hpow hK0.le
    _ ≤ K * (eps0 / K) := mul_le_mul_of_nonneg_left hn.le hK0.le
    _ = eps0 := by field_simp

/-! ## The geometry of the Section 6 anchor, on an admissible pair -/

/-- The Section 6 window `translatedCube` is the Section 9 family cube of the
same centre and triadic side. -/
theorem translatedCube_eq_cubeSet (m : ℤ) (z : Vec d) :
    translatedCube d m z = cubeSet (z, (3 : ℝ) ^ m) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro i _
    have h := hy i
    simp only [Homogenization.cubeScaleFactor, Homogenization.originCube,
      Pi.zero_apply, Int.cast_zero, zero_sub, zero_add] at h
    constructor
    · show z i - (3 : ℝ) ^ m / 2 < z i + y i
      linarith [h.1]
    · show z i + y i < z i - (3 : ℝ) ^ m / 2 + (3 : ℝ) ^ m
      linarith [h.2]
  · intro hx
    refine ⟨x - z, fun i => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hx i (Set.mem_univ i)
      simp only [Homogenization.cubeScaleFactor, Homogenization.originCube,
        Pi.zero_apply, Int.cast_zero, zero_sub, zero_add]
      have h1' : z i - (3 : ℝ) ^ m / 2 < x i := h1
      have h2' : x i < z i - (3 : ℝ) ^ m / 2 + (3 : ℝ) ^ m := h2
      constructor
      · show -(1 / 2 : ℝ) * (3 : ℝ) ^ m < x i - z i
        linarith
      · show x i - z i < (1 / 2 : ℝ) * (3 : ℝ) ^ m
        linarith
    · funext i
      show z i + (x i - z i) = x i
      ring

/-- **The inner cube of an admissible pair is a middle-half subcube of the
outer one, at relative depth `j2`.**  This is one of the two geometric
hypotheses of `SubdiffusiveProcess.Frozen.Section6.cutoff_holder_bounded_multiplier`; the other
is that the outer cube is a `translatedCube`, which is
`translatedCube_eq_cubeSet` read backwards. -/
theorem isMiddleHalfSubcube_of_pair {grid : Finset (Vec d)} {j1 j2 n : ℕ}
    {y : Vec d} {Pfam : Set (Cube d × Cube d)} {Qfam Afam : Set (Cube d)}
    (hgeom : IsLocalCubeGeometry grid j1 j2 (y, (3 : ℝ) ^ n) Pfam Qfam Afam)
    {p : Cube d × Cube d} (hp : p ∈ Pfam) :
    IsMiddleHalfSubcube ((n : ℤ) - j1) p.2.1 j2 (cubeSet p.1) := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have houter : p.2.2 = (3 : ℝ) ^ ((n : ℤ) - j1) := by
    rw [hgeom.pair_outer_side p hp]
    show (3 : ℝ) ^ (-(j1 : ℤ)) * (3 : ℝ) ^ n = (3 : ℝ) ^ ((n : ℤ) - j1)
    rw [show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast 3 n).symm,
      ← zpow_add₀ h3]
    congr 1
    ring
  have hinner : p.1.2 = (3 : ℝ) ^ ((n : ℤ) - j1 - j2) := by
    rw [hgeom.pair_inner_side p hp, houter, ← zpow_add₀ h3]
    congr 1
    ring
  refine ⟨p.1.1, ?_, ?_⟩
  · rw [translatedCube_eq_cubeSet, ← hinner]
  · intro x hx
    have hmid := hgeom.pair_middle_half p hp hx
    have hbound : ∀ i : Fin d, |x i - p.2.1 i| ≤ (3 : ℝ) ^ ((n : ℤ) - j1) / 4 := by
      intro i
      have h := hmid i (Set.mem_univ i)
      rw [← houter]
      obtain ⟨h1, h2⟩ := h
      rw [abs_le]
      constructor <;> linarith
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hbound i


/-! ## The named residual -/



def GoodCubeHarmonicContractionEvent (d : ℕ) : Prop :=
  ∀ eps0 : ℝ, 0 < eps0 →
    ∃ (j2 : ℕ) (C0 c0 : ℝ)
      (bad : (M : GMCModel d) → (n : ℕ) →
        Set (nativeBox n 1 (0 : Lattice d) → ℝ)),
      2 ≤ j2 ∧ 0 < C0 ∧ 0 < c0 ∧
        (∀ M : GMCModel d, M.delta ≤ c0 → ∀ (n : ℕ) (z : Lattice d),
          M.P.toMeasure (coefficientLocalBadEvent M n 1 (bad M n) z) ≤
            ENNReal.ofReal (C0 * Real.exp
              (-(c0 * (c0 / (M.delta ^ 2 * Real.log M.delta ^ 2)))))) ∧
        ∀ (j1 : ℕ), 2 ≤ j1 →
          ∀ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
            (Qfam0 Afam0 : Set (Cube d)),
            IsLocalCubeGeometry grid0 j1 j2 ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))
              Pfam0 Qfam0 Afam0 →
            (∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) →
            ∀ eps1 : ℝ, 0 < eps1 →
              GoodCubeReferenceDisplay d c0 eps1 1 Pfam0 Qfam0 Afam0 bad
                (fun M n _ omega _ Pfam _ _ =>
                  LocalHarmonicOscillation (aCutoff M n omega) eps0 Pfam)

/-- The contraction is strictly stronger than the clause the frozen block
exports: the block asks only for some `0 < eps0`, and P-363's calibration meets
it with `eps0 = 1`. -/
theorem lt_one_of_goodCubeHarmonicContractionEvent
    (h : GoodCubeHarmonicContractionEvent d) :
    ∃ (eps0 : ℝ) (j2 : ℕ), 0 < eps0 ∧ eps0 < 1 ∧ 2 ≤ j2 :=
  ⟨1 / 2, (h (1 / 2) (by norm_num)).choose, by norm_num, by norm_num,
    (h (1 / 2) (by norm_num)).choose_spec.choose_spec.choose_spec.choose_spec.1⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
