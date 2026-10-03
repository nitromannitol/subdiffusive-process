module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryInterior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryScales

@[expose] public section




set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The closed middle quarter or an original closed descendant cube to be covered. -/
def goodCubeAuxiliaryTargetSet {d : ℕ} (Qfam : Set (Cube d)) :
    Option (GoodCubeCompactPair Qfam) → Set (Vec d)
  | none => closure (middleQuarter ((0 : Vec d), (1 : ℝ)))
  | some p => closure (cubeSet p.val.1)

/-- The unit parent for the middle quarter and the original outer parent for every descendant. -/
def goodCubeAuxiliaryTargetParent {d : ℕ} (Qfam : Set (Cube d)) :
    Option (GoodCubeCompactPair Qfam) → Cube d
  | none => ((0 : Vec d), (1 : ℝ))
  | some p => p.val.2

/-- A fixed depth-two cube strictly inside the unit middle quarter, used only as a mass test. -/
def goodCubeQuarterMassTest (d : ℕ) : Cube d :=
  ((0 : Vec d), (3 : ℝ) ^ (-(2 : ℤ)))

/-- The separate mass-testing catalogue; inserting its new cube creates no original-family descendant obligations. -/
def goodCubeReferenceMassTests {d : ℕ} (Qfam : Set (Cube d)) : Set (Cube d) :=
  insert (goodCubeQuarterMassTest d) Qfam

/-- Containment of a positive-side cube in the unit cube bounds its side in positive dimension. -/
theorem goodCube_side_le_one_of_subset_unit {d : ℕ} [NeZero d]
    (Q : Cube d) (hQ : 0 < Q.2)
    (hinside : cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) : Q.2 ≤ 1 := by
  have hmeas : volume (cubeSet Q) ≤ volume (cubeSet ((0 : Vec d), (1 : ℝ))) :=
    measure_mono hinside
  rw [volume_cubeSet hQ.le, volume_cubeSet (by norm_num : (0:ℝ) ≤ 1)] at hmeas
  have h1 : ENNReal.ofReal (Q.2 ^ d) ≤ ENNReal.ofReal ((1 : ℝ) ^ d) := hmeas
  rw [ENNReal.ofReal_le_ofReal_iff (by norm_num : 0 ≤ (1 : ℝ) ^ d)] at h1
  exact (pow_le_one_iff_of_nonneg hQ.le (NeZero.ne d)).mp (by simpa using h1)

/-- The Option-indexed targets form a finite compact-interior family with positive parent sides at most one. -/
theorem goodCube_auxiliary_target_geometry {d : ℕ} [NeZero d]
    (Qfam : Set (Cube d)) (hfin : Qfam.Finite)
    (hpos : ∀ Q ∈ Qfam, 0 < Q.2)
    (hunit : ((0 : Vec d), (1 : ℝ)) ∈ Qfam)
    (hinside : ∀ Q ∈ Qfam, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) :
    Finite (Option (GoodCubeCompactPair Qfam)) ∧
      ∀ i : Option (GoodCubeCompactPair Qfam),
        IsCompact (goodCubeAuxiliaryTargetSet Qfam i) ∧
        goodCubeAuxiliaryTargetSet Qfam i ⊆ cubeSet (goodCubeAuxiliaryTargetParent Qfam i) ∧
        goodCubeAuxiliaryTargetParent Qfam i ∈ Qfam ∧
        0 < (goodCubeAuxiliaryTargetParent Qfam i).2 ∧
        (goodCubeAuxiliaryTargetParent Qfam i).2 ≤ 1 := by
  haveI hfp : Finite (GoodCubeCompactPair Qfam) :=
    goodCube_compact_pair_finite hfin
  refine ⟨inferInstance, ?_⟩
  intro i
  cases i with
  | none =>
    have hmq : middleQuarter ((0 : Vec d), (1 : ℝ))
        = centeredAxisCube (0 : Vec d) ((1 : ℝ) / 4) := rfl
    refine ⟨?_, ?_, hunit, ?_, ?_⟩
    · show IsCompact (closure (middleQuarter ((0 : Vec d), (1 : ℝ))))
      rw [hmq]
      exact Bornology.IsBounded.isCompact_closure
        (isBounded_centeredAxisCube (0 : Vec d) ((1 : ℝ) / 4))
    · show closure (middleQuarter ((0 : Vec d), (1 : ℝ)))
          ⊆ cubeSet ((0 : Vec d), (1 : ℝ))
      rw [hmq]
      exact closure_centeredAxisCube_subset (by norm_num : (1 : ℝ) / 4 < 1)
    · norm_num [goodCubeAuxiliaryTargetParent]
    · norm_num [goodCubeAuxiliaryTargetParent]
  | some p =>
    refine ⟨?_, ?_, p.property.2.1, ?_, ?_⟩
    · show IsCompact (closure (cubeSet p.val.1))
      exact Bornology.IsBounded.isCompact_closure
        (isBounded_centeredAxisCube p.val.1.1 p.val.1.2)
    · show closure (cubeSet p.val.1) ⊆ cubeSet p.val.2
      exact p.property.2.2
    · exact hpos p.val.2 p.property.2.1
    · exact goodCube_side_le_one_of_subset_unit p.val.2 (hpos p.val.2 p.property.2.1)
        (hinside p.val.2 p.property.2.1)

/-- Choose fixed intermediate windows and their common strict interior fraction before any cover parameters. -/
theorem exists_goodCube_auxiliary_windows {d : ℕ} {ι : Type*} [Finite ι]
    (K : ι → Set (Vec d)) (B : ι → Cube d)
    (hK : ∀ i, IsCompact (K i)) (hB : ∀ i, 0 < (B i).2)
    (hKB : ∀ i, K i ⊆ cubeSet (B i)) :
    ∃ (theta : ℝ) (W : ι → Set (Vec d)), 0 < theta ∧ theta < 1 ∧
      ∀ i, IsOpen (W i) ∧ K i ⊆ W i ∧ IsCompact (closure (W i)) ∧
        closure (W i) ⊆ cubeSet (B i) ∧
        closure (W i) ⊆ centeredAxisCube (B i).1 (theta * (B i).2) := by
  choose W hWopen hWK hWcl hWcomp using fun i : ι =>
    exists_open_between_and_isCompact_closure (hK i)
      (isOpen_centeredAxisCube (B i).1 (B i).2) (hKB i)
  obtain ⟨theta, htheta0, htheta1, huni⟩ :=
    exists_goodCube_uniform_interior_fraction
      (K := fun i : ι => closure (W i)) B hWcomp hB hWcl
  refine ⟨theta, W, htheta0, htheta1, fun i => ?_⟩
  exact ⟨hWopen i, hWK i, hWcomp i, hWcl i, (huni i).1⟩

/-- A square-root side cap gives the required squared response-scale bound. -/
theorem goodCube_auxiliary_square_cap {r L eta C : ℝ}
    (hr : 0 ≤ r) (heta : 0 < eta) (hC : 0 < C)
    (hcap : r ≤ Real.sqrt (eta / C) * L) : r ^ 2 ≤ (eta / C) * L ^ 2 := by
  have hsqr : (Real.sqrt (eta / C) * L) ^ 2 = (eta / C) * L ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg heta.le hC.le)]
  calc r ^ 2 ≤ (Real.sqrt (eta / C) * L) ^ 2 := pow_le_pow_left₀ hr hcap 2
    _ = (eta / C) * L ^ 2 := hsqr

/-- The auxiliary inner side is the negative triadic power at the sum of the two depths. -/
theorem goodCube_auxiliary_inner_side_add (j k : ℕ) :
    (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ)) =
      (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)) := by
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  push_cast
  ring

/-- The separate finite mass catalogue contains the original family and a depth-two cube compactly inside the unit middle quarter. -/
theorem goodCube_quarter_mass_catalog {d : ℕ}
    (Qfam : Set (Cube d)) (hfin : Qfam.Finite) :
    (goodCubeReferenceMassTests Qfam).Finite ∧
      Qfam ⊆ goodCubeReferenceMassTests Qfam ∧
      goodCubeQuarterMassTest d ∈ goodCubeReferenceMassTests Qfam ∧
      0 < (goodCubeQuarterMassTest d).2 ∧
      (goodCubeQuarterMassTest d).2 = (3 : ℝ) ^ (-(2 : ℤ)) ∧
      closure (cubeSet (goodCubeQuarterMassTest d)) ⊆
        middleQuarter ((0 : Vec d), (1 : ℝ)) := by
  refine ⟨hfin.insert _, Set.subset_insert _ _, Set.mem_insert _ _, ?_, rfl, ?_⟩
  · exact zpow_pos (by norm_num : (0:ℝ) < 3) (-(2:ℤ))
  · unfold goodCubeQuarterMassTest cubeSet middleQuarter
    exact closure_centeredAxisCube_subset (by norm_num : (3:ℝ)^(-(2:ℤ)) < (1:ℝ)/4)

/-- A triadic inner cube has a common positive normalized and ENNReal volume floor after every positive affine transport. -/
theorem goodCube_auxiliary_transported_volume_floor {d : ℕ}
    (Q : Cube d) (hQ : 0 < Q.2) (hQ1 : Q.2 ≤ 1)
    (a : ℕ) (x y : Vec d) {s : ℝ} (hs : 0 < s) :
    0 < ((3 : ℝ) ^ (-(a : ℤ))) ^ d ∧
      ((3 : ℝ) ^ (-(a : ℤ))) ^ d ≤
        (volume (cubeSet (affineCubeTransport y s (x, (3 : ℝ) ^ (-(a : ℤ)))))).toReal /
          (volume (cubeSet (affineCubeTransport y s Q))).toReal ∧
      ENNReal.ofReal (((3 : ℝ) ^ (-(a : ℤ))) ^ d) *
        volume (cubeSet (affineCubeTransport y s Q)) ≤
          volume (cubeSet (affineCubeTransport y s (x, (3 : ℝ) ^ (-(a : ℤ))))) := by
  have hpos : 0 < ((3 : ℝ) ^ (-(a : ℤ))) ^ d := by
    positivity
  have hratio : ((3 : ℝ) ^ (-(a : ℤ))) ^ d ≤
      (volume (cubeSet (affineCubeTransport y s (x, (3 : ℝ) ^ (-(a : ℤ)))))).toReal /
        (volume (cubeSet (affineCubeTransport y s Q))).toReal := by
    simpa [cubeSet, affineCubeTransport, affinePhi] using
      (goodCube_auxiliary_volume_ratio (affinePhi y s x) (affinePhi y s Q.1) a 0
        hs hQ hQ1).2.2
  have hfloor : ENNReal.ofReal (((3 : ℝ) ^ (-(a : ℤ))) ^ d) *
      volume (cubeSet (affineCubeTransport y s Q)) ≤
      volume (cubeSet (affineCubeTransport y s (x, (3 : ℝ) ^ (-(a : ℤ))))) := by
    simpa [cubeSet, affineCubeTransport, affinePhi] using
      goodCube_affine_volume_floor (x, (3 : ℝ) ^ (-(a : ℤ))) Q y hs
        (zpow_pos (by norm_num) _) le_rfl hQ.le hQ1
  exact ⟨hpos, hratio, hfloor⟩

/-- Construct finite covers at any prescribed response cap and harmonic depth inside the already fixed windows. -/
theorem exists_goodCube_auxiliary_cover_package {d : ℕ} {ι : Type*} [Finite ι]
    (K : ι → Set (Vec d)) (B : ι → Cube d) (W : ι → Set (Vec d)) (theta : ℝ)
    (hK : ∀ i, IsCompact (K i)) (hB : ∀ i, 0 < (B i).2)
    (hB1 : ∀ i, (B i).2 ≤ 1) (hWopen : ∀ i, IsOpen (W i))
    (hKW : ∀ i, K i ⊆ W i) (hWparent : ∀ i, closure (W i) ⊆ cubeSet (B i))
    (hWtheta : ∀ i, closure (W i) ⊆ centeredAxisCube (B i).1 (theta * (B i).2))
    (etaCap C : ℝ) (hetaCap : 0 < etaCap) (hC : 1 ≤ C) (j : ℕ) (hj : 2 ≤ j) :
    ∃ (k N : ℕ) (v0 : ℝ)
      (centers : ι → Finset (Vec d)),
      0 < v0 ∧ v0 = ((3 : ℝ) ^ (-((j + k : ℕ) : ℤ))) ^ d ∧
      ∀ i, (centers i).card ≤ N ∧ (↑(centers i) : Set (Vec d)) ⊆ K i ∧
        K i ⊆ ⋃ x ∈ centers i,
          centeredAxisCube x ((3 : ℝ) ^ (-((j + k : ℕ) : ℤ))) ∧
        ((3 : ℝ) ^ (-(k : ℤ))) ^ 2 ≤ (etaCap / C) * (B i).2 ^ 2 ∧
        ∀ x ∈ centers i,
          closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆ W i ∧
          closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆ cubeSet (B i) ∧
          closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆
            centeredAxisCube (B i).1 (theta * (B i).2) ∧
          closure (centeredAxisCube x ((3 : ℝ) ^ (-((j + k : ℕ) : ℤ)))) ⊆
            centeredAxisCube x (((3 : ℝ) ^ (-(k : ℤ))) / 2) ∧
          ∀ (y : Vec d) (s : ℝ), 0 < s →
            v0 ≤ (volume (cubeSet (affineCubeTransport y s
              (x, (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)))))).toReal /
              (volume (cubeSet (affineCubeTransport y s (B i)))).toReal ∧
            ENNReal.ofReal v0 * volume (cubeSet (affineCubeTransport y s (B i))) ≤
              volume (cubeSet (affineCubeTransport y s
                (x, (3 : ℝ) ^ (-((j + k : ℕ) : ℤ))))) := by
  classical
  have Cpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have h3 : (0 : ℝ) < 3 := by norm_num
  obtain ⟨k, N, centers, hk0, hcov⟩ :=
    exists_goodCube_auxiliary_covers (d := d) (ι := ι) K W hK hWopen hKW
      (fun i => Real.sqrt (etaCap / C) * (B i).2)
      (fun i => mul_pos (Real.sqrt_pos.2 (div_pos hetaCap Cpos)) (hB i)) j 0
  refine ⟨k, N, ((3 : ℝ) ^ (-((j + k : ℕ) : ℤ))) ^ d, centers,
    pow_pos (zpow_pos h3 _) d, rfl, ?_⟩
  intro i
  obtain ⟨hside, hcard, hsub, hcover, hout⟩ := hcov i
  have heq := goodCube_auxiliary_inner_side_add j k
  simp only [heq] at hcover
  have hcap := goodCube_auxiliary_square_cap
    (r := (3 : ℝ) ^ (-(k : ℤ))) (L := (B i).2) (eta := etaCap) (C := C)
    (le_of_lt (zpow_pos h3 _)) hetaCap Cpos hside
  refine ⟨hcard, hsub, hcover, hcap, ?_⟩
  intro x hx
  have hxW := hout x hx
  refine ⟨hxW, ?_, ?_, ?_, ?_⟩
  · exact subset_trans (subset_trans hxW subset_closure) (hWparent i)
  · exact subset_trans (subset_trans hxW subset_closure) (hWtheta i)
  · have hmid := goodCube_auxiliary_pair_middle_half x j k (by omega : (1 : ℕ) ≤ j)
    simp only [heq] at hmid
    exact hmid
  · intro y s hs
    exact (goodCube_auxiliary_transported_volume_floor (B i) (hB i) (hB1 i)
      (j + k) x y hs).2

/-- Construct the full auxiliary geometry from the original family, choosing the interior fraction before all response and cover parameters. -/
theorem exists_goodCube_complete_auxiliary_geometry {d : ℕ} [NeZero d]
    (Qfam : Set (Cube d)) (hfin : Qfam.Finite)
    (hpos : ∀ Q ∈ Qfam, 0 < Q.2)
    (hunit : ((0 : Vec d), (1 : ℝ)) ∈ Qfam)
    (hinside : ∀ Q ∈ Qfam, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) :
    let K := goodCubeAuxiliaryTargetSet Qfam
    let B := goodCubeAuxiliaryTargetParent Qfam
    ∃ (theta : ℝ) (W : Option (GoodCubeCompactPair Qfam) → Set (Vec d)),
      0 < theta ∧ theta < 1 ∧
      (∀ i, IsOpen (W i) ∧ K i ⊆ W i ∧ IsCompact (closure (W i)) ∧
        closure (W i) ⊆ cubeSet (B i) ∧
        closure (W i) ⊆ centeredAxisCube (B i).1 (theta * (B i).2)) ∧
      ∀ (etaCap C : ℝ), 0 < etaCap → 1 ≤ C → ∀ j : ℕ, 2 ≤ j →
        ∃ (k N : ℕ) (v0 : ℝ)
          (centers : Option (GoodCubeCompactPair Qfam) → Finset (Vec d)),
          0 < v0 ∧ v0 = ((3 : ℝ) ^ (-((j + k : ℕ) : ℤ))) ^ d ∧
          ∀ i, (centers i).card ≤ N ∧ (↑(centers i) : Set (Vec d)) ⊆ K i ∧
            K i ⊆ ⋃ x ∈ centers i,
              centeredAxisCube x ((3 : ℝ) ^ (-((j + k : ℕ) : ℤ))) ∧
            ((3 : ℝ) ^ (-(k : ℤ))) ^ 2 ≤ (etaCap / C) * (B i).2 ^ 2 ∧
            ∀ x ∈ centers i,
              closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆ W i ∧
              closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆ cubeSet (B i) ∧
              closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆
                centeredAxisCube (B i).1 (theta * (B i).2) ∧
              closure (centeredAxisCube x ((3 : ℝ) ^ (-((j + k : ℕ) : ℤ)))) ⊆
                centeredAxisCube x (((3 : ℝ) ^ (-(k : ℤ))) / 2) ∧
              ∀ (y : Vec d) (s : ℝ), 0 < s →
                v0 ≤ (volume (cubeSet (affineCubeTransport y s
                  (x, (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)))))).toReal /
                  (volume (cubeSet (affineCubeTransport y s (B i)))).toReal ∧
                ENNReal.ofReal v0 * volume (cubeSet (affineCubeTransport y s (B i))) ≤
                  volume (cubeSet (affineCubeTransport y s
                    (x, (3 : ℝ) ^ (-((j + k : ℕ) : ℤ))))) := by
  dsimp only
  obtain ⟨hfinite, hgeom⟩ :=
    goodCube_auxiliary_target_geometry Qfam hfin hpos hunit hinside
  letI : Finite (Option (GoodCubeCompactPair Qfam)) := hfinite
  obtain ⟨theta, W, hθ0, hθ1, hW⟩ :=
    exists_goodCube_auxiliary_windows (d := d)
      (ι := Option (GoodCubeCompactPair Qfam))
      (fun i => goodCubeAuxiliaryTargetSet Qfam i)
      (fun i => goodCubeAuxiliaryTargetParent Qfam i)
      (fun i => (hgeom i).1)
      (fun i => (hgeom i).2.2.2.1)
      (fun i => (hgeom i).2.1)
  refine ⟨theta, W, hθ0, hθ1, hW, ?_⟩
  intro etaCap C hetaCap hC j hj
  exact exists_goodCube_auxiliary_cover_package
    (d := d) (ι := Option (GoodCubeCompactPair Qfam))
    (fun i => goodCubeAuxiliaryTargetSet Qfam i)
    (fun i => goodCubeAuxiliaryTargetParent Qfam i)
    W theta
    (fun i => (hgeom i).1)
    (fun i => (hgeom i).2.2.2.1)
    (fun i => (hgeom i).2.2.2.2)
    (fun i => (hW i).1)
    (fun i => (hW i).2.1)
    (fun i => (hW i).2.2.2.1)
    (fun i => (hW i).2.2.2.2)
    etaCap C hetaCap hC j hj

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
