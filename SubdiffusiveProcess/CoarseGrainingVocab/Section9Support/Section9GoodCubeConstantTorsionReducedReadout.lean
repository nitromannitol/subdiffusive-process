module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCatalogueMembership
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionMassReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionReferenceReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryCatalog
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReducedV4
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceTemplate
@[expose] public section

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
attribute [local instance] Classical.propDecidable
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

theorem goodCube_reducedDisplaysV4_of_finiteLocalTests
    {d : ℕ} [NeZero d]
    (p A c eps1 K theta k0 etaCap epsH v0 epsL2 massFraction : ℝ)
    (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d))
    (hfin : Qfam0.Finite) (hpos : ∀ Q ∈ Qfam0, 0 < Q.2)
    (hunit : ((0 : Vec d), (1 : ℝ)) ∈ Qfam0)
    (hinside : ∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ)))
    (depth : Qfam0 → ℕ)
    (hdepth : ∀ Q : Qfam0, Q.val.2 = (3 : ℝ)^(-(depth Q : ℤ)))
    (j k J : ℕ) (G : Finset (ℕ × Vec d)) (Pairs : Set (Cube d × Cube d))
    (centers : Option (GoodCubeCompactPair Qfam0) → Finset (Vec d))
    (hGorig : ∀ Q : Qfam0, (depth Q, Q.val.1) ∈ G)
    (hGquarter : (2, (0 : Vec d)) ∈ G)
    (hGaux : ∀ i, ∀ x ∈ centers i, (k, x) ∈ G)
    (hPairs : ∀ i, ∀ x ∈ centers i,
      ((x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))), (x, (3 : ℝ)^(-(k : ℤ)))) ∈ Pairs)
    (hcover : ∀ i, goodCubeAuxiliaryTargetSet Qfam0 i ⊆
      ⋃ x ∈ centers i, cubeSet (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))))
    (hcap : ∀ i, ((3 : ℝ)^(-(k : ℤ)))^2 ≤
      etaCap / K * (goodCubeAuxiliaryTargetParent Qfam0 i).2^2)
    (haux : ∀ i, ∀ x ∈ centers i,
      closure (cubeSet (x, (3 : ℝ)^(-(k : ℤ)))) ⊆
          cubeSet (goodCubeAuxiliaryTargetParent Qfam0 i) ∧
      closure (cubeSet (x, (3 : ℝ)^(-(k : ℤ)))) ⊆
          centeredAxisCube (goodCubeAuxiliaryTargetParent Qfam0 i).1
            (theta * (goodCubeAuxiliaryTargetParent Qfam0 i).2) ∧
      closure (cubeSet (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ)))) ⊆
          centeredAxisCube x (((3 : ℝ)^(-(k : ℤ))) / 2) ∧
      ∀ (y : Vec d) (s : ℝ), 0 < s →
        ENNReal.ofReal v0 * volume (cubeSet
          (affineCubeTransport y s (goodCubeAuxiliaryTargetParent Qfam0 i))) ≤
          volume (cubeSet (affineCubeTransport y s
            (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))))))
    (hLower : GoodCubeReferenceTorsionLowerReadout d p A K theta k0 etaCap epsH v0 epsL2)
    (hcLower : c ≤ k0 / 2) (hcMass : c ≤ massFraction)
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ))
    (hbudget : ∀ M : GMCModel d, M.delta ≤ c →
      2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2)
    (htests : ∀ (M : GMCModel d), M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d)
      (omega : PotentialSample d),
      omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z →
      GoodCubeFiniteLocalTests (aCutoff M n omega) p A
        (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction
        (Section7Process.timeScale (ahom M))
        (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ)^n • q.2)))
        (affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) '' Pairs)) :
    GoodCubeReducedDisplaysV4 d c A p eps1 Pfam0 Qfam0 Afam0 bad
:= by
  classical
  have htarget := goodCube_auxiliary_target_geometry Qfam0 hfin hpos hunit hinside
  have hparentMem (i : Option (GoodCubeCompactPair Qfam0)) :
      goodCubeAuxiliaryTargetParent Qfam0 i ∈ Qfam0 := (htarget.2 i).2.2.1
  have hparentPos (i : Option (GoodCubeCompactPair Qfam0)) :
      0 < (goodCubeAuxiliaryTargetParent Qfam0 i).2 := (htarget.2 i).2.2.2.1
  let Target : Option (GoodCubeCompactPair Qfam0) → Cube d := fun i =>
    match i with
    | none => ((0 : Vec d), (1 : ℝ) / 4)
    | some q => q.val.1
  have hTargetClosure (i : Option (GoodCubeCompactPair Qfam0)) :
      closure (cubeSet (Target i)) = goodCubeAuxiliaryTargetSet Qfam0 i := by
    cases i <;> rfl
  have hinout (i : Option (GoodCubeCompactPair Qfam0)) (x : Vec d) (hx : x ∈ centers i) :
      cubeSet (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))) ⊆
        cubeSet (x, (3 : ℝ)^(-(k : ℤ))) := by
    refine subset_closure.trans (((haux i x hx).2.2.1).trans ?_)
    have hs : 0 < (3 : ℝ)^(-(k : ℤ)) := zpow_pos (by norm_num) _
    exact centeredAxisCube_mono (by linarith)
  have lowerReadout (M : GMCModel d) (hM : M.delta ≤ c) (n : ℕ) (z : Lattice d)
      (omega : PotentialSample d)
      (hnot : omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z)
      (law : Kernel (Vec d) (Path d))
      (hD : LocalDiffusionData (aCutoff M n omega) (aCutoff M n omega) law)
      (i : Option (GoodCubeCompactPair Qfam0)) :
      ∀ x ∈ cubeSet (affineCubeTransport (goodCubeCentre n z) ((3 : ℝ)^n) (Target i)),
        ENNReal.ofReal (c * Section7Process.timeScale (ahom M)
          (affineCubeTransport (goodCubeCentre n z) ((3 : ℝ)^n)
            (goodCubeAuxiliaryTargetParent Qfam0 i)).2) ≤
          meanExit law (cubeSet (affineCubeTransport (goodCubeCentre n z) ((3 : ℝ)^n)
            (goodCubeAuxiliaryTargetParent Qfam0 i))) x := by
    let Bi : Qfam0 := ⟨goodCubeAuxiliaryTargetParent Qfam0 i, hparentMem i⟩
    have hcov : cubeSet (Target i) ⊆
        ⋃ x ∈ centers i, cubeSet (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))) := by
      refine subset_closure.trans ?_
      rw [hTargetClosure i]
      exact hcover i
    have hh := hLower (depth Bi) j k Bi.val (Target i) (centers i) G Pairs
      (hdepth Bi) (hGorig Bi) (hGaux i) (hPairs i) hcov (hinout i)
      (fun x hx => subset_closure.trans (haux i x hx).1)
      (fun x hx => subset_closure.trans (haux i x hx).2.1)
      (hcap i) (fun x hx y s hs => (haux i x hx).2.2.2 y s hs)
      M J n omega (goodCubeCentre n z) law massFraction (hbudget M hM) hD
      (htests M hM n z omega hnot)
    have hclock : 0 ≤ Section7Process.timeScale (ahom M)
        (affineCubeTransport (goodCubeCentre n z) ((3 : ℝ)^n)
          (goodCubeAuxiliaryTargetParent Qfam0 i)).2 := by
      apply (Section7Process.timeScale_pos (ahom_pos M) ?_).le
      exact mul_pos (pow_pos (by norm_num) n) (hparentPos i)
    intro x hx
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcLower hclock)).trans (hh x hx)
  have massReadout (M : GMCModel d) (hM : M.delta ≤ c) (n : ℕ) (z : Lattice d)
      (omega : PotentialSample d)
      (hnot : omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z) :
      (∀ Q ∈ goodCubeReferenceFamily Qfam0 n z,
        GoodCubeSobolevDisplay (aCutoff M n omega) p A
          (Section7Process.timeScale (ahom M)) Q) ∧
      ENNReal.ofReal c * weightedMeasure (aCutoff M n omega)
        (cubeSet (goodCubeCentre n z, (3 : ℝ)^n)) ≤
          weightedMeasure (aCutoff M n omega) (middleQuarter (goodCubeCentre n z, (3 : ℝ)^n)) ∧
      ∀ Q ∈ goodCubeReferenceFamily Qfam0 n z, ∀ R ∈ goodCubeReferenceFamily Qfam0 n z,
        ENNReal.ofReal c * weightedMeasure (aCutoff M n omega) (cubeSet R) ≤
          weightedMeasure (aCutoff M n omega) (cubeSet Q) := by
    obtain ⟨hfamily, hparent, hquarter⟩ :=
      goodCube_native_catalogue_memberships Qfam0 hunit depth hdepth G hGorig hGquarter n z
    exact goodCube_finiteLocalTests_sobolev_mass_readout (aCutoff M n omega) p A
      (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction c
      (Section7Process.timeScale (ahom M))
      (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ)^n • q.2)))
      (affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) '' Pairs)
      (goodCubeReferenceFamily Qfam0 n z) (goodCubeCentre n z, (3 : ℝ)^n)
      (htests M hM n z omega hnot) hfamily hparent hquarter hcMass
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M hM n z omega hom law hD
    exact (massReadout M hM n z omega (not_mem_layerZero_of_goodCubeEvent hom)).1
  · intro M hM n z omega hom law hD x hx
    have h := lowerReadout M hM n z omega (not_mem_layerZero_of_goodCubeEvent hom)
      law hD none
    have hB : affineCubeTransport (goodCubeCentre n z) ((3 : ℝ)^n)
        (goodCubeAuxiliaryTargetParent Qfam0 none) = (goodCubeCentre n z, (3 : ℝ)^n) := by
      simp [goodCubeAuxiliaryTargetParent, affineCubeTransport]
    have hE : cubeSet (affineCubeTransport (goodCubeCentre n z) ((3 : ℝ)^n) (Target none))
        = middleQuarter (goodCubeCentre n z, (3 : ℝ)^n) := by
      simp [Target, affineCubeTransport, cubeSet, middleQuarter, div_eq_mul_inv]
    rw [hB, hE] at h
    exact h x hx
  · intro M hM n z omega hom law hD B' hB' B hB hcomp x hx
    rcases hB' with ⟨E0, hE0, rfl⟩
    rcases hB with ⟨B0, hB0, rfl⟩
    have hs : 0 < (3 : ℝ)^n := pow_pos (by norm_num) n
    have href : CompactlyInside E0 B0 :=
      (goodCube_compactlyInside_affine_iff E0 B0 (goodCubeCentre n z) hs).mp hcomp
    let pi : GoodCubeCompactPair Qfam0 := ⟨(E0, B0), hE0, hB0, href⟩
    exact lowerReadout M hM n z omega (not_mem_layerZero_of_goodCubeEvent hom)
      law hD (some pi) x hx
  · intro M hM n z omega hom law hD
    exact (massReadout M hM n z omega (not_mem_layerZero_of_goodCubeEvent hom)).2.1
  · intro M hM n z omega hom law hD B' hB' B hB hcomp
    exact (massReadout M hM n z omega (not_mem_layerZero_of_goodCubeEvent hom)).2.2
      B' hB' B hB

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
