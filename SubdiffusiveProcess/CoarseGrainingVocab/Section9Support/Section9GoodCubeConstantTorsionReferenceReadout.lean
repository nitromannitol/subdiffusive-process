import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionSobolevLower
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteLocalTests
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryCatalogTransport
/-!
Reference auxiliary covers and the actual finite local tests yield the physical exit lower bound. The calibration retains exactly the native lower witnesses, including the order of contraction and volume parameters.
-/

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
/-- Explicit reference-cover and finite-test inputs for the physical torsion lower readout. -/
def GoodCubeReferenceTorsionLowerReadout (d : ℕ)
    (p A K theta k0 etaCap epsH v0 epsL2 : ℝ) : Prop :=
  ∀ (r j k : ℕ) (B E : Cube d) (centers : Finset (Vec d))
    (G : Finset (ℕ × Vec d)) (Pairs : Set (Cube d × Cube d)),
    B.2 = (3 : ℝ)^(-(r : ℤ)) →
    (r, B.1) ∈ G →
    (∀ x ∈ centers, (k, x) ∈ G) →
    (∀ x ∈ centers,
      ((x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))), (x, (3 : ℝ)^(-(k : ℤ)))) ∈ Pairs) →
    cubeSet E ⊆ ⋃ x ∈ centers, cubeSet (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))) →
    (∀ x ∈ centers, cubeSet (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))) ⊆
      cubeSet (x, (3 : ℝ)^(-(k : ℤ)))) →
    (∀ x ∈ centers, cubeSet (x, (3 : ℝ)^(-(k : ℤ))) ⊆ cubeSet B) →
    (∀ x ∈ centers, cubeSet (x, (3 : ℝ)^(-(k : ℤ))) ⊆
      centeredAxisCube B.1 (theta * B.2)) →
    ((3 : ℝ)^(-(k : ℤ)))^2 ≤ etaCap / K * B.2^2 →
    (∀ x ∈ centers, ∀ (y : Vec d) (s : ℝ), 0 < s →
      ENNReal.ofReal v0 * volume (cubeSet (affineCubeTransport y s B)) ≤
        volume (cubeSet (affineCubeTransport y s
          (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ)))))) →
    ∀ (M : GMCModel d) (J n : ℕ) (omega : PotentialSample d) (y : Vec d)
      (law : Kernel (Vec d) (Path d)) (massFraction : ℝ),
      2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2 →
      LocalDiffusionData (aCutoff M n omega) (aCutoff M n omega) law →
      GoodCubeFiniteLocalTests (aCutoff M n omega) p A
        (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction
        (Section7Process.timeScale (ahom M))
        (G.image (fun q => ((n : ℤ) - q.1, y + (3 : ℝ)^n • q.2)))
        (affinePairTransport y ((3 : ℝ)^n) '' Pairs) →
      ∀ x ∈ cubeSet (affineCubeTransport y ((3 : ℝ)^n) E),
        ENNReal.ofReal ((k0 / 2) * Section7Process.timeScale (ahom M)
          (affineCubeTransport y ((3 : ℝ)^n) B).2) ≤
          meanExit law (cubeSet (affineCubeTransport y ((3 : ℝ)^n) B)) x


private theorem translate_openCube_eq_cubeSet {d : ℕ} (z : Vec d) (m : ℤ) :
    Homogenization.translateSet z (openCubeSet (originCube d m))
      = cubeSet (z, (3 : ℝ) ^ m) := by
  rw [← translatedCube_eq_cubeSet m z]
  ext x
  simp only [SubdiffusiveProcess.CoarseGrainingVocab.translatedCube, Set.mem_image,
    Homogenization.translateSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy, hx⟩; exact ⟨y, hy, (hx.trans (add_comm y z)).symm⟩
  · rintro ⟨y, hy, hx⟩; exact ⟨y, hy, hx.symm.trans (add_comm z y)⟩

/-- The native lower constants give the affine reference-cover readout with the same witnesses. -/
theorem exists_goodCube_reference_torsion_lower_readout_parameters
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (p A : ℝ) (hp : 2 < p) (hA : 1 ≤ A) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ theta : ℝ, 0 < theta → theta < 1 →
      ∃ k0 etaCap epsH : ℝ, 0 < k0 ∧ 0 < etaCap ∧ 0 < epsH ∧
      ∀ v0 : ℝ, 0 < v0 → ∃ epsL2 : ℝ, 0 < epsL2 ∧
        GoodCubeReferenceTorsionLowerReadout d p A K theta k0 etaCap epsH v0 epsL2 := by
  obtain ⟨K, hK, hNat1⟩ :=
    exists_goodCube_cutoff_sobolev_meanExit_lower_parameters d hd p A hp hA
  refine ⟨K, hK, fun theta htheta1 htheta2 => ?_⟩
  obtain ⟨k0, etaCap, epsH, hk0, heta, hepsH, hNat2⟩ := hNat1 theta htheta1 htheta2
  refine ⟨k0, etaCap, epsH, hk0, heta, hepsH, fun v0 hv0 => ?_⟩
  obtain ⟨epsL2, hepsL2, hNat⟩ := hNat2 v0 hv0
  refine ⟨epsL2, hepsL2, ?_⟩
  intro r j k B E centers G Pairs hB2 hGr hGk hPairs hcover hinnerOuter houterParent
    hparentCentered hcap hvolume M J n omega y law massFraction hlog hLDD hTests x hx
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := pow_pos (by norm_num) n
  have sideEq : ∀ l : ℕ, (3 : ℝ) ^ n * (3 : ℝ) ^ (-(l : ℤ)) = (3 : ℝ) ^ ((n : ℤ) - (l : ℤ)) :=
    fun l => (goodCube_native_depth_scales n l l le_rfl).1
  have parentSide : (3 : ℝ) ^ n * B.2 = (3 : ℝ) ^ ((n : ℤ) - (r : ℤ)) := by
    rw [hB2]; exact sideEq r
  have parentDom : Homogenization.translateSet (y + (3 : ℝ) ^ n • B.1)
      (openCubeSet (originCube d ((n : ℤ) - (r : ℤ))))
      = cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) B) := by
    rw [translate_openCube_eq_cubeSet]
    show cubeSet (y + (3 : ℝ) ^ n • B.1, (3 : ℝ) ^ ((n : ℤ) - (r : ℤ)))
        = cubeSet (y + (3 : ℝ) ^ n • B.1, (3 : ℝ) ^ n * B.2)
    rw [parentSide]
  have hcenteredImg : affinePhi y ((3 : ℝ) ^ n) '' centeredAxisCube B.1 (theta * B.2)
      = centeredAxisCube (y + (3 : ℝ) ^ n • B.1) (theta * (3 : ℝ) ^ ((n : ℤ) - (r : ℤ))) := by
    change affinePhi y ((3 : ℝ) ^ n) '' cubeSet (B.1, theta * B.2) = _
    rw [← cubeSet_affineCubeTransport y h3 (B.1, theta * B.2)]
    change centeredAxisCube (y + (3 : ℝ) ^ n • B.1) ((3 : ℝ) ^ n * (theta * B.2)) = _
    congr 1
    rw [← parentSide]
    ring
  have auxDom : ∀ (c : Vec d) (l : ℕ),
      Homogenization.translateSet (y + (3 : ℝ) ^ n • c)
          (openCubeSet (originCube d ((n : ℤ) - (l : ℤ))))
        = cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) (c, (3 : ℝ) ^ (-(l : ℤ)))) := by
    intro c l
    rw [translate_openCube_eq_cubeSet]
    show cubeSet (y + (3 : ℝ) ^ n • c, (3 : ℝ) ^ ((n : ℤ) - (l : ℤ)))
        = cubeSet (y + (3 : ℝ) ^ n • c, (3 : ℝ) ^ n * (3 : ℝ) ^ (-(l : ℤ)))
    rw [sideEq l]
  have cubeMono : ∀ (Q1 Q2 : Cube d), cubeSet Q1 ⊆ cubeSet Q2 →
      cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) Q1) ⊆
        cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) Q2) := by
    intro Q1 Q2 h Qpt hQpt
    rw [cubeSet_affineCubeTransport y h3 Q1] at hQpt
    rw [cubeSet_affineCubeTransport y h3 Q2]
    exact Set.image_mono h hQpt
  have hGparent : ((n : ℤ) - (r : ℤ), y + (3 : ℝ) ^ n • B.1) ∈
      G.image (fun q : ℕ × Vec d => ((n : ℤ) - q.1, y + (3 : ℝ) ^ n • q.2)) :=
    Finset.mem_image_of_mem _ hGr
  have hsobP := hTests.sobolev _ hGparent
  have hGimg : ∀ x : Vec d, x ∈ centers →
      ((n : ℤ) - (k : ℤ), y + (3 : ℝ) ^ n • x) ∈
        G.image (fun q : ℕ × Vec d => ((n : ℤ) - q.1, y + (3 : ℝ) ^ n • q.2)) := by
    intro x hxmem
    exact Finset.mem_image_of_mem _ (hGk x hxmem)
  have hsobI : ∀ i : {x : Vec d // x ∈ centers}, GoodCubeSobolevDisplay (aCutoff M n omega) p A
      (Section7Process.timeScale (ahom M))
      (y + (3 : ℝ) ^ n • (i : Vec d), (3 : ℝ) ^ ((n : ℤ) - (k : ℤ))) := by
    intro i
    exact hTests.sobolev _ (hGimg (i : Vec d) i.property)
  have htorsP := hTests.torsion _ hGparent
  have hcapT : ∀ _ : {x : Vec d // x ∈ centers},
      ((3 : ℝ) ^ ((n : ℤ) - (k : ℤ))) ^ 2 ≤ etaCap / K * ((3 : ℝ) ^ ((n : ℤ) - (r : ℤ))) ^ 2 := by
    intro _
    simpa only [parentSide] using goodCube_auxiliary_physical_square_cap n k hcap
  have hopenT : IsOpen (cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) E)) :=
    isOpen_centeredAxisCube (affineCubeTransport y ((3 : ℝ) ^ n) E).1
      (affineCubeTransport y ((3 : ℝ) ^ n) E).2
  have hcoverT : cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) E) ⊆
      ⋃ i : {x : Vec d // x ∈ centers},
        cubeSet (affineCubeTransport y ((3 : ℝ) ^ n)
          ((i : Vec d), (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)))) := by
    intro x hx
    rw [cubeSet_affineCubeTransport y h3 E] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨x0, hmem0⟩ := Set.mem_iUnion.mp (hcover hu)
    obtain ⟨hx0, hu0⟩ := Set.mem_iUnion.mp hmem0
    refine Set.mem_iUnion.mpr ⟨⟨x0, hx0⟩, ?_⟩
    show affinePhi y ((3 : ℝ) ^ n) u ∈
      cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) (x0, (3 : ℝ) ^ (-((j + k : ℕ) : ℤ))))
    rw [cubeSet_affineCubeTransport y h3]
    exact ⟨u, hu0, rfl⟩
  have hio : ∀ i : {x : Vec d // x ∈ centers},
      cubeSet (affineCubeTransport y ((3 : ℝ) ^ n)
          ((i : Vec d), (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)))) ⊆
        Homogenization.translateSet (y + (3 : ℝ) ^ n • (i : Vec d))
          (openCubeSet (originCube d ((n : ℤ) - (k : ℤ)))) := by
    intro i x hx
    rw [auxDom]
    rw [cubeSet_affineCubeTransport y h3] at hx ⊢
    exact Set.image_mono (hinnerOuter (i : Vec d) i.property) hx
  have hou : ∀ i : {x : Vec d // x ∈ centers},
      Homogenization.translateSet (y + (3 : ℝ) ^ n • (i : Vec d))
          (openCubeSet (originCube d ((n : ℤ) - (k : ℤ)))) ⊆
        Homogenization.translateSet (y + (3 : ℝ) ^ n • B.1)
          (openCubeSet (originCube d ((n : ℤ) - (r : ℤ)))) := by
    intro i x hx
    rw [parentDom]
    rw [auxDom] at hx
    exact cubeMono _ _ (houterParent (i : Vec d) i.property) hx
  have hic : ∀ i : {x : Vec d // x ∈ centers},
      cubeSet (affineCubeTransport y ((3 : ℝ) ^ n)
          ((i : Vec d), (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)))) ⊆
        Homogenization.translateSet (y + (3 : ℝ) ^ n • B.1)
          (Homogenization.scaledClosedCubeSet (originCube d ((n : ℤ) - (r : ℤ))) theta) := by
    intro i x hx
    have h1 : x ∈ cubeSet (affineCubeTransport y ((3 : ℝ) ^ n)
        ((i : Vec d), (3 : ℝ) ^ (-(k : ℤ)))) :=
      cubeMono _ _ (hinnerOuter (i : Vec d) i.property) hx
    rw [cubeSet_affineCubeTransport y h3] at h1
    obtain ⟨u, hu, rfl⟩ := h1
    have hu2 := hparentCentered (i : Vec d) i.property hu
    have h4 : affinePhi y ((3 : ℝ) ^ n) u ∈
        centeredAxisCube (y + (3 : ℝ) ^ n • B.1) (theta * (3 : ℝ) ^ ((n : ℤ) - (r : ℤ))) := by
      rw [← hcenteredImg]
      exact ⟨u, hu2, rfl⟩
    exact goodCube_centered_interior_subset_translated_profile (y + (3 : ℝ) ^ n • B.1)
      ((n : ℤ) - (r : ℤ)) htheta1 h4
  have hvol : ∀ i : {x : Vec d // x ∈ centers},
      ENNReal.ofReal v0 * volume
          (Homogenization.translateSet (y + (3 : ℝ) ^ n • B.1)
            (openCubeSet (originCube d ((n : ℤ) - (r : ℤ))))) ≤
        volume (cubeSet (affineCubeTransport y ((3 : ℝ) ^ n)
          ((i : Vec d), (3 : ℝ) ^ (-((j + k : ℕ) : ℤ))))) := by
    intro i
    rw [parentDom]
    exact hvolume (i : Vec d) i.property y ((3 : ℝ) ^ n) h3
  have hhar : ∀ i : {x : Vec d // x ∈ centers}, ∀ h : Vec d → ℝ,
      WeakHarmonic (aCutoff M n omega)
          (Homogenization.translateSet (y + (3 : ℝ) ^ n • (i : Vec d))
            (openCubeSet (originCube d ((n : ℤ) - (k : ℤ))))) h →
        oscillation (cubeSet (affineCubeTransport y ((3 : ℝ) ^ n)
            ((i : Vec d), (3 : ℝ) ^ (-((j + k : ℕ) : ℤ))))) h ≤
          ENNReal.ofReal epsH * oscillation
            (Homogenization.translateSet (y + (3 : ℝ) ^ n • (i : Vec d))
              (openCubeSet (originCube d ((n : ℤ) - (k : ℤ))))) h := by
    intro i h hw
    have hmem : affinePairTransport y ((3 : ℝ) ^ n)
        (((i : Vec d), (3 : ℝ) ^ (-((j + k : ℕ) : ℤ))), ((i : Vec d), (3 : ℝ) ^ (-(k : ℤ)))) ∈
        affinePairTransport y ((3 : ℝ) ^ n) '' Pairs :=
      ⟨(((i : Vec d), (3 : ℝ) ^ (-((j + k : ℕ) : ℤ))), ((i : Vec d), (3 : ℝ) ^ (-(k : ℤ)))),
        hPairs (i : Vec d) i.property, rfl⟩
    have hcon := hTests.harmonic.contraction _ hmem
    rw [auxDom] at hw ⊢
    exact hcon h hw
  have hres := hNat M J n omega ((n : ℤ) - (r : ℤ)) (y + (3 : ℝ) ^ n • B.1) law
    (by omega) hlog hLDD
    ((fun _ => ((n : ℤ) - (k : ℤ))) : {x : Vec d // x ∈ centers} → ℤ)
    (fun i => y + (3 : ℝ) ^ n • (i : Vec d))
    (fun i => cubeSet (affineCubeTransport y ((3 : ℝ) ^ n)
      ((i : Vec d), (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)))))
    (cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) E))
    (by intro i; change (n : ℤ) - (k : ℤ) ≤ (n : ℤ); omega) hcapT hopenT hcoverT
    (fun i => measurableSet_cubeSet (affineCubeTransport y ((3 : ℝ) ^ n)
      ((i : Vec d), (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)))))
    hio hou hic hvol hsobP hsobI htorsP hhar
  have hres' : ENNReal.ofReal ((k0 / 2) * Section7Process.timeScale (ahom M)
        ((3 : ℝ) ^ ((n : ℤ) - (r : ℤ)))) ≤
      meanExit law (Homogenization.translateSet (y + (3 : ℝ) ^ n • B.1)
        (openCubeSet (originCube d ((n : ℤ) - (r : ℤ))))) x := hres x hx
  rw [parentDom, ← parentSide] at hres'
  exact hres'

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
