import SubdiffusiveProcess.GoodCube.RobustEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5Assembly




open Homogenization hiding Vec cubeSet
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation (Lattice)
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Opus55

attribute [local instance] Classical.propDecidable

/-- **Per-sample readout.**  The selected catalogue's finite local tests for one sample and one
diffusion law give the full `LocalTorsionEstimates` at `(c, C)`. -/
theorem goodCube_localTorsionEstimates_of_tests_sample
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (p A C CE c K theta k0 etaCap epsH v0 epsL2 massFraction : ℝ)
    (hA1 : 1 ≤ A) (hCEC : CE * A ^ CE ≤ C) (hAC : A ≤ C)
    (hexit : ∀ (d : ℕ), 2 ≤ d → ∀ (a : Vec d → ℝ) (law : Kernel (Vec d) (Path d)),
      LocalDiffusion a a law → ∀ (clock : ℝ → ℝ) (A : ℝ), 1 ≤ A → ∀ (Q : Cube d),
      0 < Q.2 → 0 < clock Q.2 → weightedMeasure a (cubeSet Q) ≠ 0 →
      weightedMeasure a (cubeSet Q) ≠ ⊤ → GoodCubeSobolevDisplay a p A clock Q →
      HasContinuousKilledDensity a law (cubeSet Q) →
      ∀ x ∈ cubeSet Q, meanExit law (cubeSet Q) x ≤ ENNReal.ofReal (CE * A ^ CE * clock Q.2))
    (grid0 : Finset (Vec d)) (j1 j2 : ℕ)
    (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d))
    (hgeom : ∀ (n : ℕ) (z : Lattice d),
      IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
        (goodCubeReferencePairs Pfam0 n z) (goodCubeReferenceFamily Qfam0 n z)
        (goodCubeReferenceFamily Afam0 n z))
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
    (M : GMCModel d) (hbudget : 2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2)
    (n : ℕ) (z : Lattice d) (omega : PotentialSample d) (law : Kernel (Vec d) (Path d))
    (hD : LocalDiffusionData (aCutoff M n omega) (aCutoff M n omega) law)
    (htests : GoodCubeFiniteLocalTests (aCutoff M n omega) p A
        (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction
        (Section7Process.timeScale (ahom M))
        (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ)^n • q.2)))
        (affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) '' Pairs)) :
    LocalTorsionEstimates (aCutoff M n omega) law
      (Section7Process.timeScale (ahom M)) p c C (goodCubeCentre n z, (3 : ℝ) ^ n)
      (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z) := by
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
  have lowerReadout (i : Option (GoodCubeCompactPair Qfam0)) :
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
      M J n omega (goodCubeCentre n z) law massFraction hbudget hD htests
    have hclock : 0 ≤ Section7Process.timeScale (ahom M)
        (affineCubeTransport (goodCubeCentre n z) ((3 : ℝ)^n)
          (goodCubeAuxiliaryTargetParent Qfam0 i)).2 := by
      apply (Section7Process.timeScale_pos (ahom_pos M) ?_).le
      exact mul_pos (pow_pos (by norm_num) n) (hparentPos i)
    intro x hx
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcLower hclock)).trans (hh x hx)
  obtain ⟨hfamily, hparent, hquarter⟩ :=
    goodCube_native_catalogue_memberships Qfam0 hunit depth hdepth G hGorig hGquarter n z
  obtain ⟨hsob, hmassQ, hmassD⟩ := goodCube_finiteLocalTests_sobolev_mass_readout
    (aCutoff M n omega) p A (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction c
    (Section7Process.timeScale (ahom M))
    (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ)^n • q.2)))
    (affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) '' Pairs)
    (goodCubeReferenceFamily Qfam0 n z) (goodCubeCentre n z, (3 : ℝ)^n)
    htests hfamily hparent hquarter hcMass
  -- exit lower on the middle quarter
  have hexitLower : ∀ x ∈ middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n),
      ENNReal.ofReal (c * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ n)) ≤
        meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x := by
    intro x hx
    have h := lowerReadout none
    have hB : affineCubeTransport (goodCubeCentre n z) ((3 : ℝ)^n)
        (goodCubeAuxiliaryTargetParent Qfam0 none) = (goodCubeCentre n z, (3 : ℝ)^n) := by
      simp [goodCubeAuxiliaryTargetParent, affineCubeTransport]
    have hE : cubeSet (affineCubeTransport (goodCubeCentre n z) ((3 : ℝ)^n) (Target none))
        = middleQuarter (goodCubeCentre n z, (3 : ℝ)^n) := by
      simp [Target, affineCubeTransport, cubeSet, middleQuarter, div_eq_mul_inv]
    rw [hB, hE] at h
    exact h x hx
  -- descendant lower
  have hdescLower : ∀ B' ∈ goodCubeReferenceFamily Qfam0 n z,
      ∀ Bq ∈ goodCubeReferenceFamily Qfam0 n z, CompactlyInside B' Bq →
        ∀ x ∈ cubeSet B', ENNReal.ofReal (c * Section7Process.timeScale (ahom M) Bq.2) ≤
          meanExit law (cubeSet Bq) x := by
    intro B' hB' B hB hcomp x hx
    rcases hB' with ⟨E0, hE0, rfl⟩
    rcases hB with ⟨B0, hB0, rfl⟩
    have hs : 0 < (3 : ℝ)^n := pow_pos (by norm_num) n
    have href : CompactlyInside E0 B0 :=
      (goodCube_compactlyInside_affine_iff E0 B0 (goodCubeCentre n z) hs).mp hcomp
    let pi : GoodCubeCompactPair Qfam0 := ⟨(E0, B0), hE0, hB0, href⟩
    exact lowerReadout (some pi) x hx
  -- exit upper on every family cube
  have hup : ∀ Q ∈ goodCubeReferenceFamily Qfam0 n z, ∀ x ∈ cubeSet Q,
      meanExit law (cubeSet Q) x ≤
        ENNReal.ofReal (C * Section7Process.timeScale (ahom M) Q.2) := by
    intro Q hQ x hx
    have hQ2 := (hgeom n z).side_pos Q hQ
    have hclock := Section7Process.timeScale_pos (ahom_pos M) hQ2
    obtain ⟨hm0, hmt⟩ := goodCube_weightedMeasure_aCutoff_ne_zero_ne_top M n omega Q hQ2
    refine (hexit d hd (aCutoff M n omega) law hD.1
      (Section7Process.timeScale (ahom M)) A hA1 Q hQ2 hclock
      hm0 hmt (hsob Q hQ)
      (hasContinuousKilledDensity_cubeSet_of_localDiffusionData hD Q) x hx).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCEC hclock.le))
  refine (goodCubeAnalyticPackage_of_supportInputs (aCutoff M n omega) law
    (Section7Process.timeScale (ahom M)) p c C 1
    (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferencePairs Pfam0 n z)
    (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z)
    hexitLower (hup _ (hgeom n z).self_mem) ?_ hmassQ
    (fun B' hB' B hB _ => hmassD B' hB' B hB)
    (mass_overlap_of_mass_descendant (hgeom n z) (weightedMeasure (aCutoff M n omega))
      (ENNReal.ofReal c) (fun B' hB' B hB _ => hmassD B' hB' B hB)) ?_
    (localHarmonicOscillation_one_of_isLocalCubeGeometry (hgeom n z) (aCutoff M n omega))).1
  · intro B' hB' Bq hBq hcomp
    exact ⟨hdescLower B' hB' Bq hBq hcomp, hup Bq hBq⟩
  · intro Q hQ f
    refine (hsob Q hQ f).trans ?_
    gcongr

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Opus55
