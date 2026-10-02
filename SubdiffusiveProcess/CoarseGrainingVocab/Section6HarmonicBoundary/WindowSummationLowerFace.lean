import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.PhysicalFaceTileCap

/-!
# Lower-face form of the physical boundary tile estimate

The existing physical theorem treats a domain lying below its met face.  This
file supplies the opposite sign directly from the arbitrary-zero-set tile
estimate.  No reflection of the coefficient or potential sample is used.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The open half of a triadic cube below the coordinate hyperplane through
its centre. -/
def windowSummationCubeLowerHalf (Q : TriadicCube d) (j0 : Fin d) : Set (Vec d) :=
  Set.pi Set.univ fun i : Fin d ↦
    Set.Ioo (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
      (if i = j0 then (Q.index i : ℝ) * cubeScaleFactor Q
        else ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)

omit [NeZero d] in
theorem measurableSet_windowSummationCubeLowerHalf
    (Q : TriadicCube d) (j0 : Fin d) :
    MeasurableSet (windowSummationCubeLowerHalf Q j0) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo

omit [NeZero d] in
theorem windowSummationCubeLowerHalf_subset_openCubeSet
    (Q : TriadicCube d) (j0 : Fin d) :
    windowSummationCubeLowerHalf Q j0 ⊆ openCubeSet Q := by
  have hs : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  intro x hx
  rw [openCubeSet_eq_pi_Ioo]
  intro i _
  have hxi := hx i (Set.mem_univ i)
  by_cases h : i = j0
  · simp only [if_pos h] at hxi
    exact ⟨hxi.1, lt_of_lt_of_le hxi.2 (by nlinarith [hs])⟩
  · simpa only [if_neg h] using hxi

omit [NeZero d] in
theorem mem_windowSummationCubeLowerHalf_iff
    (Q : TriadicCube d) (j0 : Fin d) (x : Vec d) :
    x ∈ windowSummationCubeLowerHalf Q j0 ↔
      x ∈ openCubeSet Q ∧
        x j0 < (Q.index j0 : ℝ) * cubeScaleFactor Q := by
  constructor
  · intro hx
    refine ⟨windowSummationCubeLowerHalf_subset_openCubeSet Q j0 hx, ?_⟩
    simpa using (hx j0 (Set.mem_univ j0)).2
  · rintro ⟨hxQ, hxj⟩
    intro i _
    have hxi := hxQ i
    by_cases h : i = j0
    · subst h
      exact ⟨hxi.1, by simpa using hxj⟩
    · exact ⟨hxi.1, by simpa [h] using hxi.2⟩

omit [NeZero d] in
theorem volume_windowSummationCubeLowerHalf_toReal
    (Q : TriadicCube d) (j0 : Fin d) :
    (volume (windowSummationCubeLowerHalf Q j0)).toReal = cubeVolume Q / 2 := by
  have hs : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  set lo : Fin d → ℝ := fun i ↦
    ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q with hlo
  set hi : Fin d → ℝ := fun i ↦
    if i = j0 then (Q.index i : ℝ) * cubeScaleFactor Q
      else ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q with hhi
  have hab : lo ≤ hi := by
    intro i
    rw [hlo, hhi]
    by_cases h : i = j0
    · simp only [if_pos h]
      nlinarith [hs]
    · simp only [if_neg h]
      nlinarith [hs]
  have hvol : (volume (windowSummationCubeLowerHalf Q j0)).toReal =
      ∏ i : Fin d, (hi i - lo i) := by
    simpa [windowSummationCubeLowerHalf, hlo, hhi] using
      Real.volume_pi_Ioo_toReal (ι := Fin d) hab
  rw [hvol]
  have hside : ∀ i : Fin d,
      hi i - lo i = cubeScaleFactor Q *
        (if i = j0 then (1 / 2 : ℝ) else 1) := by
    intro i
    rw [hlo, hhi]
    by_cases h : i = j0
    · simp only [if_pos h]
      ring
    · simp only [if_neg h]
      ring
  calc
    ∏ i : Fin d, (hi i - lo i) =
        ∏ i : Fin d, (cubeScaleFactor Q *
          (if i = j0 then (1 / 2 : ℝ) else 1)) :=
      Finset.prod_congr rfl fun i _ ↦ hside i
    _ = (∏ _i : Fin d, cubeScaleFactor Q) *
        ∏ i : Fin d, (if i = j0 then (1 / 2 : ℝ) else 1) :=
      Finset.prod_mul_distrib
    _ = cubeVolume Q / 2 := by
      rw [Finset.prod_ite_eq' Finset.univ j0 (fun _ : Fin d ↦ (1 / 2 : ℝ))]
      simp [cubeVolume]
      ring

omit [NeZero d] in
theorem half_mul_volume_openCubeSet_le_volume_windowSummationCubeLowerHalf
    (Q : TriadicCube d) (j0 : Fin d) :
    (1 / 2 : ℝ) * (volume (openCubeSet Q)).toReal ≤
      (volume (windowSummationCubeLowerHalf Q j0)).toReal := by
  rw [volume_openCubeSet_toReal, volume_windowSummationCubeLowerHalf_toReal]
  ring_nf
  exact le_rfl

omit [NeZero d] in
/-- The zero extension read on a tile centred on a lower met face. -/
theorem exists_windowSummation_metFaceTile_zeroExtendedH1_lower
    {V : Set (Vec d)} (hV : MeasurableSet V) (rho : H10Function V)
    (c : Vec d) (k : ℤ) (j0 : Fin d)
    (houtside : ∀ x : Vec d, x j0 < 0 → x + c ∉ V) :
    ∃ w : H1Function (openCubeSet (originCube d k)),
      (∀ x, w.toFun x = zeroExtend V rho.toH1Function.toFun (x + c)) ∧
      (∀ x, w.grad x = zeroExtendGrad V rho.toH1Function.grad (x + c)) ∧
      (∀ x ∈ windowSummationCubeLowerHalf (originCube d k) j0,
        w.toFun x = 0) ∧
      IntegrableOn w.toFun (openCubeSet (originCube d k)) ∧
      IntegrableOn (fun x ↦ w.toFun x ^ 2) (openCubeSet (originCube d k)) ∧
      MemLp (fun x ↦ w.toFun x - cubeAverage (originCube d k) w.toFun) 2
        (volume.restrict (openCubeSet (originCube d k))) := by
  classical
  set T : TriadicCube d := originCube d k with hT
  letI : IsFiniteMeasure (volume.restrict (openCubeSet T)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top T
  refine ⟨translatedZeroExtendH1 hV rho c (openCubeSet T), fun x ↦ rfl,
    fun x ↦ rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx0 : x j0 < 0 := by
      have := (mem_windowSummationCubeLowerHalf_iff T j0 x).mp hx |>.2
      simpa [hT, originCube] using this
    exact zeroExtend_of_notMem _ (houtside x hx0)
  · exact (translatedZeroExtendH1 hV rho c (openCubeSet T)).memL2.integrable
      (by norm_num)
  · simpa only [IntegrableOn] using
      (translatedZeroExtendH1 hV rho c (openCubeSet T)).memL2.integrable_sq
  · exact (translatedZeroExtendH1 hV rho c (openCubeSet T)).memL2.sub
      (memLp_const _)

/-- The boundary-tile estimate with the vanishing half oriented below the
tile centre.  This is the sign-reversed companion of
`exists_boundaryTileResidualMeanCap_half`. -/
theorem exists_windowSummation_boundaryTileResidualMeanCap_lower
    (d : ℕ) [NeZero d] :
    ∃ Ctile : ℝ, 0 < Ctile ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L → ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        let T := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        ∀ (w : H1Function (openCubeSet T)) (j0 : Fin d),
          (∀ x ∈ windowSummationCubeLowerHalf T j0,
            w.toFun x = 0) →
          IntegrableOn w.toFun (openCubeSet T) →
          IntegrableOn (fun x ↦ w.toFun x ^ 2) (openCubeSet T) →
          MemLp (fun x ↦ w.toFun x - cubeAverage T w.toFun) 2
            (volume.restrict (openCubeSet T)) →
          cubeAverage T w.toFun ^ 2 ≤
            Ctile *
                (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                sigma⁻¹ * cubeScaleFactor T ^ 2 *
              cubeAverage T
                (coefficientEnergyDensity (publicCoeffField T A) w.grad) := by
  obtain ⟨Ctile, hC, hcap⟩ := exists_boundaryTileResidualMeanCap d
  refine ⟨2 * Ctile, by positivity, ?_⟩
  intro M s hs L n hnL k omega y z hcontain hgood
  dsimp only
  intro w j0 hwzero hwint hwint2 hwmem
  have hraw := hcap M s hs L n hnL k omega y z hcontain hgood w
    (windowSummationCubeLowerHalf (originCube d k) j0)
    (1 / 2 : ℝ)
    (measurableSet_windowSummationCubeLowerHalf _ _)
    (windowSummationCubeLowerHalf_subset_openCubeSet _ _)
    (by norm_num)
    (half_mul_volume_openCubeSet_le_volume_windowSummationCubeLowerHalf _ _)
    hwzero hwint hwint2 hwmem
  convert hraw using 1
  all_goals ring

/-- The physical boundary-tile estimate when the domain lies above the met
face. -/
theorem exists_windowSummation_physicalBoundaryTileResidualMeanCap_lower
    (d : ℕ) [NeZero d] :
    ∃ Ctile : ℝ, 0 < Ctile ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L → ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        ∀ (V : Set (Vec d)), MeasurableSet V → ∀ (rho : H10Function V) (j0 : Fin d),
          (∀ x : Vec d, x j0 < 0 → x + y ∉ V) →
          let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
          volumeAverage (translateSet y (openCubeSet (originCube d k)))
              (zeroExtend V rho.toH1Function.toFun) ^ 2 ≤
            Ctile *
                (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                sigma⁻¹ * ((3 : ℝ) ^ k) ^ 2 *
              volumeAverage (translateSet y (openCubeSet (originCube d k)))
                (fun p => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
                  vecNormSq (zeroExtendGrad V rho.toH1Function.grad p)) := by
  obtain ⟨Ctile, hC, hcap⟩ :=
    exists_windowSummation_boundaryTileResidualMeanCap_lower d
  refine ⟨Ctile, hC, ?_⟩
  intro M s hs L n hnL k omega y z hcontain hgood V hV rho j0 houtside
  dsimp only
  set T : TriadicCube d := originCube d k with hT
  set A := aCutoffFamily M L (translatePotentialSample y omega) with hA
  obtain ⟨w, hwfun, hwgrad, hwzero, hwint, hwint2, hwmem⟩ :=
    exists_windowSummation_metFaceTile_zeroExtendedH1_lower
      hV rho y k j0 houtside
  have hraw := hcap M s hs L n hnL k omega y z hcontain hgood w j0
    hwzero hwint hwint2 hwmem
  have hmean : cubeAverage T w.toFun =
      volumeAverage (translateSet y (openCubeSet T))
        (zeroExtend V rho.toH1Function.toFun) := by
    rw [← cubeAverage_comp_addRight_eq_volumeAverage_translateSet T y
      (zeroExtend V rho.toH1Function.toFun)]
    exact congrArg (cubeAverage T) (funext hwfun)
  have hden : cubeAverage T
      (coefficientEnergyDensity (publicCoeffField T A) w.grad) =
      volumeAverage (translateSet y (openCubeSet T))
        (fun p => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (zeroExtendGrad V rho.toH1Function.grad p)) := by
    rw [← cubeAverage_comp_addRight_eq_volumeAverage_translateSet T y,
      ← volumeAverage_openCubeSet_eq_cubeAverage,
      ← volumeAverage_openCubeSet_eq_cubeAverage]
    refine volumeAverage_eq_of_ae_eq ?_
    filter_upwards [publicCoeffField_ae_eq_openCubeSet T A] with x hx
    simp only [coefficientEnergyDensity, hwgrad x, hx]
    simp [hA, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
      vecDot_smul_right, vecNormSq,
      Section6Covariance.aCutoff_translatePotentialSample]
  rw [hmean, hden] at hraw
  simpa only [hT, cubeScaleFactor_originCube] using hraw

omit [NeZero d] in
/-- The parent-mean transfer when the domain lies above the face. -/
theorem windowSummation_sq_averageOn_le_lowerFaceTileFamily_of_tileMeanCap
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {Mt : ℕ}
    (hcard : 0 < Fintype.card (FaceIndex d j0 Mt))
    {P : Set (Vec d)} {f e : Vec d → ℝ} {Kt : ℝ} (hKt : 0 ≤ Kt)
    (hsub : faceInnerSlab j0 a b L Mt ⊆ P)
    (hPtop : volume P ≠ ⊤) (hPpos : 0 < (volume P).toReal)
    (hfzero : ∀ x : Vec d, x j0 < a → f x = 0)
    (hfW : IntegrableOn f (faceDoubledSlab j0 a b L Mt))
    (hfP : IntegrableOn f P) (hf2P : IntegrableOn (fun x ↦ f x ^ 2) P)
    (heW : IntegrableOn e (faceDoubledSlab j0 a b L Mt))
    (henonneg : ∀ x, 0 ≤ e x)
    (hcap : ∀ k : FaceIndex d j0 Mt,
      averageOn (axisCube (faceTileCorner j0 a b L k) L) f ^ 2 ≤
        Kt * averageOn (axisCube (faceTileCorner j0 a b L k) L) e) :
    averageOn P f ^ 2 ≤
      2 * (4 : ℝ) ^ d * (Kt * averageOn (faceDoubledSlab j0 a b L Mt) e) +
        2 * ((volume P).toReal /
            (volume (faceInnerSlab j0 a b L Mt)).toReal) *
          normalizedL2On P (fun x ↦ f x - averageOn P f) ^ 2 := by
  classical
  obtain ⟨hSpos, _, _⟩ := faceSlab_volumeRatio_le j0 a b hL hcard
  have hWtop : volume (faceDoubledSlab j0 a b L Mt) ≠ ⊤ := by
    rw [volume_faceDoubledSlab j0 a b hL Mt]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hStop : volume (faceInnerSlab j0 a b L Mt) ≠ ⊤ :=
    ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left)
  have hSlower : (Fintype.card (FaceIndex d j0 Mt) : ℝ) * (L / 2) ^ d ≤
      (volume (faceInnerSlab j0 a b L Mt)).toReal := by
    have h := ENNReal.toReal_mono hStop
      (volume_faceInnerSlab_lower j0 a b hL Mt)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ L / 2),
      ENNReal.toReal_ofReal (by positivity)] at h
  exact sq_averageOn_le_tileFamily_of_tileMeanCap j0 a b hL hcard hKt
    (measurableSet_faceInnerSlab j0 a b L Mt) hsub hPtop hPpos hSpos hSlower
    (setIntegral_faceInnerSlab_eq_sum_faceTiles j0 a b hL hfzero hfW)
    hfP hf2P heW henonneg hcap

/-- The physical tile-family estimate at a lower face of the ambient domain. -/
theorem windowSummation_sq_averageOn_le_lowerFaceTileFamily_of_boundaryTileResidualMeanCap
    (d : ℕ) [NeZero d] :
    ∃ Cface : ℝ, 0 < Cface ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L → ∀ (kappa : ℤ) omega z,
      ∀ (j0 : Fin d) (aface : ℝ) (bcorner : Vec d) (Mt : ℕ),
        0 < Fintype.card (FaceIndex d j0 Mt) →
        (∀ k : FaceIndex d j0 Mt,
          translateSet
              (axisCubeCenter
                (faceTileCorner j0 aface bcorner ((3 : ℝ) ^ kappa) k)
                ((3 : ℝ) ^ kappa) - z)
              (cubeSet (originCube d kappa)) ⊆
            cubeSet (originCube d ((n : ℤ) + 2))) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      ∀ (V : Set (Vec d)), MeasurableSet V → ∀ rho : H10Function V,
        (∀ p : Vec d, p j0 < aface → p ∉ V) →
      ∀ P : Set (Vec d),
        faceInnerSlab j0 aface bcorner ((3 : ℝ) ^ kappa) Mt ⊆ P →
        volume P ≠ ⊤ → 0 < (volume P).toReal →
        let f := zeroExtend V rho.toH1Function.toFun
        let W := faceDoubledSlab j0 aface bcorner ((3 : ℝ) ^ kappa) Mt
        let energy := fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (zeroExtendGrad V rho.toH1Function.grad p)
        IntegrableOn f P → IntegrableOn (fun x ↦ f x ^ 2) P →
        IntegrableOn f W → IntegrableOn energy W →
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        averageOn P f ^ 2 ≤
          Cface * (3 : ℝ) ^
              (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) *
              sigma⁻¹ * ((3 : ℝ) ^ kappa) ^ 2 * averageOn W energy +
            2 * ((volume P).toReal /
                (volume (faceInnerSlab j0 aface bcorner
                  ((3 : ℝ) ^ kappa) Mt)).toReal) *
              normalizedL2On P (fun x ↦ f x - averageOn P f) ^ 2 := by
  obtain ⟨Ctile, hC, hcap⟩ :=
    exists_windowSummation_physicalBoundaryTileResidualMeanCap_lower d
  refine ⟨2 * (4 : ℝ) ^ d * Ctile, by positivity, ?_⟩
  intro M s hs L n hnL kappa omega z j0 aface bcorner Mt hcard hanchor hgood
    V hV rho hVbelow P hsubP hPtop hPpos
  dsimp only
  intro hfP hf2P hfW heW
  set Lside : ℝ := (3 : ℝ) ^ kappa with hLside
  have hL : 0 < Lside := by
    rw [hLside]
    exact zpow_pos (by norm_num) _
  set f : Vec d → ℝ := zeroExtend V rho.toH1Function.toFun with hf
  set energy : Vec d → ℝ := fun p ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
      vecNormSq (zeroExtendGrad V rho.toH1Function.grad p) with henergy
  set sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
    with hsig
  have hsigma : 0 < sigma := by
    rw [hsig]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    convert h using 1
  set Kt : ℝ := Ctile *
      (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) *
      sigma⁻¹ * Lside ^ 2 with hKt
  have hKtnonneg : 0 ≤ Kt := by
    rw [hKt]
    have h3 : (0 : ℝ) < (3 : ℝ) ^
      (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hinv : (0 : ℝ) < sigma⁻¹ := inv_pos.mpr hsigma
    positivity
  have hfzero : ∀ x : Vec d, x j0 < aface → f x = 0 := by
    intro x hx
    exact zeroExtend_of_notMem _ (hVbelow x hx)
  have henonneg : ∀ x, 0 ≤ energy x := fun x ↦
    mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
      (vecNormSq_nonneg _)
  have htilecap : ∀ k : FaceIndex d j0 Mt,
      averageOn (axisCube (faceTileCorner j0 aface bcorner Lside k) Lside) f ^ 2 ≤
        Kt * averageOn
          (axisCube (faceTileCorner j0 aface bcorner Lside k) Lside) energy := by
    intro k
    set y : Vec d :=
      axisCubeCenter (faceTileCorner j0 aface bcorner Lside k) Lside with hy
    have hynormal : y j0 = aface := by
      rw [hy, axisCubeCenter_apply, faceTileCorner_normal]
      ring
    have houtside : ∀ x : Vec d, x j0 < 0 → x + y ∉ V := by
      intro x hx
      refine hVbelow (x + y) ?_
      have : (x + y) j0 = x j0 + aface := by
        simp only [Pi.add_apply, hynormal]
      rw [this]
      linarith
    have hraw := hcap M s hs L n hnL kappa omega y z (hanchor k) hgood V hV rho
      j0 houtside
    dsimp only at hraw
    have hset : axisCube (faceTileCorner j0 aface bcorner Lside k) Lside =
        translateSet y (openCubeSet (originCube d kappa)) := by
      rw [hy, hLside]
      exact axisCube_eq_translateSet_openCubeSet_originCube _ kappa
    rw [averageOn, averageOn, hset, hf, henergy, hKt, hLside]
    exact hraw
  have hmain := windowSummation_sq_averageOn_le_lowerFaceTileFamily_of_tileMeanCap
    j0 aface bcorner hL hcard (P := P) (f := f) (e := energy) (Kt := Kt)
    hKtnonneg hsubP hPtop hPpos hfzero hfW hfP hf2P heW henonneg htilecap
  refine hmain.trans ?_
  have hEnonneg :
      0 ≤ averageOn (faceDoubledSlab j0 aface bcorner Lside Mt) energy := by
    rw [averageOn, volumeAverage]
    refine mul_nonneg (by positivity) (setIntegral_nonneg ?_ fun x _ ↦ henonneg x)
    exact MeasurableSet.iUnion fun k ↦ measurableSet_axisCube _ _
  have hrewrite :
      2 * (4 : ℝ) ^ d *
        (Kt * averageOn (faceDoubledSlab j0 aface bcorner Lside Mt) energy) =
      (2 * (4 : ℝ) ^ d * Ctile) *
        (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) *
        sigma⁻¹ * Lside ^ 2 *
        averageOn (faceDoubledSlab j0 aface bcorner Lside Mt) energy := by
    rw [hKt]
    ring
  rw [hrewrite]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
