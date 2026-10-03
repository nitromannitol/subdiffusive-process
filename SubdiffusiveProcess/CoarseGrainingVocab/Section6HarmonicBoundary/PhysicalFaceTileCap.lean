module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.MetFaceTileDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellCover
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.FaceTileMeanTransfer

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The boundary tile price, physical frame.**

For a tile realised as `y + 𝔠_k` whose translate lies in the good-event anchor
`z + 𝔠_{n+2}`, and for the zero extension of an `H¹₀(V)` datum with `V` on the
near side of the coordinate hyperplane through the tile centre, the square of
the tile mean is priced by the physical `aCutoff`-weighted gradient energy on
the same tile, with the coarse normaliser `σ⁻¹`, the tile scale factor squared
and the single loss `3^{(s/4)(n+2−k)}`.

No pointwise ellipticity ratio occurs. -/
theorem exists_physicalBoundaryTileResidualMeanCap (d : ℕ) [NeZero d] :
    ∃ Ctile : ℝ, 0 < Ctile ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L → ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        ∀ (V : Set (Vec d)), MeasurableSet V → ∀ (rho : H10Function V) (j0 : Fin d),
          (∀ x : Vec d, 0 < x j0 → x + y ∉ V) →
          let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
          volumeAverage (translateSet y (openCubeSet (originCube d k)))
              (zeroExtend V rho.toH1Function.toFun) ^ 2 ≤
            Ctile *
                (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                sigma⁻¹ * ((3 : ℝ) ^ k) ^ 2 *
              volumeAverage (translateSet y (openCubeSet (originCube d k)))
                (fun p => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
                  vecNormSq (zeroExtendGrad V rho.toH1Function.grad p)) := by
  obtain ⟨Ctile, hC, hcap⟩ := exists_boundaryTileResidualMeanCap_half d
  refine ⟨Ctile, hC, ?_⟩
  intro M s hs L n hnL k omega y z hcontain hgood V hV rho j0 houtside
  dsimp only
  set T : TriadicCube d := originCube d k with hT
  set A := aCutoffFamily M L (translatePotentialSample y omega) with hA
  obtain ⟨w, hwfun, hwgrad, hwzero, hwint, hwint2, hwmem⟩ :=
    exists_metFaceTile_zeroExtendedH1 hV rho y k j0 houtside
  have hraw := hcap M s hs L n hnL k omega y z hcontain hgood w j0
    hwzero hwint hwint2 hwmem
  -- the mean, in the physical frame
  have hmean : cubeAverage T w.toFun =
      volumeAverage (translateSet y (openCubeSet T))
        (zeroExtend V rho.toH1Function.toFun) := by
    rw [← cubeAverage_comp_addRight_eq_volumeAverage_translateSet T y
      (zeroExtend V rho.toH1Function.toFun)]
    exact congrArg (cubeAverage T) (funext hwfun)
  -- the energy density, in the physical frame
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


/-! ## The tile family in the physical frame -/

omit [NeZero d] in
/-- An `axisCube` of triadic side is a translate of the origin cube. -/
theorem axisCube_eq_translateSet_openCubeSet_originCube
    (z : Vec d) (kappa : ℤ) :
    axisCube z ((3 : ℝ) ^ kappa) =
      translateSet (axisCubeCenter z ((3 : ℝ) ^ kappa))
        (openCubeSet (originCube d kappa)) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff]
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo,
    Pi.sub_apply, axisCubeCenter_apply]
  constructor
  · intro hx i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith
  · intro hx i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith

/-- **§13.6 item 3, assembled.**

The parent mean of the zero-extended residual on a projected parent `P` whose
met face is the coordinate hyperplane `{x_{j0} = a}` is bounded by the
`aCutoff`-weighted energy on the tiled doubled slab, with the tile scale factor
squared and the single good-event loss `3^{(s/4)(n+2−κ)}`, plus the parent
oscillation amplified by the slab volume ratio.

The tile depth is free: with `L = 3^κ` and the parent of side `3^{n-2}`, the
energy leg carries `3^{(s/4)(n+2-κ)} · 3^{2κ}` — a net `3^{-(2 - s/4) j}` gain
in the depth `j = (n-2) - κ` — while the oscillation leg carries
`|P| / |S| ≍ 3^{j}`.  No pointwise `aCutoff / σ` ratio occurs anywhere. -/
theorem sq_averageOn_le_tileFamily_of_boundaryTileResidualMeanCap
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
        (∀ p : Vec d, aface < p j0 → p ∉ V) →
      ∀ P : Set (Vec d),
        upperFaceInnerSlab j0 aface bcorner ((3 : ℝ) ^ kappa) Mt ⊆ P →
        volume P ≠ ⊤ → 0 < (volume P).toReal →
        let f := zeroExtend V rho.toH1Function.toFun
        let W := faceDoubledSlab j0 aface bcorner ((3 : ℝ) ^ kappa) Mt
        let energy := fun p => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (zeroExtendGrad V rho.toH1Function.grad p)
        IntegrableOn f P → IntegrableOn (fun x => f x ^ 2) P →
        IntegrableOn f W → IntegrableOn energy W →
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        averageOn P f ^ 2 ≤
          Cface * (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) *
              sigma⁻¹ * ((3 : ℝ) ^ kappa) ^ 2 * averageOn W energy +
            2 * ((volume P).toReal /
                (volume (upperFaceInnerSlab j0 aface bcorner
                  ((3 : ℝ) ^ kappa) Mt)).toReal) *
              normalizedL2On P (fun x => f x - averageOn P f) ^ 2 := by
  obtain ⟨Ctile, hC, hcap⟩ := exists_physicalBoundaryTileResidualMeanCap d
  refine ⟨2 * (4 : ℝ) ^ d * Ctile, by positivity, ?_⟩
  intro M s hs L n hnL kappa omega z j0 aface bcorner Mt hcard hanchor hgood
    V hV rho hVabove P hsubP hPtop hPpos
  dsimp only
  intro hfP hf2P hfW heW
  set Lside : ℝ := (3 : ℝ) ^ kappa with hLside
  have hL : 0 < Lside := by rw [hLside]; exact zpow_pos (by norm_num) _
  set f : Vec d → ℝ := zeroExtend V rho.toH1Function.toFun with hf
  set energy : Vec d → ℝ := fun p =>
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
      vecNormSq (zeroExtendGrad V rho.toH1Function.grad p) with henergy
  set sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
    with hsig
  have hsigma : 0 < sigma := by
    rw [hsig]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using! h
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
  have hfzero : ∀ x : Vec d, aface < x j0 → f x = 0 := by
    intro x hx
    exact zeroExtend_of_notMem _ (hVabove x hx)
  have henonneg : ∀ x, 0 ≤ energy x := fun x =>
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
    have houtside : ∀ x : Vec d, 0 < x j0 → x + y ∉ V := by
      intro x hx
      refine hVabove (x + y) ?_
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
  have hmain := sq_averageOn_le_upperFaceTileFamily_of_tileMeanCap
    j0 aface bcorner hL hcard (P := P) (f := f) (e := energy) (Kt := Kt)
    hKtnonneg hsubP hPtop hPpos hfzero hfW hfP hf2P heW henonneg htilecap
  refine hmain.trans ?_
  have hEnonneg : 0 ≤ averageOn (faceDoubledSlab j0 aface bcorner Lside Mt) energy := by
    rw [averageOn, volumeAverage]
    refine mul_nonneg (by positivity) (setIntegral_nonneg ?_ fun x _ => henonneg x)
    exact MeasurableSet.iUnion fun k => measurableSet_axisCube _ _
  have hcoeff : 2 * (4 : ℝ) ^ d * Kt =
      2 * (4 : ℝ) ^ d * Ctile *
        (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) *
        sigma⁻¹ * Lside ^ 2 := by
    rw [hKt]; ring
  have : 2 * (4 : ℝ) ^ d *
      (Kt * averageOn (faceDoubledSlab j0 aface bcorner Lside Mt) energy) =
      (2 * (4 : ℝ) ^ d * Ctile) *
        (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) *
        sigma⁻¹ * Lside ^ 2 *
        averageOn (faceDoubledSlab j0 aface bcorner Lside Mt) energy := by
    rw [hKt]; ring
  rw [this]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
