module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorScaleGeometry

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- One non-boundary depth-two cell in the final manuscript-scale square
budget. -/
theorem exists_interiorCellEnergy_le_manuscriptPrices (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        let k : ℤ := (n : ℤ) - 2
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          K *
            (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U
                  (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
  obtain ⟨C, B, hC, hB, hraw⟩ := exists_interiorCellEnergy_le_windowPrices d
  let P : ℝ := (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ)
  let Kparent : ℝ := 81 * B * (9 : ℝ) ^ d
  let Ksource : ℝ := B *
    ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 * (9 : ℝ) ^ d)
  let K : ℝ := (81 : ℝ) ^ d * P * max Kparent Ksource
  have hmaxC : 0 < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hKparent : 0 < Kparent := by
    dsimp [Kparent]
    positivity
  have hKsource : 0 < Ksource := by
    dsimp [Ksource]
    exact mul_pos hB (mul_pos
      (mul_pos (by positivity) (sq_pos_of_pos (caccioppoliExactDatumConstant_pos d)))
      (by positivity))
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hmL hnm z x q omega hz hx hq hpatch hgood u h g
    hdir hg hh
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hbase := hraw M sOrder hs L m n hmL hnm z x q omega hz hx hq hpatch hgood
    u h g hdir hg hh
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hPsub : translatedCube d k c ⊆ U := by
    exact translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k, U] using hq) hkm
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hratio := volume_ratio_truncatedCube_translated_predTwo_le
    (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (x := x) (c := c)
    hxDomain (by omega)
  have hratio0 : 0 ≤ (volume U).toReal /
      (volume (translatedCube d k c)).toReal := by positivity
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hX : 0 ≤ normalizedL2On U
      (fun y => u.toFun y - averageOn U u.toFun) :=
    Real.sqrt_nonneg _
  have hG : 0 ≤ (fractionalSeminormOn U sOrder.1 g).toReal := ENNReal.toReal_nonneg
  have hparent := projected_parent_factor_le
    (d := d) (n := n) hB.le hsigma.le hratio
      (X := normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun))
  have hsource := projected_source_factor_le
    (d := d) (n := n) sOrder.2.1 (caccioppoliExactDatumConstant_pos d).le
      hratio0 hratio hG
  have hfirst :
      B * sigma * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 ≤
        Kparent *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
            normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) := by
    dsimp [U] at hparent
    dsimp [U, k, Kparent]
    simpa only [mul_assoc] using hparent
  have hsecond :
      Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
          (caccioppoliExactDatumConstant d *
            cubeBesovScaleWeight (-sOrder.1) Q *
            (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 ≤
        Ksource *
          (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
    rw [show cubeBesovScaleWeight (-sOrder.1) Q =
        Real.rpow (3 : ℝ)
          (sOrder.1 * (((n : ℤ) - 2 : ℤ) : ℝ)) by
      simpa [Q, k] using cubeBesovScaleWeight_neg_origin_predTwo
        (d := d) sOrder.1 n]
    have hm := mul_le_mul_of_nonneg_left hsource
      (mul_nonneg hB.le (inv_nonneg.mpr hsigma.le))
    calc
      _ = (B * sigma⁻¹) *
          (Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            (caccioppoliExactDatumConstant d *
              Real.rpow (3 : ℝ) (sOrder.1 * (((n : ℤ) - 2 : ℤ) : ℝ)) *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2) := by ring
      _ ≤ (B * sigma⁻¹) *
          ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 *
            (9 : ℝ) ^ d * Real.rpow sOrder.1 (-12 : ℝ) *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := hm
      _ = Ksource *
          (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
        dsimp [Ksource]
        ring
  have hsum :
      B * sigma * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
          (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-sOrder.1) Q *
            (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 ≤
        max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
    have hA0 : 0 ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 := by
      positivity
    have hD0 : 0 ≤ Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg sOrder.2.1.le _)
            (inv_nonneg.mpr hsigma.le))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    calc
      _ ≤ Kparent *
            (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) +
          Ksource *
            (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) :=
        add_le_add hfirst hsecond
      _ ≤ max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
        have h1 := mul_le_mul_of_nonneg_right (le_max_left Kparent Ksource) hA0
        have h2 := mul_le_mul_of_nonneg_right (le_max_right Kparent Ksource) hD0
        linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hP.le
  have hout := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  refine hbase.trans ?_
  calc
    _ ≤ (81 : ℝ) ^ d *
        (P * (max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) := by
      simpa only [k, Q, U, sigma, P] using hout
    _ = K *
        (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
          Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
      dsimp [K]
      ring

private theorem interiorPublicIsForcedEquation_neg_of_divForm
    {Q : TriadicCube d} {a : CoeffFamily d}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn
      (fun x => ((a.coeffOn Q).toCoeffField x) 0 0) (openCubeSet Q) u g)
    (hscalar : ∀ x, (a.coeffOn Q).toCoeffField x =
      scalarMatrix (d := d) (((a.coeffOn Q).toCoeffField x) 0 0)) :
    IsForcedEquation Q a u (fun x => -g x) := by
  intro phi
  have hflux : ∀ x,
      matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x) =
        (((a.coeffOn Q).toCoeffField x) 0 0) • u.grad x := by
    intro x
    have ha := congrArg (fun A => matVecMul A (u.grad x)) (hscalar x)
    exact ha.trans (matVecMul_scalarMatrix _ _)
  have hneg : (fun x => vecDot (-g x) (phi.toH1Function.grad x)) =
      fun x => -vecDot (g x) (phi.toH1Function.grad x) := by
    funext x
    exact vecDot_neg_left _ _
  simp only [Ch02.cubeDomain_coe]
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot ((((a.coeffOn Q).toCoeffField x) 0 0) • u.grad x)
          (phi.toH1Function.grad x) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          exact congrArg (fun z => vecDot z (phi.toH1Function.grad x)) (hflux x))
    _ = -∫ x in openCubeSet Q,
        vecDot (g x) (phi.toH1Function.grad x) ∂volume := h phi
    _ = ∫ x in openCubeSet Q,
        vecDot ((fun x => -g x) x) (phi.toH1Function.grad x) ∂volume := by
      rw [hneg, integral_neg]

private noncomputable def interiorWspFieldOfFull
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    CubeEuclideanWspField Q s FiniteLpExponent.two where
  toField := f
  euclideanMemLp := hf.1
  euclideanMemWsp := hf.2

omit [NeZero d] in
@[simp] private theorem interiorWspFieldOfFull_toField
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    (interiorWspFieldOfFull hf).toField = f := rfl

private theorem forceBesovRegularity_neg_of_interiorFull
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    ForceBesovRegularity Q s.1 (fun x => -f x) := by
  let F := negCubeEuclideanWspField (interiorWspFieldOfFull hf)
  have hsob := cubeEuclideanWspField_forceSobolevRegularity s F
  simpa [F] using hsob.toForceBesovRegularity s.2.1 s.2.2.le

private theorem exists_projectedInteriorCellEnergy_readout_weak
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
        (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d) (c0 : ℝ),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        sOrder.1 ≤ 1 / 4 → k ≤ (m : ℤ) → q ∈ cube d (m : ℤ) →
        openCubeAtScale
            (q - Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) (k - 1) ⊆
          openCubeSet (originCube d k) →
        ∃ g0 : Vec d → Vec d,
          ∃ u0 : H1Function (openCubeSet (originCube d k)),
            (∀ x, g0 x = g (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d k) sOrder
              FiniteLpExponent.two (fun x => g (x +
                Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            (∀ x, u0.toFun x = u.toFun (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            IsForcedEquation (originCube d k)
                (aCutoffFamily M L
                  (translatePotentialSample
                    (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                u0 (fun x => -g0 x) ∧
            ForceBesovRegularity (originCube d k) sOrder.1 (fun x => -g0 x) ∧
            normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
                (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                  vecNormSq (u.grad x)) ≤
              (81 : ℝ) ^ d *
                (caccioppoliWithRHSPrefactor C (originCube d k)
                    (aCutoffFamily M L
                      (translatePotentialSample
                        (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                    (1 / 2) (sOrder.1 / 2) *
                  (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                      (aCutoffFamily M L
                        (translatePotentialSample
                          (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)) *
                    Real.rpow (3 : ℝ) (-2 * (((originCube d k).scale : ℤ) : ℝ)) *
                    normalizedL2SqOnSet (openCubeSet (originCube d k))
                      (fun y => u0.toFun y - c0) +
                  Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                    Real.rpow
                      (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                        (aCutoffFamily M L
                          (translatePotentialSample
                            (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)))
                      (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo
                      (originCube d k) sOrder.1 (fun x => -g0 x) ^ 2)) := by
  obtain ⟨C, hC, hinterior⟩ := exists_interior_caccioppoli_quarter_subConst d
  refine ⟨C, hC, ?_⟩
  intro M L omega m k q sOrder u g c0 hweak hg hs4 hkm hq hpatch
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  have hP : translateSet c (openCubeSet Q) = translatedCube d k c := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  have hsub : translateSet c (openCubeSet Q) ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    rw [hP]
    exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkm
  have hPopen : IsOpen (translateSet c (openCubeSet Q)) :=
    ((isOpenBoundedConvexDomain_openCubeSet Q).translateSet c).isOpen
  let uP : H1Function (translateSet c (openCubeSet Q)) := u.restrict hPopen hsub
  let u0 : H1Function (openCubeSet Q) := H1Function.untranslate c uP
  let g0 : Vec d → Vec d := fun x => g (x + c)
  have hweak' : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (openCubeSet (originCube d (m : ℤ))) u g := by
    simpa [cube] using hweak
  have heqP : IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (translateSet c (openCubeSet Q)) uP g :=
    isDivFormWeakSolutionOn_restrict
      (isOpenBoundedConvexDomain_openCubeSet (originCube d (m : ℤ))).isOpen
      hPopen hsub hweak'
  have heq0 : IsDivFormWeakSolutionOn
      (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x + c))
      (openCubeSet Q) u0 g0 :=
    isDivFormWeakSolutionOn_untranslate c heqP
  have hcoeff : ∀ x, (A.coeffOn Q).toCoeffField x =
      scalarMatrix (d := d) (((A.coeffOn Q).toCoeffField x) 0 0) := by
    intro x
    simp [A, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField]
  have hfield : (fun x => ((A.coeffOn Q).toCoeffField x) 0 0) =
      fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x + c) := by
    funext x
    simp [A, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Section6Covariance.aCutoff_translatePotentialSample]
  have heqPublic : IsForcedEquation Q A u0 (fun x => -g0 x) := by
    apply interiorPublicIsForcedEquation_neg_of_divForm (a := A) (g := g0)
    · rw [hfield]
      exact heq0
    · exact hcoeff
  have hgLocal : Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
      FiniteLpExponent.two (fun x => g (x + c)) :=
    memCubeEuclideanFullWsp_translate_of_subset Q
      (originCube d (m : ℤ)) c sOrder FiniteLpExponent.two g hsub hg
  have hgReg : ForceBesovRegularity Q sOrder.1 (fun x => -g0 x) := by
    exact forceBesovRegularity_neg_of_interiorFull hgLocal
  have hbound := hinterior u0 c0 heqPublic
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by linarith only [sOrder.2.1] : 0 < sOrder.1 / 2)
    (by linarith only [hs4] : sOrder.1 / 2 ≤ 1 / 4)
    (by linarith only [sOrder.2.2] : (1 / 2 : ℝ) + sOrder.1 / 2 < 1)
    hpatch (by simpa [show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hgReg)
  have hu0val : ∀ x, u0.toFun x = u.toFun (x + c) := by
    intro x
    rw [H1Function.untranslate_toFun]
    rfl
  have hu0grad : ∀ x, u0.grad x = u.grad (x + c) := by
    intro x
    rw [H1Function.untranslate_grad]
    rfl
  have hread := normalizedCutoffEnergy_truncatedCube_le_projectedCore
    M L omega hq hkm u u0 hu0grad
  have hfactor : (0 : ℝ) ≤ (81 : ℝ) ^ d := by positivity
  have hfinal := hread.trans (mul_le_mul_of_nonneg_left hbound hfactor)
  refine ⟨g0, u0, ?_, hgLocal, hu0val, heqPublic, hgReg, ?_⟩
  · intro x
    rfl
  · simpa [Q, A, c, show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hfinal

private theorem exists_interiorCellEnergy_le_windowPrices_weak
    (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let k : ℤ := (n : ℤ) - 2
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          (81 : ℝ) ^ d *
            ((4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) *
              (B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
                  ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  normalizedL2On U
                    (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
                Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                  (B * sigma⁻¹) *
                  (caccioppoliExactDatumConstant d *
                    cubeBesovScaleWeight (-sOrder.1) Q *
                    (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                      (Real.sqrt ((volume U).toReal /
                          (volume (translatedCube d k c)).toReal) *
                        (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2)) := by
  obtain ⟨C, hC, hinterior⟩ := exists_projectedInteriorCellEnergy_readout_weak d
  obtain ⟨_E, B, _hE, hB, hcaps⟩ :=
    exists_localBoundaryEllipticityCaps_nextWindow d
  refine ⟨C, B, hC, hB, ?_⟩
  intro M sOrder hs L m n hmL hnm z x q omega hz hx hq hpatchPhysical hgood
    u g hweak hg
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  let U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hnL : n + 2 ≤ L := by omega
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hpatch : openCubeAtScale (q - c) (k - 1) ⊆ openCubeSet Q := by
    have hbase := openCubeAtScale_wellPlaced_pullback_subset_originCube
      (d := d) (m := (m : ℤ)) (k := k) (q := q) hkm
      (by simpa only [k, sub_sub, sub_self, sub_zero] using! hpatchPhysical)
    simpa only [c, Q] using hbase
  have hPsub : translatedCube d k c ⊆ U := by
    exact translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k, U] using hq) hkm
  have hcU : c ∈ U := hPsub (by
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    simpa using Section6ExcessDecay.zero_mem_cube d k)
  have hUsub : U ⊆ openCubeSet (originCube d (m : ℤ)) := by
    intro y hy
    exact hy.2
  have hUpos : 0 < (volume U).toReal :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos x hxDomain (by omega)
  have hPpos : 0 < (volume (translatedCube d k c)).toReal := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hU0 : volume U ≠ 0 := (ENNReal.toReal_ne_zero.mp hUpos.ne').1
  have hUtop : volume U ≠ ⊤ :=
    (Section6ExcessDecay.volume_truncatedCube_lt_top d (m : ℤ) (n : ℤ) x).ne
  have hPpair' : volume (translateSet c (openCubeSet Q)) ≠ 0 ∧
      volume (translateSet c (openCubeSet Q)) ≠ ⊤ := by
    rw [volume_translateSet_eq]
    constructor
    · intro hzero
      have hz := congrArg ENNReal.toReal hzero
      rw [volume_openCubeSet_toReal] at hz
      exact (cubeVolume_pos Q).ne' hz
    · exact (volume_openCubeSet_lt_top Q).ne
  have hgUfin : fractionalSeminormOn U sOrder.1 g ≠ ⊤ := by
    have hfrac : MemFractionalOn (cube d (m : ℤ)) sOrder.1 g := by
      change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ)))
        sOrder.1 g ≠ ⊤
      rw [fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable _ _ _ hg.2.aestronglyMeasurable]
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hg.2.eSeminorm_lt_top.ne
    exact memFractionalOn_truncatedCube_of_domain hxDomain (by omega) hfrac
  obtain ⟨g0, u0, hg0, hgLocal, hu0, _heq, _hgReg, hcell⟩ :=
    hinterior M L omega m k q sOrder u g (averageOn U u.toFun)
      hweak hg hs.2 hkm (by exact hq.2) hpatch
  have hparent := normalizedL2SqOnSet_projected_le_window u u0
    (averageOn U u.toFun) hu0 hPsub hUsub hUpos hPpos
  have hsource := projectedForceSeminorm_le_window Q c U sOrder g g0
    (by simpa [Q, c] using hgLocal) hg0 (by
      rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet] at hPsub
      exact hPsub) hPpair'.1 hPpair'.2 hU0 hUtop hgUfin
  have hvolP : volume (translateSet c (openCubeSet Q)) =
      volume (translatedCube d k c) := by
    congr 1
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  rw [hvolP] at hsource
  have hcap := hcaps M sOrder.1 hs L m n hnL z x c omega hx hcU hgood
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hhalf := interiorHalfEllipticityCaps_of_sixth Q A hs0 hsigma
    hcap.2.2.2.1 hcap.2.2.1
  have hpref := caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Q) (A := A) hC hs0 hs.2 hhalf.2.2
  have hlam : Ch02.lambdaS Q (sOrder.1 / 2) A ≤ B * sigma := hhalf.2.1
  have hlamInv : Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
      B * sigma⁻¹ := by
    calc
      Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) =
          (Ch02.lambdaS Q (sOrder.1 / 2) A)⁻¹ := Real.rpow_neg_one _
      _ ≤ B * sigma⁻¹ := hhalf.1
  have hinner :
      Ch02.lambdaS Q (sOrder.1 / 2) A *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 ≤
        B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
              ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
            (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-sOrder.1) Q *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 := by
    have hscale : 0 ≤ Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hparent0 : 0 ≤ normalizedL2SqOnSet (openCubeSet Q)
        (fun y => u0.toFun y - averageOn U u.toFun) :=
      normalizedL2SqOnSet_nonneg (openCubeSet Q) _ (measurableSet_openCubeSet Q)
    have hcoef : Ch02.lambdaS Q (sOrder.1 / 2) A *
        Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) ≤
        B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hlam hscale
    have hfirst := mul_le_mul hcoef hparent hparent0
      (mul_nonneg (mul_nonneg hB.le hsigma.le) hscale)
    have hsource0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
        (fun x => -g0 x) :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (by simpa using _hgReg)
    have hsecondSq := pow_le_pow_left₀ hsource0 hsource 2
    let Sg : ℝ := caccioppoliExactDatumConstant d *
      cubeBesovScaleWeight (-sOrder.1) Q *
        (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal /
              (volume (translatedCube d k c)).toReal) *
            (fractionalSeminormOn U sOrder.1 g).toReal))
    have hcoefSecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) :=
      mul_le_mul_of_nonneg_left hlamInv
        (Real.rpow_nonneg (by linarith only [hs0] : 0 ≤ sOrder.1 / 2) _)
    have hcoefSecond0 : 0 ≤ Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        (B * sigma⁻¹) :=
      mul_nonneg (Real.rpow_nonneg (by linarith only [hs0] : 0 ≤ sOrder.1 / 2) _)
        (mul_nonneg hB.le (inv_nonneg.mpr hsigma.le))
    have hsecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
          Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
            (fun x => -g0 x) ^ 2 ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) * Sg ^ 2 :=
      mul_le_mul hcoefSecond (by simpa only [Sg] using hsecondSq)
        (sq_nonneg _) hcoefSecond0
    exact add_le_add (by simpa [mul_assoc] using hfirst)
      (by simpa only [Sg] using hsecond)
  have hrawInner0 : 0 ≤
      Ch02.lambdaS Q (sOrder.1 / 2) A *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 := by
    have hlam0 : 0 ≤ Ch02.lambdaS Q (sOrder.1 / 2) A := by
      rw [Ch02.lambdaS]
      exact Ch02.lambdaSq_finite_nonneg Q A (by linarith only [hs0]) (by norm_num)
    have hparent0 := normalizedL2SqOnSet_nonneg (openCubeSet Q)
      (fun y => u0.toFun y - averageOn U u.toFun) (measurableSet_openCubeSet Q)
    exact add_nonneg
      (mul_nonneg (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _)) hparent0)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by linarith only [hs0]) _)
          (Real.rpow_nonneg hlam0 _)) (sq_nonneg _))
  have hprefBound0 : 0 ≤
      (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) := by positivity
  have hmul := mul_le_mul hpref hinner hrawInner0 hprefBound0
  have hstep := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  have hfinal := hcell.trans (by simpa only [Q, A, c] using hstep)
  simpa only [Q, A, c, U, sigma] using hfinal

/-- Datum-free companion of `exists_interiorCellEnergy_le_manuscriptPrices`.
The interior estimate consumes only the weak equation and force regularity. -/
theorem exists_interiorCellEnergy_le_manuscriptPrices_weak
    (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let k : ℤ := (n : ℤ) - 2
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          K *
            (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U
                  (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
  obtain ⟨C, B, hC, hB, hraw⟩ := exists_interiorCellEnergy_le_windowPrices_weak d
  let P : ℝ := (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ)
  let Kparent : ℝ := 81 * B * (9 : ℝ) ^ d
  let Ksource : ℝ := B *
    ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 * (9 : ℝ) ^ d)
  let K : ℝ := (81 : ℝ) ^ d * P * max Kparent Ksource
  have hmaxC : 0 < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hKparent : 0 < Kparent := by
    dsimp [Kparent]
    positivity
  have hKsource : 0 < Ksource := by
    dsimp [Ksource]
    exact mul_pos hB (mul_pos
      (mul_pos (by positivity) (sq_pos_of_pos (caccioppoliExactDatumConstant_pos d)))
      (by positivity))
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hmL hnm z x q omega hz hx hq hpatch hgood u g
    hweak hg
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hbase := hraw M sOrder hs L m n hmL hnm z x q omega hz hx hq hpatch hgood
    u g hweak hg
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hPsub : translatedCube d k c ⊆ U :=
    translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k, U] using hq) hkm
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hratio := volume_ratio_truncatedCube_translated_predTwo_le
    (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (x := x) (c := c)
    hxDomain (by omega)
  have hratio0 : 0 ≤ (volume U).toReal /
      (volume (translatedCube d k c)).toReal := by positivity
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hX : 0 ≤ normalizedL2On U
      (fun y => u.toFun y - averageOn U u.toFun) := Real.sqrt_nonneg _
  have hG : 0 ≤ (fractionalSeminormOn U sOrder.1 g).toReal := ENNReal.toReal_nonneg
  have hparent := projected_parent_factor_le
    (d := d) (n := n) hB.le hsigma.le hratio
      (X := normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun))
  have hsource := projected_source_factor_le
    (d := d) (n := n) sOrder.2.1 (caccioppoliExactDatumConstant_pos d).le
      hratio0 hratio hG
  have hfirst :
      B * sigma * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 ≤
        Kparent *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
            normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) := by
    dsimp [U] at hparent
    dsimp [U, k, Kparent]
    simpa only [mul_assoc] using hparent
  have hsecond :
      Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
          (caccioppoliExactDatumConstant d *
            cubeBesovScaleWeight (-sOrder.1) Q *
            (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 ≤
        Ksource *
          (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
    rw [show cubeBesovScaleWeight (-sOrder.1) Q =
        Real.rpow (3 : ℝ)
          (sOrder.1 * (((n : ℤ) - 2 : ℤ) : ℝ)) by
      simpa [Q, k] using cubeBesovScaleWeight_neg_origin_predTwo
        (d := d) sOrder.1 n]
    have hm := mul_le_mul_of_nonneg_left hsource
      (mul_nonneg hB.le (inv_nonneg.mpr hsigma.le))
    calc
      _ = (B * sigma⁻¹) *
          (Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            (caccioppoliExactDatumConstant d *
              Real.rpow (3 : ℝ) (sOrder.1 * (((n : ℤ) - 2 : ℤ) : ℝ)) *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2) := by ring
      _ ≤ (B * sigma⁻¹) *
          ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 *
            (9 : ℝ) ^ d * Real.rpow sOrder.1 (-12 : ℝ) *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := hm
      _ = Ksource *
          (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
        dsimp [Ksource]
        ring
  have hsum :
      B * sigma * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
          (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-sOrder.1) Q *
            (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 ≤
        max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
    have hA0 : 0 ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 := by
      positivity
    have hD0 : 0 ≤ Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg sOrder.2.1.le _)
            (inv_nonneg.mpr hsigma.le))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    calc
      _ ≤ Kparent *
            (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) +
          Ksource *
            (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) :=
        add_le_add hfirst hsecond
      _ ≤ max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
        have h1 := mul_le_mul_of_nonneg_right (le_max_left Kparent Ksource) hA0
        have h2 := mul_le_mul_of_nonneg_right (le_max_right Kparent Ksource) hD0
        linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hP.le
  have hout := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  refine hbase.trans ?_
  calc
    _ ≤ (81 : ℝ) ^ d *
        (P * (max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) := by
      simpa only [k, Q, U, sigma, P] using hout
    _ = K *
        (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
          Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
      dsimp [K]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
