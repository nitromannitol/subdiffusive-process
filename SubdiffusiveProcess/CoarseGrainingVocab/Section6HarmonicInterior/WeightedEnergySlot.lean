module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.CoverEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergyReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedComponentAssembly

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

/-- **Frame change for the coefficient energy.**  The recentered cube average of
the coefficient energy density of `u0` equals the physical normalized average of
the scalar cutoff energy of `u` on the translated cube. -/
theorem cubeAverage_coefficientEnergyDensity_aCutoffFamily_eq_translatedCube
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (k : ℤ) (y : Vec d)
    (u0 : H1Function (openCubeSet (originCube d k)))
    (gradU : Vec d → Vec d)
    (hu0 : ∀ p, u0.grad p = gradU (p + y)) :
    cubeAverage (originCube d k)
        (coefficientEnergyDensity
          (((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
            (originCube d k)).toCoeffField) u0.grad) =
      normalizedSetAverage (translatedCube d k y)
        (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (gradU p)) := by
  have hset : translateSet y (openCubeSet (originCube d k)) =
      translatedCube d k y := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  rw [← volumeAverage_openCubeSet_eq_cubeAverage,
    ← localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity
      (openCubeSet (originCube d k))
      ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
        (originCube d k)) u0,
    localizedCoeffEnergyValue_aCutoffFamily_eq_translate M L omega
      (originCube d k) y (openCubeSet (originCube d k)) u0 gradU hu0,
    hset]

variable {d : ℕ} [NeZero d]



theorem exists_interiorWeightedEnergy_le_manuscriptPrices_weak
    (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
      ∀ (u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2)))),
        (∀ p, u0.grad p = u.grad (p + y)) →
      ∀ (s1 smid : FractionalOrder), s1.1 < smid.1 →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        Ch03.ABK26.weightedLocalSymmetricEnergyLp (originCube d ((n : ℤ) - 2))
            ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
            ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
              (originCube d ((n : ℤ) - 2))) u0 s1 smid FiniteLpExponent.two ≤
          ENNReal.ofReal
            (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
              Real.sqrt (K *
                (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                    normalizedL2On U
                      (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
                  Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                    Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                    (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) := by
  obtain ⟨K, hK, hcover⟩ := exists_interiorCoverEnergy_le_manuscriptPrices_weak d
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hmL hnm z x y omega hz hx hD hnot hgood u g hweak hg
    u0 hu0 s1 smid hgap
  dsimp only
  have henergy := hcover M sOrder hs L m n hmL hnm z x y omega hz hx hD hnot
    hgood u g hweak hg
  simp only at henergy
  have hframe := cubeAverage_coefficientEnergyDensity_aCutoffFamily_eq_translatedCube
    M L omega ((n : ℤ) - 2) y u0 u.grad hu0
  have hroot := weightedLocalSymmetricEnergyLp_two_le_rootEnergyReadout
    (originCube d ((n : ℤ) - 2))
    ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
      (originCube d ((n : ℤ) - 2))) u0 s1 smid (by linarith)
  refine hroot.trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_
    (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
  rw [hframe]
  exact Real.sqrt_le_sqrt henergy

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
