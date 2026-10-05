module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCoverAssembly

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **Datum-free interior cover energy display.**  Companion of
`Section6HarmonicApproximation.exists_interiorCoverEnergy_le_manuscriptPrices`
consuming only the weak equation and the force regularity. -/
theorem exists_interiorCoverEnergy_le_manuscriptPrices_weak (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let D := translatedCube d ((n : ℤ) - 2) y
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage D (fun q ↦
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega q * vecNormSq (u.grad q)) ≤
          K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U
                  (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
  obtain ⟨K, hK, hcell⟩ := exists_interiorCellEnergy_le_manuscriptPrices_weak d
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hmL hnm z x y omega hz hx hD hnot hgood u g
    hweak hg
  let k : ℤ := (n : ℤ) - 2
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let B : ℝ := K *
    (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
      Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2)
  have htranslated : translateSet y (openCubeSet (originCube d k)) =
      translatedCube d k y := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  have hparent : translatedCube d k y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    have hp' : p ∈ translatedCube d ((n : ℤ) - 2) y := by
      simpa only [k] using hp
    exact (hD hp').2
  apply normalizedCutoffEnergy_translatedCube_le_of_depthTwo_cell_bounds
    M L omega u hparent B
  intro R hR
  let qR : Vec d := y + triadicCubeShift R
  have hDtranslate : translateSet y (openCubeSet (originCube d k)) ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x := by
    rw [htranslated]
    simpa only [k] using hD
  have hqR : qR ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x :=
    translated_descendantCentre_mem_of_parent_subset hR hDtranslate
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hpatch : openCubeAtScale qR ((n : ℤ) - 3) ⊆ cube d (m : ℤ) :=
    openCubeAtScale_predTwo_subset_domain_of_not_boundaryTouches
      hxDomain hqR hnot
  have hbound := hcell M sOrder hs L m n hmL hnm z x qR omega hz hx hqR
    hpatch hgood u g hweak hg
  have hset : translateSet y (openCubeSet R) =
      truncatedCube d (m : ℤ) (k - 2) qR := by
    apply translate_descendant_openCubeSet_eq_truncatedCube hR
    rw [htranslated]
    simpa only [cube] using hparent
  rw [hset]
  simpa only [k, U, sigma, B] using hbound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
