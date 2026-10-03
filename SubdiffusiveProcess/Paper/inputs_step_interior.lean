module

public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.inputs_deterministic_interior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffErrorCap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.CutoffPaperError

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

theorem aux_inputs_step_interior_wellPosed (d : ℕ) [NeZero d] (n : ℕ)
    (y : Vec d)
    (uD : H1Function (translatedCube d ((n : ℤ) - 2) y)) :
    (∃ v : H1Function (translatedCube d ((n : ℤ) - 2) y),
      IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d ((n : ℤ) - 2) y) v ∧
        HasZeroTraceDifferenceOn (translatedCube d ((n : ℤ) - 2) y) v uD) ∧
    (∀ v v' : H1Function (translatedCube d ((n : ℤ) - 2) y),
      (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d ((n : ℤ) - 2) y) v ∧
          HasZeroTraceDifferenceOn (translatedCube d ((n : ℤ) - 2) y) v uD) →
      (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d ((n : ℤ) - 2) y) v' ∧
          HasZeroTraceDifferenceOn (translatedCube d ((n : ℤ) - 2) y) v' uD) →
      v.toFun =ᵐ[volume.restrict (translatedCube d ((n : ℤ) - 2) y)] v'.toFun ∧
        v.grad =ᵐ[volume.restrict (translatedCube d ((n : ℤ) - 2) y)] v'.grad) := by
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.interiorHarmonic_wellPosed
    d n y uD

theorem inputs_step_interior (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ ω,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
          (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          (∃ v : H1Function (translatedCube d (n - 2) y),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
          (∀ v v' : H1Function (translatedCube d (n - 2) y),
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
            v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
              v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            indicatorValue (goodEvent M (some L) (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-3 / 2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                  C * s ^ (-15 / 2 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal) := by
  classical
  obtain ⟨Cerr, hCerr, hErrorCap⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.exists_section6HomogenizationError_le_of_cutoffGoodEvent
      (d := d)
  obtain ⟨C, hC, hDet⟩ :=
    Paper.inputs_deterministic_interior d hd Cerr hCerr
  refine ⟨C, hC, ?_⟩
  intro M s hs L m n hnm z hz x hx hnot ω u g hweak hg y hy hcov hloc uD huval hugrad
  have hs0 : 0 < s := by
    have hδ : 0 < M.delta := M.shellPrefix.delta_pos
    exact (mul_pos (by norm_num) (sq_pos_of_pos hδ)).trans_le hs.1
  let ν := SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample z ω
  have hcoef :
      (fun q : Vec d => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω (q + z)) =
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ν := by
    funext q
    exact (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.aCutoff_translatePotentialSample
      M L z ω q).symm
  let data : ScalarTriadicCoeffData
      (fun q : Vec d => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω (q + z)) :=
    hcoef.symm ▸ SubdiffusiveProcess.CoarseGrainingVocab.aCutoffTriadicData M L ν
  have hDataFam : data.toTriadicCoeffFamily =
      SubdiffusiveProcess.CoarseGrainingVocab.aCutoffFamily M L ν := by
    dsimp [data, SubdiffusiveProcess.CoarseGrainingVocab.aCutoffFamily,
      SubdiffusiveProcess.CoarseGrainingVocab.aCutoffTriadicData]
    rfl
  let a0 := tailCoefficientCubeAverage M L (n + 2) ν
  have ha0 : 0 < a0 := by
    dsimp [a0]
    exact tailCoefficientCubeAverage_pos M L (n + 2) ν
  have ha0eq : a0 = tailAverage M L (n + 2) ω
      (translatedCube d (n + 2) z) := by
    dsimp [a0]
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample
      M L (n + 2) z ω
  refine ⟨(aux_inputs_step_interior_wellPosed d n y uD).1,
    (aux_inputs_step_interior_wellPosed d n y uD).2, ?_⟩
  intro v hv htrace
  have hB : 0 ≤
      C * s ^ (-3 / 2 : ℝ) *
          section6HomogenizationError M (s / 8) L (n + 2) ω z *
          normalizedL2On (truncatedCube d m n x)
            (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
        C * s ^ (-15 / 2 : ℝ) *
          (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
          (3 : ℝ) ^ ((1 + s) * n) *
          (fractionalSeminormOn (truncatedCube d m n x) s g).toReal := by
    have herror : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z :=
      ENNReal.toReal_nonneg
    have hosc : 0 ≤ normalizedL2On (truncatedCube d m n x)
        (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) :=
      Section6Iteration.normalizedL2On_nonneg _ _
    have hfrac : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
      ENNReal.toReal_nonneg
    have htail : 0 < tailAverage M L (n + 2) ω (translatedCube d (n + 2) z) := by
      rw [← ha0eq]
      exact ha0
    positivity
  refine Section6HarmonicApproximation.indicatorValue_le_of_mem_imp _ _ _ hB ?_
  intro hgood
  have hsection6 := hErrorCap M s hs L (n + 2) ω z hgood
  have hpaper :
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
        (s / 8) Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 =
      ENNReal.ofReal (section6HomogenizationError M (s / 8) L (n + 2) ω z) := by
    have hsLower : 64 * M.delta ^ 2 ≤ s / 8 := by
      have hδ : 0 ≤ M.delta ^ 2 := sq_nonneg M.delta
      nlinarith [hs.1]
    have hsUpper : s / 8 ≤ 1 / 2 := by linarith [hs.2]
    have hpaper0 := @SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.paperHomogenizationError_eq_ofReal_cutoffGoodEvent d inferInstance M
      (s / 8) hsLower hsUpper L (n + 2) ω z (1 : ℝ) (by norm_num) (by norm_num) hgood
    have hscale : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
    calc
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
          (s / 8) Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0 =
        paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
          (s / 8) Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffFamily M L ν)
          (tailCoefficientCubeAverage M L (n + 2) ν) := by
            rw [hDataFam]
      _ = ENNReal.ofReal (section6HomogenizationError M (s / 8) L (n + 2) ω z) := by
        simpa only [hscale] using hpaper0
  have herr :
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
        (s / 8) Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr := by
    rw [hpaper]
    exact ENNReal.ofReal_le_ofReal hsection6
  have hdet := hDet s hs0 hs.2 m n hnm z hz x hx
      hnot (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) data a0 ha0 herr
      u g hweak hg y hy hcov hloc uD huval hugrad
  have hreal :
      (paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
        (s / 8) Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0).toReal =
          section6HomogenizationError M (s / 8) L (n + 2) ω z := by
    rw [hpaper]
    exact ENNReal.toReal_ofReal ENNReal.toReal_nonneg
  have hbound := hdet.2.2 v hv htrace
  rw [hreal] at hbound
  rw [ha0eq] at hbound
  exact hbound

end Paper

