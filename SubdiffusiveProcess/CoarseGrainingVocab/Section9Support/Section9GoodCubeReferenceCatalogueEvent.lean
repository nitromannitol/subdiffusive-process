import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCatalogueLocalEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryCatalogTransport
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteTestTranslation
/-! One total family of local bad predicates supplies the native affine reference tests at every cutoff and lattice site. -/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem exists_goodCube_reference_catalogue_event_family
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      ∀ epsH : ℝ, 0 < epsH →
        ∃ j : ℕ, 2 ≤ j ∧
          ∀ (J N : ℕ) (eps : ℝ), 0 < eps →
            ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
              ∀ G : Finset (ℕ × Vec d), G.card ≤ N →
                (∀ q ∈ G, q.1 ≤ J) →
                (∀ q ∈ G, cubeSet (q.2, (3 : ℝ) ^ (-(q.1 : ℤ))) ⊆
                  cubeSet ((0 : Vec d), (1 : ℝ))) →
              ∀ (k : ℕ) (X : Finset (Vec d)),
                (∀ x ∈ X, cubeSet (x, (3 : ℝ) ^ (-(k : ℤ))) ⊆
                  cubeSet ((0 : Vec d), (1 : ℝ))) →
                (goodCubeAuxiliaryPairs X j (-(k : ℤ))).card ≤ N →
                ∃ bad : (M : GMCModel d) → (n : ℕ) →
                  Set (nativeBox n 1 (0 : Lattice d) → ℝ),
                  ∀ M : GMCModel d, M.delta ≤ c → ∀ n : ℕ,
                    (∀ z : Lattice d,
                      M.P.toMeasure (coefficientLocalBadEvent M n 1 (bad M n) z) ≤
                        ENNReal.ofReal (Real.exp
                          (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2))))) ∧
                    ∀ (z : Lattice d) (omega : PotentialSample d),
                      omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z →
                      GoodCubeFiniteLocalTests (aCutoff M n omega)
                        p A (if J ≤ n then ahom M n else 1) eps epsH
                        ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 3)
                        (Section7Process.timeScale (ahom M))
                        (G.image (fun q => ((n : ℤ) - q.1,
                          goodCubeCentre n z + (3 : ℝ) ^ n • q.2)))
                        (affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) ''
                          (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d))) := by
  classical
  obtain ⟨p, A, hp2, hA, hloc⟩ := exists_goodCube_finite_catalogue_local_event d hd
  refine ⟨p, A, hp2, hA, ?_⟩
  intro epsH hepsH
  obtain ⟨j, hj, hloc⟩ := hloc epsH hepsH
  refine ⟨j, hj, ?_⟩
  intro J N eps heps
  obtain ⟨c, hc, hcHalf, huse⟩ := hloc J N eps heps
  refine ⟨c, hc, hcHalf, ?_⟩
  intro G hGcard hGdepth hGinside k X hX hPcard
  have hp : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 2) hp2
  have hj1 : 1 ≤ j := le_trans (by norm_num : (1 : ℕ) ≤ 2) hj
  have key : ∀ (M : GMCModel d) (n : ℕ),
      ∃ bad : Set (nativeBox n 1 (0 : Lattice d) → ℝ),
      M.delta ≤ c →
        (∀ z : Lattice d,
          M.P.toMeasure (coefficientLocalBadEvent M n 1 bad z) ≤
            ENNReal.ofReal (Real.exp
              (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2))))) ∧
        ∀ (z : Lattice d) (omega : PotentialSample d),
          omega ∉ coefficientLocalBadEvent M n 1 bad z →
          GoodCubeFiniteLocalTests (aCutoff M n omega)
            p A (if J ≤ n then ahom M n else 1) eps epsH
            ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 3)
            (Section7Process.timeScale (ahom M))
            (G.image (fun q => ((n : ℤ) - q.1,
              goodCubeCentre n z + (3 : ℝ) ^ n • q.2)))
            (affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) ''
              (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d))) := by
    intro M n
    obtain ⟨hcard, hprop⟩ :=
      goodCube_auxiliary_pair_catalog_native X j k hj1 hX n (0 : Vec d)
    have hPcardN : ((goodCubeAuxiliaryPairs X j (-(k : ℤ))).image
        (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n))).card ≤ N := hcard.le.trans hPcard
    have hgeom : ∀ q ∈ (goodCubeAuxiliaryPairs X j (-(k : ℤ))).image
        (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n)),
        0 < q.1.2 ∧ q.2.2 = (3 : ℝ) ^ (((n : ℤ) - k)) ∧
        q.1.2 = (3 : ℝ) ^ (-(j : ℤ)) * q.2.2 ∧
        cubeSet q.1 ⊆ SubdiffusiveProcess.Section9.centeredAxisCube q.2.1 (q.2.2 / 2) := by
      intro q hq
      obtain ⟨h0, h1, h2, h3, -, -⟩ := hprop q hq
      exact ⟨h0, h1, h2, subset_closure.trans h3⟩
    have hnativeBox : nativeBox n 1 (0 : Lattice d) =
        cubeSet ((0 : Vec d), (3 : ℝ) ^ n) := by
      simp only [nativeBox, one_mul, goodCubeCentre_zero_lattice, cubeSet]
    have hparent : ∀ q ∈ (goodCubeAuxiliaryPairs X j (-(k : ℤ))).image
        (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n)),
        cubeSet q.2 ⊆ nativeBox n 1 (0 : Lattice d) := by
      intro q hq
      obtain ⟨-, -, -, -, h4, -⟩ := hprop q hq
      rw [hnativeBox]
      exact h4
    by_cases hM : M.delta ≤ c
    · obtain ⟨bad, hbad, htests⟩ :=
        huse M hM n G hGcard hGdepth hGinside ((n : ℤ) - k)
          ((goodCubeAuxiliaryPairs X j (-(k : ℤ))).image
            (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n)))
          hPcardN hgeom hparent
      refine ⟨bad, fun _ => ⟨hbad, ?_⟩⟩
      intro z omega homega
      have hT := htests z omega homega
      rw [Finset.coe_image] at hT
      exact goodCube_finiteLocalTests_native_translate (goodCubeCentre n z) n
        (aCutoff M n omega) (continuous_aCutoff M n omega).measurable p A
        (if J ≤ n then ahom M n else 1) eps epsH
        ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 3) hp
        (Section7Process.timeScale (ahom M)) G
        (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d)) hT
    · exact ⟨∅, fun hM' => absurd hM' hM⟩
  choose bad hbad using key
  exact ⟨bad, fun M hM n => hbad M n hM⟩
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
