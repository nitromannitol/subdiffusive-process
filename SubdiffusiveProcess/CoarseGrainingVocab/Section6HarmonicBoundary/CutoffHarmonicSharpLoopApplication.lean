
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySharpLoopApplication
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicLeaves

@[expose] public section

/-!
# The boundary sharp-loop application, at a finite cutoff

Cutoff companion of
`Section6HarmonicApproximation.exists_boundaryHarmonicComparison_le_sharpLoopBound_of_weightedEnergy`:
the binder `m ≤ L` is deleted and the good event is `𝒢^{(L)}_{n+2,z}`.  The
single changed leaf is the cutoff sharp comparator loop, reached through
`Section6CutoffHarmonic.CutoffHarmonicLeaves`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]



theorem exists_boundaryHarmonicComparison_le_sharpLoopBound_of_weightedEnergy
    (d : ℕ) [NeZero d] :
    ∃ (C : ℝ≥0∞) (Cd : ℝ), C < ∞ ∧ 0 < Cd ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
      let Q := originCube d ((n : ℤ) - 2)
      let U := truncatedCube d (m : ℤ) (n : ℤ) x
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      let E := Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z)
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (originCube d (m : ℤ)) u h g →
        MemCubeEuclideanFullWsp (originCube d (m : ℤ)) s2
          FiniteLpExponent.two g →
      ∀ (S : ℝ),
        (∀ u0 : H1Function (openCubeSet Q),
          (∀ p, u0.grad p = u.grad (p + y)) →
          weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
            ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn Q)
              u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S) →
      ∀ (uD v : H1Function (translatedCube d ((n : ℤ) - 2) y)),
        (∀ p, uD.toFun p = u.toFun p) →
        IsWeaklyHarmonicOn (fun _ ↦ (1 : ℝ))
          (translatedCube d ((n : ℤ) - 2) y) v →
        HasZeroTraceDifferenceOn (translatedCube d ((n : ℤ) - 2) y) v uD →
        normalizedL2On (translatedCube d ((n : ℤ) - 2) y)
            (fun p ↦ u.toFun p - v.toFun p) ≤
          flatComparatorSharpGoodEventLoopBound C d n sigma smid s1 s2 E S
            (Cd * Real.rpow s (-(1 / 2 : ℝ)) *
              (fractionalSeminormOn U s g).toReal)
            Q (fun p ↦ g (p + y)) := by
  obtain ⟨C, hCtop, hloop⟩ :=
    exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp_neZero d
  obtain ⟨Cd, hCd, hforce⟩ := exists_interiorForceOverlap_le_windowSeminorm d
  refine ⟨C, Cd, hCtop, hCd, ?_⟩
  intro M s hs L m n hnm z x y omega hz hx hD hgood
  dsimp only
  intro u h g hdir hg S hweighted
  have hDset : translatedCube d ((n : ℤ) - 2) y =
      translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))) := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  rw [hDset]
  intro uD v huD hharm htrace
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hsubOpen : translatedCube d ((n : ℤ) - 2) y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    exact (hD hp).2
  obtain ⟨g0, hg0, hg0eq, u0, _v0, hu0forced, _hv0, _huv0, hu0val,
      hu0grad⟩ :=
    exists_localSourceComparisonDatum_of_dirichlet_retained M L omega m
      ((n : ℤ) - 2) y ⟨s, by
        exact (mul_pos (by norm_num)
          (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
        by linarith [hs.2]⟩ u h g hdir hg
      hsubOpen _ hsigma
  have hS := hweighted u0 hu0grad
  have hDforce := hforce ⟨s, by
      exact (mul_pos (by norm_num)
        (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
      by linarith [hs.2]⟩ m n hnm z x y
    hx hD g g0 hg hg0 hg0eq
  have hcontain : translateSet (y - z)
      (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
        cubeSet (originCube d ((n : ℤ) + 2)) :=
    closedOffGridCube_subset_originAnchorParent hx hD
  have hharm' : IsUnitWeaklyHarmonicOn
      (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2)))) v := by
    exact isUnitWeaklyHarmonicOn_iff.mpr hharm
  have htrace' : MemH10
      (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))))
        (fun p ↦ v.toFun p - u.toFun p) := by
    exact memH10_sub_physical_of_hasZeroTraceDifferenceOn htrace huD
  have hg0fun : (fun p ↦ g (p + y)) = g0 := (funext hg0eq).symm
  rw [hg0fun]
  exact hloop M s hs L n omega y z hcontain hgood g0 hg0 u0 hu0forced
    u.toFun v hharm' htrace' hu0val S _ hS hDforce

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
