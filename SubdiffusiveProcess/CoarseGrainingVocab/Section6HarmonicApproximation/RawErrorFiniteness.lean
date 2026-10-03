module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularResummation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Transport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.SubunitTail

@[expose] public section

/-!
# Finiteness of the raw Section 6 paper error on the good event

The frozen Section 6 observable stores an `ENNReal` paper error through
`ENNReal.toReal`.  Before that real observable can control Chapter 2's error,
one must know that the raw series is not `⊤`.  This file exposes the raw
annular estimate already proved by the Step-1 resummation and records the
resulting `ofReal ∘ toReal` identity under a finite annular budget.

PROVENANCE: this is the explicit finiteness half of the error-cap/reindex step
in `Algsuperdiff/Section4/Provider/ExcessDecay/GoodEventCaps.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The raw (pre-`toReal`) paper error satisfies the same refined annular
bound as the frozen real observable. -/
theorem paperHomogenizationError_le_annularSupTwo
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hd : 1 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) ≤
      (192 * annularSupTwo s (m : ℤ)
          (section6LocalProbeMax M L omega z
            (tailCoefficientCubeAverage M L m
              (translatePotentialSample z omega)))) ^ (1 / 2 : ℝ) := by
  let alpha := tailCoefficientCubeAverage M L m (translatePotentialSample z omega)
  let g : TriadicCube d → ℝ≥0∞ := section6LocalProbeMax M L omega z alpha
  have hcentral : ∀ n : ℤ, n ≤ (m : ℤ) →
      g (originCube d n) ≤
        ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * (t : ℝ))) *
          annulusMax g (n - 1 - (t : ℤ)) := by
    intro n _hn
    exact section6LocalProbeMax_originCube_le_onion M L omega z alpha n
  have hchild : ∀ R : TriadicCube d, ∃ R' ∈ childCubes R, g R ≤ g R' := by
    intro R
    exact section6LocalProbeMax_le_child M L omega z alpha R
  have hseries : ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
      (⨆ R : {R : TriadicCube d // R ∈ descendantsAtScale
          (originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))}, g R.1) ≤
      64 * annularSup s (m : ℤ) g :=
    tsum_geometricWeight_descendantSup_le_annularSup hs hs2 hd m g hcentral
  have hrefined : 64 * annularSup s (m : ℤ) g ≤
      192 * annularSupTwo s (m : ℤ) g := by
    calc
      64 * annularSup s (m : ℤ) g ≤
          64 * (3 * annularSupTwo s (m : ℤ) g) := by
        gcongr
        exact annularSup_le_three_mul_annularSupTwo hs2 _ hchild
      _ = 192 * annularSupTwo s (m : ℤ) g := by ring
  have hsum := hseries.trans hrefined
  have hterm : ∀ l : ℕ,
      (paperScaleResponseAtScale (originCube d (m : ℤ))
          ((m : ℤ) - (l : ℤ)) .infinity
          (aCutoffFamily M L (translatePotentialSample z omega)) alpha) ^ (2 : ℝ) =
        ⨆ R : {R : TriadicCube d // R ∈ descendantsAtScale
            (originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))}, g R.1 := by
    intro l
    simp only [paperScaleResponseAtScale]
    rw [← ENNReal.rpow_mul]
    norm_num
    rw [paperMaxDescendantProbeAtScale_aCutoffFamily_eq_transported]
    refine iSup_congr fun R => ?_
    simp only [g, section6LocalProbeMax]
    rw [scale_eq_of_mem_descendantsAtScale R.2]
  unfold paperHomogenizationError paperHomogenizationErrorFinite
  apply ENNReal.rpow_le_rpow
  · calc
      (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
          (paperScaleResponseAtScale (originCube d (m : ℤ))
            ((m : ℤ) - (l : ℤ)) .infinity
            (aCutoffFamily M L (translatePotentialSample z omega)) alpha) ^ (2 : ℝ)) =
          ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
            (⨆ R : {R : TriadicCube d // R ∈ descendantsAtScale
              (originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))}, g R.1) := by
            apply tsum_congr
            intro l
            rw [hterm l]
      _ ≤ 192 * annularSupTwo s (m : ℤ) g := hsum
  · norm_num

/-- A finite refined annular budget makes the raw paper error equal to the
`ofReal` of the frozen real-valued Section 6 observable. -/
theorem paperHomogenizationError_eq_ofReal_section6HomogenizationError_of_annular_ne_top
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hd : 1 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hfinite : annularSupTwo s (m : ℤ)
      (section6LocalProbeMax M L omega z
        (tailCoefficientCubeAverage M L m
          (translatePotentialSample z omega))) ≠ ⊤) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) =
      ENNReal.ofReal (section6HomogenizationError M s L m omega z) := by
  let E := paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s
    .infinity (.finite 2)
    (aCutoffFamily M L (translatePotentialSample z omega))
    (tailCoefficientCubeAverage M L m (translatePotentialSample z omega))
  have hEtop : E ≠ ⊤ := by
    have hle := paperHomogenizationError_le_annularSupTwo hs hs2 hd M L m omega z
    exact ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinite))
      hle
  have hreal : section6HomogenizationError M s L m omega z = E.toReal := rfl
  rw [hreal, ENNReal.ofReal_toReal hEtop]

/-- The frozen good event supplies the finite annular budget required by the
raw-to-real identity, at every translated centre. -/
theorem paperHomogenizationError_eq_ofReal_section6HomogenizationError_of_goodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    {L m : ℕ} (hmL : m ≤ L)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hgood : omega ∈ goodEvent M none m z 1 s) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) =
      ENNReal.ofReal (section6HomogenizationError M s L m omega z) := by
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  have hd1 : 1 ≤ d := le_trans (by norm_num) M.shellPrefix.dimension
  let nu := translatePotentialSample z omega
  have hnu : nu ∈ goodEvent M none m 0 1 s :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.mem_goodEvent_iff_translate_zero
      M none m 1 s z omega).mp hgood
  have hbudget :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.annularSupTwo_le_goodScaleBudget
      M hmL hsLower hsUpper nu hnu
  have hfinite0 : annularSupTwo s (m : ℤ)
      (section6LocalProbeMax M L nu 0
        (tailCoefficientCubeAverage M L m nu)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbudget
  have hfinite : annularSupTwo s (m : ℤ)
      (section6LocalProbeMax M L omega z
        (tailCoefficientCubeAverage M L m
          (translatePotentialSample z omega))) ≠ ⊤ := by
    have hlocal : section6LocalProbeMax M L nu 0
          (tailCoefficientCubeAverage M L m nu) =
        section6LocalProbeMax M L omega z
          (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) := by
      funext R
      simp only [nu, section6LocalProbeMax,
        Section6Covariance.translatePotentialSample_zero]
    rw [← hlocal]
    exact hfinite0
  exact
    paperHomogenizationError_eq_ofReal_section6HomogenizationError_of_annular_ne_top
      hs0 hsUpper hd1 M L m omega z hfinite

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
