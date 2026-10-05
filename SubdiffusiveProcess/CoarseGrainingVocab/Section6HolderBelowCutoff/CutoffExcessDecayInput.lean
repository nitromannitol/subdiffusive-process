module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.Geometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodEventCap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffErrorCap

@[expose] public section

/-!
# The finite-cutoff interior inputs, with the `s`-powers as parameters

`l.cutoff.regularity.good.scale.estimates` (`l.cutoff.regularity.good.scale.estimates`)
states two clauses: the harmonic-approximation lemma and the excess-decay lemma,
each "with its hypothesis `L ≥ m` removed" and with `𝒢_{n+2,z}` replaced by
`𝒢^{(L)}_{n+2,z}`.  "All right-hand-side and boundary terms in those lemmas are
retained."

This module records the interior branch of those two clauses as `Prop`s, in the
same style as `Section6SealAdapters.InteriorHarmonicApproximationInput` and
`Section6HolderInterior.InteriorHolderExcessDecayInput`, with two differences:

* the binder `m ≤ L` is deleted and the good event is `goodEvent M (some L) …`;
* **the two `s`-exponents are parameters** `p` (on the `𝓔` leg, and on the
  `epsilon` leg of the excess-decay display) and `q` (on the force leg).  The
  D-073 cut fixes them at `p = -2`, `q = -8` for the interior harmonic anchor
  v2 and for excess decay v4; the abbreviations `…V2` / `…V4` name that
  instantiation, so a later re-shape is a substitution of the two numerals.

`MathcalECutoffCapInput` is the cutoff replacement for
`Section6ExcessDecay.MathcalECapInput`: it is the `epsilon`-form of the fifth
conjunct of the **proved** `SubdiffusiveProcess.Frozen.Section6.cutoff_regularity_good_scales`,
and is therefore a theorem, not a hypothesis (`mathcalECutoffCapInput_of_proved_cutoffGoodScales`).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The interior harmonic-approximation clause of
`l.cutoff.regularity.good.scale.estimates`: the body of the frozen interior
anchor with `m ≤ L` deleted, `𝒢_{n+2,z}` replaced by `𝒢^{(L)}_{n+2,z}`, and the
two `s`-exponents carried as parameters. -/
def InteriorCutoffHarmonicApproximationInput (d : ℕ) (p q : ℝ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ ω,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
          (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q', uD.toFun q' = u.toFun q') → (∀ q', uD.grad q' = u.grad q') →
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
                    (fun q' => u.toFun q' - v.toFun q')) ω ≤
                C * s ^ p * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    normalizedL2On (truncatedCube d m n x)
                      (fun q' => u.toFun q' - averageOn (truncatedCube d m n x) u.toFun) +
                  C * s ^ q *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal

/-- The D-073 instantiation: interior harmonic anchor **v2**. -/
abbrev InteriorCutoffHarmonicApproximationInputV2 (d : ℕ) : Prop :=
  InteriorCutoffHarmonicApproximationInput d (-2 : ℝ) (-8 : ℝ)

/-- The interior excess-decay clause of
`l.cutoff.regularity.good.scale.estimates`: word-for-word
`Section6HolderInterior.InteriorHolderExcessDecayInput` with the binder `m ≤ L`
deleted, `goodEvent M none (n+2) z epsilon (s/8)` replaced by
`goodEvent M (some L) (n+2) z epsilon (s/8)`, and the `s`-exponents carried as
parameters. -/
def InteriorCutoffHolderExcessDecayInput (d : ℕ) (p q : ℝ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ ω,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
            (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M (some L) (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ p * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ p *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                Real.sqrt (vecNormSq ell.slope) +
              C * s ^ q * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal

/-- The D-073 instantiation: excess decay **v4** powers, interior branch. -/
abbrev InteriorCutoffHolderExcessDecayInputV4 (d : ℕ) : Prop :=
  InteriorCutoffHolderExcessDecayInput d (-2 : ℝ) (-8 : ℝ)

/-- Cutoff replacement for `Section6ExcessDecay.MathcalECapInput`: the
`epsilon`-form of the error cap on the cutoff good event, with no relation
between `L` and `m`. -/
def MathcalECutoffCapInput (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      ∀ L m : ℕ, ∀ ω,
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
          ω ∈ goodEvent M (some L) m 0 epsilon s →
            section6HomogenizationError M s L m ω 0 ≤ C * epsilon

/-- **The cutoff cap is a theorem.**  It is the fifth conjunct of the proved
`SubdiffusiveProcess.Frozen.Section6.cutoff_regularity_good_scales` at translate zero. -/
theorem mathcalECutoffCapInput_of_proved_cutoffGoodScales (d : ℕ) :
    MathcalECutoffCapInput d := by
  obtain ⟨C, hC, hcut⟩ := SubdiffusiveProcess.Frozen.Section6.cutoff_regularity_good_scales d
  refine ⟨C, hC, ?_⟩
  intro M s hs L m omega epsilon hepsilon homega
  have hcap := ((hcut M L).2.2.2.2 s hs epsilon hepsilon m 0 omega).2
  rwa [indicatorValue_of_mem homega] at hcap

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
