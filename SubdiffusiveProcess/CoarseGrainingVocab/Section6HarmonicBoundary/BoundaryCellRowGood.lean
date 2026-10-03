module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.FrozenAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.GoodEventErrorCap

@[expose] public section

/-!
# The good-event ("honest") form of the boundary-cell manuscript row

`BoundaryCellManuscriptRow` (`BoundaryCellRow.lean`) prices the boundary-cell
cutoff energy by a *constant* multiple of the four printed budgets.  Every
route to that row that goes through the homogenization comparator produces
instead a bound with the local Section 6 error `𝓔 = section6HomogenizationError`
as an extra factor, because the comparator error is what the good event
controls.  Since the first leg of the frozen v6 comparison clause is itself
`C s^{-2} 𝓔 ‖u − (u)_U‖`, one might hope that carrying a factor `(1 + 𝓔)` in
the row is admissible and easier to prove.

This file records that hope precisely, as `BoundaryCellManuscriptRowGood`, and
settles it: the two rows are **equivalent up to the value of the constant**.
The good event of the frozen v6 anchor is evaluated at amplitude `1`, and the
proved `p.good.scale.mathcal.E` export then bounds `𝓔` by a dimension-only
constant (`Section6HarmonicApproximation.exists_section6HomogenizationError_le_of_goodEvent`).
So the `(1 + 𝓔)` weakening costs nothing and gains nothing: any route that
closes only under a *small* `𝓔` is not helped by it.

The consequence for `OPEN-18` is recorded in
`ledger/reports/provider-48-harmonic-boundary.md`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The four printed budgets are nonnegative on the frozen corridor. -/
theorem harmonicPhysicalFourBudgets_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m n : ℕ)
    (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {s : ℝ} (hs : 0 < s)
    (hsigma : 0 ≤ tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z))
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d) :
    0 ≤ harmonicPhysicalFourBudgets M L m n z x omega s u h g := by
  have hpow : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * (n : ℤ))) :=
    (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hrpow3 : ∀ t : ℝ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) t := fun t =>
    Real.rpow_nonneg (by norm_num) t
  have hrpows : ∀ t : ℝ, (0 : ℝ) ≤ Real.rpow s t := fun t => Real.rpow_nonneg hs.le t
  unfold harmonicPhysicalFourBudgets
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · exact mul_nonneg (mul_nonneg hsigma hpow) (sq_nonneg _)
  · split_ifs with hb
    · exact mul_nonneg hsigma (vecNormSq_nonneg _)
    · exact le_rfl
  · exact mul_nonneg (mul_nonneg (mul_nonneg (hrpows _)
      (inv_nonneg.mpr hsigma)) (hrpow3 _)) (sq_nonneg _)
  · split_ifs with hb
    · exact mul_nonneg (mul_nonneg (mul_nonneg hsigma (hrpows _)) (hrpow3 _))
        (sq_nonneg _)
    · exact le_rfl

/-- **The good-event form of the boundary-cell manuscript row.**

Identical to `BoundaryCellManuscriptRow` except that the four printed budgets
may be multiplied by `1 + 𝓔`, where `𝓔` is the local Section 6 homogenization
error appearing in the first leg of the frozen v6 comparison clause.  This is
the weakest row that any comparator-based route can be expected to produce. -/
def BoundaryCellManuscriptRowGood (d : ℕ) (Cboundary : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder),
    sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
  ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
  ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    z ∈ cube d (m : ℤ) →
    x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
    q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
    ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
    omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
  ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d),
    IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (originCube d (m : ℤ)) u h g →
    Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
    MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
    normalizedSetAverage (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)
        (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (u.grad p)) ≤
      Cboundary *
        (1 + section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z) *
        harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g

/-- **The `(1 + 𝓔)` weakening is free.**

On the frozen v6 good event — amplitude `1` — the proved
`p.good.scale.mathcal.E` export caps `𝓔` by a dimension-only constant, so the
honest row implies the constant-coefficient row with the constant enlarged by
`1 + C(d)`. -/
theorem boundaryCellManuscriptRow_of_good (d : ℕ) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hrow : BoundaryCellManuscriptRowGood d Cb) :
    ∃ Cb' : ℝ, 0 ≤ Cb' ∧ BoundaryCellManuscriptRow d Cb' := by
  obtain ⟨Cerr, hCerr0, hcap⟩ :=
    exists_section6HomogenizationError_le_of_goodEvent (d := d)
  refine ⟨Cb * (1 + Cerr), mul_nonneg hCb (by linarith), ?_⟩
  intro M sOrder hs L m n hmL hnm z x q omega hz hx hq hbd hgood u h g hdir hg hh
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < sOrder.1 :=
    (mul_pos (by norm_num : (0 : ℝ) < 512) (pow_pos hdelta 2)).trans_le hs.1
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hB : 0 ≤ harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g :=
    harmonicPhysicalFourBudgets_nonneg M L m n z x omega hs0 hsigma.le u h g
  have hE : section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z ≤ Cerr :=
    hcap M sOrder.1 hs L (n + 2) (by omega) omega z hgood
  have hstep := hrow M sOrder hs L m n hmL hnm z x q omega hz hx hq hbd hgood
    u h g hdir hg hh
  refine hstep.trans ?_
  have hmono : Cb *
      (1 + section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z) ≤
      Cb * (1 + Cerr) :=
    mul_le_mul_of_nonneg_left (by linarith) hCb
  exact mul_le_mul_of_nonneg_right hmono hB



theorem harmonic_approximation_good_scales_of_cellRowGood
    (d : ℕ) [NeZero d] {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hrow : BoundaryCellManuscriptRowGood d Cb) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, m ≤ L → n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemFractionalOn (cube d m) s h.grad →
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
            indicatorValue (goodEvent M none (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    (normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
                        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                    else 0)) +
                  C * s ^ (-8 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    C * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal else 0) := by
  obtain ⟨Cb', hCb', hrow'⟩ := boundaryCellManuscriptRow_of_good d hCb hrow
  exact harmonic_approximation_good_scales_of_cellRow d hCb' hrow'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
