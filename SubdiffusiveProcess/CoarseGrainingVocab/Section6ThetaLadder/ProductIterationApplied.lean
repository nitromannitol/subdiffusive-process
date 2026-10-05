module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductBadScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductCutoffGoodStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TranslatedIteration
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.Restriction

@[expose] public section

/-!
# Theta-perturbed ladder: application of the iteration lemma

This module threads the finite-cutoff product good-scale recurrence through
the proved iteration lemma on concentric translated cubes.  The forcing and
boundary defects are zero.  The only iteration coefficient is the product
error's slope term, and the only bad scales are the initial block and failures
of the ordinary finite-cutoff good event.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- The dimension-only slope coefficient in one product recurrence. -/
def productIterationSlopeCoefficient
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (k : ℕ) (error : ℝ) : ℝ :=
  productOriginRecurrenceErrorConstant d hd k * error *
    (Real.sqrt (d : ℝ) / 2)

theorem productIterationSlopeCoefficient_nonneg
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) {error : ℝ}
    (herror : 0 ≤ error) (k : ℕ) :
    0 ≤ productIterationSlopeCoefficient d hd k error := by
  unfold productIterationSlopeCoefficient
  exact mul_nonneg
    (mul_nonneg (productOriginRecurrenceErrorConstant_nonneg d hd k) herror)
    (div_nonneg (Real.sqrt_nonneg _) (by norm_num))

/-- The product good-scale recurrence, assembled on every non-bad scale and
fed to the translated-cube iteration lemma. -/
theorem exists_productIterationApplied (d : ℕ) [NeZero d] :
    ∃ Kbase Cgain Citer : ℝ,
      0 < Kbase ∧ 0 < Cgain ∧ 0 < Citer ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
      ∀ L n top k : ℕ, n < top → 6 ≤ k →
      ∀ z : Vec d, ∀ omega,
      ∀ eta ∈ Set.Icc ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1,
      ∀ b epsilon : ℝ, 0 < b → 0 < epsilon → epsilon ≤ 1 / 2 →
      Kbase * eta + Cgain * Real.sqrt epsilon ≤ 1 →
      ∀ theta : Vec d → ℝ,
      ContinuousOn theta (translatedCube d (top : ℤ) z) →
      (∀ x ∈ translatedCube d (top : ℤ) z,
        |b⁻¹ * theta x - 1| ≤ epsilon) →
      ∀ contraction : ℝ, contraction ∈ Set.Ioo (0 : ℝ) 1 →
      contraction ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) +
        productOriginRecurrenceErrorConstant d M.shellPrefix.dimension k *
          (Kbase * eta + Cgain * Real.sqrt epsilon) ≤ contraction ^ k →
      ∀ B : ℝ,
      (∑ j ∈ Finset.Icc n top,
          ((1 : ℝ) - if omega ∈ goodEvent M (some L) j z eta (1 / 32 : ℝ)
            then 1 else 0)) < B →
      ∀ u : H1Function (translatedCube d (top : ℤ) z),
      IsWeaklyHarmonicOn
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x)
          (translatedCube d (top : ℤ) z) u →
      let error := Kbase * eta + Cgain * Real.sqrt epsilon
      let epsRow : ℤ → ℝ := fun _ ↦
        productIterationSlopeCoefficient d M.shellPrefix.dimension k error
      let bad := productBadScales M L eta (1 / 32 : ℝ) n top k z omega
      let A := Citer * (k + 1) * (bad.card + 1) +
        Citer * ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow j
      ((bad.card : ℝ) < (k : ℝ) + B) ∧
      (3 : ℝ) ^ (-(n : ℤ)) *
          normalizedL2On (translatedCube d (n : ℤ) z)
            (fun x ↦ u.toFun x -
              averageOn (translatedCube d (n : ℤ) z) u.toFun) ≤
        Real.exp A * ((3 : ℝ) ^ (-(top : ℤ)) *
          normalizedL2On (translatedCube d (top : ℤ) z)
            (fun x ↦ u.toFun x -
              averageOn (translatedCube d (top : ℤ) z) u.toFun)) := by
  obtain ⟨Kbase, Cgain, hKbase, hCgain, hrec⟩ :=
    exists_productTranslated_goodScaleRecurrence d
  obtain ⟨Citer, hCiter, hiter⟩ := translatedCube_iteration d
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro M hs L n top k hntop hk z omega eta heta b epsilon hb hepsilon
    hepsilonHalf herrorOne theta htheta hnear contraction hcontraction
    hcontractionPow hcontract B hfailure u hu
  dsimp only
  let error := Kbase * eta + Cgain * Real.sqrt epsilon
  let epsRow : ℤ → ℝ := fun _ ↦
    productIterationSlopeCoefficient d M.shellPrefix.dimension k error
  let bad := productBadScales M L eta (1 / 32 : ℝ) n top k z omega
  let defect : ℤ → ℝ := fun _ ↦ 0
  let A := Citer * (k + 1) * (bad.card + 1) +
    Citer * ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow j
  have heta0 : 0 ≤ eta := by
    have : 0 ≤ (1 / 32 : ℝ)⁻¹ * M.delta ^ 2 := by positivity
    exact this.trans heta.1
  have herror0 : 0 ≤ error := by
    dsimp only [error]
    positivity
  have heps0 : 0 ≤
      productIterationSlopeCoefficient d M.shellPrefix.dimension k error :=
    productIterationSlopeCoefficient_nonneg d M.shellPrefix.dimension herror0 k
  have hnonneg : ∀ j ∈ Finset.Icc (n : ℤ) (top : ℤ),
      0 ≤ epsRow j ∧ 0 ≤ defect j := by
    intro j _
    exact ⟨heps0, le_rfl⟩
  have hrecurrence : ∀ j ∈ Finset.Icc (n : ℤ) (top : ℤ), j ∉ bad →
      ∀ ell : Affine d,
        ell ∈ affineMinimizers (translatedCube d j z) u.toFun →
        excess (j - k) (translatedCube d (j - k) z) u.toFun ≤
          contraction ^ k * excess j (translatedCube d j z) u.toFun +
            epsRow j * Real.sqrt (vecNormSq ell.slope) + defect j := by
    intro j hj hnot ell hell
    obtain ⟨hnkj, hgood⟩ :=
      notMem_productBadScales M L eta (1 / 32 : ℝ) z omega hj hnot
    have hkj : k ≤ j.toNat := (Nat.le_add_left k n).trans hnkj
    have hj0 : 0 ≤ j :=
      (Int.natCast_nonneg n).trans (Finset.mem_Icc.1 hj).1
    have hjtop : j.toNat ≤ top := by
      have := (Finset.mem_Icc.1 hj).2
      rw [← Int.toNat_of_nonneg hj0] at this
      exact_mod_cast this
    have hsub : translatedCube d (j.toNat : ℤ) z ⊆
        translatedCube d (top : ℤ) z := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, cube_subset_cube_of_le (by exact_mod_cast hjtop) hy, rfl⟩
    let uj : H1Function (translatedCube d (j.toNat : ℤ) z) :=
      u.restrict
        (Section6CutoffRegularity.isOpen_translatedCube d (j.toNat : ℤ) z) hsub
    have huj : IsWeaklyHarmonicOn
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x)
        (translatedCube d (j.toNat : ℤ) z) uj :=
      Section6BoundaryL2.isWeaklyHarmonicOn_restrict
        (Section6CutoffRegularity.isOpen_translatedCube d (top : ℤ) z)
        (Section6CutoffRegularity.isOpen_translatedCube d (j.toNat : ℤ) z)
        hsub hu
    have hthetaJ : ContinuousOn theta (translatedCube d (j.toNat : ℤ) z) :=
      htheta.mono hsub
    have hnearJ : ∀ x ∈ translatedCube d (j.toNat : ℤ) z,
        |b⁻¹ * theta x - 1| ≤ epsilon := fun x hx ↦ hnear x (hsub hx)
    have hjcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
    have hellJ : ell ∈ affineMinimizers
        (translatedCube d (j.toNat : ℤ) z) uj.toFun := by
      simpa only [uj, hjcast] using! hell
    have hraw := hrec M hs L j.toNat z omega eta heta hgood b epsilon hb
      hepsilon hepsilonHalf herrorOne theta hthetaJ hnearJ k hk uj huj ell hellJ
    have hraw' :
        excess (j - k) (translatedCube d (j - k) z) u.toFun ≤
          oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
              ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
              excess j (translatedCube d j z) u.toFun +
            productOriginRecurrenceErrorConstant d M.shellPrefix.dimension k *
              (Kbase * eta + Cgain * Real.sqrt epsilon) *
              (excess j (translatedCube d j z) u.toFun +
                Real.sqrt (d : ℝ) / 2 * Real.sqrt (vecNormSq ell.slope)) := by
      simpa only [uj, hjcast] using! hraw
    have hE0 : 0 ≤ excess j (translatedCube d j z) u.toFun := by
      rw [Section6Iteration.excess_eq_affineExcessScaled]
      exact Section6Iteration.affineExcessScaled_nonneg _ _ _
    have hcoeff := mul_le_mul_of_nonneg_right hcontract hE0
    dsimp only [epsRow, defect, error]
    norm_num only [add_zero]
    unfold productIterationSlopeCoefficient
    nlinarith only [hraw', hcoeff]
  have hcore := hiter k (by omega) contraction hcontraction hcontractionPow
    (n : ℤ) (top : ℤ) (by exact_mod_cast hntop) z u bad
    (productBadScales_subset_Icc M L eta (1 / 32 : ℝ) n top k z omega)
    epsRow defect hnonneg hrecurrence
  have hcard := productBadScales_card_lt_of_failure_bound
    M L eta (1 / 32 : ℝ) B n top k z omega hfailure
  refine ⟨hcard, ?_⟩
  dsimp only at hcore
  have hfirst := hcore.1
  simp only [defect, Finset.sum_const_zero, add_zero] at hfirst
  simpa only [A] using hfirst

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
