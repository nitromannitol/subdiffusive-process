module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowWindowStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodScaleSaturation

@[expose] public section

/-!
# Centered energy at a good scale

Paper Lemma `l.centered.energy.good.scale`. Let `u` solve the Dirichlet problem for the
cutoff coefficient `a_L` on the cube `□_m` with boundary datum `h` and forcing `g`, where `g`
has fractional regularity of order `s ∈ [512 δ², 1/4]` and `∇h` is fractional of order `s`. On the
good event at scale `n + 2` with parameters `(1, s/8)`, for every `q` in the truncated
cube `U_{m,n-1}(x)`, the coefficient-normalized energy of `u` on `U_{m,n-4}(q)` is bounded by
four terms on `U = U_{m,n}(x)`: the centered `L²` oscillation of `u`, the squared mean of `∇h`,
the fractional seminorm of `g` and the fractional seminorm of `∇h`. The two boundary terms
carry the indicator that the closure of `U` meets `∂□_m`. The normalizing coefficient is the
tail average `a₀` of the cutoff coefficient over the scale-`(n+2)` cube centered at the anchor `z`.
The constant depends only on the dimension. The same estimate holds on the cutoff good event
without any relation between `L` and `m`; on the unmodified good event it holds when `m ≤ L`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Paper

/-- Scalar normalization of the four physical energy budgets. -/
theorem aux_l_centered_energy_good_scale_normalize
    (sigma C P A F H : ℝ) (b : Prop) (hsigma : sigma ≠ 0) :
    sigma⁻¹ * (C * (sigma * P + (if b then sigma * A else 0) +
        sigma⁻¹ * F + (if b then sigma * H else 0))) =
      C * P + (if b then C * A else 0) + C * (sigma⁻¹) ^ 2 * F +
        (if b then C * H else 0) := by
  split_ifs <;> field_simp
  all_goals ring

/-- The centered energy estimate at a good scale, including its cutoff variant.
The event disjunction represents exactly the two cases of the paper's statement: the cutoff
event at arbitrary `L`, or the unmodified event with `m ≤ L`. The constant is chosen
before the model, order, cutoff, domain, anchor and data. -/
theorem l_centered_energy_good_scale (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 5 ≤ m →
      ∀ z ∈ cube d (m : ℤ),
      ∀ x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z,
      ∀ omega,
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (originCube d (m : ℤ)) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g) →
        MemFractionalOn (cube d (m : ℤ)) s h.grad →
        ∀ q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x,
          (omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) ∨
            (m ≤ L ∧ omega ∈ goodEvent M none (n + 2) z 1 (s / 8))) →
          let U := truncatedCube d (m : ℤ) (n : ℤ) x
          let a0 := tailAverage M L (n + 2) omega
            (translatedCube d ((n : ℤ) + 2) z)
          a0⁻¹ * normalizedSetAverage
              (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)
              (fun p => _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
                vecNormSq (u.grad p)) ≤
            C * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U (fun p => u.toFun p - averageOn U u.toFun) ^ 2 +
              (if BoundaryTouches U (cube d (m : ℤ)) then
                C * vecNormSq (averageVecOn U h.grad) else 0) +
              C * Real.rpow s (-12 : ℝ) * (a0⁻¹) ^ 2 *
                Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
                (fractionalSeminormOn U s g).toReal ^ 2 +
              (if BoundaryTouches U (cube d (m : ℤ)) then
                C * Real.rpow s (-4 : ℝ) *
                  Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
                  (fractionalSeminormOn U s h.grad).toReal ^ 2 else 0) := by
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension (by norm_num)⟩
  have : NeZero d := ⟨hdpos.ne'⟩
  obtain ⟨Cbd, hCbd, hbrow⟩ :=
    Section6CutoffHarmonic.exists_boundaryStepCellParentRow d
  obtain ⟨Cb, hCb, hrow⟩ :=
    Section6CutoffHarmonic.exists_boundaryCellManuscriptRow_of_boundaryStepCellParentRow
      d hCbd hbrow
  obtain ⟨Ki, hKi, hint⟩ :=
    Section6HolderBelowCutoff.exists_interiorCellEnergy_le_manuscriptPrices_datumCutoff d
  let C := Ki + Cb + 1
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro M s hs L m n hnm z hz x hx omega u h g hdir hgex hh q hq hgoodCases
  obtain ⟨sOrder, hsOrder, hg⟩ := hgex
  subst s
  have hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) := by
    rcases hgoodCases with hgood | ⟨hmL, hgood⟩
    · exact hgood
    · exact (Section6Cutoff.mem_goodEvent_some_iff_none_of_scale_le_cutoff M
        (by omega : n + 2 ≤ L) z 1 (sOrder.1 / 8) omega).mpr hgood
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  have hBud : 0 ≤ harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g :=
    Section6HarmonicBoundary.harmonicPhysicalFourBudgets_nonneg
      M L m n z x omega sOrder.2.1 hsigma.le u h g
  have hraw : normalizedSetAverage
      (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)
      (fun p => _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      C * harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g := by
    by_cases hpatch : openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ)
    · have hhFull : Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad := by
        apply memCubeEuclideanFullWsp_grad_of_memFractionalOn
        simpa only [cube] using hh
      have hi := hint M sOrder hs L m n hnm z x q omega hz hx hq hpatch hgood
        u h g hdir hg hhFull
      have hprices : sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
          normalizedL2On U (fun p => u.toFun p - averageOn U u.toFun) ^ 2 +
          Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2 ≤
          harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g := by
        have ha : 0 ≤ (if BoundaryTouches U (cube d (m : ℤ)) then
            sigma * vecNormSq (averageVecOn U h.grad) else 0) := by
          split_ifs
          · exact mul_nonneg hsigma.le (vecNormSq_nonneg _)
          · exact le_rfl
        have hb : 0 ≤ (if BoundaryTouches U (cube d (m : ℤ)) then
            sigma * Real.rpow sOrder.1 (-4 : ℝ) *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 h.grad).toReal ^ 2 else 0) := by
          split_ifs
          · exact mul_nonneg
              (mul_nonneg (mul_nonneg hsigma.le (Real.rpow_nonneg sOrder.2.1.le _))
                (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)
          · exact le_rfl
        unfold harmonicPhysicalFourBudgets
        dsimp only
        dsimp only [U, sigma] at ha hb ⊢
        linarith only [ha, hb]
      have hi' : normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)
          (fun p => _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
          Ki * harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g := by
        have hi0 := hi.trans (mul_le_mul_of_nonneg_left hprices hKi.le)
        simpa only [sub_sub, show (2 : ℤ) + 2 = 4 by norm_num] using hi0
      exact hi'.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hBud)
    · exact (hrow M sOrder hs L m n hnm z x q omega hz hx hq hpatch hgood
        u h g hdir hg hh).trans
        (mul_le_mul_of_nonneg_right (show Cb ≤ C by dsimp only [C]; linarith) hBud)
  have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hsigma.le)
  dsimp only
  refine hscaled.trans_eq ?_
  unfold harmonicPhysicalFourBudgets
  dsimp only
  have hn := aux_l_centered_energy_good_scale_normalize sigma C
    ((3 : ℝ) ^ (-(2 * (n : ℤ))) *
      normalizedL2On U (fun p => u.toFun p - averageOn U u.toFun) ^ 2)
    (vecNormSq (averageVecOn U h.grad))
    (Real.rpow sOrder.1 (-12 : ℝ) * Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
      (fractionalSeminormOn U sOrder.1 g).toReal ^ 2)
    (Real.rpow sOrder.1 (-4 : ℝ) * Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
      (fractionalSeminormOn U sOrder.1 h.grad).toReal ^ 2)
    (BoundaryTouches U (cube d (m : ℤ))) hsigma.ne'
  convert hn using 1 <;> split_ifs <;> ring

end SubdiffusiveProcess.Paper
