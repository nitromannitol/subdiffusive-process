module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.InhomogeneousForcingCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffGoodStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.GoodStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowMean
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffInputs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.RecurrenceBudget

@[expose] public section

/-!
# Hölder Step 3: `e.ready.for.iteration.lemma`

This module normalizes the raw good-scale recurrence by the parent coefficient,
the top forcing seminorm, and the top boundary norms.  Its conclusion is in
the exact `epsilon_j * |slope| + defect_j` form consumed by the iteration
lemma.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable

private theorem inverse_local_le_cut {a b E : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a / b ≤ E) : b⁻¹ ≤ E * a⁻¹ := by
  calc
    b⁻¹ = (a / b) * a⁻¹ := by field_simp
    _ ≤ E * a⁻¹ := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr ha.le)

/-- The concrete one-step inequality `e.ready.for.iteration.lemma`. -/
theorem exists_boundaryRowTwoCutoffReadyStep {d : ℕ} [NeZero d]
    (hExcess : BoundaryCutoffHolderExcessDecayInputV4 d) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ epsilon ∈ Set.Icc
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
      ∀ k : ℕ, 0 < k → ∀ theta : ℝ,
      ∀ L m n j : ℕ, n ≤ j → k ≤ j → j + 5 ≤ m →
      ∀ z ∈ cube d m, ∀ omega,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d m) u h g →
        MemHolder (cube d m) (1 / 2) g →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d,
          ell ∈ affineMinimizers (truncatedCube d m j z) u.toFun →
          omega ∈ goodEvent M (some L) (j + 2) z epsilon
            Section6Stopping.holderStoppingS →
          C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                  (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) ≤ theta ^ k →
          ∀ exponential : ℝ, 0 ≤ exponential →
          tailCoefficientCubeAverage M L m omega /
              tailAverage M L (j + 2) omega
                (translatedCube d (j + 2 : ℕ) z) ≤ exponential →
          let Keps := C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K
          let Kforce := C * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
          let Kmean := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)
          let Kboundary := C * (1 / 4 : ℝ) ^ (-3 : ℤ) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
          excess (j - k) (truncatedCube d m (j - k) z) u.toFun ≤
            theta ^ k * excess j (truncatedCube d m j z) u.toFun +
              holderRecurrenceEpsilon_cut L Keps M epsilon
                  Section6Stopping.holderStoppingS j z omega *
                Real.sqrt (vecNormSq ell.slope) +
              holderReadyDefect_cut Kforce Kmean Kboundary
                ((3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2))) exponential
                ((tailCoefficientCubeAverage M L m omega)⁻¹ *
                  (3 : ℝ) ^ ((m : ℝ) / 2) *
                  holderSeminormOn (cube d m) (1 / 2) g)
                (holderRecurrenceEpsilon_cut L Keps M epsilon
                  Section6Stopping.holderStoppingS j z omega)
                (vectorSupNormOn (cube d m) h.grad)
                ((3 : ℝ) ^ ((m : ℝ) / 2) *
                  holderSeminormOn (cube d m) (1 / 2) h.grad)
                (if BoundaryTouches (truncatedCube d m j z) (cube d m) then 1 else 0) := by
  obtain ⟨C, K, hC, hK, hraw⟩ := exists_boundaryRowTwoCutoffGoodStepRaw hExcess
  refine ⟨C, K, hC, hK, ?_⟩
  intro M hsmall epsilon hepsilon k hk theta L m n j hnj hkj hjm z hz omega
    u h g hsol hg hh ell hell hgood hcontract exponential hE0 hratio
  dsimp only
  have hgfrac : ∃ sOrder : FractionalOrder, sOrder.1 = (1 / 4 : ℝ) ∧
      Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d m) sOrder FiniteLpExponent.two g :=
    Section6ExcessDecay.exists_fractionalOrder_memCubeEuclideanFullWsp_of_memHolder
      (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)) (by norm_num) le_rfl hg
  have hstep := hraw M hsmall epsilon hepsilon k hk L m j hkj hjm z hz omega
    u h g hsol hgfrac hh ell hell hgood
  let Keps := C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K
  let epsJ := holderRecurrenceEpsilon_cut L Keps M epsilon
    Section6Stopping.holderStoppingS j z omega
  have hepsEq : epsJ = Keps * min epsilon (M.delta ^ 2 + epsilon ^ 8 +
      accumulatedError M (some L) (j + 2) z Section6Stopping.holderStoppingS omega) := by
    simp only [epsJ, holderRecurrenceEpsilon_cut, ite_eq_left hgood, mul_one]
  have htop : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hlocal : 0 < tailAverage M L (j + 2) omega
      (translatedCube d (j + 2 : ℕ) z) := by
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (j + 2) (translatePotentialSample z omega)
  have hinv := inverse_local_le_cut htop hlocal hratio
  have hforcingLocal := forcing_fractional_window_le
    (m := (m : ℤ)) (j := (j : ℤ)) (x := z) (g := g) (s := (1 / 4 : ℝ))
    hz (by norm_num) (by norm_num) hg
  have hforcing :
      C * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (tailAverage M L (j + 2) omega
            (translatedCube d (j + 2 : ℕ) z))⁻¹ *
          (3 : ℝ) ^ ((1 / 4 : ℝ) * j) *
          (fractionalSeminormOn (truncatedCube d m j z) (1 / 4 : ℝ) g).toReal ≤
        (C * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)) *
          (3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2)) * exponential *
          ((tailCoefficientCubeAverage M L m omega)⁻¹ *
            (3 : ℝ) ^ ((m : ℝ) / 2) *
            holderSeminormOn (cube d m) (1 / 2) g) := by
    let coef := C * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
      (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
    have hcoef : 0 ≤ coef := by
      dsimp only [coef]
      positivity
    have h1 := mul_le_mul_of_nonneg_left hforcingLocal
      (mul_nonneg hcoef (inv_nonneg.mpr hlocal.le))
    have hsemi0 := holderSeminormOn_nonneg hg
    let D := coef * Section6ExcessDecay.fractionalHolderConst d *
      Real.sqrt (1 / 4 : ℝ) * (3 : ℝ) ^ ((j : ℝ) / 2) *
      holderSeminormOn (cube d m) (1 / 2) g
    have hD0 : 0 ≤ D := by
      dsimp only [D]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hcoef (Section6ExcessDecay.fractionalHolderConst_nonneg d))
            (Real.sqrt_nonneg _))
          (Real.rpow_nonneg (by norm_num) _))
        hsemi0
    have h2 := mul_le_mul_of_nonneg_right hinv hD0
    dsimp only [D, coef] at h1 h2
    have hscale : (3 : ℝ) ^ ((j : ℝ) / 2) =
        (3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2)) *
          (3 : ℝ) ^ ((m : ℝ) / 2) := by
      simpa only [Int.cast_natCast] using three_half_scale_decay (m : ℤ) (j : ℤ)
    norm_num only [Int.cast_natCast] at h1
    rw [hscale] at h1 h2
    ring_nf at h1 h2 ⊢
    linarith only [h1, h2]
  have hmean := sqrt_vecNormSq_averageVecOn_truncatedCube_le_vectorSupNormOn_cube
    (j := (j : ℤ)) h hz (by omega) hh
  have hmeanTerm :
      C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K *
          min epsilon (M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M (some L) (j + 2) z Section6Stopping.holderStoppingS omega) *
          (if BoundaryTouches (truncatedCube d m j z) (cube d m) then
            (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
              Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m j z) h.grad))
          else 0) ≤
        (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsJ *
          vectorSupNormOn (cube d m) h.grad *
          (if BoundaryTouches (truncatedCube d m j z) (cube d m) then 1 else 0) := by
    rw [hepsEq]
    by_cases hb : BoundaryTouches (truncatedCube d m j z) (cube d m)
    · simp only [ite_eq_left hb, mul_one]
      have hnonneg : 0 ≤ Keps * min epsilon (M.delta ^ 2 + epsilon ^ 8 +
          accumulatedError M (some L) (j + 2) z Section6Stopping.holderStoppingS omega) *
          (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) := by
        have hlower : 0 ≤ Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 :=
          mul_nonneg (inv_nonneg.mpr Section6Stopping.holderStoppingS_pos.le)
            (sq_nonneg M.delta)
        have he0 : 0 ≤ epsilon := hlower.trans hepsilon.1
        have herr := accumulatedError_nonneg M (some L) Section6Stopping.holderStoppingS
          (j + 2) z omega
        have hmin0 : 0 ≤ min epsilon (M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M (some L) (j + 2) z Section6Stopping.holderStoppingS omega) :=
          le_min he0 (by positivity)
        dsimp only [Keps]
        positivity
      have hmul := mul_le_mul_of_nonneg_left hmean hnonneg
      dsimp only [Keps] at hmul ⊢
      nlinarith only [hmul]
    · simp only [ite_eq_right hb, mul_zero]
      exact le_rfl
  have hholder := holderSeminormOn_mono (by norm_num) hh
    (truncatedCube_subset_cube d m j z)
  have hboundary :
      (if BoundaryTouches (truncatedCube d m j z) (cube d m) then
        C * (1 / 4 : ℝ) ^ (-3 : ℤ) *
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (3 : ℝ) ^ ((j : ℝ) / 2) *
          holderSeminormOn (truncatedCube d m j z) (1 / 2) h.grad
      else 0) ≤
        (C * (1 / 4 : ℝ) ^ (-3 : ℤ) *
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
          (3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            holderSeminormOn (cube d m) (1 / 2) h.grad) *
          (if BoundaryTouches (truncatedCube d m j z) (cube d m) then 1 else 0) := by
    by_cases hb : BoundaryTouches (truncatedCube d m j z) (cube d m)
    · simp only [ite_eq_left hb, mul_one]
      have hcoefB : 0 ≤ C * (1 / 4 : ℝ) ^ (-3 : ℤ) *
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2)) *
          (3 : ℝ) ^ ((m : ℝ) / 2) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hholder hcoefB
      have hscale : (3 : ℝ) ^ ((j : ℝ) / 2) =
          (3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2)) *
            (3 : ℝ) ^ ((m : ℝ) / 2) := by
        simpa only [Int.cast_natCast] using three_half_scale_decay (m : ℤ) (j : ℤ)
      rw [hscale]
      nlinarith only [hmul]
    · simp only [ite_eq_right hb, mul_zero]
      exact le_rfl
  have hEx0 : 0 ≤ excess j (truncatedCube d m j z) u.toFun := by
    rw [Section6Iteration.excess_eq_affineExcessScaled]
    exact Section6Iteration.affineExcessScaled_nonneg _ _ _
  have hcontractTerm := mul_le_mul_of_nonneg_right hcontract hEx0
  rw [← hepsEq] at hstep hmeanTerm
  unfold holderReadyDefect_cut
  change excess (j - k) (truncatedCube d m (j - k) z) u.toFun ≤
    theta ^ k * excess j (truncatedCube d m j z) u.toFun +
      epsJ * Real.sqrt (vecNormSq ell.slope) +
      (_ * _ * _ * _ + _ * epsJ * _ * _ + _ * _ * _ * _)
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hstep hcontractTerm hforcing hmeanTerm hboundary ⊢
  nlinarith only [hstep, hcontractTerm, hforcing, hmeanTerm, hboundary]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
