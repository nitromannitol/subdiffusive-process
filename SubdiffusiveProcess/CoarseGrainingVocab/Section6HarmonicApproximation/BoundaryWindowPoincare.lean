import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryZeroSetPoincare
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryTraceMeasure
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.ZeroTrace

/-!
# Boundary-window Poincare at a projected cell

If the scale-`k-1` cube about a cell centre exits the ambient cube, the zero
extension of an ambient `H1_0` datum vanishes on a fixed fraction of the larger
scale-`k+1` cube.  The zero-set Poincare estimate therefore has the physical
scale `3^k`.

PROVENANCE: this is the translated-cell specialization of
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryWindowPoincare.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem mem_axisCube_iff {c : Vec d} {L : ℝ} {y : Vec d} :
    y ∈ axisCube c L ↔ ∀ j, c j < y j ∧ y j < c j + L := by
  simp [axisCube, Set.mem_pi, Set.mem_Ioo]

/-- Failure of local containment produces a strict overhang in one signed
coordinate. -/
theorem exists_signedOverhang_of_not_translatedCube_subset
    {m k : ℤ} {q : Vec d}
    (hnot : ¬ translatedCube d (k - 1) q ⊆ cube d m) :
    ∃ (i : Fin d) (sigma : ℝ), (sigma = 1 ∨ sigma = -1) ∧
      (1 / 2 : ℝ) * (3 : ℝ) ^ m <
        sigma * q i + (1 / 2 : ℝ) * (3 : ℝ) ^ (k - 1) := by
  classical
  rw [Set.not_subset] at hnot
  obtain ⟨p, hp, hpout⟩ := hnot
  have hpLocal := Section6ExcessDecay.mem_translatedCube_iff.mp hp
  rw [cube, mem_openCubeSet_originCube_iff] at hpout
  push_neg at hpout
  obtain ⟨i, hi⟩ := hpout
  rw [cube, mem_openCubeSet_originCube_iff] at hpLocal
  obtain ⟨hlo, hhi⟩ := hpLocal i
  simp only [Pi.sub_apply] at hlo hhi
  by_cases hcase : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < p i
  · have hup := hi hcase
    exact ⟨i, 1, Or.inl rfl, by simp only [one_mul]; linarith only [hup, hhi]⟩
  · push_neg at hcase
    exact ⟨i, -1, Or.inr rfl, by simp only [neg_mul]; linarith only [hcase, hlo]⟩

/-- The exterior slab cut out by the overhang occupies at least one third of
the enclosing scale-`k+1` cube. -/
theorem volume_le_three_mul_projectedBoundarySlab
    {m k : ℤ} {q : Vec d} {sigma : ℝ} {i : Fin d}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hover : (1 / 2 : ℝ) * (3 : ℝ) ^ m <
      sigma * q i + (1 / 2 : ℝ) * (3 : ℝ) ^ (k - 1)) :
    volume (axisCube
        (fun j => q j - (1 / 2 : ℝ) * (3 : ℝ) ^ (k + 1))
        ((3 : ℝ) ^ (k + 1))) ≤
      3 * volume ((axisCube
          (fun j => q j - (1 / 2 : ℝ) * (3 : ℝ) ^ (k + 1))
          ((3 : ℝ) ^ (k + 1))) ∩
        {y | (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ sigma * y i}) := by
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ (k + 1) := zpow_pos (by norm_num) _
  have hbase : (0 : ℝ) < (3 : ℝ) ^ (k - 1) := zpow_pos (by norm_num) _
  have hscale : (3 : ℝ) ^ (k + 1) = 9 * (3 : ℝ) ^ (k - 1) := by
    rw [show k + 1 = (k - 1) + 2 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hsquare : sigma * sigma = 1 := by
    rcases hsigma with h | h <;> rw [h] <;> norm_num
  refine volume_le_three_mul_slab (g := fun y => sigma * y i)
    (e := sigma • basisVec i)
    (lo := sigma * q i - (1 / 2 : ℝ) * (3 : ℝ) ^ (k + 1))
    (hi := sigma * q i + (1 / 2 : ℝ) * (3 : ℝ) ^ (k + 1)) ?_ ?_ ?_ ?_ ?_
  · intro y s
    have hcoord : (y + s • (sigma • basisVec i)) i = y i + s * sigma := by
      simp [basisVec_apply]
    simp only [hcoord]
    rw [show sigma * (y i + s * sigma) = sigma * y i + s * (sigma * sigma) by ring,
      hsquare, mul_one]
  · intro y hy
    rw [mem_axisCube_iff] at hy
    obtain ⟨h1, h2⟩ := hy i
    rcases hsigma with h | h <;> subst h <;>
      exact ⟨by simp only [one_mul, neg_mul]; linarith only [h1, h2],
        by simp only [one_mul, neg_mul]; linarith only [h1, h2]⟩
  · intro y hy s hs1 hs2
    rw [mem_axisCube_iff] at hy ⊢
    intro j
    by_cases hj : j = i
    · subst hj
      obtain ⟨h1, h2⟩ := hy j
      have hcoord : (y + s • (sigma • basisVec j)) j = y j + s * sigma := by
        simp [basisVec_apply]
      simp only [hcoord]
      simp only at h1 h2 hs1 hs2 ⊢
      rcases hsigma with h | h <;> subst h <;>
        simp only [one_mul, neg_mul] at hs1 hs2 ⊢ <;>
        exact ⟨by linarith only [hs1, hs2], by linarith only [hs1, hs2]⟩
    · obtain ⟨h1, h2⟩ := hy j
      have hcoord : (y + s • (sigma • basisVec i)) j = y j := by
        simp [basisVec_apply, hj]
      rw [hcoord]
      exact ⟨h1, h2⟩
  · linarith only [hover, hscale, hbase]
  · linarith only [hover, hscale, hbase]

/-- Dimension-only constant in the projected boundary-window Poincare bound. -/
def projectedBoundaryWindowPoincareConst (d : ℕ) : ℝ :=
  (1 + Real.sqrt 3) * (unitMeanZeroPoincareConst d * 3)

theorem projectedBoundaryWindowPoincareConst_nonneg (d : ℕ) :
    0 ≤ projectedBoundaryWindowPoincareConst d := by
  exact mul_nonneg (by positivity)
    (mul_nonneg (unitMeanZeroPoincareConst_nonneg d) (by norm_num))

/-- Boundary-window Poincare for an ambient zero-trace function, at the scale
of the projected cell. -/
theorem eLpNorm_le_projectedBoundaryWindowPoincare [NeZero d]
    {m k : ℤ} {q : Vec d}
    (hnot : ¬ translatedCube d (k - 1) q ⊆ cube d m)
    (rho : H10Function (openCubeSet (originCube d m))) :
    (eLpNorm rho.toFun 2
        (volume.restrict (translatedCube d (k + 1) q ∩ cube d m))).toReal ≤
      projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k *
        ∑ j : Fin d,
          (eLpNorm (fun x => rho.grad x j) 2
            (volume.restrict (translatedCube d (k + 1) q ∩ cube d m))).toReal := by
  classical
  obtain ⟨i, sigma, hsigma, hover⟩ :=
    exists_signedOverhang_of_not_translatedCube_subset hnot
  let A : Set (Vec d) := axisCube
    (fun j => q j - (1 / 2 : ℝ) * (3 : ℝ) ^ (k + 1)) ((3 : ℝ) ^ (k + 1))
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ (k + 1) := zpow_pos (by norm_num) _
  have hm : MeasurableSet (openCubeSet (originCube d m)) :=
    (isOpen_openCubeSet (originCube d m)).measurableSet
  let E : Set (Vec d) := A ∩ {y | (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ sigma * y i}
  have hEmeas : MeasurableSet E :=
    (isOpen_axisCube _ _).measurableSet.inter
      (measurableSet_le measurable_const (measurable_const.mul (measurable_pi_apply i)))
  have hzero : ∀ y ∈ E, (zeroExtendH1 hm rho A).toFun y = 0 := by
    intro y hy
    refine zeroExtendH1_eq_zero_of_notMem hm rho A ?_
    intro hym
    obtain ⟨hlo, hhi⟩ := mem_openCubeSet_originCube_iff.mp hym i
    have hyout : (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ sigma * y i := hy.2
    rcases hsigma with h | h <;> subst h <;>
      simp only [one_mul, neg_mul] at hyout <;> linarith only [hlo, hhi, hyout]
  have hvol : volume A ≤ ENNReal.ofReal 3 * volume E := by
    have hthree : ENNReal.ofReal (3 : ℝ) = 3 := by simp
    rw [hthree]
    exact volume_le_three_mul_projectedBoundarySlab hsigma hover
  have hcore := eLpNorm_le_of_zeroSet_of_volume_le
    (fun j => q j - (1 / 2 : ℝ) * (3 : ℝ) ^ (k + 1)) hLpos
    (by norm_num : (0 : ℝ) ≤ 3) (zeroExtendH1 hm rho A)
    Set.inter_subset_left hEmeas hzero hvol
  have hAeq : A = translatedCube d (k + 1) q := by
    dsimp [A]
    rw [Section6BoundaryL2.translatedCube_eq_axisCube]
    rfl
  have hvalue : eLpNorm (zeroExtendH1 hm rho A).toFun 2 (volumeMeasureOn A) =
      eLpNorm rho.toFun 2
        (volume.restrict (translatedCube d (k + 1) q ∩ cube d m)) := by
    show eLpNorm (zeroExtend (openCubeSet (originCube d m)) rho.toFun) 2
      (volume.restrict A) = _
    rw [eLpNorm_zeroExtend_eq hm, hAeq, cube]
  have hgrads : ∀ j : Fin d,
      eLpNorm (fun x => (zeroExtendH1 hm rho A).grad x j) 2 (volumeMeasureOn A) =
        eLpNorm (fun x => rho.grad x j) 2
          (volume.restrict (translatedCube d (k + 1) q ∩ cube d m)) := by
    intro j
    show eLpNorm (fun x => zeroExtendGrad (openCubeSet (originCube d m)) rho.grad x j) 2
      (volume.restrict A) = _
    rw [eLpNorm_zeroExtendGrad_eq hm, hAeq, cube]
  rw [hvalue, show (∑ j : Fin d,
      (eLpNorm (fun x => (zeroExtendH1 hm rho A).grad x j) 2
        (volumeMeasureOn A)).toReal) =
      ∑ j : Fin d, (eLpNorm (fun x => rho.grad x j) 2
        (volume.restrict (translatedCube d (k + 1) q ∩ cube d m))).toReal from
      Finset.sum_congr rfl fun j _ => by rw [hgrads j]] at hcore
  have hscale : (1 + Real.sqrt 3) *
      (unitMeanZeroPoincareConst d * (3 : ℝ) ^ (k + 1)) =
      projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k := by
    rw [projectedBoundaryWindowPoincareConst,
      zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  rwa [hscale] at hcore

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
