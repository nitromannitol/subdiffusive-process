import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitDepthSelection
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.GlobalRepresentative

/-!
# Safe subset readout for literal oscillations

The project oscillation is a conditional supremum.  Monotonicity therefore
requires an explicit bounded-above witness; it cannot be inferred from an
inequality about `sSup` alone.  These lemmas provide that witness from
continuity on a compact closed ball and then perform the target-set readout.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The closed ball at every selected contraction depth stays strictly
inside the ambient translated cube.  This supplies the compact carrier on
which the global canonical representative is continuous. -/
theorem selectedSubunit_closedBall_subset_translatedCube
    [NeZero d] {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {L : ℕ}
    {m : ℤ} {z z' : Vec d}
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    {p : Fin d → ℤ} {n : ℕ}
    (hballCell : euclideanBall z'
      (boundedMultiplierLocalRadius M L m z omega) ⊆
        boundedMultiplierCoverCell d m z p) :
    Metric.closedBall z'
        ((boundedMultiplierLocalRadius M L m z omega / 2) /
          (2 * (d : ℝ)) *
            (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))) ⊆
      translatedCube d m z := by
  let R := boundedMultiplierLocalRadius M L m z omega
  let r := (R / 2) / (2 * (d : ℝ)) *
    (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))
  have hdNat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hR : 0 < R := boundedMultiplierLocalRadius_pos M L m z omega
  have hpowPos : 0 < (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpowLt : (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    exact neg_lt_zero.mpr (by positivity)
  have hrlt : r < R / (2 * (d : ℝ)) := by
    dsimp only [r]
    have hden : 0 < 2 * (d : ℝ) := mul_pos (by norm_num) hd
    have hquarter : (R / 2) / (2 * (d : ℝ)) <
        R / (2 * (d : ℝ)) := by
      exact div_lt_div_of_pos_right (by linarith) hden
    exact (mul_lt_of_lt_one_right (by positivity) hpowLt).trans hquarter
  have hclosed : Metric.closedBall z' r ⊆
      Metric.ball z' (R / (2 * (d : ℝ))) :=
    Metric.closedBall_subset_ball hrlt
  have hmetric : Metric.ball z' (R / (2 * (d : ℝ))) ⊆
      euclideanBall z' ((d : ℝ) * (R / (2 * (d : ℝ)))) :=
    metricBall_subset_euclideanBall_dimension z' _
  have heq : (d : ℝ) * (R / (2 * (d : ℝ))) = R / 2 := by
    field_simp [hd.ne']
  have heuc : euclideanBall z' ((d : ℝ) * (R / (2 * (d : ℝ)))) ⊆
      euclideanBall z' R := by
    rw [heq]
    exact euclideanBall_subset_euclideanBall (by positivity) (by linarith)
  simpa only [R, r] using
    hclosed.trans (hmetric.trans (heuc.trans
      (hballCell.trans Set.inter_subset_left)))

/-- Continuity on the compact closed ball bounds all pairwise differences
on its open ball. -/
theorem bddAbove_oscillationValues_metricBall_of_continuousOn_closedBall
    {x : Vec d} {r : ℝ} {f : Vec d → ℝ}
    (hcont : ContinuousOn f (Metric.closedBall x r)) :
    BddAbove {q : ℝ | ∃ u ∈ Metric.ball x r, ∃ v ∈ Metric.ball x r,
      q = |f u - f v|} := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn
    hcont.norm
  refine ⟨2 * C, ?_⟩
  rintro q ⟨u, hu, v, hv, rfl⟩
  have huC : |f u| ≤ C := by
    simpa only [Real.norm_eq_abs, abs_abs] using
      hC u (Metric.ball_subset_closedBall hu)
  have hvC : |f v| ≤ C := by
    simpa only [Real.norm_eq_abs, abs_abs] using
      hC v (Metric.ball_subset_closedBall hv)
  exact (abs_sub (f u) (f v)).trans (by linarith)

/-- Literal oscillation is monotone under set inclusion once the larger
pair-difference carrier is explicitly known to be bounded above. -/
theorem oscillationOn_le_of_subset_of_bddAbove
    {S T : Set (Vec d)} {f : Vec d → ℝ}
    (hS : S.Nonempty) (hsub : S ⊆ T)
    (hbdd : BddAbove {q : ℝ | ∃ x ∈ T, ∃ y ∈ T,
      q = |f x - f y|}) :
    oscillationOn S f ≤ oscillationOn T f := by
  unfold oscillationOn
  apply csSup_le
  · obtain ⟨x, hx⟩ := hS
    exact ⟨0, x, hx, x, hx, by simp⟩
  · intro q hq
    rcases hq with ⟨x, hx, y, hy, rfl⟩
    exact le_csSup hbdd ⟨x, hsub hx, y, hsub hy, rfl⟩

/-- Safe target-to-ball oscillation readout.  The continuity premise is the
explicit boundedness certificate omitted by an unconditional `sSup`
monotonicity argument. -/
theorem oscillationOn_le_of_subset_metricBall
    {S : Set (Vec d)} {x : Vec d} {r K : ℝ} {f : Vec d → ℝ}
    (hS : S.Nonempty) (hsub : S ⊆ Metric.ball x r)
    (hcont : ContinuousOn f (Metric.closedBall x r))
    (hball : oscillationOn (Metric.ball x r) f ≤ K) :
    oscillationOn S f ≤ K := by
  exact (oscillationOn_le_of_subset_of_bddAbove hS hsub
    (bddAbove_oscillationValues_metricBall_of_continuousOn_closedBall
      hcont)).trans hball

/-- Complete deep-target oscillation readout.  The selected local-ball
oscillation is transferred to the literal target cube using the global
canonical representative and an explicit compact boundedness certificate. -/
theorem exists_middleHalfSubcube_deepTargetOscillation_caccioppoli
    [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) (j : ℕ)
    {B' : Set (Vec d)} (hB' : IsMiddleHalfSubcube m z j B')
    (omega : PotentialSample d)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d m z))
    (hthetaPos : ∀ y ∈ translatedCube d m z, 0 < theta y)
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d m z) h)
    (hfirst : 1 / 2 * (3 : ℝ) ^ (m - j) ≤
      boundedMultiplierLocalRadius M L m z omega /
        (12 * (d : ℝ))) :
    ∃ n : ℕ, ∃ z' : Vec d, ∃ p ∈ shellCoverShifts d m,
      B' = translatedCube d (m - j) z' ∧
      z' ∈ boundedMultiplierCoverCell d m z p ∧
      euclideanBall z' (boundedMultiplierLocalRadius M L m z omega) ⊆
        boundedMultiplierCoverCell d m z p ∧
      oscillationOn B' (euclideanBallAverageRepresentative h.toFun) ≤
        smallContrastSchauderConstant d *
            halfBallCaccioppoliDataPrice d z'
              (boundedMultiplierLocalRadius M L m z omega) h.toFun
              (averageOn (boundedMultiplierCoverCell d m z p) h.toFun) *
          (boundedMultiplierLocalRadius M L m z omega / 2) *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) ∧
      (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) ≤
        Real.sqrt
          (36 * (d : ℝ) * (1 / 2 * (3 : ℝ) ^ (m - j)) /
            boundedMultiplierLocalRadius M L m z omega) := by
  obtain ⟨n, z', p, hp, hB'eq, hsub, hz'cell, hballCell,
      hcontract, hdecay⟩ :=
    exists_middleHalfSubcube_selectedSubunitDepth_caccioppoli
      hd M L m z j hB' omega hthetaCont hb hthetaClose hharm hfirst
  let s : Vec d → ℝ := fun y ↦ aCutoff M L omega y * theta y
  have hsCont : ContinuousOn s (translatedCube d m z) :=
    (continuous_aCutoff M L omega).continuousOn.mul hthetaCont
  have hsPos : ∀ y ∈ translatedCube d m z, 0 < s y := by
    intro y hy
    exact mul_pos (aCutoff_pos M L omega y) (hthetaPos y hy)
  have hcubeOpen : IsOpen (translatedCube d m z) := by
    rw [translatedCube_eq_metricBall]
    exact Metric.isOpen_ball
  have hrep := continuousOn_and_ae_eq_euclideanBallAverageRepresentative
    hd hcubeOpen hsCont hsPos hharm
  have hclosed := selectedSubunit_closedBall_subset_translatedCube
    (M := M) (L := L) (m := m) (z := z) (z' := z')
      (omega := omega) (p := p) (n := n) hballCell
  have hcontClosed := hrep.1.mono hclosed
  have hB'ne : B'.Nonempty := by
    refine ⟨z', ?_⟩
    rw [hB'eq, SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.mem_translatedCube_iff,
      sub_self]
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.zero_mem_cube d (m - j)
  have htarget := oscillationOn_le_of_subset_metricBall
    hB'ne hsub hcontClosed hcontract
  exact ⟨n, z', p, hp, hB'eq, hz'cell, hballCell, htarget, hdecay⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
