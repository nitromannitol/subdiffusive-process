module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionCrossingScaleCap

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- A scale cap on the bracket ball rules out a short crossing once the cap,
source radius, and bracket radius satisfy the displayed numerical margins. -/
theorem not_repairedStoppingShortCrossing_of_scaleCap
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (x0 : Vec d) {R S epsilon : ℝ} {k : ℕ}
    (hS : 0 < S)
    (hsrc : ∀ s ∈ source,
      dist (refinedStoppingCenter s) x0 ≤ R + 3 / 2 * S)
    (hcap : ∀ p : RefinedStoppingCell failure omega base,
      dist (refinedStoppingCenter p) x0 ≤ (3 : ℝ) ^ k * R →
        cubeScaleFactor (refinedStoppingFailureCube p) ≤ S)
    (hsmall : 210 * S * epsilon ≤ R)
    (hfar : 2 * R + 240 * S ≤ (3 : ℝ) ^ k * R) :
    ¬ RepairedStoppingShortCrossing source hsource x0 R epsilon k := by
  intro hcross
  obtain ⟨q, ⟨x, hxcell, hxout⟩, hdist⟩ := hcross
  let n := stoppingGraphDistance repairedStoppingGraph source hsource q
  let rho := (3 : ℝ) ^ k * R
  have hpow : 0 ≤ (3 : ℝ) ^ k := pow_nonneg (by norm_num) k
  have hdistReal : (n : ℝ) < epsilon * (3 : ℝ) ^ k := by
    exact Nat.lt_ceil.mp hdist
  have hhalf : 105 * S * epsilon ≤ R / 2 := by
    nlinarith [hsmall]
  have hscaledHalf : 105 * S * epsilon * (3 : ℝ) ^ k ≤ rho / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hhalf hpow
    dsimp only [rho]
    nlinarith [hmul]
  have hstep : 105 * S * (n : ℝ) < rho / 2 := by
    have hmul := mul_lt_mul_of_pos_left hdistReal (by positivity : 0 < 105 * S)
    nlinarith [hmul, hscaledHalf]
  have hguard : R + 3 / 2 * S + 105 * S * (n : ℝ) ≤ rho := by
    dsimp only [rho] at hfar ⊢
    nlinarith [hstep, hfar, hS]
  have hcenter : dist (refinedStoppingCenter q) x0 ≤
      R + 3 / 2 * S + 105 * S * (n : ℝ) := by
    exact dist_refinedStoppingCenter_le_of_stoppingGraphDistance_le
      hinitial hrepair source hsource x0 hS.le hsrc hcap n hguard q le_rfl
  have hcenterBall : dist (refinedStoppingCenter q) x0 ≤ rho :=
    hcenter.trans hguard
  have hside : cubeScaleFactor (refinedStoppingFailureCube q) ≤ S :=
    hcap q hcenterBall
  have hxcenter : dist x (refinedStoppingCenter q) < S / 2 := by
    have hx := dist_refinedStoppingCenter_lt_of_mem hxcell
    rw [dist_comm] at hx
    nlinarith [hx, hside]
  have hxradius : rho ≤ dist x x0 := by
    rw [Set.mem_compl_iff, Metric.mem_ball] at hxout
    exact not_lt.mp hxout
  have htriangle : dist x x0 ≤
      dist x (refinedStoppingCenter q) +
        dist (refinedStoppingCenter q) x0 :=
    dist_triangle x (refinedStoppingCenter q) x0
  have hrho : rho < R + 2 * S + 105 * S * (n : ℝ) := by
    nlinarith [hxradius, htriangle, hxcenter, hcenter]
  dsimp only [rho] at hrho hstep hfar
  nlinarith [hrho, hstep, hfar, hS]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
