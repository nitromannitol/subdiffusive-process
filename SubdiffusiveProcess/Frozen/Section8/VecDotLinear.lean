module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FrozenNamespace

@[expose] public section

open Homogenization

noncomputable section
open SubdiffusiveProcess.Frozen.Section8


def SubdiffusiveProcess.Frozen.Section8.vecDotLinear (d : ℕ) : Vec d →ₗ[ℝ] Vec d →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ vecDot
    (by intros; simp [vecDot, Finset.sum_add_distrib, add_mul])
    (by intros; simp [vecDot, Finset.mul_sum, mul_assoc])
    (by intros; simp [vecDot, Finset.sum_add_distrib, mul_add])
    (by intros; simp [vecDot, Finset.mul_sum, mul_left_comm])


