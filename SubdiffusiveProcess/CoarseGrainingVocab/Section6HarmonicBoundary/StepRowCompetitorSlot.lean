import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergy




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ}

/-- **The boundary Caccioppoli row with a competitor-energy slot.**

For any competitor `v` solving the same forced equation on the cube and having
localized zero trace difference with `u` through the patch, the core coefficient
energy of `u` is bounded by the parent `L²` distance to `v` (with the printed
Caccioppoli prefactor) plus a dimension-only multiple of *any* upper bound `Hv`
for the competitor's own parent coefficient energy.

No Besov norm of the boundary datum occurs, and hence no negative power of the
Besov order. -/
theorem exists_boundaryCaccioppoliEnergy_of_competitorEnergy (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} {x : Vec d}
        {g : Vec d → Vec d}
        (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (Hv : ℝ),
        IsForcedEquation Q a u g → IsForcedEquation Q a v g →
        Ch01.LocalizedZeroTraceFunctionOn
          (Ch02.cubeDomain Q : Set (Vec d)) (openCubeAtScale x (Q.scale - 1))
          (fun y => u.toFun y - v.toFun y) →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        x ∈ openCubeSet Q →
        localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v ≤ Hv →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            2 * (caccioppoliWithRHSPrefactor C Q a s t *
                (Ch02.lambdaS Q t a *
                  (3 : ℝ) ^ (-(2 * Q.scale)) *
                  normalizedL2SqOnSet (openCubeSet Q)
                    (fun y => u.toFun y - v.toFun y))) +
              2 * ((18 : ℝ) ^ d * Hv) := by
  obtain ⟨C, hC, hcacc⟩ := exists_boundaryCaccioppoliEnergy_ofDifference d
  refine ⟨C, hC, ?_⟩
  intro Q a s t x g u v Hv hu hv hdiff hs hs1 ht ht2 hst hx hHv
  have hd := hcacc u v hu hv hdiff hs hs1 ht ht2 hst hx
  have hvcore := localizedCoeffEnergyValue_core_le_eighteen_pow_mul_parent
    (a := a) hx v
  have hvHv : localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) v ≤
      (18 : ℝ) ^ d * Hv :=
    hvcore.trans (mul_le_mul_of_nonneg_left hHv (by positivity))
  have hmink := localizedCoeffEnergyValue_core_le_two_mul_sub_add
    (x := x) (a := a) u v
  linarith only [hmink, hd, hvHv]

/-- Splitting the parent `L²` distance at an arbitrary scalar. -/
theorem normalizedL2SqOnSet_sub_le_two_mul_add {d : ℕ} {W : Set (Vec d)}
    {f g : Vec d → ℝ} (hf : MemLp f 2 (MeasureTheory.volume.restrict W))
    (hg : MemLp g 2 (MeasureTheory.volume.restrict W)) :
    normalizedL2SqOnSet W (fun y => f y - g y) ≤
      2 * normalizedL2SqOnSet W f + 2 * normalizedL2SqOnSet W g := by
  have hneg : MemLp (fun y => -g y) 2 (MeasureTheory.volume.restrict W) := by
    simpa using hg.neg
  have hmink := Section6Iteration.normalizedL2On_add_le (W := W) (f := f)
    (g := fun y => -g y) hf hneg
  have hsub : (fun y => f y + -g y) = fun y => f y - g y := by
    funext y; ring
  rw [hsub] at hmink
  have hnegEq : normalizedL2On W (fun y => -g y) =
      normalizedL2On W g := by
    unfold normalizedL2On
    refine congrArg Real.sqrt (congrArg (Homogenization.volumeAverage W) ?_)
    funext y; ring
  rw [hnegEq] at hmink
  have h0f : 0 ≤ normalizedL2On W f :=
    Real.sqrt_nonneg _
  have h0g : 0 ≤ normalizedL2On W g :=
    Real.sqrt_nonneg _
  have hsq : normalizedL2On W (fun y => f y - g y) ^ 2 ≤
      (normalizedL2On W f +
        normalizedL2On W g) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hmink 2
  have hexpand :
      (normalizedL2On W f +
          normalizedL2On W g) ^ 2 ≤
        2 * normalizedL2On W f ^ 2 +
          2 * normalizedL2On W g ^ 2 := by
    nlinarith only [sq_nonneg (normalizedL2On W f -
      normalizedL2On W g)]
  have hid : ∀ p : Vec d → ℝ,
      normalizedL2SqOnSet W p = normalizedL2On W p ^ 2 := by
    intro p
    rw [Section6Iteration.normalizedL2On_sq]
    rfl
  rw [hid, hid, hid]
  linarith only [hsq, hexpand]

/-- **The competitor-slot boundary Caccioppoli row, centred at a scalar.**

The parent leg of the previous theorem is split at an arbitrary scalar `c₀`,
leaving the competitor's own oscillation as a separate carrier.  Choosing
`c₀ = (v)_Q` makes that carrier the competitor's parent oscillation, which the
coarse `L²` Poincare inequality prices by the *same* `Hv`; the manuscript's
datum-centred scalar `(h)_Q` is then never used, and with it disappears the
`t^{-3}` that report §12.4 records on the datum **mean**. -/
theorem exists_boundaryCaccioppoliEnergy_of_competitorEnergy_centered
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} {x : Vec d}
        {g : Vec d → Vec d}
        (u v : H1Function (openCubeSet Q)) (c0 Hv : ℝ),
        IsForcedEquation Q a u g → IsForcedEquation Q a v g →
        Ch01.LocalizedZeroTraceFunctionOn
          (Ch02.cubeDomain Q : Set (Vec d)) (openCubeAtScale x (Q.scale - 1))
          (fun y => u.toFun y - v.toFun y) →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        x ∈ openCubeSet Q →
        localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v ≤ Hv →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            4 * (caccioppoliWithRHSPrefactor C Q a s t *
                (Ch02.lambdaS Q t a *
                  (3 : ℝ) ^ (-(2 * Q.scale)) *
                  normalizedL2SqOnSet (openCubeSet Q)
                    (fun y => u.toFun y - c0))) +
              4 * (caccioppoliWithRHSPrefactor C Q a s t *
                (Ch02.lambdaS Q t a *
                  (3 : ℝ) ^ (-(2 * Q.scale)) *
                  normalizedL2SqOnSet (openCubeSet Q)
                    (fun y => v.toFun y - c0))) +
              2 * ((18 : ℝ) ^ d * Hv) := by
  obtain ⟨C, hC, hslot⟩ := exists_boundaryCaccioppoliEnergy_of_competitorEnergy d
  refine ⟨C, hC, ?_⟩
  intro Q a s t x g u v c0 Hv hu hv hdiff hs hs1 ht ht2 hst hx hHv
  have hraw := hslot u v Hv hu hv hdiff hs hs1 ht ht2 hst hx hHv
  have hmemu : MemLp (fun y => u.toFun y - c0) 2
      (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    u.memL2.sub (memLp_const c0)
  have hmemv : MemLp (fun y => v.toFun y - c0) 2
      (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    v.memL2.sub (memLp_const c0)
  have hsplit : normalizedL2SqOnSet (openCubeSet Q)
      (fun y => u.toFun y - v.toFun y) ≤
      2 * normalizedL2SqOnSet (openCubeSet Q) (fun y => u.toFun y - c0) +
        2 * normalizedL2SqOnSet (openCubeSet Q) (fun y => v.toFun y - c0) := by
    have := normalizedL2SqOnSet_sub_le_two_mul_add hmemu hmemv
    have hfun : (fun y => (u.toFun y - c0) - (v.toFun y - c0)) =
        fun y => u.toFun y - v.toFun y := by funext y; ring
    rwa [hfun] at this
  have hpref : 0 ≤ caccioppoliWithRHSPrefactor C Q a s t :=
    caccioppoliWithRHSPrefactor_nonneg hC.le hs ht hst
  have hlam : 0 ≤ Ch02.lambdaS Q t a := by
    rw [Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)
  have hscale : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * Q.scale)) := by positivity
  have hmul : caccioppoliWithRHSPrefactor C Q a s t *
      (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
        normalizedL2SqOnSet (openCubeSet Q)
          (fun y => u.toFun y - v.toFun y)) ≤
      caccioppoliWithRHSPrefactor C Q a s t *
        (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
          (2 * normalizedL2SqOnSet (openCubeSet Q) (fun y => u.toFun y - c0) +
            2 * normalizedL2SqOnSet (openCubeSet Q)
              (fun y => v.toFun y - c0))) := by
    refine mul_le_mul_of_nonneg_left ?_ hpref
    exact mul_le_mul_of_nonneg_left hsplit (mul_nonneg hlam hscale)
  nlinarith only [hraw, hmul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
