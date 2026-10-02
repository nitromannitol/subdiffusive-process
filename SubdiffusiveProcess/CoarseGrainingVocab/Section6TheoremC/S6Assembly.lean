import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ComparisonConvergence
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.LimitPassage

/-!
# S6 assembly: from the energy limit to the displays (B4)

`ComparisonConvergence` (B3) delivers the Dirichlet energy limit
`∫_{𝔠_m}|∇u_N − ∇u|² → 0`.  `LimitPassage` (block five) moves a two-sided
seminorm estimate across a limit, but consumes convergence stated in the
*seminorm* `vectorNormalizedL2On`, not in the raw energy integral.

This file is the seam.  The normalized seminorm is the square root of the
volume-averaged energy,

```
‖g‖_{L̲²(W)}²  =  |W|⁻¹ · ∫_W |g|² ,
```

so the energy limit gives the seminorm limit by continuity of `√·` at `0`.
Composing the two closes S6 for the energy display, which is the half that moves
with both the solution and the coefficient.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The vector seminorm is the square root of the volume-averaged energy. -/
theorem vectorNormalizedL2On_eq_sqrt (W : Set (Vec d)) (g : Vec d → Vec d) :
    vectorNormalizedL2On W g =
      Real.sqrt ((volume W).toReal⁻¹ * ∫ x in W, vecNormSq (g x) ∂volume) := by
  rw [vectorNormalizedL2On, normalizedL2On, volumeAverage]
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  exact euclideanNorm_sq (g x)

/-- **B4, the seam.**  A vanishing Dirichlet energy gives a vanishing seminorm. -/
theorem tendsto_vectorNormalizedL2On_of_tendsto_energy {W : Set (Vec d)}
    {G : ℕ → Vec d → Vec d}
    (hE : Tendsto (fun N ↦ ∫ x in W, vecNormSq (G N x) ∂volume) atTop
      (nhds 0)) :
    Tendsto (fun N ↦ vectorNormalizedL2On W (G N)) atTop (nhds 0) := by
  have hscaled : Tendsto
      (fun N ↦ (volume W).toReal⁻¹ * ∫ x in W, vecNormSq (G N x) ∂volume)
      atTop (nhds 0) := by
    simpa using hE.const_mul ((volume W).toReal⁻¹)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hscaled
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun N ↦ ?_
  exact (vectorNormalizedL2On_eq_sqrt W (G N)).symm

/-- **S6 for the energy display, assembled.**  Given the energy convergence of
B3 on each of the two windows, the two-sided estimate
`e.large.scale.energy.multifractal` passes from the comparison solutions to the
limit.

`F N` is the composite field `√(ã_N)∇u_N` and `Flim` is `√(a)∇u`; the
hypothesis is stated on the difference, as `LimitPassage` requires, because the
field moves with both the solution and the coefficient. -/
theorem vectorNormalizedL2On_le_mul_of_tendsto_energy {V W : Set (Vec d)}
    {F : ℕ → Vec d → Vec d} {Flim : Vec d → Vec d} {K : ℝ}
    (hFV : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x)) 2 (volume.restrict V))
    (hFlimV : MemLp (fun x ↦ euclideanNorm (Flim x)) 2 (volume.restrict V))
    (hFsubV : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x - Flim x)) 2
      (volume.restrict V))
    (hEV : Tendsto (fun N ↦ ∫ x in V, vecNormSq (F N x - Flim x) ∂volume)
      atTop (nhds 0))
    (hFW : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x)) 2 (volume.restrict W))
    (hFlimW : MemLp (fun x ↦ euclideanNorm (Flim x)) 2 (volume.restrict W))
    (hFsubW : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x - Flim x)) 2
      (volume.restrict W))
    (hEW : Tendsto (fun N ↦ ∫ x in W, vecNormSq (F N x - Flim x) ∂volume)
      atTop (nhds 0))
    (hle : ∀ j, vectorNormalizedL2On V (F j) ≤
      K * vectorNormalizedL2On W (F j)) :
    vectorNormalizedL2On V Flim ≤ K * vectorNormalizedL2On W Flim :=
  vectorNormalizedL2On_le_mul_of_tendsto hFV hFlimV hFsubV
    (tendsto_vectorNormalizedL2On_of_tendsto_energy hEV)
    hFW hFlimW hFsubW
    (tendsto_vectorNormalizedL2On_of_tendsto_energy hEW) hle

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
