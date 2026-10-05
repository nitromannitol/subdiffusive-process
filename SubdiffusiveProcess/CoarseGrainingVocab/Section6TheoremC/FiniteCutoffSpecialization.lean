module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CubeGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ZeroDatum
public import SubdiffusiveProcess.Section6.Defs.HolderRegularityConclusions

@[expose] public section

/-!
# The interior harmonic specialization of the Hölder regularity conclusions

This file proves the first sentence of the proof of Theorem C
(`t.large.scale.Holder.multifractal`), :

> For finite `L`, the two estimates are the interior, harmonic specialization
> of Proposition `p.cutoff.Holder.regularity`: take `g = 0`, `x = z`, and
> `ℓ = n` in `e.Holder.estimate.boxes.local`, and use
> `e.energy.density.estimate`.

`HolderRegularityConclusions` is the
three-clause conclusion package shared by `p.Holder.regularity` and
`p.cutoff.Holder.regularity`.  It is a *definition*, so it may be
imported directly; no hypothesis-shaping against the still-anchor
`p.cutoff.Holder.regularity` is needed for this step.  What the two theorems
below take as input is precisely that package, instantiated at the zero
divergence datum `g = 0` and at the boundary datum `h = u`.

The output is byte-for-byte the pair of displays of Theorem C,
`e.large.scale.Holder.multifractal`  and
`e.large.scale.energy.multifractal`, on the
untruncated window `z + 𝔠_n`.

Three specializations do the work:

* `ℓ = n` makes the gain factor `3^{α(n-ℓ)}` on the left of
  `e.Holder.estimate.boxes.local` equal to one;
* `x = y = z` with the interior hypothesis `z + 𝔠_n ⊆ 𝔠_{m-1}` collapses the
  truncated window `(z + 𝔠_n) ∩ 𝔠_m` to `z + 𝔠_n` and kills the boundary
  indicator `𝟙_{x ∉ 𝔠_{m-1}}` carrying every `∇h` term;
* `g = 0` kills the datum term `[g]_{W̲^{1/2,∞}(𝔠_m)}`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The averaged oscillation estimate `e.large.scale.Holder.multifractal` of
Theorem C, obtained from the first clause of `HolderRegularityConclusions` by
the specialization.

The hypothesis is the conclusion package at the zero datum `g = 0` and the
boundary datum `h = u`; `hn` is `n ≤ m - 𝓛_L(γ,m)`, `hgrid` is `z ∈ 3^n ℤᵈ`,
and `hsub` is `z + 𝔠_n ⊆ 𝔠_{m-1}`. -/
theorem normalizedL2On_translatedCube_le_of_holderRegularityConclusions
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {C : ℝ} {L : ℕ}
    {ω : _root_.SubdiffusiveProcess.Model.PotentialSample d} {alpha : ℝ} {m X : ℕ}
    {u : H1Function (openCubeSet (originCube d m))} {n : ℕ} {z : Vec d}
    (hconc : HolderRegularityConclusions M C L ω alpha m X u u
      (fun _ ↦ (0 : Vec d)))
    (hn : (n : ℤ) ≤ (m : ℤ) - (X : ℤ))
    (hgrid : OnTriadicGrid n z)
    (hsub : translatedCube d n z ⊆ cube d ((m : ℤ) - 1)) :
    normalizedL2On (translatedCube d (n : ℤ) z)
        (fun x ↦ u.toFun x - averageOn (translatedCube d (n : ℤ) z) u.toFun) ≤
      C * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
        normalizedL2On (cube d m)
          (fun x ↦ u.toFun x - averageOn (cube d m) u.toFun) := by
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_translatedCube_subset_pred hsub
  have hzpred : z ∈ cube d ((m : ℤ) - 1) :=
    mem_cube_pred_of_translatedCube_subset hsub
  have hwin : truncatedCube d (m : ℤ) (n : ℤ) z = translatedCube d (n : ℤ) z :=
    truncatedCube_eq_translatedCube_of_subset_pred hsub
  -- Instantiate the first clause at `x = z`, `ℓ = n`, `y = z`.
  have hmem : z ∈ truncatedCube d (m : ℤ) (n : ℤ) z :=
    mem_truncatedCube_self (n : ℤ) hzm
  have hmain := hconc.1 n hn z hzm n le_rfl z hgrid hmem
  -- `ℓ = n` makes the left-hand gain factor one.
  rw [show alpha * ((n : ℝ) - (n : ℝ)) = 0 by ring, Real.rpow_zero,
    one_mul, hwin] at hmain
  -- `g = 0` kills the datum term; `z ∈ 𝔠_{m-1}` kills the boundary indicator.
  rw [holderSeminormOn_zero, mul_zero, ite_eq_left hzpred, add_zero,
    add_zero] at hmain
  exact hmain

/-- The energy-density estimate `e.large.scale.energy.multifractal` of
Theorem C, obtained from the second clause of `HolderRegularityConclusions`
(the display `e.energy.density.estimate` cited ) by the
same specialization. -/
theorem vectorNormalizedL2On_translatedCube_le_of_holderRegularityConclusions
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {C : ℝ} {L : ℕ}
    {ω : _root_.SubdiffusiveProcess.Model.PotentialSample d} {alpha : ℝ} {m X : ℕ}
    {u : H1Function (openCubeSet (originCube d m))} {n : ℕ} {z : Vec d}
    (hconc : HolderRegularityConclusions M C L ω alpha m X u u
      (fun _ ↦ (0 : Vec d)))
    (hn : (n : ℤ) ≤ (m : ℤ) - (X : ℤ))
    (hsub : translatedCube d n z ⊆ cube d ((m : ℤ) - 1)) :
    vectorNormalizedL2On (translatedCube d (n : ℤ) z)
        (fun x ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L ω x) •
          u.grad x) ≤
      C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
        vectorNormalizedL2On (cube d m)
          (fun x ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L ω x) •
            u.grad x) := by
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_translatedCube_subset_pred hsub
  have hzpred : z ∈ cube d ((m : ℤ) - 1) :=
    mem_cube_pred_of_translatedCube_subset hsub
  have hwin : truncatedCube d (m : ℤ) (n : ℤ) z = translatedCube d (n : ℤ) z :=
    truncatedCube_eq_translatedCube_of_subset_pred hsub
  have hmain := hconc.2.1 n hn z hzm
  rw [hwin] at hmain
  rw [holderSeminormOn_zero, mul_zero, ite_eq_left hzpred, add_zero,
    add_zero] at hmain
  exact hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
