module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.SecondMoment
public import MarkovProcess.Trajectory.DynkinMartingale

@[expose] public section

/-!
# §1.1, the deterministic reversal identity

For the reversed path `ω′(r) = ω(T − r)`,

```text
M̂_u(ω) = M_u(ω′)      (u ≤ T),
```

exactly, with no extra sign or constant.  In the repo's carriers the forward object is
`dynkinProcess f`, which carries **no** `−f(ω 0)` term, so the statement proved here is

```text
reversedDynkin f T u ω = dynkinProcess f u (reversePath T ω) − dynkinProcess f 0 (reversePath T ω),
```

the *increment* form, which is what `sq_three_term_le` consumes.  The two sign flips the soldiers
describe are `intervalIntegral.integral_comp_sub_left` (one) and the reversal of the limits
(the other); they cancel, and `sub_toNNReal_eq` is what makes the `ℝ≥0` truncated subtraction agree
with the real one on `[0, u]` -- which is the only place `u ≤ T` is used.

`iSup_sq_reversedDynkin_eq` is the same identity read on the maximal functional, which is the shape
§1.3 consumes.

## A remark on `u = T`

One might expect `M̂_T = −M_T` "deterministically" at `u = T`.  That is
**false**: with these definitions `M̂_T + M_T = −2∫₀ᵀΔφ(ω r)dr`.  What holds at `u = T` is
this file's identity, `M̂_T(ω) = M_T(ω′)`.  The expected remark would only be used to argue that the
terminal second moment needs no reversal argument; the main line is unaffected, since reversal is
needed for the supremum in any case.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

variable {d : ℕ}

/-- The time reversal of a path at horizon `T`.  Beyond `T` the reversed path is constant at
`ω 0`, which is harmless: only `u ≤ T` is ever used. -/
def reversePath (T : ℝ≥0) (ω : ContinuousPath (Vec d)) : ContinuousPath (Vec d) :=
  ⟨fun u => ω (T - u),
    ω.continuous.comp (continuous_real_toNNReal.comp
      (continuous_const.sub NNReal.continuous_coe))⟩

@[simp] theorem reversePath_apply (T : ℝ≥0) (ω : ContinuousPath (Vec d)) (u : ℝ≥0) :
    reversePath T ω u = ω (T - u) := rfl

/-- The reversed Dynkin increment at horizon `T`. -/
def reversedDynkin (f : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain)
    (T u : ℝ≥0) (ω : ContinuousPath (Vec d)) : ℝ :=
  (f : C₀(Vec d, ℝ)) (ω (T - u)) - (f : C₀(Vec d, ℝ)) (ω T)
    - ∫ s in ((T : ℝ) - (u : ℝ))..(T : ℝ),
        ((isFeller_laplacianSemigroup (d := d)).c0Semigroup.generator f) (ω (Real.toNNReal s))

/-- **§1.1, the deterministic reversal identity.** -/
theorem reversedDynkin_eq_dynkinProcess_reversePath
    (f : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain)
    {T u : ℝ≥0} (hu : u ≤ T) (ω : ContinuousPath (Vec d)) :
    reversedDynkin f T u ω
      = isFeller_laplacianSemigroup.dynkinProcess f u (reversePath T ω)
        - isFeller_laplacianSemigroup.dynkinProcess f 0 (reversePath T ω) := by
  have hzero : isFeller_laplacianSemigroup.dynkinProcess f 0 (reversePath T ω)
      = (f : C₀(Vec d, ℝ)) (ω T) := by
    rw [SubMarkovKernelSemigroup.IsFellerKernelSemigroup.dynkinProcess_apply]
    simp
  have hsub : (∫ s in ((T : ℝ) - (u : ℝ))..(T : ℝ),
        ((isFeller_laplacianSemigroup (d := d)).c0Semigroup.generator f) (ω (Real.toNNReal s)))
      = ∫ s in (0 : ℝ)..(u : ℝ),
        ((isFeller_laplacianSemigroup (d := d)).c0Semigroup.generator f)
          ((reversePath T ω) (Real.toNNReal s)) := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := fun s : ℝ => ((isFeller_laplacianSemigroup (d := d)).c0Semigroup.generator f)
        (ω (Real.toNNReal s))) (a := (0 : ℝ)) (b := (u : ℝ)) (T : ℝ)
    rw [sub_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le u.coe_nonneg] at hs
    have hsT : s ≤ (T : ℝ) := le_trans hs.2 (by exact_mod_cast hu)
    rw [reversePath_apply, sub_toNNReal_eq hs.1 hsT]
  rw [reversedDynkin, hzero,
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.dynkinProcess_apply, reversePath_apply, hsub]
  ring

/-- The same identity, read on the maximal functional over `[0, T]`. -/
theorem iSup_sq_reversedDynkin_eq
    (f : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain)
    (T : ℝ≥0) (ω : ContinuousPath (Vec d)) :
    (⨆ u : ℝ≥0, ⨆ (_ : u ≤ T), ENNReal.ofReal ((reversedDynkin f T u ω) ^ 2))
      = ⨆ u : ℝ≥0, ⨆ (_ : u ≤ T), ENNReal.ofReal
          ((isFeller_laplacianSemigroup.dynkinProcess f u (reversePath T ω)
            - isFeller_laplacianSemigroup.dynkinProcess f 0 (reversePath T ω)) ^ 2) := by
  refine iSup_congr fun u => ?_
  refine iSup_congr fun hu => ?_
  rw [reversedDynkin_eq_dynkinProcess_reversePath f hu ω]

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
