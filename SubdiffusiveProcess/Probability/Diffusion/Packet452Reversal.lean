module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452SecondMoment
public import MarkovProcess.Trajectory.DynkinMartingale

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- The time reversal of a path at horizon `T`.  Beyond `T` the reversed path is frozen at
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

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
