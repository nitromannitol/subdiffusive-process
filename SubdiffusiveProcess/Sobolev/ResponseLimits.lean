module

public import SubdiffusiveProcess.Sobolev.ResponsePositivity
public import SubdiffusiveProcess.Variational.DualEnergy
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology
/-! The weak lower bound for the literal dual energy follows from the actual
finite-coefficient variational formula and convergence of volume responses. -/

namespace SubdiffusiveProcess

theorem quadraticDual_le_liminf_responseForm
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : ℕ → PositiveCoefficient Ω)
    (G : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (uN : ℕ → S.space) (u : DomainL2 Ω)
    (hweak : ∀ f : DomainL2 Ω,
      Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u)))
    (hresponse : ∀ f : DomainL2 Ω,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f)))) :
    (⨆ f : DomainL2 Ω, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) ≤
      Filter.liminf (fun n => ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)) atTop := by
  refine iSup_le fun f => ?_
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad f).comp S.space.subtypeL
  have hfinite : ∀ n, 2 * inner ℝ f (uN n).val.1 - inverseResponse S (a n) L ≤
      responseForm S (a n) (uN n) (uN n) := by
    intro n
    have hmax := (inverseResponse_isGreatest S (a n) L).2
      (show 2 * L (uN n) - responseForm S (a n) (uN n) (uN n) ∈
        Set.range (fun v : S.space => 2 * L v - responseForm S (a n) v v) from
        ⟨uN n, rfl⟩)
    change 2 * inner ℝ f (uN n).val.1 - responseForm S (a n) (uN n) (uN n) ≤
      inverseResponse S (a n) L at hmax
    linarith
  have hreal : Tendsto
      (fun n => 2 * inner ℝ f (uN n).val.1 - inverseResponse S (a n) L) atTop
      (𝓝 (2 * inner ℝ f u - inner ℝ f (G f))) := by
    exact ((tendsto_const_nhds.mul (hweak f)).sub (hresponse f))
  have hereal : Tendsto
      (fun n => ((2 * inner ℝ f (uN n).val.1 - inverseResponse S (a n) L : ℝ) : EReal))
      atTop (𝓝 ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr hreal
  calc
    ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) =
        Filter.liminf
          (fun n => ((2 * inner ℝ f (uN n).val.1 - inverseResponse S (a n) L : ℝ) : EReal))
          atTop := hereal.liminf_eq.symm
    _ ≤ Filter.liminf
        (fun n => ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n => EReal.coe_le_coe_iff.mpr (hfinite n))

/-- The actual weak solutions recover the limiting dual energy on the range of G. -/
theorem volumeResponse_recovery_on_range
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : ℕ → PositiveCoefficient Ω)
    (G : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (hsym : ∀ x y : DomainL2 Ω, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Ω, 0 ≤ inner ℝ x (G x))
    (hstrong : ∀ f : DomainL2 Ω,
      Tendsto (fun n => (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) atTop (𝓝 (G f)))
    (f : DomainL2 Ω) :
    Tendsto (fun n =>
      ((responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1,
       ((responseForm S (a n)
         (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
         (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)) : ℝ) : EReal)))
      atTop (𝓝 (G f,
        ⨆ g : DomainL2 Ω, ((2 * inner ℝ g (G f) - inner ℝ g (G g) : ℝ) : EReal))) := by
  rw [iSup_quadraticDual_apply_image G hsym hpos f]
  have henergy : Tendsto (fun n =>
      responseForm S (a n)
        (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
        (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)))
      atTop (𝓝 (inner ℝ f (G f))) := by
    simp only [responseSolution_spec]
    exact tendsto_const_nhds.inner (hstrong f)
  exact (hstrong f).prodMk_nhds (EReal.tendsto_coe.mpr henergy)

end SubdiffusiveProcess
