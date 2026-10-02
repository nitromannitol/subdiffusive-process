import SubdiffusiveProcess.Paper.prop_21_full_cluster_convergence
import SubdiffusiveProcess.Paper.prop_killed_inverse
import SubdiffusiveProcess.Paper.weighted_killed_form
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.ResponseMarkov

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}



theorem prop_21_full_mosco
    (S : ResponseSpace Q)
    (arho : ℕ → PositiveCoefficient Q)
    (Grho : DomainL2 Q →L[ℝ] DomainL2 Q)
    (GrhoN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGrhoN : ∀ (n : ℕ) (f : DomainL2 Q), GrhoN n f =
      (responseSolution S (arho n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (Grho x) y = inner ℝ x (Grho y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (Grho x))
    (hconv : Tendsto GrhoN atTop (𝓝 Grho)) :
    (∀ u ∈ limitFormDomain Grho, ∃ w : ℕ → S.space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm S (arho n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy Grho u))) ∧
    (∀ (uN : ℕ → S.space) (u : DomainL2 Q),
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
          (𝓝 (inner ℝ f u))) →
      limitFormEnergy Grho u ≤
        liminf (fun n =>
          ((responseForm S (arho n) (uN n) (uN n) : ℝ) : EReal)) atTop) := by
  have hpt : ∀ f : DomainL2 Q, Tendsto (fun n => GrhoN n f) atTop (𝓝 (Grho f)) :=
    fun f => ((continuous_id.clm_apply continuous_const).tendsto Grho).comp hconv
  have hstrong : ∀ f : DomainL2 Q,
      Tendsto (fun n => (responseSolution S (arho n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) atTop (𝓝 (Grho f)) :=
    fun f => (hpt f).congr' (Filter.Eventually.of_forall fun n => hGrhoN n f)
  have hweakresponse : ∀ f : DomainL2 Q,
      Tendsto (fun n => inverseResponse S (arho n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 (inner ℝ f (Grho f))) :=
    fun f => (tendsto_const_nhds.inner (hpt f)).congr'
      (Filter.Eventually.of_forall fun n => by
        rw [hGrhoN n f]
        show inner ℝ f (responseSolution S (arho n)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 =
          inverseResponse S (arho n) ((sobolevVolumeLoad f).comp S.space.subtypeL)
        rw [inverseResponse_eq_load]
        rfl)
  obtain ⟨hlow, hrec⟩ :=
    killedInverse_mosco S arho Grho hsym hpos hstrong hweakresponse
  exact ⟨hrec, hlow⟩


end Paper
