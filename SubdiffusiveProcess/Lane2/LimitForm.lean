import SubdiffusiveProcess.Lane2.KilledInverse
import SubdiffusiveProcess.Sobolev.ResponseRecovery

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- `E(u)` of `eq:mfd-18`:
the dual energy of the killed inverse `G`. -/
def limitFormEnergy (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) : EReal :=
  ⨆ f : DomainL2 Q, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)

/-- `D(E) = {u : E(u) < ∞}` (`eq:mfd-18`). -/
def limitFormDomain (G : DomainL2 Q →L[ℝ] DomainL2 Q) : Set (DomainL2 Q) :=
  {u : DomainL2 Q | limitFormEnergy G u < (⊤ : EReal)}

/-- `E(u,v)` by polarization (`mfd:prop-killed-consistency`). -/
def limitFormBilinear (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u v : DomainL2 Q) : EReal :=
  (limitFormEnergy G (u + v) - limitFormEnergy G (u - v)) / (4 : EReal)

/-- The paper's core `D(E) ∩ C_c(Q)` (`mfd:prop-regularity`). -/
def MemFormCore (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) : Prop :=
  u ∈ limitFormDomain G ∧
    ∃ f : SpatialCoordinates d → ℝ, Continuous f ∧ HasCompactSupport f ∧
      tsupport f ⊆ (Q : Set (SpatialCoordinates d)) ∧
      (u : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f

theorem limitFormEnergy_nonneg (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) :
    (0 : EReal) ≤ limitFormEnergy G u :=
  le_iSup_of_le (0 : DomainL2 Q) (by simp)

/-- **`mfd:prop-killed-inverse`, the Mosco statements**
(`eq:mfd-18`, proof 1857-1868): the weak lower bound and
the existence of recovery sequences for the dual-energy form of `G`. -/
theorem killedInverse_mosco
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (hstrong : ∀ f : DomainL2 Q,
      Tendsto (fun n => (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) atTop (𝓝 (G f)))
    (hweakresponse : ∀ f : DomainL2 Q,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 (inner ℝ f (G f)))) :
    (∀ (uN : ℕ → S.space) (u : DomainL2 Q),
        (∀ f : DomainL2 Q,
          Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy G u ≤
          liminf (fun n => ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
    (∀ u ∈ limitFormDomain G, ∃ w : ℕ → S.space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm S (a n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G u))) := by
  constructor
  · intro uN u hweak
    exact quadraticDual_le_liminf_responseForm S a G uN u hweak hweakresponse
  · intro u hu
    exact exists_responseForm_recoverySequence S a G hsym hpos hstrong u hu

end SubdiffusiveProcess
