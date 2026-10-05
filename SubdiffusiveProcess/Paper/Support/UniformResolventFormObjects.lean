module

public import SubdiffusiveProcess.Paper.Support.UniformResolventFormData
public import SubdiffusiveProcess.Section9.RepresentedComparisonDraft

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.Section9
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Paper

structure aux_mfd_prop_uniform_resolvent_FormObjects {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (mu : Measure (SpatialCoordinates d)) where
  T : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder → Lp ℝ 2 mu
  Ctrace : ℝ
  Ktr : ℝ
  J : DomainL2 (centeredCube z r hr) → SpatialCoordinates d → ℝ
  ustar : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube z r hr)

def aux_mfd_prop_uniform_resolvent_FormSpec {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (mu : Measure (SpatialCoordinates d)) (K : ℝ)
    (lift : (u : DomainL2 (centeredCube z r hr)) → (limitFormEnergy G u).toENNReal ≠ ∞ →
      CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    (O : aux_mfd_prop_uniform_resolvent_FormObjects hd z r hr mu) : Prop :=
  0 ≤ K ∧ 0 ≤ O.Ctrace ∧ 0 ≤ O.Ktr ∧
  CubeTraceCharacterization hd z hr mu K O.Ctrace O.T ∧
  (∀ u hu, O.J u =ᵐ[mu] (O.T (lift u hu) : SpatialCoordinates d → ℝ)) ∧
  (∀ u, (limitFormEnergy G u).toENNReal ≠ ∞ →
    (∫⁻ x, ENNReal.ofReal (O.J u x ^ 2) ∂mu) ≤ ENNReal.ofReal O.Ktr * (limitFormEnergy G u).toENNReal) ∧
  ∀ lam, 0 < lam → ∀ f,
    (limitFormEnergy G (O.ustar lam f)).toENNReal ≠ ∞ ∧
    let F := fun u => (limitFormEnergy G u).toENNReal.toReal + lam * ∫ x, O.J u x ^ 2 ∂mu -
      2 * ∫ x, f x * O.J u x ∂mu
    (∀ u, (limitFormEnergy G u).toENNReal ≠ ∞ → Integrable (fun x => O.J u x ^ 2) mu ∧
      Integrable (fun x => f x * O.J u x) mu ∧ F (O.ustar lam f) ≤ F u) ∧
    ∀ u, (limitFormEnergy G u).toENNReal ≠ ∞ →
      (∀ v, (limitFormEnergy G v).toENNReal ≠ ∞ → F u ≤ F v) → u = O.ustar lam f

theorem aux_mfd_prop_uniform_resolvent_form_objects
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Interp : CubeFractionalInterpolationInput d hd)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (G : KilledInverseFamily d Ω)
    (muFull : Ω → Measure (SpatialCoordinates d)) (K : ℕ → Ω → ℝ)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (hhalf : ∀ i omega (u : DomainL2 (determiningCube d i)),
      (limitFormEnergy (G i omega) u).toENNReal ≠ ∞ →
      ∃ v : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
        (rationalTriadicSide_pos d i) halfFractionalOrder, v.val 0 = u)
    (hfrac : ∀ᵐ omega ∂P, ∀ i,
      (∀ x y : DomainL2 (determiningCube d i), inner ℝ (G i omega x) y = inner ℝ x (G i omega y)) ∧
      (∀ x : DomainL2 (determiningCube d i), 0 ≤ inner ℝ x (G i omega x)) ∧
      ∃ Cbase : ℝ, 0 < Cbase ∧ ∀ u : DomainL2 (determiningCube d i),
        (limitFormEnergy (G i omega) u).toENNReal ≠ ∞ →
        ∃ v : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) threeQuarterOrder, v.val 0 = u ∧
          cubeFractionalL2Norm hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
            (rationalTriadicSide_pos d i) threeQuarterOrder v ^ 2 ≤ Cbase * (limitFormEnergy (G i omega) u).toReal)
    (hmu : ∀ᵐ omega ∂P, ∀ i,
      muFull omega (closure (determiningCube d i : Set (SpatialCoordinates d))) < ∞ ∧
      0 ≤ K i omega ∧ ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
        ∀ rho, 0 < rho → rho ≤ 1 → muFull omega (Metric.ball x rho) ≤ ENNReal.ofReal (K i omega * rho ^ t)) :
    let mu := fun i omega => (muFull omega).restrict (closure (determiningCube d i : Set (SpatialCoordinates d)))
    ∃ (lift : ∀ i omega (u : DomainL2 (determiningCube d i)),
        (limitFormEnergy (G i omega) u).toENNReal ≠ ∞ →
          CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
            (rationalTriadicSide_pos d i) halfFractionalOrder)
      (O : ∀ i omega, aux_mfd_prop_uniform_resolvent_FormObjects hd (rationalTriadicCenter d i)
        (rationalTriadicSide d i) (rationalTriadicSide_pos d i) (mu i omega)),
      (∀ i omega u hu, (lift i omega u hu).val 0 = u) ∧
      ∀ᵐ omega ∂P, ∀ i, aux_mfd_prop_uniform_resolvent_FormSpec hd (rationalTriadicCenter d i)
        (rationalTriadicSide d i) (rationalTriadicSide_pos d i) (G i omega) (mu i omega)
        (K i omega) (lift i omega) (O i omega) := by
  classical
  intro mu
  choose lift hlift using hhalf
  let good := fun i omega =>
    (∀ x y : DomainL2 (determiningCube d i), inner ℝ (G i omega x) y = inner ℝ x (G i omega y)) ∧
    (∀ x : DomainL2 (determiningCube d i), 0 ≤ inner ℝ x (G i omega x)) ∧
    (∃ Cbase : ℝ, 0 < Cbase ∧ ∀ u : DomainL2 (determiningCube d i),
      (limitFormEnergy (G i omega) u).toENNReal ≠ ∞ →
      ∃ v : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
        (rationalTriadicSide_pos d i) threeQuarterOrder, v.val 0 = u ∧
        cubeFractionalL2Norm hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) threeQuarterOrder v ^ 2 ≤ Cbase * (limitFormEnergy (G i omega) u).toReal) ∧
    muFull omega (closure (determiningCube d i : Set (SpatialCoordinates d))) < ∞ ∧
    0 ≤ K i omega ∧ ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
      ∀ rho, 0 < rho → rho ≤ 1 → muFull omega (Metric.ball x rho) ≤ ENNReal.ofReal (K i omega * rho ^ t)
  have hO : ∀ i omega, ∃ O : aux_mfd_prop_uniform_resolvent_FormObjects hd
      (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i) (mu i omega),
      good i omega → aux_mfd_prop_uniform_resolvent_FormSpec hd (rationalTriadicCenter d i)
        (rationalTriadicSide d i) (rationalTriadicSide_pos d i) (G i omega) (mu i omega)
        (K i omega) (lift i omega) O := by
    intro i omega
    by_cases hg : good i omega
    · obtain ⟨hsym, hpos, ⟨Cbase, hCbase, hfr⟩, hfin, hK, hgr⟩ := hg
      obtain ⟨T, C, Ktr, J, us, hC, hKtr, hT, hJ, hJtr, hmin⟩ :=
        aux_mfd_prop_uniform_resolvent_form_data hd Interp (rationalTriadicCenter d i)
          (rationalTriadicSide d i) (rationalTriadicSide_pos d i) (G i omega) hsym hpos
          Cbase hCbase hfr (lift i omega) (hlift i omega) (muFull omega) hfin
          (K i omega) t hK ht hgr
      exact ⟨⟨T, C, Ktr, J, us⟩, fun _ => ⟨hK, hC, hKtr, hT, hJ, hJtr, hmin⟩⟩
    · exact ⟨⟨fun _ => 0, 0, 0, fun _ _ => 0, fun _ _ => 0⟩, fun h => (hg h).elim⟩
  choose O hOSpec using hO
  refine ⟨lift, O, hlift, ?_⟩
  filter_upwards [hfrac, hmu] with omega hf hm i
  exact hOSpec i omega ⟨(hf i).1, (hf i).2.1, (hf i).2.2, (hm i).1, (hm i).2⟩

end SubdiffusiveProcess.Paper
