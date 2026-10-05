module

public import SubdiffusiveProcess.Paper.limit_form_package_side

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A core function supported in an open subdomain has a recovery sequence supported
in one compact subset of that subdomain. -/
theorem limit_form_localized_recovery_support
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (side : aux_limit_form_package_limit_side d hd z r hr S G a)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (u : DomainL2 (centeredCube z r hr)) (hu : u ∈ limitFormDomain G)
    (uc : SpatialCoordinates d → ℝ) (_huc : Continuous uc)
    (hucs : HasCompactSupport uc) (hucq : tsupport uc ⊆ q)
    (huae : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc) :
    ∃ (Y : ℕ → S.space) (K : Set (SpatialCoordinates d)), IsCompact K ∧ K ⊆ q ∧
      Tendsto (fun n => ((Y n).val.1,
        (responseForm S (a n) (Y n) (Y n) : EReal))) atTop (𝓝 (u, limitFormEnergy G u)) ∧
      ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        x ∉ K → (Y n).val.1 x = 0 := by
  obtain ⟨_, hLower, hRecovery⟩ := aux_limit_form_package_mosco_free d hd z r hr S G a
    side.response side.response_eq side.response_tendsto
  obtain ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, t, ht, htd, hcutoffs, _⟩ := side.bounds
  have hb1 := exists_open_between_and_isCompact_closure hucs.isCompact hq hucq
  obtain ⟨O, hO, hKO, hOq, hOc⟩ := hb1
  have hb2 := hcutoffs (tsupport uc) O hucs.isCompact hO hKO (hOq.trans hqQ)
  obtain ⟨V, chi, chic, B, hV, hKV, _hVO, hB, hchi⟩ := hb2
  have hb3 := hRecovery u hu
  obtain ⟨vN, hvN⟩ := hb3
  have hb4 := aux_prop_locality_recovery_recovery_parts
    (fun n => (vN n).val.1) (fun n => responseForm S (a n) (vN n) (vN n))
    u (limitFormEnergy G u) (limitFormEnergy_nonneg G u) hu hvN
  obtain ⟨hvN1, hvNE⟩ := hb4
  have hb5 := aux_prop_locality_recovery_smooth_seq S hS a vN u _ hvN1 hvNE
  obtain ⟨phi, Phi, hPhi, hPhi1, hPhiE⟩ := hb5
  let Y := fun n => aux_prop_locality_recovery_modV S hS (phi n) (chi n)
  have hin := fun n => aux_prop_locality_recovery_inner_ae
    (chi n).val (S.le_weak (chi n).2) (chic n)
    (hchi n).2.1 (hchi n).2.2.1 V hV (hchi n).2.2.2.1
    u uc huae hKV
  have hrec := aux_limit_form_package_modV_recovery hd hInterp z r hr t ht S a G
    hLower KN hKN Kstar hKstar hfrac hcoercive chi B hB
    (fun n => (hchi n).2.2.2.2.2.1) (fun n => (hchi n).2.2.2.2.2.2)
    u hu Phi hPhi1 hPhiE hS phi hPhi hin
  refine ⟨Y, closure O, hOc, hOq, hrec, ?_⟩
  intro n
  filter_upwards [aux_prop_locality_recovery_modV_fst_ae S hS (phi n) (chi n),
    (hchi n).2.1, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxchi hxQ hxK
  change (Y n).val.1 x = phi n x * (chi n).val.1 x at hx
  rw [hx, hxchi, (hchi n).2.2.2.2.1 x hxQ (fun hxO => hxK (subset_closure hxO)), mul_zero]

end SubdiffusiveProcess.Paper
