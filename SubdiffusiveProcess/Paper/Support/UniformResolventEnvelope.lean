module

public import SubdiffusiveProcess.Paper.Support.UniformResolventOscillationFamily

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Paper

def aux_mfd_prop_uniform_resolvent_oscillationBound {d : ℕ}
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (beta A : ℝ)
    (w : DomainL2 (centeredCube z s hs)) : Prop :=
  ∀ x r, 0 < r → r ≤ 1 →
    (∫ y in Metric.ball x r,
      (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d)) (fun y => w y) y -
        (volume.real (Metric.ball x r))⁻¹ * ∫ y' in Metric.ball x r,
          Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d)) (fun y => w y) y') ^ 2) ≤
      A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * beta)

theorem aux_mfd_prop_uniform_resolvent_envelope
    {d : ℕ} (hd : 2 ≤ d) (Cp : CampanatoInput d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (epsilon beta : ℝ) (hbeta : 1 / 4 ≤ beta)
    (V : ℝ) (hV : 0 ≤ V)
    (RN : ℕ → Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (w : ℕ → Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube z s hs))
    (Kmu : Ω → ℝ) (Kcoer Khol : ℕ → Ω → ℝ)
    (q : ℝ) (hq : 1 ≤ q)
    (hmeas : Measurable Kmu ∧ (∀ N, Measurable (Kcoer N)) ∧ ∀ N, Measurable (Khol N))
    (hnonneg : ∀ᵐ omega ∂P, 0 ≤ Kmu omega ∧ ∀ N, 0 ≤ Kcoer N omega ∧ 0 ≤ Khol N omega)
    (hmom : MemLp Kmu (ENNReal.ofReal q) P ∧
      (∃ B : ℝ, ∀ N, (eLpNorm (Kcoer N) (ENNReal.ofReal q) P).toReal ≤ B ∧
        (eLpNorm (Khol N) (ENNReal.ofReal q) P).toReal ≤ B) ∧
      ∀ N, MemLp (Kcoer N) (ENNReal.ofReal q) P ∧ MemLp (Khol N) (ENNReal.ofReal q) P)
    (hvar : ∀ᵐ omega ∂P, ∀ N lam, 0 < lam → ∀ f,
      aux_mfd_prop_uniform_resolvent_oscillationBound z s hs beta
        (2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s
          (Kmu omega) (V * Kmu omega) (Kcoer N omega) (Khol N omega) * ‖f‖) (w N omega lam f))
    (hfinite : ∀ᵐ omega ∂P, ∀ N lam, 0 < lam → ∀ f,
      RN N omega lam f =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
        (w N omega lam f : SpatialCoordinates d → ℝ))
    (hpoint : ∀ᵐ omega ∂P, ∀ N lam, 0 < lam → ∀ f,
      ∀ v : SpatialCoordinates d → ℝ, Continuous v →
        (v =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] RN N omega lam f) →
        (∀ x ∉ (centeredCube z s hs : Set (SpatialCoordinates d)), v x = 0) →
        ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)), RN N omega lam f x = v x) :
    ∃ B : Ω → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
      MemLp B (ENNReal.ofReal (q / 2)) P ∧
      (∀ᵐ omega ∂P, ∀ Mb : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ N, Kcoer N omega ≤ Mb → Khol N omega ≤ Mb → ∀ lam, 0 < lam → ∀ f,
          aux_mfd_prop_uniform_resolvent_oscillationBound z s hs beta (K * ‖f‖) (w N omega lam f)) ∧
      (∀ᵐ omega ∂P, ∃ Mb : ℕ,
        (∃ᶠ N in atTop, Kcoer N omega ≤ Mb ∧ Khol N omega ≤ Mb) ∧
        ∀ N, Kcoer N omega ≤ Mb → Khol N omega ≤ Mb → ∀ lam, 0 < lam → ∀ f,
          (∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
            |RN N omega lam f x| ≤ B omega * ‖f‖) ∧
          ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
              |RN N omega lam f x - RN N omega lam f y| ≤ B omega * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
      (∀ᵐ omega ∂P, ∀ N lam, 0 < lam → ∀ f,
        ContinuousOn (RN N omega lam f) (closure (centeredCube z s hs : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier (centeredCube z s hs : Set (SpatialCoordinates d)), RN N omega lam f x = 0) := by
  classical
  let Q : Set (SpatialCoordinates d) := centeredCube z s hs
  have hQm : MeasurableSet Q := (centeredCube z s hs).isOpen.measurableSet
  obtain ⟨Cc, hCc, hc⟩ := SubdiffusiveProcess.Analysis.exists_zero_extension_holder_of_mean_oscillation Cp (1 / 4)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨x0, hx0⟩ := aux_prop_uniform_resolvent_ident_cube_compl_nonempty hd z hs
  obtain ⟨Cg, hCg, hgeom⟩ := SubdiffusiveProcess.Analysis.exists_bound_of_local_holder_zero
    (closure Q) (centeredCube_isBounded z hs).closure x0 (1 / 4 : ℝ) (by norm_num)
  let J0 := 2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s 1 V 1 1
  have hJ0 : 0 ≤ J0 := by dsimp [J0, aux_prop_uniform_resolvent_cutoff_oscillation_Kinst]; positivity
  obtain ⟨E, hEm, hE0, hEp, hEf⟩ := SubdiffusiveProcess.Probability.exists_common_level_envelope P {q}
    (Finset.singleton_nonempty q) (fun p hp => by simpa only [Finset.mem_singleton.mp hp] using hq)
    Kcoer Khol hmeas.2.1 hmeas.2.2
    (by filter_upwards [hnonneg] with omega h; exact h.2)
    (fun p hp => by simpa only [Finset.mem_singleton.mp hp] using hmom.2)
  let B : Ω → ℝ := fun omega => (Cg * Cc * J0) * |Kmu omega| * (E omega + 2)
  have hB0 : ∀ omega, 0 ≤ B omega := fun omega => by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hCg.le hCc.le) hJ0) (abs_nonneg _))
      (add_nonneg (hE0 omega) (by norm_num))
  have hBm : Measurable B := (measurable_const.mul hmeas.1.abs).mul (hEm.add_const 2)
  have hBp : MemLp B (ENNReal.ofReal (q / 2)) P := by
    have hkm : MemLp (fun omega => |Kmu omega|) (ENNReal.ofReal q) P := by
      simpa only [Real.norm_eq_abs] using hmom.1.norm
    have hep : MemLp (fun omega => E omega + 2) (ENNReal.ofReal q) P :=
      (hEp q (Finset.mem_singleton_self q)).add (memLp_const 2)
    have hprod := SubdiffusiveProcess.Probability.memLp_mul_half q (lt_of_lt_of_le zero_lt_one hq) hkm hep
    simpa only [B, mul_assoc] using hprod.const_mul (Cg * Cc * J0)
  have hrep : ∀ᵐ omega ∂P, ∀ N lam, 0 < lam → ∀ f,
      ∃ v : SpatialCoordinates d → ℝ, Continuous v ∧
        (∀ x ∈ closure Q, RN N omega lam f x = v x) ∧
        (∀ x y, dist x y ≤ 1 → |v x - v y| ≤
          Cc * (2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s
            (Kmu omega) (V * Kmu omega) (Kcoer N omega) (Khol N omega) * ‖f‖) *
            dist x y ^ (1 / 4 : ℝ)) ∧ ∀ x ∉ Q, v x = 0 := by
    filter_upwards [hvar, hfinite, hpoint] with omega hv hf hp
    intro N lam hlam f
    have hJ : 0 ≤ 2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s
        (Kmu omega) (V * Kmu omega) (Kcoer N omega) (Khol N omega) := by
      dsimp [aux_prop_uniform_resolvent_cutoff_oscillation_Kinst]; positivity
    obtain ⟨v, hvc, hvae, hvH, hv0⟩ := aux_prop_uniform_resolvent_camp_holder z s hs Cc hc beta hbeta
      _ (mul_nonneg hJ (norm_nonneg _)) (w N omega lam f) (hv N lam hlam f)
    have hvRN : v =ᵐ[volume.restrict Q] RN N omega lam f := by
      refine (hvae.restrict (s := Q)).trans ?_
      filter_upwards [(hf N lam hlam f).symm, ae_restrict_mem hQm] with x hxeq hxQ
      rw [Set.indicator_of_mem hxQ]
      exact hxeq
    exact ⟨v, hvc, hp N lam hlam f v hvc hvRN hv0, hvH, hv0⟩
  refine ⟨B, hBm, hB0, hBp, ?_, ?_, ?_⟩
  · filter_upwards [hvar, hnonneg] with omega hv hn
    intro Mb
    refine ⟨J0 * Kmu omega * Mb, mul_nonneg (mul_nonneg hJ0 hn.1) (Nat.cast_nonneg _), ?_⟩
    intro N hk hh lam hlam f x r hr hr1
    refine (hv N lam hlam f x r hr hr1).trans ?_
    have hJ := aux_mfd_prop_uniform_resolvent_Kinst_bound d epsilon s V hs hV
      (Kmu omega) (Kcoer N omega) (Khol N omega) Mb hn.1 (hn.2 N).1 (hn.2 N).2
      (Nat.cast_nonneg _) hk hh
    have hJnn : 0 ≤ 2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s
        (Kmu omega) (V * Kmu omega) (Kcoer N omega) (Khol N omega) := by
      dsimp [aux_prop_uniform_resolvent_cutoff_oscillation_Kinst]; positivity
    dsimp [J0] at *
    gcongr
  · filter_upwards [hEf, hrep, hnonneg] with omega hEf hr hn
    obtain ⟨Mb, hMb, hfreq⟩ := hEf
    refine ⟨Mb, hfreq, ?_⟩
    intro N hk hh lam hlam f
    obtain ⟨v, hvc, hp, hvH, hv0⟩ := hr N lam hlam f
    let J := 2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s
      (Kmu omega) (V * Kmu omega) (Kcoer N omega) (Khol N omega)
    have hJ : 0 ≤ J := by dsimp [J, aux_prop_uniform_resolvent_cutoff_oscillation_Kinst]; positivity
    have hJb : J ≤ J0 * |Kmu omega| * (E omega + 2) := by
      rw [abs_of_nonneg hn.1]
      refine (aux_mfd_prop_uniform_resolvent_Kinst_bound d epsilon s V hs hV
        (Kmu omega) (Kcoer N omega) (Khol N omega) Mb hn.1 (hn.2 N).1 (hn.2 N).2
        (Nat.cast_nonneg _) hk hh).trans ?_
      exact mul_le_mul_of_nonneg_left hMb (mul_nonneg hJ0 hn.1)
    have hbv := hgeom v (Cc * (J * ‖f‖)) (by positivity) (hv0 x0 hx0) hvH
    have hCb : Cg * (Cc * (J * ‖f‖)) ≤ B omega * ‖f‖ := by
      have h := mul_le_mul_of_nonneg_left hJb (mul_nonneg hCg.le hCc.le)
      have h' := mul_le_mul_of_nonneg_right h (norm_nonneg f)
      simpa only [B, mul_assoc] using h'
    constructor
    · intro x hx; rw [hp x hx]; exact (hbv.1 x hx).trans hCb
    · intro x hx y hy; rw [hp x hx, hp y hy]
      exact (hbv.2 x hx y hy).trans
        (mul_le_mul_of_nonneg_right hCb (Real.rpow_nonneg dist_nonneg _))
  · filter_upwards [hrep] with omega hr N lam hlam f
    obtain ⟨v, hvc, hp, -, hv0⟩ := hr N lam hlam f
    refine ⟨hvc.continuousOn.congr (fun x hx => hp x hx), ?_⟩
    intro x hx
    rw [hp x (frontier_subset_closure hx)]
    apply hv0 x
    rw [(centeredCube z s hs).isOpen.frontier_eq] at hx
    exact hx.2

end SubdiffusiveProcess.Paper
