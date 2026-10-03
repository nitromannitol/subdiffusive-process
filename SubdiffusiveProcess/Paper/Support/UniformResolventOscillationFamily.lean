module

public import SubdiffusiveProcess.Paper.Support.UniformResolventOscillation
public import SubdiffusiveProcess.Paper.Support.UniformResolventSelectedReduction
public import SubdiffusiveProcess.Analysis.LocalCampanatoCriterion
public import SubdiffusiveProcess.Probability.LiminfMomentEnvelope

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal
noncomputable section
namespace Paper

theorem aux_mfd_prop_uniform_resolvent_Kinst_bound (d : ℕ) (e s V : ℝ)
    (hs : 0 < s) (hV : 0 ≤ V) (m k h b : ℝ)
    (hm : 0 ≤ m) (hk : 0 ≤ k) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hkb : k ≤ b) (hhb : h ≤ b) :
    2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d e s m (V * m) k h ≤
      (2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d e s 1 V 1 1) * m * b := by
  unfold aux_prop_uniform_resolvent_cutoff_oscillation_Kinst
  have hσ : 0 ≤ min s (1 / 3 : ℝ) := le_min hs.le (by norm_num)
  have hsq : 0 ≤ Real.sqrt (d : ℝ) * s := mul_nonneg (Real.sqrt_nonneg _) hs.le
  conv_rhs => rw [mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.sqrt (2 * h ^ 2 * m ^ 2 * (min s (1 / 3)) ^ (-2 * e) +
        2 * (k ^ 2 * (V * m) * ((m + V * m) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - e))) * (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) /
        (1 - Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) - e - d + 1)))) ^ 2) / 2 ^ d) ≤
      Real.sqrt (2 * b ^ 2 * m ^ 2 * (min s (1 / 3)) ^ (-2 * e) +
        2 * (b ^ 2 * (V * m) * ((m + V * m) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - e))) * (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) /
        (1 - Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) - e - d + 1)))) ^ 2) / 2 ^ d) := by
          apply Real.sqrt_le_sqrt
          gcongr
    _ = Real.sqrt (2 * 1 ^ 2 * 1 ^ 2 * (min s (1 / 3)) ^ (-2 * e) +
        2 * (1 ^ 2 * V * ((1 + V) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - e))) * (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) /
        (1 - Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) - e - d + 1)))) ^ 2) / 2 ^ d) * (m * b) := by
          rw [mul_comm _ (m * b), ← Real.sqrt_sq (mul_nonneg hm hb),
            ← Real.sqrt_mul (sq_nonneg (m * b))]
          congr 1
          ring


theorem aux_mfd_prop_uniform_resolvent_oscillation_family
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (Qtri : Homogenization.TriadicCube d)
    (z : SpatialCoordinates d) (s : ℝ) (hr : 0 < s)
    (hroot : closure (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qtri))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (RN : ℕ → BilateralField d → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (uN : ℕ → BilateralField d → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      killedSobolevGraph (centeredCube z s hr))
    (Kmu : BilateralField d → ℝ) (Kcoer Khol : ℕ → BilateralField d → ℝ)
    (hnonneg : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      0 ≤ Kmu omega ∧ ∀ N, 0 ≤ Kcoer N omega ∧ 0 ≤ Khol N omega)
    (hgrowth : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x ∈ closure (Homogenization.openCubeSet Qtri), ∀ rho, 0 < rho → rho ≤ 1 → ∀ N,
        cutoffSpeedMeasure M H omega N (Metric.ball x rho) ≤
          ENNReal.ofReal (Kmu omega * rho ^ ((d : ℝ) - epsilon)))
    (hcoer : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      ∀ v : killedSobolevGraph (centeredCube z s hr),
        ‖v.val.1‖ ^ 2 ≤ Kcoer N omega *
          sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr) v.val v.val ∧
        globalFractionalSqNorm (3 / 4)
          (Set.indicator (centeredCube z s hr : Set (SpatialCoordinates d)) (fun x => v.val.1 x)) ≤
          ENNReal.ofReal (Kcoer N omega *
            sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr) v.val v.val))
    (hHolder : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      ∀ F : SpatialCoordinates d → ℝ, Measurable F → ∀ MF : ℝ, 0 ≤ MF →
        (∀ x ∈ (centeredCube z s hr : Set (SpatialCoordinates d)), |F x| ≤ MF) →
      ∀ v : killedSobolevGraph (centeredCube z s hr),
        (∀ w : killedSobolevGraph (centeredCube z s hr),
          sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr) v.val w.val =
            ∫ x in (centeredCube z s hr : Set (SpatialCoordinates d)), F x * w.val.1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube z s hr : Set (SpatialCoordinates d))] vc ∧
          (∀ x ∉ (centeredCube z s hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          ∀ x ∈ closure (centeredCube z s hr : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube z s hr : Set (SpatialCoordinates d)),
              |vc x - vc y| ≤ Khol N omega * MF * dist x y ^ (1 / 2 : ℝ))
    (hfinite : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N lam, 0 < lam → ∀ f,
      (RN N omega lam f =ᵐ[volume.restrict (centeredCube z s hr : Set (SpatialCoordinates d))]
        (uN N omega lam f).val.1) ∧
      (∀ x ∈ (centeredCube z s hr : Set (SpatialCoordinates d)), |RN N omega lam f x| ≤ ‖f‖ / lam) ∧
      ∀ w : killedSobolevGraph (centeredCube z s hr),
        sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr)
          (uN N omega lam f).val w.val =
            ∫ x, (f x - lam * RN N omega lam f x) * w.val.1 x
              ∂((cutoffSpeedMeasure M H omega N).restrict
                (closure (centeredCube z s hr : Set (SpatialCoordinates d))))) :
    ∃ V : ℝ, 0 ≤ V ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N lam, 0 < lam → ∀ f x rho,
        0 < rho → rho ≤ 1 →
        (∫ y in Metric.ball x rho,
          (Set.indicator (centeredCube z s hr : Set (SpatialCoordinates d))
              (fun y => (uN N omega lam f).val.1 y) y -
            (volume.real (Metric.ball x rho))⁻¹ *
              ∫ w in Metric.ball x rho,
                Set.indicator (centeredCube z s hr : Set (SpatialCoordinates d))
                  (fun y => (uN N omega lam f).val.1 y) w) ^ 2) ≤
          (2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s
            (Kmu omega) (V * Kmu omega) (Kcoer N omega) (Khol N omega) * ‖f‖) ^ 2 *
              volume.real (Metric.ball x rho) * rho ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z s hr
  let muN := fun N omega => (cutoffSpeedMeasure M H omega N).restrict (closure Q)
  have hQo : IsOpen Q := (centeredCube z s hr).isOpen
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hacQ : ∀ omega N, (muN N omega).restrict Q ≪ volume := fun omega N =>
    aux_prop_uniform_resolvent_cutoff_oscillation_cutoffSpeedMeasure_restrict_ac M H omega N (closure Q) Q
  have hfront : ∀ omega N, cutoffSpeedMeasure M H omega N (frontier Q) = 0 := by
    intro omega N
    have hv : volume (frontier Q) = 0 := by
      change volume (frontier (Metric.ball z (s / 2))) = 0
      rw [frontier_ball _ (ne_of_gt (half_pos hr))]
      haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      exact Measure.addHaar_sphere volume _ _
    exact withDensity_absolutelyContinuous _ _ hv
  obtain ⟨V, hV, hcover⟩ := aux_mfd_prop_uniform_resolvent_oscillation_cover z s hr
  refine ⟨V, hV, ?_⟩
  filter_upwards [hnonneg, hgrowth, hcoer, hHolder, hfinite] with omega hnn hgr hco hHol hfi
  intro N lam hlam f x rho hrho hrho1
  have hng : ∀ x ∈ closure (Homogenization.openCubeSet Qtri), ∀ r : ℝ, 0 < r → r ≤ 1 →
      muN N omega (Metric.ball x r) ≤ ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) :=
    fun x hx r hr0 hr1 => (Measure.restrict_apply_le _ _).trans (hgr x hx r hr0 hr1 N)
  have hmass : muN N omega Q ≤ ENNReal.ofReal (V * Kmu omega) :=
    hcover (muN N omega) (Kmu omega) hnn.1
      (fun x hx => by simpa using hng x (hroot hx) 1 zero_lt_one le_rfl)
  have hac' : (muN N omega).restrict Q ≪ volume.restrict Q := by
    have h := (hacQ omega N).restrict Q
    rwa [Measure.restrict_restrict hQm, Set.inter_self] at h
  obtain ⟨hfae, hfsup, hfeq⟩ := hfi N lam hlam f
  have hRm : AEMeasurable (RN N omega lam f) ((muN N omega).restrict Q) :=
    ((Lp.aestronglyMeasurable _).aemeasurable.congr hfae.symm).mono_ac hac'
  have hsrcm : AEStronglyMeasurable (fun x => f x - lam * RN N omega lam f x)
      ((muN N omega).restrict Q) :=
    ((f.continuous.measurable.aemeasurable).sub (hRm.const_mul lam)).aestronglyMeasurable
  have hsrcb : ∀ᵐ x ∂((muN N omega).restrict Q), |f x - lam * RN N omega lam f x| ≤ 2 * ‖f‖ := by
    refine (ae_restrict_iff' hQm).2 (ae_of_all _ (fun x hx => ?_))
    have hb := hfsup x hx
    have hfx : |f x| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
    have hl : |lam * RN N omega lam f x| ≤ ‖f‖ := by
      rw [abs_mul, abs_of_pos hlam]
      calc lam * |RN N omega lam f x| ≤ lam * (‖f‖ / lam) := mul_le_mul_of_nonneg_left hb hlam.le
        _ = ‖f‖ := by field_simp
    exact (abs_sub _ _).trans (by linarith)
  have hmem : ∀ᵐ x ∂(muN N omega), x ∈ Q := by
    change ∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict (closure Q)), x ∈ Q
    rw [ae_restrict_iff' isClosed_closure.measurableSet]
    refine measure_mono_null ?_ (hfront omega N)
    intro x hx
    rw [hQo.frontier_eq]
    by_contra hc
    exact hx (fun h1 => Classical.byContradiction (fun h2 => hc ⟨h1, h2⟩))
  have heq : ∀ w : killedSobolevGraph (centeredCube z s hr),
      sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr)
        (uN N omega lam f).val w.val =
        ∫ x in Q, (f x - lam * RN N omega lam f x) * w.val.1 x ∂(muN N omega) := by
    rw [Measure.restrict_eq_self_of_ae_mem hmem]
    exact hfeq
  have h := aux_mfd_prop_uniform_resolvent_oscillation_instance hd epsilon hepsilon hepsilon1 Qtri z s hr hroot
    (muN N omega) (hacQ omega N) (Kmu omega) (V * Kmu omega) (Kcoer N omega) (Khol N omega)
    hnn.1 (mul_nonneg hV hnn.1) (hnn.2 N).1 (hnn.2 N).2 hng hmass
    (cutoffPositiveCoefficient M H omega N z hr) (hco N) (hHol N)
    (uN N omega lam f) _ hsrcm (2 * ‖f‖) (by positivity) hsrcb heq
    _ (fun _ => rfl) x rho hrho hrho1
  convert h using 1
  ring

end Paper
