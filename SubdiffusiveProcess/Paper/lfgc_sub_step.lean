import SubdiffusiveProcess.Paper.lfgc_sub_window

/-! Excess-iteration data on the scales below the last wavelength, from the small-oscillation window of the coefficient.
The quantitative prefix and weak-equation assumptions remain explicit; no good event is assumed. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper
attribute [local instance] Classical.propDecidable

/-- The scales below the wavelength carry excess-iteration data with a bounded bad count and explicit source defects. -/
theorem lfgc_sub_step
    (d : ℕ) [NeZero d] (I : Paper.in_J d) (alpha s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel) (hE0 : 0 < E0)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (eps : ℝ)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k : ℕ) (hkN : k ≤ N) (qside : ℝ) (hqpos : 0 < qside)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d)
    (G0 : ℝ) (hG0 : 0 ≤ G0)
    (hpad : ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) •
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤ G0)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hqp : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (Lane4.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (huU : ((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U)
    (D : ℕ) (x : SpatialCoordinates d) (hx : x ∈ Metric.ball qcenter (qside / 2)) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) ∧
    ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ (9 * d / 2 * G0) / min 1 (E0 / 5) + 2 ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), epsilon j ≤
        Ceps * 5 * (9 * d / 2 * G0) ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), defect j ≤
        Cdel * (cutoffCoefficient M H omega N x)⁻¹ *
          (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
            (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal *
          ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), (3 : ℝ) ^ (alpha * (j : ℝ)) := by
  have hc1 : 0 < min 1 (E0 / 5) := lt_min one_pos (by positivity)
  have ha0 := aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos M H omega N x
  have hxq : ∀ i, |x i - qcenter i| < qside / 2 := by
    intro i
    have hx' : dist x qcenter < qside / 2 := hx
    rw [dist_pi_lt_iff (by positivity)] at hx'
    have := hx' i
    rwa [Real.dist_eq] at this
  refine aux_in_deterministic_onestep_sub_core k N hkN (-((k : ℤ) + (D : ℤ))) (9 * d / 2 * G0)
    (min 1 (E0 / 5)) 5 Ceps Cdel _ (cutoffCoefficient M H omega N x)⁻¹ alpha (by positivity) hc1
    (by norm_num) hCeps hCdel ENNReal.toReal_nonneg (inv_nonneg.mpr ha0.le)
    (fun j => I.err x ((3 : ℝ) ^ (-(-j - 2))) (by positivity)
      (Lane4.cutoffPositiveCoefficient M H omega N x (by positivity))
      x ((3 : ℝ) ^ (-(-j - 2))) (cutoffCoefficient M H omega N x) s 2)
    (fun j => I.err_nonneg _ _ _ _ _ _ _ _ _)
    (fun j e δ => ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
      excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
        theta ^ h * excess j (translatedCube d j x) U + e * Real.sqrt (vecNormSq ell.slope) + δ)
    ?_
  intro j hj hjk hθ
  rw [Finset.mem_Icc] at hj
  set r : ℝ := (3 : ℝ) ^ (-(-j - 2)) with hr
  have hr0 : 0 < r := by positivity
  set θ : ℝ := 9 * d / 2 * G0 * (3 : ℝ) ^ ((N : ℤ) + j) with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := hθ.trans (min_le_left _ _)
  have hθE : θ ≤ E0 / 5 := hθ.trans (min_le_right _ _)
  -- the window scale and the wavelength
  have hrN : (3 : ℝ) ^ N * r = 9 * (3 : ℝ) ^ ((N : ℤ) + j) := by
    rw [hr, ← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      show (N : ℤ) + -(-j - 2) = ((N : ℤ) + j) + 2 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num; ring
  have hrq : r ≤ qside := by
    rw [hr, hqside]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hratio := lfgc_sub_window M H omega N eta hEta hIR s eps
    Fsc Psc Rsc Dsc Zsc goodEvt hPS k hkN qside hqpos hqside qcenter G0 hG0 hpad x hxq r hr0 hrq
    θ hθ0 hθ1 (le_of_eq (by rw [hθdef, hrN]; ring))
  have herr := aux_in_deterministic_onestep_err_nearconst I M H omega N x r hr0
    (cutoffCoefficient M H omega N x) ha0 s hs (3 * θ) (by positivity) hratio
  have herr5 : Real.sqrt (2 * (3 * θ) ^ 2) ≤ 5 * θ := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith only [sq_nonneg θ]
  have herrθ := herr.trans herr5
  refine ⟨herrθ, ?_⟩
  intro ell hell
  have hE : I.err x ((3 : ℝ) ^ (-(-j - 2))) (by positivity)
      (Lane4.cutoffPositiveCoefficient M H omega N x (by positivity))
      x ((3 : ℝ) ^ (-(-j - 2))) (cutoffCoefficient M H omega N x) s 2 ≤ E0 := by
    exact herrθ.trans (by linarith only [hθE])
  have hx' : x ∈ Metric.ball qcenter ((3 : ℝ) ^ (((1 : ℤ) - k) - 1) / 2) := by
    rw [show ((1 : ℤ) - k) - 1 = -(k : ℤ) by ring, ← hqside]; exact hx
  have hw : x ∈ Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) := by
    rw [Metric.mem_ball]
    have hx'' : dist x qcenter < qside / 2 := hx
    have : qside / 2 ≤ (3 : ℝ) ^ ((1 : ℤ) - k) / 2 := by
      rw [hqside]; gcongr
      · norm_num
      · omega
    linarith only [hx'', this]
  have hxx : x ∈ Metric.ball x ((3 : ℝ) ^ (j - 3) / 2) := Metric.mem_ball_self (by positivity)
  exact hOS M H omega N Qcentre Qside hQside qcenter ((1 : ℤ) - k) hqp f hf fL2 hfL2 u hu U hU
    huU x hx' j (-j - 2) (by omega) (by ring) x hw hxx (cutoffCoefficient M H omega N x) ha0 hE
    ell hell


end Paper
