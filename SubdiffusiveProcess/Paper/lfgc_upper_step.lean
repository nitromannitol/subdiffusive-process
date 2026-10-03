module

public import SubdiffusiveProcess.Paper.lfgc_ratio_ray

@[expose] public section

/-! One excess-decay step above the last wavelength for either infrared variant, from a prefix test and the deterministic one-step window.
The quantitative prefix and weak-equation assumptions remain explicit; no good event is assumed. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper
attribute [local instance] Classical.propDecidable

/-- Above the wavelength, a prefix-tested descendant scale is either counted bad or gives one excess-decay step with explicit error and source budgets. -/
theorem lfgc_upper_step
    (d : ℕ) [NeZero d] (I : Paper.in_J d) (alpha s : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
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
    (Cg : ℝ) (hCg : 0 ≤ Cg)
    (hG : ∀ (j : ℤ) (w : SpatialCoordinates d), 0 ≤ j → j ≤ (N : ℤ) →
      Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ →
      Zsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (Lane4.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w)).toReal))
    (c0 : ℝ) (hc0 : 0 < c0) (hcap : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 ≤ E0)
    (k cbuf k0 DA : ℕ) (hkDA : k + DA ≤ N) (jlo : ℤ)
    (hjlo1 : jlo ≤ -((k : ℤ) + DA) + 4) (hjlo2 : -((k : ℤ) + DA) - 2 ≤ jlo)
    (qcenter x w : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter ((3 : ℝ) ^ (-(k : ℤ)) / 2))
    (hxw : ∀ i, |x i - w i| ≤ (3 : ℝ) ^ (-((k : ℤ) + DA)) / 2)
    (hwq : ∀ i, |w i - qcenter i| < (3 : ℝ) ^ (-(k : ℤ)) / 2)
    (lamCut : ℝ) (hlam : 0 ≤ lamCut)
    (hprefix : k0 ≤ DA →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) < lamCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w)).toReal < lamCut * DA)
    (hfin : k0 ≤ DA → ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
      Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hqpQ : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
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
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc jlo (-(k : ℤ)) ∧ ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc jlo (-(k : ℤ)), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc jlo (-(k : ℤ)), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ 10 + k0 + lamCut * DA * (1 + c0⁻¹) ∧
      ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), epsilon j ≤
        Ceps * Cg * ((M.delta ^ 2 + eps ^ 8) * ((DA : ℝ) + 1) + lamCut * DA) ∧
      ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), defect j ≤
        Cdel * (Real.exp (((d : ℝ) + 2) * (lamCut * DA) + (DA : ℝ) * M.delta ^ 2) *
            (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹) *
          (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
            (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal *
          ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), (3 : ℝ) ^ (alpha * (j : ℝ)) := by
  set F : ℝ := (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
    (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal with hF
  set sk : ℝ := aux_in_deterministic_onestep_sref M H omega N k qcenter with hsk
  have hsk0 : 0 < sk := aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  set Y : ℝ := ((d : ℝ) + 2) * (lamCut * DA) + (DA : ℝ) * M.delta ^ 2 with hY
  have hRs : 0 ≤ Real.exp Y * sk⁻¹ := mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hsk0.le)
  refine aux_in_deterministic_onestep_upper_core k DA cbuf k0 jlo hjlo1 hjlo2
    (fun l => Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w))
    (fun l => (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w)).toReal)
    (fun l => aux_in_deterministic_onestep_Z_nonneg M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt hPS
      _ _)
    (fun l => ENNReal.toReal_nonneg)
    lamCut c0 Cg (M.delta ^ 2 + eps ^ 8) Ceps Cdel F (Real.exp Y * sk⁻¹) alpha
    hlam hc0 hCg (by positivity) hCeps hCdel ENNReal.toReal_nonneg hRs hprefix
    (fun j => I.err w ((3 : ℝ) ^ (-(-j - 2))) (by positivity)
      (Lane4.cutoffPositiveCoefficient M H omega N w (by positivity))
      w ((3 : ℝ) ^ (-(-j - 2))) (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w) s 2)
    (fun j => aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)
    (fun j => I.err_nonneg _ _ _ _ _ _ _ _ _)
    (fun j => aux_in_deterministic_onestep_sref_pos M H omega N (-j - 2) w)
    (fun j e δ => ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
      excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
        theta ^ h * excess j (translatedCube d j x) U + e * Real.sqrt (vecNormSq ell.slope) + δ)
    ?_
  intro j hj hk0 hZ hD
  rw [Finset.mem_Icc] at hj
  have hlN : -j - 2 ≤ (N : ℤ) := by omega
  have hlS : -j - 2 ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA) := by
    rw [Finset.mem_Icc]; constructor <;> omega
  have herr := hG (-j - 2) w (by omega) hlN (hfin hk0 _ hlS) hZ
  refine ⟨herr, ?_, ?_⟩
  · -- the reference comparison along the ray
    have hSig := (hprefix hk0).2.le
    have hray := lfgc_ratio_ray M H omega N eta hEta hIR s eps hs
      Fsc Psc Rsc Dsc Zsc goodEvt hPS k qcenter w hwq
      (Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA))
      (by rw [Finset.mem_Icc]; constructor <;> omega) (-j - 2) (by omega) hlN
      (by intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_Icc]; constructor <;> omega)
      (hfin hk0) (lamCut * DA) hSig
    have hpos := aux_in_deterministic_onestep_sref_pos M H omega N (-j - 2) w
    have hlk : ((-j - 2 - (k : ℤ) : ℤ) : ℝ) * M.delta ^ 2 ≤ (DA : ℝ) * M.delta ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have : -j - 2 - (k : ℤ) ≤ (DA : ℤ) := by omega
      exact_mod_cast this
    have hray' : sk ≤ aux_in_deterministic_onestep_sref M H omega N (-j - 2) w * Real.exp Y := by
      refine hray.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hpos.le)
      rw [hY]; linarith only [hlk]
    show (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)⁻¹ ≤ Real.exp Y * sk⁻¹
    have hq : sk * (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)⁻¹ ≤
        Real.exp Y := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]; linarith only [hray']
    calc (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)⁻¹
        = sk⁻¹ * (sk * (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)⁻¹) := by
          field_simp
      _ ≤ sk⁻¹ * Real.exp Y := mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hsk0.le)
      _ = Real.exp Y * sk⁻¹ := mul_comm _ _
  · -- the one-step estimate from the per-window input
    intro ell hell
    have hE : I.err w ((3 : ℝ) ^ (-(-j - 2))) (by positivity)
        (Lane4.cutoffPositiveCoefficient M H omega N w (by positivity))
        w ((3 : ℝ) ^ (-(-j - 2))) (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w) s 2
        ≤ E0 := by
      refine herr.trans ?_
      have : Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - (-j - 2)).toNat (((3 : ℝ) ^ N) • w)).toReal) ≤
          Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 := by
        have hDc := mul_le_mul_of_nonneg_left hD hCg
        rw [mul_add]; linarith only [hDc]
      linarith only [this, hcap]
    have hx' : x ∈ Metric.ball qcenter ((3 : ℝ) ^ (((1 : ℤ) - k) - 1) / 2) := by
      rw [show ((1 : ℤ) - k) - 1 = -(k : ℤ) by ring]; exact hx
    have hw : w ∈ Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) := by
      rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      refine (hwq i).trans_le ?_
      gcongr
      · norm_num
      · omega
    have hxw' : x ∈ Metric.ball w ((3 : ℝ) ^ (j - 3) / 2) := by
      rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      refine (hxw i).trans_lt ?_
      have : (3 : ℝ) ^ (-((k : ℤ) + DA)) < (3 : ℝ) ^ (j - 3) :=
        zpow_lt_zpow_right₀ (by norm_num) (by omega)
      linarith only [this]
    exact hOS M H omega N Qcentre Qside hQside qcenter ((1 : ℤ) - k) hqpQ f hf fL2 hfL2 u hu U hU
      huU x hx' j (-j - 2) (by omega) (by ring) w hw hxw'
      (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)
      (aux_in_deterministic_onestep_sref_pos M H omega N (-j - 2) w) hE ell hell


end Paper
