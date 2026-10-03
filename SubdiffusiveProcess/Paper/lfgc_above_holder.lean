module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Paper.lfgc_iteration_data
public import SubdiffusiveProcess.Paper.lfgc_holder_from_iteration
public import SubdiffusiveProcess.Paper.lfgc_good_scale_transfer
public import SubdiffusiveProcess.Analysis.IterationBudgetConstants
public import SubdiffusiveProcess.Sobolev.BoundedSourceLoad
public import SubdiffusiveProcess.Lane4.InDetLowAlphaCont

@[expose] public section

/-! Above the last wavelength, the prefix iteration gives the anchored Holder norm of a
finite-cutoff solution on a good cell in terms of the centred oscillation on its padded
cube and the bounded source. The padded oscillation is converted to energy elsewhere. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper
attribute [local instance] Classical.propDecidable

/-- The padded side is three times the cell side. -/
theorem aux_lfgc_above_holder_three_pow (k : ℕ) :
    (3 : ℝ) ^ ((1 : ℤ) - k) = 3 * (3 : ℝ) ^ (-(k : ℤ)) := by
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]

/-- The prefix tests on a cell with remaining cutoff at least one give the excess-iteration
budgets at every depth and every point of the cell. -/
theorem aux_lfgc_above_holder_data
    (d : ℕ) [NeZero d] (I : Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Cg C2 C3 : ℝ) (hCg : 0 < Cg) (hC20 : 0 ≤ C2)
    (hC2a : 11 + (E0 / (2 * Cg))⁻¹ ≤ C2) (hC2b : 2 * Ceps * Cg ≤ C2)
    (hC2c : 3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2)
    (hC2d : ((d : ℝ) + 3) / Real.log 3 ≤ C2) (hE0 : 0 < E0)
    (hC3card : 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2 ≤ C3)
    (hC3eps : Ceps * 5 * (9 * (d : ℝ) / 2) ≤ C3)
    (hC3a : 9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C3)
    (hC3b : (2 * (d : ℝ) + 4) / Real.log 3 ≤ C3)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (m k : ℕ)
    (hm : 1 ≤ m) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - ((m + k : ℕ) : ℤ)) (((3 : ℝ) ^ (-((m + k : ℕ) : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (hG : ∀ (j : ℤ) (w : SpatialCoordinates d), 0 ≤ j → j ≤ ((m + k : ℕ) : ℤ) →
      Dsc (((m + k : ℕ) : ℤ) - j).toNat (((3 : ℝ) ^ (m + k)) • w) ≠ ⊤ →
      Zsc (((m + k : ℕ) : ℤ) - j).toNat (((3 : ℝ) ^ (m + k)) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (Lane4.cutoffPositiveCoefficient M H omega (m + k) w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega (m + k) j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc (((m + k : ℕ) : ℤ) - j).toNat (((3 : ℝ) ^ (m + k)) • w)).toReal))
    (hcapE : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * (E0 / (2 * Cg)) ≤ E0)
    (hdel0 : 0 ≤ M.delta) (hdel1 : M.delta ≤ 1)
    (z : SpatialCoordinates d) (lam lamDet : ℝ) (hlam0 : 0 ≤ lam) (hlamlt : lam ≤ lamDet)
    (hfin : ∀ (n : ℕ) (y : Vec d), Dsc n y ≠ ⊤)
    (hpre : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), 1 ≤ DA → k + DA ≤ m + k →
      ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          Zsc (((m + k : ℕ) : ℤ) - l).toNat
            (((3 : ℝ) ^ (m + k)) • descendantCenter 1 z ((3 : ℝ) ^ (-(k : ℤ))) DA dword) <
        lam * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          (Dsc (((m + k : ℕ) : ℤ) - l).toNat
            (((3 : ℝ) ^ (m + k)) • descendantCenter 1 z ((3 : ℝ) ^ (-(k : ℤ))) DA dword)).toReal <
        lam * DA)
    (hpad : ∀ (D : ℕ) (pword : Fin D → OddGridIndex d 1), D = m + 1 →
      (Dsc 0 (((3 : ℝ) ^ (m + k)) •
        descendantCenter 1 z (3 * (3 : ℝ) ^ (-(k : ℤ))) D pword)).toReal ≤ lam * (D : ℝ))
    (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hsub : Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube zP R hR : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube zP R hR))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube zP R hR : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube zP R hR))
    (hu : ∀ psi : killedSobolevGraph (centeredCube zP R hR),
        sobolevCoefficientForm
          (Lane4.cutoffPositiveCoefficient M H omega (m + k) zP hR)
          (u : SobolevData (centeredCube zP R hR))
          (psi : SobolevData (centeredCube zP R hR)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube zP R hR)))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (centeredCube zP R hR : Set (SpatialCoordinates d)))
    (huU : ((u : SobolevData (centeredCube zP R hR)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube zP R hR : Set (SpatialCoordinates d))] U)
    (fN : ℝ) (hfN : 0 ≤ fN)
    (hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball z ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fN * ((3 * (3 : ℝ) ^ (-(k : ℤ))) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha)))) :
    ∀ (D : ℕ), 0 < D → ∀ x ∈ (centeredCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
        Set (SpatialCoordinates d)),
      aux_lfgc_holder_from_iteration_data d k h theta (C2 + C3 + 0)
        (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) (lamDet + M.delta ^ 2 + eps ^ 8)
        (((3 : ℝ) ^ (-(k : ℤ))) ^ 2 *
          (aux_in_deterministic_onestep_sref M H omega (m + k) k z)⁻¹ * fN)
        ((3 : ℝ) ^ (-(k : ℤ))) U D x := by
  intro D _hD x hx
  have hqp : Metric.ball z ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d)) := by
    rw [aux_lfgc_above_holder_three_pow]
    exact Metric.ball_subset_closedBall.trans hsub
  exact lfgc_iteration_data d I alpha s halpha hs h theta Ceps Cdel E0 hCeps hCdel hOS
    Cg (E0 / (2 * Cg)) C2 0 hCg.le (by positivity) hC20 hC2a hC2b hC2c hC2d le_rfl
    C3 hE0 hC3card hC3eps hC3a hC3b M H omega (m + k) eta hEta hIR eps heps
    Fsc Psc Rsc Dsc Zsc goodEvt hPS hG hcapE hdel0 hdel1 k 1 1 D (by omega)
    ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) rfl z lam lamDet hlam0 hlamlt
    (fun DA dword h1 _ h3 => hpre DA dword h1 h3)
    (fun DA dword _ l _ => hfin _ _)
    zP R hR hqp f hf fL2 hfL2 u hu U hU huU
    (aux_in_deterministic_onestep_sref M H omega (m + k) k z) fN rfl hfN hFq
    (fun _ _ pword => ⟨hfin _ _, hpad _ pword (by omega)⟩)
    D le_rfl x hx (fun _ h2 => absurd h2 (by omega))

/-- Choosing the prefix threshold, the disorder and the tolerance below the iteration's
subcritical margin makes the growth factor harmless. -/
theorem aux_lfgc_above_holder_margin (alpha C t0 lamDet delta eps : ℝ) (halpha : alpha < 1)
    (hC : 1 ≤ C) (ht0 : t0 ≤ (1 - alpha) / (4 * C)) (hlamDet : lamDet ≤ t0)
    (hdel0 : 0 ≤ delta) (hdel1 : delta ≤ 1) (hdelt : delta ≤ t0)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) (hepst : eps ≤ t0) :
    C * (lamDet + delta ^ 2 + eps ^ 8) < 1 - alpha := by
  have hδ2 : delta ^ 2 ≤ delta := by nlinarith only [hdel0, hdel1]
  have he8 : eps ^ 8 ≤ eps := pow_le_of_le_one heps0 heps1 (by norm_num)
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have ht3 : lamDet + delta ^ 2 + eps ^ 8 ≤ 3 * ((1 - alpha) / (4 * C)) := by
    linarith only [hδ2, he8, hlamDet, hdelt, hepst, ht0]
  calc C * (lamDet + delta ^ 2 + eps ^ 8) ≤ C * (3 * ((1 - alpha) / (4 * C))) :=
        mul_le_mul_of_nonneg_left ht3 hC0.le
    _ = 3 * (1 - alpha) / 4 := by field_simp
    _ < 1 - alpha := by linarith only [halpha]

/-- The local source norm on the padded cube is attained by a nonnegative normalized scalar
bounded by the source bound. -/
theorem aux_lfgc_above_holder_source (d : ℕ) [NeZero d] (k : ℕ) (alpha : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hbound : ∀ x ∈ Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2), |F x| ≤ Kf) :
    ∃ fN : ℝ, 0 ≤ fN ∧ fN ≤ Kf ∧
      (SubdiffusiveProcess.RawLp.eLpNorm F (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
        (volume.restrict (Metric.ball z ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
        fN * ((3 * (3 : ℝ) ^ (-(k : ℤ))) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))) := by
  have h3 : 0 < 3 * (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  have hX : 0 < ((3 * (3 : ℝ) ^ (-(k : ℤ))) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))) :=
    Real.rpow_pos_of_pos (pow_pos h3 d) _
  have hp : 0 < (d : ℝ) / (1 - alpha) := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact div_pos hd0 (by linarith only [halpha.2])
  refine ⟨(SubdiffusiveProcess.RawLp.eLpNorm F (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball z ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal /
      ((3 * (3 : ℝ) ^ (-(k : ℤ))) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))),
    div_nonneg ENNReal.toReal_nonneg hX.le, ?_, (div_mul_cancel₀ _ hX.ne').symm⟩
  rw [aux_lfgc_above_holder_three_pow]
  exact boundedSource_eLpNorm_ball_le z h3 F Kf hKf hbound _ hp

/-- Above the wavelength, the prefix tests give the anchored Holder norm of every bounded-source
solution by the padded centred oscillation and the source, with deterministic constants. -/
theorem lfgc_above_holder (d : ℕ) (hd : 2 ≤ d) [NeZero d] (I : Paper.in_J d)
    (Det : Paper.lane4_deterministic_good_scale_input d) (alpha sigma : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hsigma32 : sigma ≤ 1 / 32) :
    ∃ Ca t0 delta1 : ℝ, 1 ≤ Ca ∧ 0 < t0 ∧ 0 < delta1 ∧
    ∀ (eps lam lamDet : ℝ), eps ∈ Set.Ioo (0 : ℝ) 1 → eps ≤ t0 → 0 ≤ lam → lam ≤ lamDet →
      lamDet ≤ t0 →
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta1 →
    ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (m k : ℕ),
      1 ≤ m →
    ∀ (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
      (∀ (i : ℕ) (y : SpatialCoordinates d),
        eta i y = omega ((i : ℤ) - ((m + k : ℕ) : ℤ)) (((3 : ℝ) ^ (-((m + k : ℕ) : ℤ))) • y)) →
      (Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0) →
    ∀ (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
      (goodEvt : ℕ → Vec d → Prop),
      Paper.primitive_scores d M sigma eps eta Fsc Psc Rsc Dsc Zsc goodEvt →
      (∀ (n : ℕ) (y : Vec d), Dsc n y ≠ ⊤) →
    ∀ (z : SpatialCoordinates d),
      (∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), 1 ≤ DA → k + DA ≤ m + k →
        ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
            Zsc (((m + k : ℕ) : ℤ) - l).toNat
              (((3 : ℝ) ^ (m + k)) • descendantCenter 1 z ((3 : ℝ) ^ (-(k : ℤ))) DA dword) <
          lam * DA ∧
        ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
            (Dsc (((m + k : ℕ) : ℤ) - l).toNat
              (((3 : ℝ) ^ (m + k)) • descendantCenter 1 z ((3 : ℝ) ^ (-(k : ℤ))) DA dword)).toReal <
          lam * DA) →
      (∀ (D : ℕ) (pword : Fin D → OddGridIndex d 1), D = m + 1 →
        (Dsc 0 (((3 : ℝ) ^ (m + k)) •
          descendantCenter 1 z (3 * (3 : ℝ) ^ (-(k : ℤ))) D pword)).toReal ≤ lam * (D : ℝ)) →
    ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
        (centeredCube zP R hR : Set (SpatialCoordinates d)) →
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), Measurable F → 0 ≤ Kf →
      (∀ x ∈ (centeredCube zP R hR : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
    ∀ u : weakSobolevGraph (centeredCube zP R hR),
      (∀ psi : killedSobolevGraph (centeredCube zP R hR),
        sobolevCoefficientForm (cutoffPositiveCoefficient M H omega (m + k) zP hR) u.val psi.val =
          ∫ x in (centeredCube zP R hR : Set (SpatialCoordinates d)), F x * psi.val.1 x) →
    ∃ U : SpatialCoordinates d → ℝ,
      ContinuousOn U (centeredCube zP R hR : Set (SpatialCoordinates d)) ∧
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube zP R hR : Set (SpatialCoordinates d))] U) ∧
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - U z) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - U z) ≤
        Ca * (normalizedL2On (Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2))
              (fun y => U y - (volume.real (Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2)))⁻¹ *
                ∫ v in Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2), U v) +
            ((3 : ℝ) ^ (-(k : ℤ))) ^ 2 *
              (aux_in_deterministic_onestep_sref M H omega (m + k) k z)⁻¹ * Kf) := by
  obtain ⟨h, theta, Ceps, Cdel, E0, hh, htheta, hthetah, hE0, hCeps, hCdel, hOS⟩ :=
    aux_in_deterministic_core_onestep_window_holds d hd I Det alpha sigma halpha hsigma hsigma32
  obtain ⟨Cg, deltaG, hCg, hdeltaG, hGST⟩ := lfgc_good_scale_transfer d I sigma hsigma hsigma32
  obtain ⟨C2, C3, hC20, hC30, hC2a, hC2b, hC2c, hC2d, hC3card, hC3eps, hC3a, hC3b⟩ :=
    exists_iterationBudgetConstants d alpha Ceps Cdel E0 Cg hE0 hCg
  obtain ⟨C, hC1, hHold⟩ := lfgc_holder_from_iteration d alpha halpha h theta (C2 + C3 + 0)
    hh htheta hthetah (by positivity)
  have ha : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by positivity
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hmargin : 0 < (1 - alpha) / (4 * C) := div_pos (by linarith only [halpha.2]) (by positivity)
  refine ⟨C * (3 : ℝ) ^ (C * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))),
    min ((1 - alpha) / (4 * C)) (E0 / (4 * Cg)),
    min deltaG (min (min ((1 - alpha) / (4 * C)) (E0 / (4 * Cg))) 1), ?_,
    lt_min hmargin (by positivity), lt_min hdeltaG (lt_min (lt_min hmargin (by positivity)) one_pos),
    ?_⟩
  · exact one_le_mul_of_one_le_of_one_le hC1
      (Real.one_le_rpow (by norm_num) (mul_nonneg hC0 ha))
  intro eps lam lamDet heps hepst hlam0 hlamlt hlamDet M hdelta H omega m k hm eta hEta hIR
    Fsc Psc Rsc Dsc Zsc goodEvt hPS hfin z hpre hpad zP R hR hsub F Kf hF hKf hbound u heq
  have hdel0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hdelG : M.delta ≤ deltaG := hdelta.trans (min_le_left _ _)
  have hdel1 : M.delta ≤ 1 := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdelt : M.delta ≤ min ((1 - alpha) / (4 * C)) (E0 / (4 * Cg)) :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcapE := iteration_error_cap Cg E0 M.delta eps hCg hdel0 hdel1
    (hdelt.trans (min_le_right _ _)) heps.1.le heps.2.le (hepst.trans (min_le_right _ _))
  have hG : ∀ (j : ℤ) (w : SpatialCoordinates d), 0 ≤ j → j ≤ ((m + k : ℕ) : ℤ) →
      Dsc (((m + k : ℕ) : ℤ) - j).toNat (((3 : ℝ) ^ (m + k)) • w) ≠ ⊤ →
      Zsc (((m + k : ℕ) : ℤ) - j).toNat (((3 : ℝ) ^ (m + k)) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (Lane4.cutoffPositiveCoefficient M H omega (m + k) w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega (m + k) j w) sigma 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc (((m + k : ℕ) : ℤ) - j).toNat (((3 : ℝ) ^ (m + k)) • w)).toReal) :=
    fun j w hj0 hjN hD hZ => hGST M H omega (m + k) j hj0 hjN hdelG eta hEta hIR eps heps
      Fsc Psc Rsc Dsc Zsc goodEvt hPS w hD hZ
  obtain ⟨fL2, hfL2, hload⟩ := boundedSource_load zP hR F Kf hF hbound
  have hf := boundedSource_memLp zP hR F Kf hF hbound (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
  have hu : ∀ psi : killedSobolevGraph (centeredCube zP R hR),
      sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega (m + k) zP hR)
          (u : SobolevData (centeredCube zP R hR)) (psi : SobolevData (centeredCube zP R hR)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube zP R hR)) := by
    intro psi
    rw [hload]
    exact heq psi
  obtain ⟨U, hU, huU⟩ := aux_in_deterministic_lowalpha_cont hd M H omega (m + k) zP R hR alpha
    halpha.1 halpha.2 F hf fL2 hfL2 u hu
  have hballsub : ∀ x ∈ Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2), |F x| ≤ Kf :=
    fun x hx => hbound x (hsub (Metric.ball_subset_closedBall hx))
  obtain ⟨fN, hfN, hfNK, hFq⟩ := aux_lfgc_above_holder_source d k alpha halpha z F Kf hKf hballsub
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hF.aestronglyMeasurable] at hFq
  have hdata := aux_lfgc_above_holder_data d I alpha sigma halpha hsigma h theta Ceps Cdel E0
    hCeps hCdel hOS Cg C2 C3 hCg hC20 hC2a hC2b hC2c hC2d hE0 hC3card hC3eps hC3a hC3b M H
    omega m k hm eta hEta hIR eps heps Fsc Psc Rsc Dsc Zsc goodEvt hPS hG hcapE hdel0 hdel1 z
    lam lamDet hlam0 hlamlt hfin hpre hpad zP R hR hsub F hf fL2 hfL2 u hu U hU huU fN hfN hFq
  have hs := aux_in_deterministic_onestep_sref_pos M H omega (m + k) k z
  have hS : 0 ≤ ((3 : ℝ) ^ (-(k : ℤ))) ^ 2 *
      (aux_in_deterministic_onestep_sref M H omega (m + k) k z)⁻¹ * fN :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hs.le)) hfN
  have hsmall := aux_lfgc_above_holder_margin alpha C _ lamDet M.delta eps halpha.2 hC1
    (min_le_left _ _) hlamDet hdel0 hdel1 hdelt heps.1.le heps.2.le hepst
  obtain ⟨hHolder, hnorm⟩ := hHold k z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) rfl U
    (hU.mono hsub) _ (lamDet + M.delta ^ 2 + eps ^ 8) _ ha
    (add_nonneg (add_nonneg (hlam0.trans hlamlt) (sq_nonneg _)) (pow_nonneg heps.1.le 8))
    hS hsmall hdata
  refine ⟨U, hU, huU, hHolder, hnorm.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _))
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hfNK (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hs.le)))

end Paper
