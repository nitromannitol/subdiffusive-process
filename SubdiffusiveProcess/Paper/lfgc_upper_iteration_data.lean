import SubdiffusiveProcess.Paper.lfgc_upper_step

/-! Excess-iteration budgets on the scales above the last wavelength for either infrared variant.
The quantitative prefix and weak-equation assumptions remain explicit; no good event is assumed. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper
attribute [local instance] Classical.propDecidable

/-- The scales above the wavelength carry excess-iteration data whose bad count, errors and source defects are bounded linearly in depth. -/
theorem lfgc_upper_iteration_data
    (d : ℕ) [NeZero d] (I : Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Cg c0 C2 Csub : ℝ) (hCg : 0 ≤ Cg) (hc0 : 0 < c0) (_hC20 : 0 ≤ C2)
    (hC2a : 11 + c0⁻¹ ≤ C2) (hC2b : 2 * Ceps * Cg ≤ C2)
    (hC2c : 3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2)
    (hC2d : ((d : ℝ) + 3) / Real.log 3 ≤ C2) (_hCsub : 0 ≤ Csub)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (hG : ∀ (j : ℤ) (w : SpatialCoordinates d), 0 ≤ j → j ≤ (N : ℤ) →
      Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ →
      Zsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (Lane4.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w)).toReal))
    (hcapE : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 ≤ E0)
    (hdel0 : 0 ≤ M.delta) (hdel1 : M.delta ≤ 1)
    (k cbuf k0 horizon : ℕ) (hkN : k ≤ N)
    (qside : ℝ) (hqpos : 0 < qside) (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (qcenter : SpatialCoordinates d)
    (lambdaCut lambdaDet : ℝ) (hlam0 : 0 ≤ lambdaCut) (hlamlt : lambdaCut ≤ lambdaDet)
    (hpreAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA → DA ≤ horizon →
      k + DA ≤ N →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword)).toReal <
        lambdaCut * DA)
    (hfinAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k + DA ≤ N →
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
        Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) ≠ ⊤)
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
    (sk fN : ℝ) (hsk : sk = aux_in_deterministic_onestep_sref M H omega N k qcenter)
    (hfN : 0 ≤ fN)
    (hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fN * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))))
    (D : ℕ) (hDh : D ≤ horizon) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter (qside / 2))
    (jlo : ℤ) (hjlo1 : jlo ≤ -((k : ℤ) + (min D (N - k) : ℕ)) + 4)
    (hjlo2 : -((k : ℤ) + (min D (N - k) : ℕ)) - 2 ≤ jlo) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc jlo (-(k : ℤ)) ∧
    ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc jlo (-(k : ℤ)), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc jlo (-(k : ℤ)), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ C2 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), epsilon j ≤ C2 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), defect j ≤
        C2 * (3 : ℝ) ^ (C2 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) / qside := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hxq : ∀ i, |x i - qcenter i| < qside / 2 := by
    intro i
    have hx' : dist x qcenter < qside / 2 := hx
    rw [dist_pi_lt_iff (by positivity)] at hx'
    have := hx' i
    rwa [Real.dist_eq] at this
  obtain ⟨DA, hDAdef⟩ : ∃ DA : ℕ, DA = min D (N - k) := ⟨_, rfl⟩
  obtain ⟨dword, hdw⟩ := aux_in_deterministic_onestep_descendant_exists qcenter qside hqpos x
    (fun i => (hxq i).le) DA
  obtain ⟨w, hwdef⟩ : ∃ w : SpatialCoordinates d, w = descendantCenter 1 qcenter qside DA dword :=
    ⟨_, rfl⟩
  have hside : descendantSide 1 DA qside = (3 : ℝ) ^ (-((k : ℤ) + DA)) := by
    rw [aux_in_deterministic_onestep_descendantSide_one, hqside, neg_add,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), _root_.zpow_neg (3 : ℝ) (DA : ℤ), zpow_natCast,
      div_eq_mul_inv]
  have hxw : ∀ i, |x i - w i| ≤ (3 : ℝ) ^ (-((k : ℤ) + DA)) / 2 := by
    intro i; rw [← hside, hwdef]; exact (hdw i).1
  have hwq : ∀ i, |w i - qcenter i| < (3 : ℝ) ^ (-(k : ℤ)) / 2 := by
    intro i
    have h1 := (hdw i).2
    have h2 := descendantSide_pos 1 DA hqpos
    rw [← hqside, hwdef]; linarith only [h1, h2]
  have hkDA : k + DA ≤ N := by omega
  have hpre : k0 ≤ DA →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w)).toReal < lambdaCut * DA := by
    intro hk0
    rw [hwdef]
    exact hpreAll DA dword hk0 (by omega) hkDA
  have hfin : k0 ≤ DA → ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
      Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ := by
    intro _ l hl
    rw [hwdef]
    exact hfinAll DA dword hkDA l hl
  have hxk : x ∈ Metric.ball qcenter ((3 : ℝ) ^ (-(k : ℤ)) / 2) := by rw [← hqside]; exact hx
  have hup := fun (jlo : ℤ) (h1 : jlo ≤ -((k : ℤ) + DA) + 4) (h2 : -((k : ℤ) + DA) - 2 ≤ jlo) =>
    lfgc_upper_step d I alpha s hs h theta Ceps Cdel E0 hCeps hCdel hOS
      M H omega N eta hEta hIR eps Fsc Psc Rsc Dsc Zsc goodEvt hPS Cg hCg hG c0 hc0 hcapE
      k cbuf k0 DA hkDA jlo h1 h2 qcenter x w hxk hxw hwq lambdaCut hlam0 hpre hfin
      Qcentre Qside hQside hqp f hf fL2 hfL2 u hu U hU huU
  -- budget constants
  have hlamD : 0 ≤ lambdaDet := hlam0.trans hlamlt
  have ht0 : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by positivity
  have hX0 : 0 ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by positivity
  have hDA_le : (DA : ℝ) ≤ D := by rw [hDAdef]; exact_mod_cast (min_le_left D (N - k))
  have hsk0 : 0 < sk := by rw [hsk]; exact aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  have hW : 0 ≤ qside ^ 2 * sk⁻¹ * fN := by positivity
  have htl : lambdaCut ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ M.delta ^ 2 + eps ^ 8 := by positivity
    linarith only [this, hlamlt]
  have htd : M.delta ^ 2 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ eps ^ 8 := by positivity
    linarith only [this, hlamD]
  have hYb : ((d : ℝ) + 2) * (lambdaCut * DA) + (DA : ℝ) * M.delta ^ 2 ≤
      ((d : ℝ) + 3) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) := by
    have h1 : lambdaCut * DA ≤ (lambdaDet + M.delta ^ 2 + eps ^ 8) * D :=
      mul_le_mul htl hDA_le (Nat.cast_nonneg _) ht0
    have h2 : (DA : ℝ) * M.delta ^ 2 ≤ D * (lambdaDet + M.delta ^ 2 + eps ^ 8) :=
      mul_le_mul hDA_le htd (sq_nonneg _) (Nat.cast_nonneg D)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith only [h1, h2, hd0]
  have hTX : (lambdaDet + M.delta ^ 2 + eps ^ 8) * D ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by
    have : (0 : ℝ) ≤ (k0 : ℝ) + (cbuf : ℝ) := by positivity
    linarith only [this]
  have hdefect := fun (Sm : ℝ) (hSm0 : 0 ≤ Sm)
      (hSm : Sm ≤ (3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) / (1 - (3 : ℝ) ^ (-alpha))) =>
    aux_in_deterministic_onestep_budget_defect d hd k qside alpha Cdel
      (((d : ℝ) + 2) * (lambdaCut * DA) + (DA : ℝ) * M.delta ^ 2)
      sk _ fN Sm ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) C2 ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D)
      hqside halpha.1 halpha.2 hCdel hsk0 hfN hFq hSm0 hSm (by positivity) hYb hTX hC2c hC2d
  have hgeo := fun (a : ℤ) => aux_in_deterministic_onestep_geom_sum_le alpha halpha.1 a (-(k : ℤ))
  have hgeo0 := fun (a : ℤ) => Finset.sum_nonneg (fun j (_ : j ∈ Finset.Icc a (-(k : ℤ))) =>
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (alpha * (j : ℝ)))
  have hcardB := aux_in_deterministic_onestep_budget_card (k0 : ℝ) (cbuf : ℝ) (DA : ℝ) (D : ℝ)
    lambdaCut lambdaDet (lambdaDet + M.delta ^ 2 + eps ^ 8) c0 C2 (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hDA_le (Nat.cast_nonneg _) hlam0 hlamlt
    (by have : 0 ≤ M.delta ^ 2 + eps ^ 8 := by positivity
        linarith only [this]) hc0 hC2a
  have hepsB := aux_in_deterministic_onestep_budget_eps (k0 : ℝ) (cbuf : ℝ) (DA : ℝ) (D : ℝ)
    lambdaCut lambdaDet M.delta eps Ceps Cg C2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hDA_le
    (Nat.cast_nonneg _) hlam0 hlamlt hdel0 hdel1 heps.1.le heps.2.le hCeps hCg hC2b
  obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
    hup jlo (by rw [hDAdef]; exact hjlo1) (by rw [hDAdef]; exact hjlo2)
  refine ⟨bad, hbad, e, dl, hnn, hP, hc.trans hcardB, hse.trans hepsB, ?_⟩
  have hU3 := hdefect _ (hgeo0 jlo) (hgeo jlo)
  rw [← hsk] at hsd
  rw [le_div_iff₀ hqpos, mul_comm]
  exact (mul_le_mul_of_nonneg_left hsd hqpos.le).trans hU3


end Paper
