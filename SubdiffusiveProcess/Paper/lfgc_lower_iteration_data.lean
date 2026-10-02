import SubdiffusiveProcess.Paper.lfgc_sub_step
import SubdiffusiveProcess.Paper.lfgc_lower_defect

/-! Excess-iteration budgets on the scales below the last wavelength, when the padded prefix reaches the cutoff.
The quantitative prefix and weak-equation assumptions remain explicit; no good event is assumed. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper
attribute [local instance] Classical.propDecidable

/-- The below-wavelength scales carry excess-iteration data with budgets linear in depth. -/
theorem lfgc_lower_iteration_data
    (d : ℕ) [NeZero d] (I : Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Cg c0 C3 : ℝ) (hE0 : 0 < E0)
    (hC3card : 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2 ≤ C3)
    (hC3eps : Ceps * 5 * (9 * (d : ℝ) / 2) ≤ C3)
    (hC3a : 9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C3)
    (hC3b : (2 * (d : ℝ) + 4) / Real.log 3 ≤ C3)
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
    (_hG : ∀ (j : ℤ) (w : SpatialCoordinates d), 0 ≤ j → j ≤ (N : ℤ) →
      Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ →
      Zsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (Lane4.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w)).toReal))
    (_hcapE : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 ≤ E0)
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
    (hpadAll : ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤
        lambdaCut * ((N - k + 1 : ℕ) : ℝ))
    (D : ℕ) (hDh : D ≤ horizon) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter (qside / 2))
    (hreg : k0 ≤ N - k) (hcase : N + 1 < k + D) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) ∧
    ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ C3 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), epsilon j ≤ C3 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), defect j ≤
        C3 * (3 : ℝ) ^ (C3 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) / qside := by
  have hlamD : 0 ≤ lambdaDet := hlam0.trans hlamlt
  have ht0 : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by positivity
  have htl : lambdaCut ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ M.delta ^ 2 + eps ^ 8 := by positivity
    linarith only [this, hlamlt]
  have hk0cb : (0 : ℝ) ≤ (k0 : ℝ) + (cbuf : ℝ) := by positivity
  have hG0 : 0 ≤ lambdaCut * ((N - k + 1 : ℕ) : ℝ) := by positivity
  have hDG : lambdaCut * ((N - k + 1 : ℕ) : ℝ) ≤ (lambdaDet + M.delta ^ 2 + eps ^ 8) * D := by
    have : ((N - k + 1 : ℕ) : ℝ) ≤ D := by exact_mod_cast (by omega : N - k + 1 ≤ D)
    exact mul_le_mul htl this (Nat.cast_nonneg _) ht0
  have hTX : (lambdaDet + M.delta ^ 2 + eps ^ 8) * D ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by linarith only [hk0cb]
  obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
    lfgc_sub_step d I alpha s hs h theta Ceps Cdel E0 hCeps hCdel hE0 hOS
      M H omega N eta hEta hIR eps Fsc Psc Rsc Dsc Zsc goodEvt hPS k hkN qside hqpos hqside
      qcenter (lambdaCut * ((N - k + 1 : ℕ) : ℝ)) hG0 hpadAll Qcentre Qside hQside hqp f hf fL2
      hfL2 u hu U hU huU D x hx
  refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
  · have hc1 : 0 < min 1 (E0 / 5) := lt_min one_pos (by positivity)
    exact hc.trans (aux_in_deterministic_onestep_budget_card_sub (9 * (d : ℝ) / 2)
      (min 1 (E0 / 5)) (lambdaCut * ((N - k + 1 : ℕ) : ℝ)) ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) C3 (by positivity) hc1 hG0
      (hDG.trans hTX) hC3card)
  · have hb := aux_in_deterministic_onestep_budget_eps_sub (Ceps * 5 * (9 * (d : ℝ) / 2))
      (lambdaCut * ((N - k + 1 : ℕ) : ℝ)) ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) C3 (by positivity) hG0 (hDG.trans hTX) hC3eps
    refine hse.trans (le_trans (le_of_eq ?_) hb)
    ring
  · exact lfgc_lower_defect d I alpha s halpha hs M H omega N eta
      hEta hIR eps heps Fsc Psc Rsc Dsc Zsc goodEvt hPS hdel0 hdel1 k cbuf k0 horizon hkN
      qside hqpos hqside qcenter lambdaCut lambdaDet hlam0 hlamlt hpreAll hfinAll Cdel hCdel
      C3 hC3a hC3b f sk fN hsk hfN hFq D hDh x hx hreg hcase _ hsd


end Paper
