module

public import SubdiffusiveProcess.Paper.lfgc_upper_iteration_data
public import SubdiffusiveProcess.Paper.lfgc_lower_iteration_data

@[expose] public section

/-! Excess-iteration budgets at every depth of a cell, spliced from the scales above and below the last wavelength.
The quantitative prefix and weak-equation assumptions remain explicit; no good event is assumed. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper
attribute [local instance] Classical.propDecidable

/-- Every depth D and point of the cell carry excess-iteration data with budgets C(1+k₀+c+tD) and C·3^{C(k₀+c+tD)} r² s⁻¹ f_N. -/
theorem lfgc_iteration_data
    (d : ℕ) [NeZero d] (I : Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Cg c0 C2 Csub : ℝ) (hCg : 0 ≤ Cg) (hc0 : 0 < c0) (hC20 : 0 ≤ C2)
    (hC2a : 11 + c0⁻¹ ≤ C2) (hC2b : 2 * Ceps * Cg ≤ C2)
    (hC2c : 3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2)
    (hC2d : ((d : ℝ) + 3) / Real.log 3 ≤ C2) (hCsub : 0 ≤ Csub)
    (C3 : ℝ) (hE0 : 0 < E0)
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
    (hpadAll : k0 ≤ N - k → N - k + 1 ≤ horizon → ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤
        lambdaCut * ((N - k + 1 : ℕ) : ℝ))
    (D : ℕ) (hDh : D ≤ horizon) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter (qside / 2))
    (hlow : N + 1 < k + D → N < k + k0 →
      ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) ∧
      ∃ epsilon defect : ℤ → ℝ,
        (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
        (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), j ∉ bad →
          ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
            excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
              theta ^ h * excess j (translatedCube d j x) U +
                epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
        (bad.card : ℝ) ≤ Csub * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
        ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), epsilon j ≤
          Csub * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
        qside * ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), defect j ≤
          Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)) ∧
    ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ (C2 + C3 + Csub) * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), epsilon j ≤
        (C2 + C3 + Csub) * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      qside * ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), defect j ≤
        (C2 + C3 + Csub) * (3 : ℝ) ^ ((C2 + C3 + Csub) * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) := by
  have hlamD : 0 ≤ lambdaDet := hlam0.trans hlamlt
  have ht0 : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by positivity
  have hX0 : 0 ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by positivity
  have hsk0 : 0 < sk := by rw [hsk]; exact aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  have hW : 0 ≤ qside ^ 2 * sk⁻¹ * fN := by positivity
  have h1X : 0 ≤ 1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by linarith only [hX0]
  have hC30 : 0 ≤ C3 :=
    (by positivity : (0 : ℝ) ≤ 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2).trans hC3card
  have hCs1 : 0 ≤ Csub * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) := mul_nonneg hCsub h1X
  have hC31 : 0 ≤ C3 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) := mul_nonneg hC30 h1X
  have hup := fun (jlo : ℤ) (h1 : jlo ≤ -((k : ℤ) + (min D (N - k) : ℕ)) + 4)
      (h2 : -((k : ℤ) + (min D (N - k) : ℕ)) - 2 ≤ jlo) =>
    lfgc_upper_iteration_data d I alpha s halpha hs h theta Ceps Cdel E0
      hCeps hCdel hOS Cg c0 C2 Csub hCg hc0 hC20 hC2a hC2b hC2c hC2d hCsub M H omega N eta hEta
      hIR eps heps Fsc Psc Rsc Dsc Zsc goodEvt hPS hG hcapE hdel0 hdel1 k cbuf k0 horizon hkN
      qside hqpos hqside qcenter lambdaCut lambdaDet hlam0 hlamlt hpreAll hfinAll Qcentre Qside
      hQside hqp f hf fL2 hfL2 u hu U hU huU sk fN hsk hfN hFq D hDh x hx jlo h1 h2
  -- monotonicity of the defect budget in the constant
  have hmono : ∀ (C C' A : ℝ), 0 ≤ C → C ≤ C' →
      A ≤ C * (3 : ℝ) ^ (C * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) →
      A ≤ C' * (3 : ℝ) ^ (C' * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) := by
    intro C C' A hC hCC' hA
    have := aux_in_deterministic_onestep_budget_add C (C' - C) ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) (qside ^ 2 * sk⁻¹ * fN)
      A 0 hC (sub_nonneg.mpr hCC') hX0 hW hA (by
        have : 0 ≤ (C' - C) * (3 : ℝ) ^ ((C' - C) * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) := by
          have : 0 ≤ C' - C := sub_nonneg.mpr hCC'
          positivity
        exact this)
    rw [add_zero, show C + (C' - C) = C' by ring] at this
    exact this
  rcases Nat.lt_or_ge (N + 1) (k + D) with hcase | hcase
  · obtain ⟨badU, hbU, eU, dU, hnnU, hPU, hcU, hsU, htU⟩ :=
      hup (-(N : ℤ) - 3 + 1) (by omega) (by omega)
    by_cases hreg : k0 ≤ N - k
    · -- below the wavelength, prefix reaching the cutoff available: the proved lower range
      obtain ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL⟩ :=
        lfgc_lower_iteration_data d I alpha s halpha hs h theta Ceps Cdel E0
          hCeps hCdel hOS Cg c0 C3 hE0 hC3card hC3eps hC3a hC3b M H omega N eta hEta hIR eps heps
          Fsc Psc Rsc Dsc Zsc goodEvt hPS hG hcapE hdel0 hdel1 k cbuf k0 horizon hkN qside hqpos
          hqside qcenter lambdaCut lambdaDet hlam0 hlamlt hpreAll hfinAll Qcentre Qside hQside hqp
          f hf fL2 hfL2 u hu U hU huU sk fN hsk hfN hFq (hpadAll hreg (by omega)) D hDh x hx
          hreg hcase
      obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
        aux_in_deterministic_onestep_splice (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) (-(k : ℤ))
          (by omega) (by omega) (fun j e δ => ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              e * Real.sqrt (vecNormSq ell.slope) + δ)
          _ _ _ _ _ _ ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL⟩
          ⟨badU, hbU, eU, dU, hnnU, hPU, hcU, hsU, htU⟩
      refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
      · linarith only [hc, hCs1]
      · linarith only [hse, hCs1]
      · have hadd := aux_in_deterministic_onestep_budget_add C3 C2 ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))
          (qside ^ 2 * sk⁻¹ * fN) _ _ hC30 hC20 hX0 hW
          (le_refl (C3 * (3 : ℝ) ^ (C3 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
          (le_refl (C2 * (3 : ℝ) ^ (C2 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
        have hmul := mul_le_mul_of_nonneg_left hsd hqpos.le
        rw [mul_add, mul_div_cancel₀ _ hqpos.ne', mul_div_cancel₀ _ hqpos.ne'] at hmul
        have h2 := hmono (C3 + C2) (C2 + C3 + Csub) _ (add_nonneg hC30 hC20) (by linarith only [hCsub])
          (hmul.trans hadd)
        exact h2
    · -- below the wavelength, no prefix reaching the cutoff: the residual obligation
      obtain ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL⟩ := hlow hcase (by omega)
      have htL' : ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), dL j ≤
          Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) / qside := by
        rw [le_div_iff₀ hqpos, mul_comm]; exact htL
      obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
        aux_in_deterministic_onestep_splice (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) (-(k : ℤ))
          (by omega) (by omega) (fun j e δ => ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              e * Real.sqrt (vecNormSq ell.slope) + δ)
          _ _ _ _ _ _ ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL'⟩
          ⟨badU, hbU, eU, dU, hnnU, hPU, hcU, hsU, htU⟩
      refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
      · linarith only [hc, hC31]
      · linarith only [hse, hC31]
      · have hadd := aux_in_deterministic_onestep_budget_add C2 Csub ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))
          (qside ^ 2 * sk⁻¹ * fN) _ _ hC20 hCsub hX0 hW
          (le_refl (C2 * (3 : ℝ) ^ (C2 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
          (le_refl (Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
        have hmul := mul_le_mul_of_nonneg_left hsd hqpos.le
        rw [mul_add, mul_div_cancel₀ _ hqpos.ne', mul_div_cancel₀ _ hqpos.ne'] at hmul
        rw [add_comm C2 Csub] at hadd
        exact hmono (Csub + C2) (C2 + C3 + Csub) _ (add_nonneg hCsub hC20) (by linarith only [hC30])
          (by linarith only [hmul, hadd])
  · -- at or above the wavelength: the upper range is the whole ray
    obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
      hup (-((k : ℤ) + (D : ℤ))) (by omega) (by omega)
    refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
    · linarith only [hc, hCs1, hC31]
    · linarith only [hse, hCs1, hC31]
    · have hmul := mul_le_mul_of_nonneg_left hsd hqpos.le
      rw [mul_div_cancel₀ _ hqpos.ne'] at hmul
      exact hmono C2 (C2 + C3 + Csub) _ hC20 (by linarith only [hC30, hCsub]) hmul


end Paper
