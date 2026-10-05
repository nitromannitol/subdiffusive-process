module

public import SubdiffusiveProcess.Paper.lfgc_sub_reference

@[expose] public section

/-! The source defects of the scales below the wavelength are bounded by the iteration's source budget.
The quantitative prefix and weak-equation assumptions remain explicit; no good event is assumed. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The summed below-wavelength source defect is bounded by C₃ 3^{C₃(k₀+c+tD)} r² s_k⁻¹ f_N / r. -/
theorem lfgc_lower_defect
    (d : ℕ) [NeZero d] (_I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
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
    (Cdel : ℝ) (hCdel : 0 ≤ Cdel) (C3 : ℝ)
    (hC3a : 9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C3)
    (hC3b : (2 * (d : ℝ) + 4) / Real.log 3 ≤ C3)
    (f : SpatialCoordinates d → ℝ)
    (sk fN : ℝ) (hsk : sk = aux_in_deterministic_onestep_sref M H omega N k qcenter)
    (hfN : 0 ≤ fN)
    (hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fN * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))))
    (D : ℕ) (hDh : D ≤ horizon) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter (qside / 2))
    (hreg : k0 ≤ N - k) (hcase : N + 1 < k + D) (Sd : ℝ)
    (hsd : Sd ≤ Cdel * (cutoffCoefficient M H omega N x)⁻¹ *
          (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
            (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal *
          ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), (3 : ℝ) ^ (alpha * (j : ℝ))) :
    Sd ≤ C3 * (3 : ℝ) ^ (C3 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) / qside := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hlamD : 0 ≤ lambdaDet := hlam0.trans hlamlt
  have ht0 : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by positivity
  have htl : lambdaCut ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ M.delta ^ 2 + eps ^ 8 := by positivity
    linarith only [this, hlamlt]
  have htd : M.delta ^ 2 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ eps ^ 8 := by positivity
    linarith only [this, hlamD]
  have hk0cb : (0 : ℝ) ≤ (k0 : ℝ) + (cbuf : ℝ) := by positivity
  have hTX : (lambdaDet + M.delta ^ 2 + eps ^ 8) * D ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by linarith only [hk0cb]
  set Sig : ℝ := lambdaCut * ((N - k : ℕ) : ℝ) with hSig
  have hDAh : N - k ≤ horizon := by omega
  have hself : ∀ dword : Fin (N - k) → OddGridIndex d 1,
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside (N - k) dword)).toReal ≤ Sig ∧
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)),
        Dsc ((N : ℤ) - l).toNat
          (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside (N - k) dword) ≠ ⊤ := by
    intro dword
    exact ⟨(hpreAll (N - k) dword hreg hDAh (by omega)).2.le,
      hfinAll (N - k) dword (by omega)⟩
  have hratio := lfgc_sub_reference M H omega N eta hEta hIR s eps hs
    Fsc Psc Rsc Dsc Zsc goodEvt hPS k cbuf hkN qside hqpos hqside qcenter x hx Sig hself
  rw [← hsk] at hratio
  have hsk0 : 0 < sk := by rw [hsk]; exact aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  set Ysub : ℝ := ((d : ℝ) + 2) * Sig + ((N - k : ℕ) : ℝ) * M.delta ^ 2 + (d : ℝ) * Sig + Sig +
    M.delta ^ 2 with hYsub
  set S : ℝ := ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3),
    (3 : ℝ) ^ (alpha * (j : ℝ)) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (by norm_num) _
  have hSle : S ≤ (3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) / (1 - (3 : ℝ) ^ (-alpha)) := by
    have hg := aux_in_deterministic_onestep_geom_sum_le alpha halpha.1 (-((k : ℤ) + (D : ℤ)))
      (-(N : ℤ) - 3)
    refine hg.trans ?_
    have hr : (3 : ℝ) ^ (-alpha) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [halpha.1])
    apply div_le_div_of_nonneg_right _ (by linarith only [hr])
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ halpha.1.le
    have : (-(N : ℤ) - 3 : ℤ) ≤ -(k : ℤ) := by omega
    exact_mod_cast this
  have hYb : Ysub ≤ (2 * (d : ℝ) + 4) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) + 1 := by
    have hNk : ((N - k : ℕ) : ℝ) ≤ D := by exact_mod_cast (by omega : N - k ≤ D)
    have hs1 : Sig ≤ (lambdaDet + M.delta ^ 2 + eps ^ 8) * D :=
      mul_le_mul htl hNk (Nat.cast_nonneg _) ht0
    have hs2 : ((N - k : ℕ) : ℝ) * M.delta ^ 2 ≤ (lambdaDet + M.delta ^ 2 + eps ^ 8) * D := by
      rw [mul_comm (lambdaDet + M.delta ^ 2 + eps ^ 8)]
      exact mul_le_mul hNk htd (sq_nonneg _) (Nat.cast_nonneg _)
    have hδ1 : M.delta ^ 2 ≤ 1 := by
      have := mul_le_mul hdel1 hdel1 hdel0 zero_le_one
      nlinarith only [this]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hSig0 : 0 ≤ Sig := by positivity
    have e1 : (d : ℝ) * Sig ≤ (d : ℝ) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) :=
      mul_le_mul_of_nonneg_left hs1 hd0
    have e2 : ((d : ℝ) + 2) * Sig ≤ ((d : ℝ) + 2) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) :=
      mul_le_mul_of_nonneg_left hs1 (by positivity)
    have e3 : (2 * (d : ℝ) + 4) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) =
        ((d : ℝ) + 2) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) +
          (d : ℝ) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) +
          (lambdaDet + M.delta ^ 2 + eps ^ 8) * D +
          (lambdaDet + M.delta ^ 2 + eps ^ 8) * D := by ring
    rw [hYsub, e3]
    linarith only [e1, e2, hs1, hs2, hδ1]
  have hmono : Sd ≤ Cdel * (Real.exp Ysub * sk⁻¹) *
        (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
          (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal * S := by
    refine hsd.trans ?_
    apply mul_le_mul_of_nonneg_right _ hS0
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    exact mul_le_mul_of_nonneg_left hratio hCdel
  have hB := aux_in_deterministic_onestep_budget_defect_gen d hd k qside alpha Cdel Ysub sk _ fN
    S ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) C3 ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) (2 * (d : ℝ) + 4) hqside halpha.1 halpha.2
    hCdel hsk0 hfN hFq hSle (by positivity) (by positivity) hYb hTX hC3a hC3b
  rw [le_div_iff₀ hqpos, mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono hqpos.le).trans hB


end SubdiffusiveProcess.Paper
