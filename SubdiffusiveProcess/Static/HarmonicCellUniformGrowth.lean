module

public import SubdiffusiveProcess.Static.HarmonicCellJoinedMoment
public import SubdiffusiveProcess.Static.HarmonicCellMacroscopicBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Transport

@[expose] public section

/-! # Closed uniform all-radius harmonic growth for signed physical cells -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Uniform all-radius native harmonic cell growth, including negative scales.
Every PDE and stochastic estimate is discharged by a proved library supplier. -/
theorem exists_uniform_cutoffHarmonicCell_growth (d : ℕ) :
    ∀ q : ℝ, 1 ≤ q →
      ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ M : GMCModel d, M.delta ≤ delta0 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (j : ℕ) (k : ℤ), j ≤ k.toNat → ∀ z : Vec d,
              ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
                eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C ∧
                ∀ᵐ omega ∂M.P.toMeasure,
                  CutoffHarmonicCellGrowth M j k z omega (K omega) := by
  intro q hq
  let n := d + 6
  let Q := q * (n : ℝ)
  let eta := 1 / (8 * (n : ℝ))
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by dsimp only [n]; omega)
  have hQ : 1 ≤ Q := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by dsimp only [n]; omega)
    dsimp only [Q]
    nlinarith
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hcost : eta * (n : ℝ) ≤ 1 / 4 := by
    dsimp only [eta]
    field_simp
    nlinarith
  obtain ⟨deltaR, A, hdeltaR, hA, hRs⟩ :=
    exists_harmonicMicroscopicCoefficientBank_moment_bound d Q eta hQ heta
  obtain ⟨deltaD, Cder, hdeltaD, hCder, hDs⟩ :=
    exists_harmonicMicroscopicDerivativeBank_moment_bound d Q eta hQ heta
  obtain ⟨deltaG, hdeltaG, hGs⟩ :=
    exists_uniform_cutoffHarmonicCell_macroscopic_growth d Q hQ
  refine ⟨min deltaG (min deltaR deltaD), lt_min hdeltaG (lt_min hdeltaR hdeltaD), ?_⟩
  intro M hM
  have hMR := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMD := hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hMG := hM.trans (min_le_left _ _)
  obtain ⟨Bpos, hBpos, hGpos⟩ := hGs M hMG
  let B := Bpos + 1 + A * (d : ℝ) ^ 2
  let C := B + harmonicCellJoiningPrice d (harmonicCellContrast d) *
    (A + B + 2 / harmonicCellContrast d * (Cder + 1)) ^ (d + 6)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBposB : Bpos ≤ B := by
    dsimp only [B]
    have h : 0 ≤ A * (d : ℝ) ^ 2 := by positivity
    linarith
  have hQprice := harmonicCellJoiningPrice_nonneg d (harmonicCellContrast_pos d).le
  have hcontrast := harmonicCellContrast_pos d
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro j k hjk z
  have hmp := Section6Covariance.measurePreserving_translatePotentialSample M z
  let R := harmonicMicroscopicCoefficientBank M j k.toNat ∘ translatePotentialSample z
  let D := harmonicMicroscopicDerivativeBank M j k.toNat ∘ translatePotentialSample z
  have hRm : Measurable R := (measurable_harmonicMicroscopicCoefficientBank M j k.toNat).comp hmp.measurable
  have hDm : Measurable D := (measurable_harmonicMicroscopicDerivativeBank M j k.toNat).comp hmp.measurable
  have hR : ∀ omega, 1 ≤ R omega := fun omega => one_le_harmonicMicroscopicCoefficientBank _ _ _ _
  have hD : ∀ omega, 1 ≤ D omega := fun omega => one_le_harmonicMicroscopicDerivativeBank _ _ _ _
  have hRn : eLpNorm R (ENNReal.ofReal Q) M.P.toMeasure ≤
      ENNReal.ofReal (A * (3 : ℝ) ^ (eta * (k.toNat : ℝ))) := by
    rw [eLpNorm_comp_measurePreserving
      (measurable_harmonicMicroscopicCoefficientBank M j k.toNat).aestronglyMeasurable hmp]
    exact hRs M hMR j k.toNat hjk
  have hDn : eLpNorm D (ENNReal.ofReal Q) M.P.toMeasure ≤
      ENNReal.ofReal (Cder * (3 : ℝ) ^ (eta * (k.toNat : ℝ))) := by
    rw [eLpNorm_comp_measurePreserving
      (measurable_harmonicMicroscopicDerivativeBank M j k.toNat).aestronglyMeasurable hmp]
    exact hDs M hMD j k.toNat hjk
  have hmacro : ∃ G : PotentialSample d → ℝ, Measurable G ∧ (∀ omega, 1 ≤ G omega) ∧
      eLpNorm G (ENNReal.ofReal Q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
      ∀ᵐ omega ∂M.P.toMeasure,
        CutoffHarmonicCellSignedMacroscopicGrowth M j k z omega (G omega) := by
    by_cases hk : 0 ≤ k
    · obtain ⟨G, hGm, hGone, hGn, hGa⟩ := hGpos j k.toNat hjk z
      refine ⟨G, hGm, hGone, hGn.trans (ENNReal.ofReal_le_ofReal hBposB), ?_⟩
      filter_upwards [hGa] with omega hGaomega
      have hkE : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
      simpa only [CutoffHarmonicCellSignedMacroscopicGrowth, CutoffHarmonicCellMacroscopicGrowth,
        vecNormSq, ← zpow_natCast, hkE] using hGaomega
    · have hk0 : k ≤ 0 := (lt_of_not_ge hk).le
      have hkN : k.toNat = 0 := by omega
      let G := fun omega => 1 + R omega * (d : ℝ) ^ 2
      have hGm : Measurable G := measurable_const.add (hRm.mul_const _)
      have hGone : ∀ omega, 1 ≤ G omega := fun omega =>
        le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans (hR omega)) (sq_nonneg _))
      have hGn : eLpNorm G (ENNReal.ofReal Q) M.P.toMeasure ≤ ENNReal.ofReal B := by
        have h1 : eLpNorm (fun _ : PotentialSample d => (1 : ℝ)) (ENNReal.ofReal Q) M.P.toMeasure = 1 := by
          rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hQ)).ne'
            (NeZero.ne M.P.toMeasure)]
          simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
        have hRn0 : eLpNorm R (ENNReal.ofReal Q) M.P.toMeasure ≤ ENNReal.ofReal A := by
          simpa only [hkN, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] using hRn
        have hmul : eLpNorm (fun omega => R omega * (d : ℝ) ^ 2)
            (ENNReal.ofReal Q) M.P.toMeasure ≤ ENNReal.ofReal (A * (d : ℝ) ^ 2) := by
          calc
            _ = ENNReal.ofReal ((d : ℝ) ^ 2) * eLpNorm R (ENNReal.ofReal Q) M.P.toMeasure := by
              have hf : (fun omega => R omega * (d : ℝ) ^ 2) = (d : ℝ) ^ 2 • R := by
                funext omega
                simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
              rw [hf, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
                abs_of_nonneg (sq_nonneg (d : ℝ))]
            _ ≤ ENNReal.ofReal ((d : ℝ) ^ 2) * ENNReal.ofReal A := mul_le_mul_right hRn0 _
            _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; ring
        have hs := (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hQ)).trans (add_le_add (le_of_eq h1) hmul)
        refine hs.trans ?_
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [B]
        linarith
      refine ⟨G, hGm, hGone, hGn, Filter.Eventually.of_forall ?_⟩
      intro omega
      exact cutoffHarmonicCellSignedMacroscopicGrowth_of_nonpos M j k hk0 z omega
  obtain ⟨G, hGm, hG, hGn, hGa⟩ := hmacro
  let K := fun omega => harmonicCellJoinedEnvelope d k.toNat (R omega) (D omega) (G omega)
  refine ⟨K, measurable_harmonicCellJoinedEnvelope d k.toNat R D G hRm hDm hGm,
    fun omega => one_le_harmonicCellJoinedEnvelope d k.toNat (hR omega) (hD omega) (hG omega), ?_, ?_⟩
  · exact harmonicCellJoinedEnvelope_norm_le M.P.toMeasure d k.toNat q hq R D G hRm hDm hGm
      hR hD hG hA.le hB.le hCder.le heta.le hcost hRn hDn hGn
  · filter_upwards [hGa] with omega hGaomega
    exact cutoffHarmonicCellGrowth_of_signed_macroscopic M j k z omega (hG omega) hGaomega

end SubdiffusiveProcess.Static
