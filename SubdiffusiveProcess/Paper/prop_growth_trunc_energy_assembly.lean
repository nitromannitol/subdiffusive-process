module

public import SubdiffusiveProcess.Paper.prop_growth_trunc_macro_energy
public import SubdiffusiveProcess.Paper.prop_growth_trunc_bank
public import SubdiffusiveProcess.Paper.truncation_local_lipschitz_majorant
public import SubdiffusiveProcess.Paper.prop_growth_energy_assembly
public import SubdiffusiveProcess.Paper.infrared_characterization_local_lipschitz_majorant
public import SubdiffusiveProcess.Paper.aux_macro_moment_bank
public import SubdiffusiveProcess.Analysis.InfraredTruncationBound
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

@[expose] public section

/-!
# All-radii energy growth at a finite infrared truncation

The energy half of `mfd:prop-growth` for every `H_{L'}`: the macro bound above the wavelength
and the microscopic estimate below it, with the coefficient envelope and log-Lipschitz
majorant transferred from the characterized field.  Not claimed: constants uniform in the model.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Envelope transfer: if `M⁻¹ ≤ a_H ≤ M` at `x` and `|HT - H| ≤ W` there, then
`(M e^W)⁻¹ ≤ a_HT ≤ M e^W` at `x`. -/
theorem aux_prop_growth_trunc_energy_assembly_envelope_transfer {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H HT : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) (Mx W : ℝ) (hMx : 0 < Mx)
    (hlo : Mx⁻¹ ≤ cutoffCoefficient M H om N x) (hhi : cutoffCoefficient M H om N x ≤ Mx)
    (hW : |HT om x - H om x| ≤ W) :
    (Mx * Real.exp W)⁻¹ ≤ cutoffCoefficient M HT om N x ∧
      cutoffCoefficient M HT om N x ≤ Mx * Real.exp W := by
  rw [aux_prop_growth_trunc_bank_ratio M H HT om N x]
  have hpos := cutoffCoefficient_pos M H om N x
  have h1 : Real.exp (-W) ≤ Real.exp (HT om x - H om x) :=
    Real.exp_le_exp.2 (by linarith [neg_abs_le (HT om x - H om x)])
  have h2 : Real.exp (HT om x - H om x) ≤ Real.exp W :=
    Real.exp_le_exp.2 ((le_abs_self _).trans hW)
  constructor
  · rw [mul_inv, ← Real.exp_neg]
    exact mul_le_mul hlo h1 (Real.exp_pos _).le hpos.le
  · exact mul_le_mul hhi h2 (Real.exp_pos _).le hMx.le

/-- Log-Lipschitz transfer: the log-Lipschitz majorant of `a_HT` at scale `3^{-N}` is that of
`a_H` plus the Lipschitz constants of `HT` and `H`. -/
theorem aux_prop_growth_trunc_energy_assembly_loglip_transfer {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H HT : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (x y : SpatialCoordinates d) (D GT GH : ℝ) (hGT : 0 ≤ GT) (hGH : 0 ≤ GH)
    (hlog : |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
      D * (3 : ℝ) ^ N * dist x y)
    (hT : |HT om x - HT om y| ≤ GT * dist x y) (hH : |H om x - H om y| ≤ GH * dist x y) :
    |Real.log (cutoffCoefficient M HT om N x) - Real.log (cutoffCoefficient M HT om N y)| ≤
      (D + GT + GH) * (3 : ℝ) ^ N * dist x y := by
  rw [aux_prop_growth_trunc_bank_ratio M H HT om N x,
    aux_prop_growth_trunc_bank_ratio M H HT om N y,
    Real.log_mul (cutoffCoefficient_pos M H om N x).ne' (Real.exp_pos _).ne',
    Real.log_mul (cutoffCoefficient_pos M H om N y).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp]
  have e : Real.log (cutoffCoefficient M H om N x) + (HT om x - H om x) -
      (Real.log (cutoffCoefficient M H om N y) + (HT om y - H om y)) =
      (Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)) +
        (HT om x - HT om y) + -(H om x - H om y) := by ring
  rw [e]
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  have hd0 : 0 ≤ dist x y := dist_nonneg
  have hT3 : GT * dist x y ≤ GT * (3 : ℝ) ^ N * dist x y := by
    have := mul_le_mul_of_nonneg_left h3 hGT
    exact mul_le_mul_of_nonneg_right (by linarith) hd0
  have hH3 : GH * dist x y ≤ GH * (3 : ℝ) ^ N * dist x y := by
    have := mul_le_mul_of_nonneg_left h3 hGH
    exact mul_le_mul_of_nonneg_right (by linarith) hd0
  have hsum := abs_add_three
    (Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y))
    (HT om x - HT om y) (-(H om x - H om y))
  rw [abs_neg] at hsum
  have hexp : (D + GT + GH) * (3 : ℝ) ^ N * dist x y = D * (3 : ℝ) ^ N * dist x y +
      GT * (3 : ℝ) ^ N * dist x y + GH * (3 : ℝ) ^ N * dist x y := by ring
  linarith

/-- Moments of the transferred log-Lipschitz majorant `D + G_T + G_H`. -/
theorem aux_prop_growth_trunc_energy_assembly_loglip_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℝ) (hq : 1 ≤ q) (D GT GH : Ω → ℝ) (CDp CT CH : ℝ)
    (hD : MemLp D (ENNReal.ofReal (2 * q)) μ)
    (hDb : eLpNorm D (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal CDp)
    (hGT : MemLp GT (ENNReal.ofReal q) μ) (hGTb : eLpNorm GT (ENNReal.ofReal q) μ ≤ ENNReal.ofReal CT)
    (hGH : MemLp GH (ENNReal.ofReal q) μ) (hGHb : eLpNorm GH (ENNReal.ofReal q) μ ≤ ENNReal.ofReal CH) :
    MemLp (fun om => D om + GT om + GH om) (ENNReal.ofReal q) μ ∧
      eLpNorm (fun om => D om + GT om + GH om) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal CDp + ENNReal.ofReal CT + ENNReal.ofReal CH := by
  have hle : ENNReal.ofReal q ≤ ENNReal.ofReal (2 * q) := ENNReal.ofReal_le_ofReal (by linarith)
  have hDq : MemLp D (ENNReal.ofReal q) μ := hD.mono_exponent hle
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  refine ⟨(hDq.add hGT).add hGH, ?_⟩
  refine (eLpNorm_add_le hp1).trans (add_le_add ?_ hGHb)
  refine (eLpNorm_add_le hp1).trans (add_le_add ?_ hGTb)
  exact (eLpNorm_le_eLpNorm_of_exponent_le hle).trans hDb

/-- Moments of the transferred envelope `M_x R_T R_H` by Hölder's inequality. -/
theorem aux_prop_growth_trunc_energy_assembly_envelope_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ) (Mx RT RH : Ω → ℝ) (B : ℝ)
    (hMx : MemLp Mx (ENNReal.ofReal (2 * q)) μ)
    (hMxb : eLpNorm Mx (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal B)
    (hRT : MemLp RT (ENNReal.ofReal (2 * (2 * q))) μ)
    (hRH : MemLp RH (ENNReal.ofReal (2 * (2 * q))) μ) :
    MemLp (fun om => Mx om * (RT om * RH om)) (ENNReal.ofReal q) μ ∧
      eLpNorm (fun om => Mx om * (RT om * RH om)) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal B * (eLpNorm RT (ENNReal.ofReal (2 * (2 * q))) μ *
          eLpNorm RH (ENNReal.ofReal (2 * (2 * q))) μ) := by
  have hW : eLpNorm (fun om => RT om * RH om) (ENNReal.ofReal (2 * q)) μ ≤
      eLpNorm RT (ENNReal.ofReal (2 * (2 * q))) μ * eLpNorm RH (ENNReal.ofReal (2 * (2 * q))) μ :=
    aux_aux_macro_moment_bank_product_moment μ (2 * q) RT RH hRT.aestronglyMeasurable hRH.aestronglyMeasurable
  have hb : eLpNorm (fun om => Mx om * (RT om * RH om)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal B * (eLpNorm RT (ENNReal.ofReal (2 * (2 * q))) μ *
        eLpNorm RH (ENNReal.ofReal (2 * (2 * q))) μ) :=
    (aux_aux_macro_moment_bank_product_moment μ q Mx _ hMx.aestronglyMeasurable (hRT.aestronglyMeasurable.mul hRH.aestronglyMeasurable)).trans
      (mul_le_mul' hMxb hW)
  have hfin : ENNReal.ofReal B * (eLpNorm RT (ENNReal.ofReal (2 * (2 * q))) μ *
      eLpNorm RH (ENNReal.ofReal (2 * (2 * q))) μ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hRT.eLpNorm_lt_top.ne hRH.eLpNorm_lt_top.ne)
  exact ⟨lt_of_le_of_lt hb (lt_top_iff_ne_top.2 hfin), hb⟩

/-- **Root envelope at a finite infrared truncation.**  For `H_L` the coefficient envelope and
the log-Lipschitz majorant of `root_extremes` persist on every root `Q̄(z,r)`, `r ≤ 1`; the
growth rate `C_d δ + C_p δ²` and the threshold are those of `root_extremes`, fixed before the
model, and only the moment constants change, by the weight `e^{H_L - H}`. -/
theorem aux_prop_growth_trunc_energy_assembly_root_extremes (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cp Cd cd : ℝ, 0 < Cp ∧ 0 < Cd ∧ 0 < cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L0 : ℕ), M.delta ≤ cd / (2 * q) →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ (D Mx : ℕ → BilateralField d → ℝ) (CD CE : ℝ), 0 ≤ CD ∧ 0 ≤ CE ∧
          (∀ N om, 0 ≤ D N om ∧ 0 ≤ Mx N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < Mx N om ∧
            (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              (Mx N om)⁻¹ ≤ cutoffCoefficient M (fun om' => infraredPartialSum om' L0) om N x ∧
                cutoffCoefficient M (fun om' => infraredPartialSum om' L0) om N x ≤ Mx N om) ∧
            (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M (fun om' => infraredPartialSum om' L0) om N x) -
                  Real.log (cutoffCoefficient M (fun om' => infraredPartialSum om' L0) om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y)) ∧
          (∀ N, MemLp (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
            MemLp (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ)))) ∧
          (∀ N, eLpNorm (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CE * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N))) := by
  obtain ⟨Cp, Cd, cd, hCp, hCd, hcd, hroot⟩ :=
    aux_prop_growth_energy_assembly_root_extremes d hd (2 * q) (by linarith)
  refine ⟨Cp, Cd, cd / 2, hCp, hCd, by positivity, ?_⟩
  intro M L0 hδ z r hr hr1
  have hδ' : M.delta ≤ cd / (2 * (2 * q)) := by
    have e : cd / 2 / (2 * q) = cd / (2 * (2 * q)) := by ring
    rw [← e]; exact hδ
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  obtain ⟨D, Mx, CE, hCE, hDMx0, hae, hmem, hDmom, hMxmom⟩ := hroot M H hH hδ' z r hr hr1
  obtain ⟨CT, hCT, hTlip⟩ := truncation_local_lipschitz_majorant d hd z r hr q hq
  obtain ⟨GT, hGT0, hGTae, hGTmem, hGTnorm⟩ := hTlip M L0
  obtain ⟨CH, hCH, hHlip⟩ := infrared_characterization_local_lipschitz_majorant d hd z r hr q hq
  obtain ⟨GH, hGH0, hGHae, hGHmem, hGHnorm⟩ := hHlip M H hH
  have hRT : MemLp (fun om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr)
      (ENNReal.ofReal (2 * (2 * q))) (chaosSampleLaw M).toMeasure :=
    (aux_prop_growth_trunc_bank_reference hd M L0 (closedCube z r hr) (2 * (2 * q)) (by linarith)).2.2
  have hRH : MemLp (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z r hr)
      (ENNReal.ofReal (2 * (2 * q))) (chaosSampleLaw M).toMeasure :=
    (aux_aux_macro_moment_bank_reference hd M H hH (closedCube z r hr) (2 * (2 * q))
      (by linarith)).2.2
  obtain ⟨BW, hBW⟩ : ∃ BW : ℝ≥0∞, BW =
      eLpNorm (fun om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr)
          (ENNReal.ofReal (2 * (2 * q))) (chaosSampleLaw M).toMeasure *
        eLpNorm (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z r hr)
          (ENNReal.ofReal (2 * (2 * q))) (chaosSampleLaw M).toMeasure := ⟨_, rfl⟩
  have hBWfin : BW ≠ ⊤ := by
    rw [hBW]; exact ENNReal.mul_ne_top hRT.eLpNorm_lt_top.ne hRH.eLpNorm_lt_top.ne
  have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hsq : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hlip := fun N => aux_prop_growth_trunc_energy_assembly_loglip_moment (chaosSampleLaw M).toMeasure q hq (D N) GT GH
    (Cp * Real.sqrt (1 + (N : ℝ))) (CT * M.delta * Real.sqrt q) (CH * M.delta * Real.sqrt q)
    (hmem N).1 (hDmom N) hGTmem hGTnorm hGHmem hGHnorm
  have henv := fun N => aux_prop_growth_trunc_energy_assembly_envelope_moment (chaosSampleLaw M).toMeasure q (Mx N)
    (fun om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr)
    (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z r hr)
    (CE * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)) (hmem N).2 (hMxmom N) hRT hRH
  refine ⟨fun N om => D N om + GT om + GH om,
    fun N om => Mx N om * (aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr *
      aux_prop_growth_trunc_bank_refFactor (H om) z r hr),
    Cp + CT * M.delta * Real.sqrt q + CH * M.delta * Real.sqrt q, CE * BW.toReal,
    by positivity, mul_nonneg hCE ENNReal.toReal_nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · intro N om
    exact ⟨add_nonneg (add_nonneg (hDMx0 N om).1 (hGT0 om)) (hGH0 om),
      mul_nonneg (hDMx0 N om).2 (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)⟩
  · filter_upwards [hae, hGTae, hGHae] with om h1 hT hHl
    intro N
    obtain ⟨hpos, hbd, hlg⟩ := h1 N
    refine ⟨mul_pos hpos (mul_pos (Real.exp_pos _) (Real.exp_pos _)), ?_, ?_⟩
    · intro x hx
      have h := aux_prop_growth_trunc_energy_assembly_envelope_transfer M H (fun om' => infraredPartialSum om' L0) om N x
        (Mx N om) _ hpos (hbd x hx).1 (hbd x hx).2
        (aux_prop_growth_trunc_bank_diff_le (infraredPartialSum om L0) (H om) z r hr x hx)
      rw [Real.exp_add] at h
      exact h
    · intro x y hx hy
      exact aux_prop_growth_trunc_energy_assembly_loglip_transfer M H (fun om' => infraredPartialSum om' L0) om N x y
        (D N om) (GT om) (GH om) (hGT0 om) (hGH0 om) (hlg x y hx hy) (hT x y hx hy)
        (hHl x y hx hy)
  · intro N
    exact ⟨(hlip N).1, (henv N).1⟩
  · intro N
    refine (hlip N).2.trans ?_
    have h1 : (1 : ℝ) ≤ Real.sqrt (1 + (N : ℝ)) := by
      have h := Real.sqrt_le_sqrt
        (show (1 : ℝ) ≤ 1 + (N : ℝ) by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
      rwa [Real.sqrt_one] at h
    have hT0 : 0 ≤ CT * M.delta * Real.sqrt q := by positivity
    have hH0 : 0 ≤ CH * M.delta * Real.sqrt q := by positivity
    rw [← ENNReal.ofReal_add (by positivity) hT0, ← ENNReal.ofReal_add (by positivity) hH0]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (Cp + CT * M.delta * Real.sqrt q + CH * M.delta * Real.sqrt q) *
        Real.sqrt (1 + (N : ℝ)) = Cp * Real.sqrt (1 + (N : ℝ)) +
          CT * M.delta * Real.sqrt q * Real.sqrt (1 + (N : ℝ)) +
          CH * M.delta * Real.sqrt q * Real.sqrt (1 + (N : ℝ)) := by ring
    rw [e]
    have a1 := le_mul_of_one_le_right hT0 h1
    have a2 := le_mul_of_one_le_right hH0 h1
    linarith
  · intro N
    refine (henv N).2.trans (le_of_eq ?_)
    rw [← hBW, ← ENNReal.ofReal_toReal hBWfin, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal hBWfin]
    congr 1
    ring


theorem prop_growth_trunc_energy_assembly :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d) (_S : SobolevFoundationalInput d hd)
    (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 →
    (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (L0 : ℕ),
      H = (fun om' => infraredPartialSum om' L0) → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t := by

  intro d hd _ _ E P X W Cp S t alpha k ps ht htd halp halt hps
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨p1, hp1, hp1t⟩ := aux_prop_growth_energy_assembly_p1_choice d hd t htd
  obtain ⟨t1, ht1def⟩ : ∃ s : ℝ, s = (t + d) / 2 := ⟨_, rfl⟩
  have htt1 : t < t1 := by rw [ht1def]; linarith
  have ht1d : t1 < d := by rw [ht1def]; linarith
  obtain ⟨C, hC, hmic, hmom⟩ :=
    aux_prop_growth_energy_assembly_micro_local d hd W p1 t t1 hp1 ht htt1 ht1d hp1t
  obtain ⟨Q0, hQ0def⟩ : ∃ q : ℝ, q = 2 * (1 + ∑ i, ps i) * max 1 t := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg (fun i _ => le_trans zero_le_one (hps i))
  have hmax1 : 1 ≤ max 1 t := le_max_left _ _
  have hQ0 : 1 ≤ Q0 := by
    rw [hQ0def]
    have h1 : 1 ≤ 2 * (1 + ∑ i, ps i) := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 2 * (1 + ∑ i, ps i) * max 1 t := mul_le_mul h1 hmax1 zero_le_one (by linarith)
  have hqi : ∀ i, 2 * ps i * max 1 t ≤ Q0 := by
    intro i
    rw [hQ0def]
    have h1 : ps i ≤ 1 + ∑ j, ps j := by
      have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j))
        (Finset.mem_univ i)
      linarith
    have h2 : 2 * ps i ≤ 2 * (1 + ∑ j, ps j) := by linarith
    exact mul_le_mul_of_nonneg_right h2 (by linarith)
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    aux_prop_growth_trunc_energy_assembly_root_extremes d hd Q0 hQ0
  obtain ⟨dM, hdM, hmacro⟩ := prop_growth_trunc_macro_energy d hd E P X S t1 1 (fun _ => Q0)
    (by linarith) ht1d (fun _ => hQ0)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrmax : 0 < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := by
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith))) hlog3
  obtain ⟨delta0, aRate, hδ0, hδM, hδc, haR0, haR, hmono⟩ :=
    aux_prop_growth_energy_assembly_threshold Cd Cpe _ dM (cd / (2 * Q0)) hCd hCpe hrmax hdM
      (by positivity)
  refine ⟨delta0, hδ0, ?_⟩
  intro M Rm H L0 hHT hδ z r hr hr1
  obtain ⟨Kmac, CbM, hKmac0, hKmem, hKnorm, hKae⟩ :=
    hmacro M Rm H L0 hHT (hδ.trans hδM) z r hr hr1
  subst hHT
  obtain ⟨D, Mx, CD, CE, hCD, hCE, hDMx0, hae, hmem, hDmom, hMxmom⟩ :=
    hroot M L0 (hδ.trans hδc) z r hr hr1
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ aRate :=
    hmono _ M.shellPrefix.delta_pos.le hδ
  have hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      eLpNorm (fun o => (1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o)
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
      eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
      eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + D N o) ^ t)
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
    intro i
    have hle : ENNReal.ofReal (2 * ps i * max 1 t) ≤ ENNReal.ofReal Q0 :=
      ENNReal.ofReal_le_ofReal (hqi i)
    have hqi1 : 1 ≤ 2 * ps i * max 1 t := by
      have := hps i
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 * ps i * max 1 t := mul_le_mul (by linarith) hmax1 zero_le_one (by linarith)
    have hMxN : ∀ N : ℕ, eLpNorm (fun o => Mx N o + Mx N o)
        (ENNReal.ofReal (2 * ps i * max 1 t)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (2 * CE * Real.exp (aRate * (N : ℝ))) := by
      intro N
      have h1 := aux_prop_growth_energy_assembly_double (chaosSampleLaw M).toMeasure (Mx N)
        (2 * ps i * max 1 t) Q0 (CE * Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N))
        hqi1 (hqi i) (hmem N).2.aestronglyMeasurable (by positivity) (hMxmom N)
      refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have he : Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N) ≤
          Real.exp (aRate * (N : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate hN)
      have := mul_le_mul_of_nonneg_left he hCE
      linarith
    exact hmom (BilateralField d) (chaosSampleLaw M).toMeasure (ps i) (hps i) D Mx Mx Kmac
      CD (2 * CE) (max (CbM 0) 0) aRate hCD (by positivity) (le_max_right _ _) haR0 haR
      (fun N o => ⟨(hDMx0 N o).1, (hDMx0 N o).2, (hDMx0 N o).2, hKmac0 N o⟩)
      (fun N => ⟨(hmem N).1.mono_exponent hle, (hmem N).2.mono_exponent hle,
        (hmem N).2.mono_exponent hle, (hKmem 0 N).mono_exponent hle⟩)
      (fun N => (eLpNorm_le_eLpNorm_of_exponent_le hle).trans (hDmom N))
      hMxN
      (fun N => (eLpNorm_le_eLpNorm_of_exponent_le hle).trans
        ((hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  have hKps : ∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (max (CbM 0) 0) := by
    intro i N
    have hle : ENNReal.ofReal (ps i) ≤ ENNReal.ofReal Q0 := by
      refine ENNReal.ofReal_le_ofReal ?_
      have := hqi i
      have h2 : ps i ≤ 2 * ps i * max 1 t := by
        have hp := hps i
        calc ps i = ps i * 1 * 1 := by ring
          _ ≤ ps i * 2 * max 1 t := by
            apply mul_le_mul _ hmax1 zero_le_one (by linarith)
            exact mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
          _ = 2 * ps i * max 1 t := by ring
      linarith
    exact (eLpNorm_le_eLpNorm_of_exponent_le hle).trans
      ((hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have h2r : 0 ≤ (2 / r) ^ t := Real.rpow_nonneg (by positivity) _
  obtain ⟨K, Cbound, hKmem', hKnorm', hK1, hKdom⟩ :=
    aux_prop_growth_energy_assembly_final (chaosSampleLaw M).toMeasure k ps hps t t1 (d : ℝ)
      ((2 / r) ^ t) (aux_prop_growth_energy_assembly_Cr d r t t1 C) (max (CbM 0) 0) h2r
      (aux_prop_growth_energy_assembly_Cr_nonneg d r t t1 C hr hC.le) (le_max_right _ _)
      Kmac D Mx (fun N => (hKmem 0 N).aestronglyMeasurable) (fun N => (hmem N).1.aestronglyMeasurable) (fun N => (hmem N).2.aestronglyMeasurable)
      hKps hB
  refine ⟨K, Cbound, hKmem', hKnorm', Filter.Eventually.of_forall (fun om N => hK1 N om), ?_⟩
  filter_upwards [hKae, hae] with om hmac hen
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad0 hrad1
  obtain ⟨hMxpos, henvN, hlipN⟩ := hen N
  have hphys := aux_prop_growth_energy_assembly_physical t t1 C ht0 htt1 ht1d hC hmic M
    (fun om' => infraredPartialSum om' L0) om N z r hr hr1 (Kmac N om) (D N om) (Mx N om) (hKmac0 N om) (hDMx0 N om).1 hMxpos henvN hlipN
    (hmac N) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad0 hrad1
  refine hphys.trans ?_
  have hE : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have hradt : 0 ≤ rad ^ t := Real.rpow_nonneg hrad0.le _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hKdom N om) hE) hradt

end Paper
