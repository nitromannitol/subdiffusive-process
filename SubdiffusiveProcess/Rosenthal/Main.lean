module

public import SubdiffusiveProcess.Rosenthal.NonNeg
public import SubdiffusiveProcess.Rosenthal.Constants

@[expose] public section

/-!
# Rosenthal's inequality with the constants `6√p` and `4p`

For `p ≥ 2` and independent mean-zero `X_1,…,X_N`:
`‖∑ X_i‖_p ≤ 6 √p (∑ E X_i²)^{1/2} + 4 p ‖max_i |X_i|‖_p`  (all moments in `[0,∞]`).

Proof: with `A = ∑ X_i²`, `T = ‖A‖_{p/2}`, `M = max |X_i|`: `‖∑ X_i‖_p ≤ 2K_p T^{1/2}` (symmetrization + Khintchine) and
`T ≤ ∑ E X_i² + 2 K_{p/2} ‖M‖_p T^{1/2}` (nonnegative case), so `T^{1/2} ≤ (∑ E X_i²)^{1/2} + 2 K_{p/2} ‖M‖_p`;
finally `2 K_p ≤ 6 √p` and `4 K_p K_{p/2} ≤ 4 p`.
-/

namespace SubdiffusiveProcess.Rosenthal

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Homogenization.IndependentSums

theorem quad_bound {u c k : ℝ} (hc : 0 ≤ c) (hk : 0 ≤ k) (h : u ^ 2 ≤ c + k * u) :
    u ≤ Real.sqrt c + k := by
  by_contra hcon
  push Not at hcon
  have hs := Real.sqrt_nonneg c
  have hs2 := Real.sq_sqrt hc
  nlinarith

theorem iSup_ofReal_abs_eq {N : ℕ} (hne : (Finset.univ : Finset (Fin N)).Nonempty) (x : Fin N → ℝ) :
    (⨆ i, ENNReal.ofReal |x i|) = ENNReal.ofReal (Finset.univ.sup' hne (fun i => |x i|)) := by
  apply le_antisymm
  · exact iSup_le (fun i => ENNReal.ofReal_le_ofReal
      (Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)))
  · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' hne (fun i => |x i|)
    rw [hj]
    exact le_iSup (fun i => ENNReal.ofReal |x i|) j

theorem rosenthal_main {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 1 ≤ N) (p : ℝ) (hp : 2 ≤ p) (X : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    (∫⁻ ω, ENNReal.ofReal (|∑ i, X i ω| ^ p) ∂μ) ^ (1 / p) ≤
      ENNReal.ofReal (6 * Real.sqrt p) *
          (∑ i, ∫⁻ ω, ENNReal.ofReal ((X i ω) ^ 2) ∂μ) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (4 * p) *
          (∫⁻ ω, (⨆ i, ENNReal.ofReal |X i ω|) ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  set M : Ω → ℝ := fun ω => Finset.univ.sup' hne (fun i => |X i ω|) with hMdef
  have hMm : Measurable M := by
    have h := Finset.measurable_sup' hne (fun i _ => (hmeas i).abs)
    have e : M = Finset.univ.sup' hne (fun i ω => |X i ω|) := by
      funext ω; simp [hMdef, Finset.sup'_apply]
    rw [e]; exact h
  have hXM : ∀ i ω, |X i ω| ≤ M ω := fun i ω =>
    Finset.le_sup' (fun i => |X i ω|) (Finset.mem_univ i)
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => (abs_nonneg (X ⟨0, hN⟩ ω)).trans (hXM _ ω)
  have hsup : ∀ ω, (⨆ i, ENNReal.ofReal |X i ω|) = ENNReal.ofReal (M ω) := fun ω =>
    iSup_ofReal_abs_eq hne _
  set B : ℝ≥0∞ := ∫⁻ ω, (⨆ i, ENNReal.ofReal |X i ω|) ^ p ∂μ with hB
  have hBeq : B = ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ :=
    lintegral_congr (fun ω => by
      rw [hsup, ENNReal.ofReal_rpow_of_nonneg (hM0 ω) hp0.le])
  by_cases hBtop : B = ∞
  · have h4 : ENNReal.ofReal (4 * p) * (∞ : ℝ≥0∞) ^ (1 / p) = ⊤ := by
      rw [ENNReal.top_rpow_of_pos (by positivity)]
      exact ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    rw [hBtop, h4, add_top]
    exact le_top
  -- finite case
  have hr : 1 ≤ p / 2 := by linarith
  have hr0 : 0 < p / 2 := by linarith
  have hLp : ∀ i, Integrable (fun ω => |X i ω| ^ p) μ := by
    intro i
    refine ⟨((hmeas i).abs.pow_const p).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun ω => by positivity))]
    calc ∫⁻ ω, ENNReal.ofReal (|X i ω| ^ p) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ :=
          lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow (abs_nonneg _) (hXM i ω) hp0.le))
      _ = B := hBeq.symm
      _ < ⊤ := lt_top_iff_ne_top.mpr hBtop
  -- the squares
  set Y : Fin N → Ω → ℝ := fun i ω => X i ω ^ 2 with hYdef
  have hYm : ∀ i, Measurable (Y i) := fun i => (hmeas i).pow_const 2
  have hYnn : ∀ i ω, 0 ≤ Y i ω := fun i ω => sq_nonneg _
  have hYind : iIndepFun Y μ := hind.comp (fun _ x => x ^ 2) (fun _ => measurable_id.pow_const 2)
  have habs : ∀ i ω, |Y i ω| ^ (p / 2) = |X i ω| ^ p := by
    intro i ω
    simp only [hYdef]
    rw [abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1; push_cast; ring
  have hYint : ∀ i, Integrable (fun ω => |Y i ω| ^ (p / 2)) μ := by
    intro i
    simpa only [habs] using hLp i
  have hYi_int : ∀ i, Integrable (Y i) μ := fun i => integrable_of_integrable_abs_rpow hr (hYm i) (hYint i)
  -- Mx
  set Mx : Ω → ℝ := fun ω => M ω ^ 2 with hMxdef
  have hMxm : Measurable Mx := hMm.pow_const 2
  have hMx0 : ∀ ω, 0 ≤ Mx ω := fun ω => sq_nonneg _
  have hYM : ∀ i ω, Y i ω ≤ Mx ω := by
    intro i ω
    have := abs_le.mp (hXM i ω)
    simp only [hYdef, hMxdef]
    exact sq_le_sq' this.1 this.2
  have hMxr : ∀ ω, Mx ω ^ (p / 2) = M ω ^ p := by
    intro ω
    simp only [hMxdef]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hM0 ω)]
    congr 1; push_cast; ring
  have hstep := nonneg_step (μ := μ) hYm hYnn hYind hr hYint hMxm hMx0 hYM
  simp only [hMxr, ← hBeq] at hstep
  set Aint : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((∑ i, Y i ω) ^ (p / 2)) ∂μ with hAint
  set u : ℝ≥0∞ := Aint ^ (1 / p) with hu
  set b : ℝ≥0∞ := B ^ (1 / p) with hb
  set K : ℝ := khintchineConst (p / 2) with hK
  set μ0 : ℝ := ∑ i, ∫ ω, Y i ω ∂μ with hμ0
  have hμ0nn : 0 ≤ μ0 := Finset.sum_nonneg (fun i _ => integral_nonneg (hYnn i))
  have hexp1 : (1 / (p / 2)) * (1 / 2 : ℝ) = 1 / p := by field_simp
  have hexp2 : (1 / p) * (2 : ℝ) = 1 / (p / 2) := by field_simp
  have hu' : (Aint ^ (1 / (p / 2))) ^ (1 / 2 : ℝ) = u := by
    rw [← ENNReal.rpow_mul, hexp1]
  have hb' : (B ^ (1 / (p / 2))) ^ (1 / 2 : ℝ) = b := by
    rw [← ENNReal.rpow_mul, hexp1]
  have hT : Aint ^ (1 / (p / 2)) = u ^ 2 := by
    rw [hu, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1; rw [← hexp2]; push_cast; ring
  rw [hu', hb'] at hstep
  have hquad : u ^ 2 ≤ ENNReal.ofReal μ0 + ENNReal.ofReal K * 2 * (b * u) := by
    rw [← hT]; exact hstep
  -- finiteness
  have hAfin : Aint ≠ ∞ := by
    have hpt : ∀ ω, ENNReal.ofReal ((∑ i, Y i ω) ^ (p / 2)) ≤
        ENNReal.ofReal ((N : ℝ) ^ (p / 2)) * ENNReal.ofReal (M ω ^ p) := by
      intro ω
      have h1 : ∑ i, Y i ω ≤ (N : ℝ) * Mx ω := by
        calc ∑ i, Y i ω ≤ ∑ i : Fin N, Mx ω := Finset.sum_le_sum (fun i _ => hYM i ω)
          _ = (N : ℝ) * Mx ω := by simp
      calc ENNReal.ofReal ((∑ i, Y i ω) ^ (p / 2)) ≤ ENNReal.ofReal (((N : ℝ) * Mx ω) ^ (p / 2)) :=
            ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => hYnn i ω)) h1 hr0.le)
        _ = ENNReal.ofReal ((N : ℝ) ^ (p / 2) * M ω ^ p) := by
            rw [Real.mul_rpow (by positivity) (hMx0 ω), hMxr]
        _ = _ := ENNReal.ofReal_mul (by positivity)
    have : Aint ≤ ENNReal.ofReal ((N : ℝ) ^ (p / 2)) * B := by
      calc Aint ≤ ∫⁻ ω, ENNReal.ofReal ((N : ℝ) ^ (p / 2)) * ENNReal.ofReal (M ω ^ p) ∂μ :=
            lintegral_mono hpt
        _ = ENNReal.ofReal ((N : ℝ) ^ (p / 2)) * B := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hBeq]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop) this
  have hufin : u ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) hAfin).ne
  have hbfin : b ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) hBtop).ne
  -- pass to reals
  have hK0 : 0 ≤ K := khintchineConst_nonneg hr0
  have hreal : u.toReal ^ 2 ≤ μ0 + K * 2 * b.toReal * u.toReal := by
    have hrhs : ENNReal.ofReal μ0 + ENNReal.ofReal K * 2 * (b * u) ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))
          (ENNReal.mul_ne_top hbfin hufin)⟩
    have := ENNReal.toReal_mono hrhs hquad
    rw [ENNReal.toReal_pow, ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))
        (ENNReal.mul_ne_top hbfin hufin)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hμ0nn, ENNReal.toReal_ofReal hK0] at this
    simpa [mul_assoc] using this
  have hqb : u.toReal ≤ Real.sqrt μ0 + K * 2 * b.toReal :=
    quad_bound hμ0nn (by positivity) (by nlinarith [hreal]) |> fun h => h
  have hle : u ≤ ENNReal.ofReal (Real.sqrt μ0) + ENNReal.ofReal (K * 2) * b := by
    calc u = ENNReal.ofReal u.toReal := (ENNReal.ofReal_toReal hufin).symm
      _ ≤ ENNReal.ofReal (Real.sqrt μ0 + K * 2 * b.toReal) := ENNReal.ofReal_le_ofReal hqb
      _ = _ := by
          rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hbfin]
  have hcen := lintegral_centered_root_le (μ := μ) hmeas hind (show 1 ≤ p by linarith) hLp
  simp only [hmean, sub_zero] at hcen
  have hconst := constants_le hp
  rw [← hK] at hconst
  have hsum : ∑ i, ∫⁻ ω, ENNReal.ofReal ((X i ω) ^ 2) ∂μ = ENNReal.ofReal μ0 := by
    rw [hμ0, ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg (hYnn i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (ofReal_integral_eq_lintegral_ofReal (hYi_int i) (ae_of_all _ (hYnn i))).symm
  have hsq : (ENNReal.ofReal μ0) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt μ0) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hμ0nn (by norm_num), Real.sqrt_eq_rpow]
  have hKp0 : 0 ≤ khintchineConst p := khintchineConst_nonneg hp0
  have e1 : ENNReal.ofReal (2 * khintchineConst p) = ENNReal.ofReal (khintchineConst p) * 2 := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp [mul_comm]
  have e2 : ENNReal.ofReal (2 * khintchineConst p) * ENNReal.ofReal (K * 2) =
      ENNReal.ofReal (4 * (khintchineConst p * K)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  rw [hsum, hsq]
  calc _ ≤ ENNReal.ofReal (khintchineConst p) * 2 * u := hcen
    _ ≤ ENNReal.ofReal (khintchineConst p) * 2 *
          (ENNReal.ofReal (Real.sqrt μ0) + ENNReal.ofReal (K * 2) * b) := by gcongr
    _ = ENNReal.ofReal (2 * khintchineConst p) * ENNReal.ofReal (Real.sqrt μ0) +
          ENNReal.ofReal (4 * (khintchineConst p * K)) * b := by
        rw [← e1, mul_add, ← mul_assoc, e2]
    _ ≤ ENNReal.ofReal (6 * Real.sqrt p) * ENNReal.ofReal (Real.sqrt μ0) +
          ENNReal.ofReal (4 * p) * b := by
        exact add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hconst.1) le_rfl)
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hconst.2) le_rfl)

end SubdiffusiveProcess.Rosenthal
