import SubdiffusiveProcess.Section10.ReversibleCubeSobolev
import SubdiffusiveProcess.Section10.KilledResolventDomainSmoothing
import SubdiffusiveProcess.Section10.TorsionExitBassInterfaces

/-! The exact arbitrary-open reversible smoothing supplier. The enclosing
cube Sobolev estimate is derived from the native embedding and actual local
coefficient bounds. No caller's smoothing or energy estimate is assumed. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Every bounded carrier fits inside a positive-side native axis cube. -/
theorem exists_axisCube_enclosing_bounded {d : ℕ} {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) :
    ∃ z : Vec d, ∃ L : ℝ, 0 < L ∧ U ⊆ axisCube z L := by
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : Vec d)
  let R := max r 0 + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hrR : r < R := by dsimp only [R]; linarith [le_max_left r 0]
  refine ⟨fun _ ↦ -R, 2 * R, by positivity, ?_⟩
  intro x hx i _hi
  have hdist := (dist_le_pi_dist x (0 : Vec d) i).trans_lt (Metric.mem_ball.mp (hr hx))
  have habs : |x i| < R := by
    simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hdist.trans hrR
  change -R < x i ∧ x i < -R + 2 * R
  constructor <;> linarith [(abs_lt.mp habs).1, (abs_lt.mp habs).2]

/-- The source subcritical exponent gives the exact deterministic normalized
Sobolev assumption on an enclosing cube. -/
theorem exists_weighted_cube_sobolevAssumption {d : ℕ} (hd : 2 ≤ d)
    (z : Vec d) (L : ℝ) (hL : 0 < L) (c rho : Vec d → ℝ)
    (hc : CoefficientOn (axisCube z L) c) (hr : CoefficientOn (axisCube z L) rho)
    (hm : 0 < ((weightedMeasure rho) (axisCube z L)).toReal) :
    ∃ p0 F : ℝ, 2 < p0 ∧ 0 < F ∧
      SobolevAssumption c rho (axisCube z L) p0 1 F := by
  letI : NeZero d := ⟨by omega⟩
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  let p0 := 2 * (d : ℝ) / ((d : ℝ) - 1)
  have hp0 : 2 < p0 := by
    dsimp only [p0]
    rw [lt_div_iff₀ (by linarith : 0 < (d : ℝ) - 1)]
    linarith
  let p : FiniteLpExponent :=
    ⟨ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1)), by
      rw [ENNReal.one_lt_ofReal]
      rw [lt_div_iff₀ (by linarith : 0 < (d : ℝ) + 1)]
      linarith, ENNReal.ofReal_lt_top⟩
  let q : FiniteLpExponent :=
    ⟨ENNReal.ofReal p0, by rw [ENNReal.one_lt_ofReal]; linarith,
      ENNReal.ofReal_lt_top⟩
  have hpR : p.exponent.toReal = 2 * (d : ℝ) / ((d : ℝ) + 1) :=
    ENNReal.toReal_ofReal (by positivity)
  have hqR : q.exponent.toReal = p0 := ENNReal.toReal_ofReal (by linarith)
  have hp : p.exponent ≤ 2 := by
    change ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1)) ≤ 2
    rw [ENNReal.ofReal_le_ofNat, div_le_iff₀ (by linarith : 0 < (d : ℝ) + 1)]
    linarith
  have hpd : p.exponent.toReal < d := by
    rw [hpR, div_lt_iff₀ (by linarith : 0 < (d : ℝ) + 1)]
    nlinarith
  have hpq : q.exponent.toReal⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹ := by
    rw [hpR, hqR]
    dsimp only [p0]
    field_simp
    ring
  obtain ⟨K, hK, hbound⟩ :=
    exists_weighted_h10_cube_energy_bound p q hp hpd hpq z L hL c rho hc hr
  let M := ((weightedMeasure rho) (axisCube z L)).toReal
  let theta := 1 - 2 / p0
  let F := K * M ^ theta
  have hF : 0 < F := mul_pos hK (Real.rpow_pos_of_pos hm _)
  have hprice : M ^ (-theta) * F = K := by
    dsimp only [F]
    calc
      M ^ (-theta) * (K * M ^ theta) = K * (M ^ (-theta) * M ^ theta) := by ring
      _ = K * M ^ (-theta + theta) := by rw [← Real.rpow_add hm]
      _ = K := by rw [neg_add_cancel, Real.rpow_zero, mul_one]
  refine ⟨p0, F, hp0, hF, fun u ↦ ?_⟩
  have h := hbound u
  change lpSq rho (axisCube z L) p0 u.toFun ≤
    ENNReal.ofReal (1 * M ^ (-theta)) *
      (lpSq rho (axisCube z L) 2 u.toFun +
        ENNReal.ofReal (F * energy c (axisCube z L) u.toH1Function))
  change eLpNorm u.toFun (ENNReal.ofReal p0)
      ((weightedMeasure rho).restrict (axisCube z L)) ^ 2 ≤ _
  refine h.trans ?_
  rw [one_mul]
  calc
    ENNReal.ofReal K * ENNReal.ofReal (energy c (axisCube z L) u.toH1Function) =
        ENNReal.ofReal (M ^ (-theta)) *
          ENNReal.ofReal (F * energy c (axisCube z L) u.toH1Function) := by
      rw [← ENNReal.ofReal_mul hK.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hm.le _), ← mul_assoc, hprice]
    _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_left (zero_le _))

/-- The exact lead interface is inhabited, for every bounded open domain,
including empty, disconnected and nonsmooth carriers. -/
theorem reversibleKilledSmoothingSupplier : ReversibleKilledSmoothingSupplier := by
  intro d hd a _hapos _ha law _hK hD U hU hUb _hfinite
  obtain ⟨z, L, hL, hUV⟩ := exists_axisCube_enclosing_bounded hUb
  have hrcompact : ∀ W : Set (Vec d), IsCompact W → CoefficientOn W a :=
    fun W hW ↦ (hD.2.1 W hW).2
  have hccompact : ∀ W : Set (Vec d), IsCompact W → CoefficientOn W a :=
    fun W hW ↦ (hD.2.1 W hW).1
  have hm0 := (weightedMeasure_axisCube_pos hrcompact z L hL).ne'
  have hmtop := (weightedMeasure_axisCube_lt_top hrcompact z L).ne
  letI : IsFiniteMeasure ((weightedMeasure a).restrict (axisCube z L)) :=
    isFiniteMeasure_restrict.mpr hmtop
  obtain ⟨p0, F, hp0, hF, hSob⟩ := exists_weighted_cube_sobolevAssumption hd z L hL a a
    (coefficientOn_axisCube hccompact z L) (coefficientOn_axisCube hrcompact z L)
    (weightedMeasure_axisCube_toReal_pos hrcompact z L hL)
  obtain ⟨N, _hN, C, hC, hbound⟩ :=
    exists_ae_sup_bound_killedResolventLp_pow_of_enclosing hD hU hUb
      (by norm_num : (0 : ℝ) < 1) hUV (isOpenBoundedConvexDomain_axisCube z L)
      hm0 hmtop hp0 (le_refl 1) hF hSob
  exact ⟨N, C, hC.le, hbound⟩

end SubdiffusiveProcess.Section10
