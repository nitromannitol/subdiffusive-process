import SubdiffusiveProcess.Section10.PhysicalTightnessActualContainment

/-! Finite-cover transport of the actual small-cube bank to the uniform
quenched ball-exit input of the independent strong-Markov chaining theorem.
No chaining proof or static moment bookkeeping is repeated here. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

/-- Domain inclusion orders lifetime exit times, before any conservativity
or initial-position assumption. -/
theorem exitTime_le_of_subset {d : ℕ} {U V : Set (Vec d)} (hUV : U ⊆ V) (w : Path d) :
    LifetimePath.exitTime U w ≤ LifetimePath.exitTime V w := by
  apply le_sInf
  intro t ht
  rcases ht with ⟨s, rfl, hs⟩
  apply sInf_le
  exact ⟨s, rfl, fun hU => hs (Set.image_mono hUV hU)⟩

/-- A finite deterministic spatial cover gives an integrable random constant
for exits from EVERY ball centered at the starting point. The same scale k
and expected bound serve all N>=k and both physical source branches. -/
theorem actual_uniform_ball_exit_bank_of_local_analytic_bank {d : ℕ}
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(Vec d, ℝ))
    (hH : InfraredCharacterization M H)
    (Hf : BilateralField d → C(Vec d, ℝ)) (hHf : Hf = H ∨ Hf = fun _ => 0)
    (LN : ℕ → Kernel (BilateralField d × Vec d) (Path d))
    (hdata : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      LocalDiffusionData (cutoffCoefficient M Hf xi N) (cutoffSpeedDensity M Hf xi N)
        (Kernel.comap (LN N) (fun x => (xi, x)) measurable_prodMk_left))
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
      ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        (∫⁻ omega, ENNReal.ofReal (K omega ^ (2 : ℝ))
          ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
        ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
          LocalExitCertificate (localCoefficient M L m z omega) (localSpeed M L m z omega) (K omega))
    (R r : ℝ) (_hR : 0 < R) (hr : 0 < r) :
    ∃ k : ℕ, ∃ Cball : ℝ, 0 < Cball ∧
      ∀ N : ℕ, k ≤ N → ∃ F : BilateralField d → ℝ, Measurable F ∧ (∀ xi, 1 ≤ F xi) ∧
        (∫⁻ xi, ENNReal.ofReal (F xi) ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal Cball ∧
        ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ t : ℝ, 0 < t →
          ∀ x ∈ Metric.ball (0 : Vec d) R,
            LN N (xi, x) {w | LifetimePath.exitTime (Metric.ball x (r / 4)) w ≤ ENNReal.ofReal t} ≤
              ENNReal.ofReal (F xi * Real.sqrt t) := by
  classical
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < r / 4)
    (by norm_num : (3 : ℝ)⁻¹ < 1)
  let rho : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  have hrho : 0 < rho := zpow_pos (by norm_num) _
  have hrhor : rho ≤ r / 4 := by
    simpa only [rho, zpow_neg, zpow_natCast, inv_pow] using hk.le
  obtain ⟨centres, hcover⟩ := (isCompact_closedBall (0 : Vec d) R).elim_finite_subcover
    (fun y : Vec d => Metric.ball y (rho / 18)) (fun _ => Metric.isOpen_ball) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by positivity)⟩)
  let theta : ℝ := (3 : ℝ) ^ (-(2 * k : ℤ)) / Real.exp (2 * tauSq M.P * (k : ℝ))
  have htheta : 0 < theta := div_pos (zpow_pos (by norm_num) _) (Real.exp_pos _)
  let J : ℝ := Real.sqrt theta⁻¹
  have hJ : 0 ≤ J := Real.sqrt_nonneg _
  let D : ℝ := 1 + 8 * C
  have hD : 0 ≤ D := by positivity
  let Cball : ℝ := 1 + J * ((Fintype.card centres : ℕ) : ℝ) * D
  refine ⟨k, Cball, by positivity, ?_⟩
  intro N hNk
  have hbank := actual_common_exit_moment_bank_of_local_analytic_bank
    M H hH Hf hHf LN hdata 1 C (by norm_num) hC (by simpa only [mul_one] using hlocal)
  have hscale : (3 : ℝ) ^ (((N - k : ℕ) : ℤ) - N) = rho := by
    rw [show (((N - k : ℕ) : ℤ) - N) = -(k : ℤ) by omega]
  have hf : ∀ i : centres, ∃ F : BilateralField d → ℝ, Measurable F ∧ (∀ xi, 1 ≤ F xi) ∧
      (∫⁻ xi, ENNReal.ofReal (F xi) ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal D ∧
      ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ t : ℝ, 0 < t →
        ∀ x ∈ Metric.ball (i : Vec d) (rho / 18),
          LN N (xi, x) {w | LifetimePath.exitTime (Metric.ball (i : Vec d) (rho / 2)) w ≤
            ENNReal.ofReal t} ≤ ENNReal.ofReal (F xi * Real.sqrt (t / theta)) := by
    intro i
    obtain ⟨L, hbranch, F, hF, hFone, hFint, hFbound⟩ := hbank N (N - k) i
    have hclock : theta ≤ relativeClock M L N (N - k) := by
      rcases hbranch with ⟨hL, -⟩ | ⟨hL, -⟩ <;> subst L
      · exact top_relativeClock_small_lower M hNk
      · exact finite_relativeClock_small_lower M hNk
    refine ⟨F, hF, hFone, ?_, ?_⟩
    · have hnum : (1 : ℝ) + 2 * (4 * C) = D := by dsimp only [D]; ring
      simpa only [Real.rpow_one, hnum] using hFint
    · filter_upwards [hFbound] with xi hxi
      intro t ht x hx
      have hb := hxi t ht x (by simpa only [hscale] using hx)
      simp only [hscale] at hb
      exact hb.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_left ht.le htheta hclock)) (zero_le_one.trans (hFone xi))))
  choose F hF hFone hFint hFbound using hf
  let Ftotal : BilateralField d → ℝ := fun xi => 1 + J * ∑ i : centres, F i xi
  have hFtotal : Measurable Ftotal := measurable_const.add
    (measurable_const.mul (Finset.measurable_sum _ (fun i _ => hF i)))
  have hFtotalOne : ∀ xi, 1 ≤ Ftotal xi := by
    intro xi
    exact le_add_of_nonneg_right (mul_nonneg hJ
      (Finset.sum_nonneg fun i _ => zero_le_one.trans (hFone i xi)))
  have hsum : (∫⁻ xi, ENNReal.ofReal (∑ i : centres, F i xi) ∂(chaosSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (((Fintype.card centres : ℕ) : ℝ) * D) := by
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => zero_le_one.trans (hFone i _))]
    rw [lintegral_finset_sum Finset.univ (f := fun i xi => ENNReal.ofReal (F i xi))
      (fun i _ => ENNReal.measurable_ofReal.comp (hF i))]
    calc
      _ ≤ ∑ _i : centres, ENNReal.ofReal D := Finset.sum_le_sum fun i _ => hFint i
      _ = ENNReal.ofReal (((Fintype.card centres : ℕ) : ℝ) * D) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hD)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hFtotalInt : (∫⁻ xi, ENNReal.ofReal (Ftotal xi) ∂(chaosSampleLaw M).toMeasure) ≤
      ENNReal.ofReal Cball := by
    have hpoint : ∀ xi, ENNReal.ofReal (Ftotal xi) =
        1 + ENNReal.ofReal J * ENNReal.ofReal (∑ i : centres, F i xi) := by
      intro xi
      change ENNReal.ofReal (1 + J * ∑ i : centres, F i xi) = _
      rw [ENNReal.ofReal_add zero_le_one
        (mul_nonneg hJ (Finset.sum_nonneg fun i _ => zero_le_one.trans (hFone i xi))),
        ENNReal.ofReal_one, ENNReal.ofReal_mul hJ]
    simp_rw [hpoint]
    rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp only [lintegral_const, measure_univ, mul_one]
    calc
      _ ≤ 1 + ENNReal.ofReal J * ENNReal.ofReal (((Fintype.card centres : ℕ) : ℝ) * D) := by
        gcongr
      _ = ENNReal.ofReal Cball := by
        rw [← ENNReal.ofReal_mul hJ, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (by positivity)]
        congr 1
        dsimp only [Cball]
        ring
  refine ⟨Ftotal, hFtotal, hFtotalOne, hFtotalInt, ?_⟩
  filter_upwards [ae_all_iff.mpr hFbound] with xi hxi
  intro t ht x hx
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover (Metric.ball_subset_closedBall hx))
  obtain ⟨hyc, hxy⟩ := mem_iUnion.mp hy
  let i : centres := ⟨y, hyc⟩
  have houter : Metric.ball y (rho / 2) ⊆ Metric.ball x (r / 4) := by
    apply Metric.ball_subset_ball'
    have hdist := Metric.mem_ball.mp hxy
    rw [dist_comm y x]
    linarith only [hdist, hrhor, hrho]
  have hmass : LN N (xi, x) {w | LifetimePath.exitTime (Metric.ball x (r / 4)) w ≤
      ENNReal.ofReal t} ≤ LN N (xi, x) {w | LifetimePath.exitTime (Metric.ball y (rho / 2)) w ≤
        ENNReal.ofReal t} := measure_mono fun w hw => (exitTime_le_of_subset houter w).trans hw
  have hb := hxi i t ht x hxy
  refine (hmass.trans hb).trans (ENNReal.ofReal_le_ofReal ?_)
  have hsingle : F i xi ≤ ∑ j : centres, F j xi :=
    Finset.single_le_sum (fun j _ => zero_le_one.trans (hFone j xi)) (Finset.mem_univ i)
  have htotal : J * F i xi ≤ Ftotal xi :=
    (mul_le_mul_of_nonneg_left hsingle hJ).trans (le_add_of_nonneg_left zero_le_one)
  rw [div_eq_mul_inv, Real.sqrt_mul ht.le]
  calc
    _ = (J * F i xi) * Real.sqrt t := by dsimp only [J]; ring
    _ ≤ Ftotal xi * Real.sqrt t := mul_le_mul_of_nonneg_right htotal (Real.sqrt_nonneg _)

end SubdiffusiveProcess.Section10.PhysicalTightness
