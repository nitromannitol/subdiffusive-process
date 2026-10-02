import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationMeasure
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveMaximumPrinciple

/-!
# Positive-level energy estimates for the killed resolvent

Testing the normalized massive equation with `(u - k)₊` gives its weighted mass
plus `s` times its energy. The local Sobolev inequality then bounds every positive
truncation in the original weighted measure. All coefficient bounds are used
almost everywhere; the final representative agrees with the raw killed resolvent.
-/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal
noncomputable section
set_option autoImplicit false

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

/-- The positive-level square is bounded by the mass testing product. -/
lemma positivePart_mass_le {r a k : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k) :
    r * max (a-k) 0 * max (a-k) 0 ≤ r * a * max (a-k) 0 := by
  by_cases h : a ≤ k
  · rw [max_eq_right (sub_nonpos.mpr h)]
    simp
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_self a hk) hr) (sub_nonneg.mpr (le_of_not_ge h))

/-- The truncation gradient converts the mixed energy into its own energy. -/
lemma positivePart_energy_eq {d : ℕ} {U : Set (Vec d)} {c : Vec d → ℝ}
    {u v : H10Function U} {k : ℝ}
    (hv : v.toH1Function.grad =ᵐ[volume.restrict U]
      fun x => {y | k < u.toH1Function.toFun y}.indicator u.toH1Function.grad x) :
    (∫ x in U, vecDot (c x • u.toH1Function.grad x) (v.toH1Function.grad x)) =
      energy c U v.toH1Function := by
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx]
  by_cases h : x ∈ {y | k < u.toH1Function.toFun y}
  · simp only [Set.indicator_of_mem h, vecDot_smul_left]
  · simp [Set.indicator_of_notMem h, vecDot]

/-- Testing the normalized massive equation at a positive level retains both mass and energy. -/
theorem positivePart_mass_add_energy_le {d : ℕ} {U : Set (Vec d)}
    {c rho f : Vec d → ℝ} {s rhoMax k : ℝ}
    (hs : 0 < s) (hk : 0 ≤ k)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict U))
    (hrhoBdd : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ rhoMax)
    (hrhoNonneg : ∀ᵐ x ∂volume.restrict U, 0 ≤ rho x)
    {u v : H10Function U} (hf : MemL2On U f)
    (hvf : ∀ x, v.toH1Function.toFun x = max (u.toH1Function.toFun x-k) 0)
    (hvg : v.toH1Function.grad =ᵐ[volume.restrict U]
      fun x => {y | k < u.toH1Function.toFun y}.indicator u.toH1Function.grad x)
    (hu : IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function (fun x => s⁻¹*f x)) :
    (∫ x in U, rho x * v.toH1Function.toFun x * v.toH1Function.toFun x) +
      s * energy c U v.toH1Function ≤
      ∫ x in U, rho x * |f x| * v.toH1Function.toFun x := by
  have hv0 (x : Vec d) : 0 ≤ v.toH1Function.toFun x := by
    rw [hvf x]
    exact le_max_right _ _
  have hmassU := integrableOn_mass_term hrhoMeas hrhoBdd
    u.toH1Function.memL2 v.toH1Function.memL2
  have hmassV := integrableOn_mass_term hrhoMeas hrhoBdd
    v.toH1Function.memL2 v.toH1Function.memL2
  have hmassF := integrableOn_mass_term hrhoMeas hrhoBdd hf v.toH1Function.memL2
  have hfabs : MemL2On U (fun x => |f x|) := by simpa only [Real.norm_eq_abs] using hf.norm
  have hmassAbs := integrableOn_mass_term hrhoMeas hrhoBdd hfabs v.toH1Function.memL2
  have hmassle : (∫ x in U, rho x * v.toH1Function.toFun x * v.toH1Function.toFun x) ≤
      ∫ x in U, rho x * u.toH1Function.toFun x * v.toH1Function.toFun x := by
    refine integral_mono_ae hmassV hmassU ?_
    filter_upwards [hrhoNonneg] with x hx
    rw [hvf x]
    exact positivePart_mass_le hx hk
  have hforcingle : (∫ x in U, rho x * f x * v.toH1Function.toFun x) ≤
      ∫ x in U, rho x * |f x| * v.toH1Function.toFun x := by
    refine integral_mono_ae hmassF hmassAbs ?_
    filter_upwards [hrhoNonneg] with x hx
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self _) hx) (hv0 x)
  have heq := hu v
  rw [positivePart_energy_eq hvg] at heq
  have hscaled : (∫ x in U, rho x * (s⁻¹ * f x) * v.toH1Function.toFun x) =
      s⁻¹ * ∫ x in U, rho x * f x * v.toH1Function.toFun x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  rw [hscaled] at heq
  have heq' := congrArg (fun z : ℝ => s * z) heq
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at heq'
  linarith


/-- Integrable nonnegative weighted products agree with their weighted lower integrals. -/
lemma weighted_lintegral_ofReal_eq {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {rho g : Vec d → ℝ} (hr : AEStronglyMeasurable rho (volume.restrict U))
    (hg : AEStronglyMeasurable g (volume.restrict U))
    (hr0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ rho x)
    (hg0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ g x)
    (hi : Integrable (fun x => rho x * g x) (volume.restrict U)) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂(weightedMeasure rho).restrict U =
      ENNReal.ofReal (∫ x in U, rho x * g x) := by
  unfold weightedMeasure
  rw [restrict_withDensity hU,
    lintegral_withDensity_eq_lintegral_mul₀ hr.aemeasurable.ennreal_ofReal
      hg.aemeasurable.ennreal_ofReal,
    ofReal_integral_eq_lintegral_ofReal hi (hr0.and hg0 |>.mono fun x hx => mul_nonneg hx.1 hx.2)]
  apply lintegral_congr_ae
  filter_upwards [hr0] with x hx
  exact (ENNReal.ofReal_mul hx).symm

/-- The square of the weighted `L²` seminorm is its nonnegative square integral. -/
lemma lpSq_two_eq_lintegral {d : ℕ} {U : Set (Vec d)} {rho f : Vec d → ℝ} :
    lpSq rho U 2 f = ∫⁻ x, ENNReal.ofReal (f x * f x) ∂(weightedMeasure rho).restrict U := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f)
    (μ := (weightedMeasure rho).restrict U) (p := (2 : ℝ≥0)) (by norm_num)
  have he (x : Vec d) : ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (f x * f x) := by
    rw [ENNReal.rpow_two, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    congr 1
    simp [Real.norm_eq_abs, pow_two]
  simpa only [lpSq, weightedMeasure, ENNReal.ofReal_ofNat, ENNReal.coe_ofNat,
    NNReal.coe_ofNat, ENNReal.rpow_two, he] using h

/-- A mass-plus-energy bound controls any nonnegative energy weight. -/
lemma mass_add_energy_absorb {s F M E H : ℝ} (hs : 0 < s) (hF : 0 ≤ F)
    (hM : 0 ≤ M) (hE : 0 ≤ E) (h : M + s * E ≤ H) :
    M + F * E ≤ (1 + F / s) * H := by
  have hFs : 0 ≤ F / s := div_nonneg hF hs.le
  have hcancel : F / s * s = F := div_mul_cancel₀ F hs.ne'
  calc
    M + F * E ≤ (1 + F / s) * (M + s * E) := by
      nlinarith [mul_nonneg hFs hM, mul_nonneg hs.le hE]
    _ ≤ (1 + F / s) * H := mul_le_mul_of_nonneg_left h (by positivity)


/-- The Sobolev bound for every positive truncation of a normalized massive solution. -/
theorem positivePart_lpSq_le {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {c rho f : Vec d → ℝ} (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {s k p A F : ℝ} (hs : 0 < s) (hk : 0 ≤ k) (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hSob : SobolevAssumption c rho U p A F)
    {u v : H10Function U} (hf : MemL2On U f)
    (hvf : ∀ x, v.toH1Function.toFun x = max (u.toH1Function.toFun x-k) 0)
    (hvg : v.toH1Function.grad =ᵐ[volume.restrict U]
      fun x => {y | k < u.toH1Function.toFun y}.indicator u.toH1Function.grad x)
    (hu : IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function (fun x => s⁻¹*f x)) :
    lpSq rho U p v.toH1Function.toFun ≤
      ENNReal.ofReal (A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p)) *
        (1 + F / s)) *
      ∫⁻ x, ENNReal.ofReal (|f x| * v.toH1Function.toFun x)
        ∂(weightedMeasure rho).restrict U := by
  obtain ⟨hrMeas, lo, hi, hlo, hrBounds⟩ := hr
  have hr0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ rho x :=
    hrBounds.mono fun _ hx => hlo.le.trans hx.1
  have hrAbs : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ hi := by
    filter_upwards [hr0, hrBounds] with x hx hxB
    simpa only [abs_of_nonneg hx] using hxB.2
  have hc0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ c x := by
    obtain ⟨_, lo', hi', hlo', hb⟩ := hc
    exact hb.mono fun _ hx => hlo'.le.trans hx.1
  have hv0 (x : Vec d) : 0 ≤ v.toH1Function.toFun x := by
    rw [hvf x]
    exact le_max_right _ _
  let M := ∫ x in U, rho x * v.toH1Function.toFun x * v.toH1Function.toFun x
  let E := energy c U v.toH1Function
  let H := ∫ x in U, rho x * |f x| * v.toH1Function.toFun x
  have hM : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [hr0] with x hx
    exact mul_nonneg (mul_nonneg hx (hv0 x)) (hv0 x)
  have hE : 0 ≤ E := by
    apply integral_nonneg_of_ae
    filter_upwards [hc0] with x hx
    exact mul_nonneg hx (vecNormSq_nonneg _)
  have hfabs : MemL2On U (fun x => |f x|) := by simpa only [Real.norm_eq_abs] using hf.norm
  have hmassV := integrableOn_mass_term hrMeas hrAbs
    v.toH1Function.memL2 v.toH1Function.memL2
  have hmassAbs := integrableOn_mass_term hrMeas hrAbs hfabs v.toH1Function.memL2
  have hnorm : lpSq rho U 2 v.toH1Function.toFun = ENNReal.ofReal M := by
    rw [lpSq_two_eq_lintegral]
    simpa only [M, mul_assoc] using weighted_lintegral_ofReal_eq hU hrMeas
      (v.toH1Function.memL2.aestronglyMeasurable.mul v.toH1Function.memL2.aestronglyMeasurable)
      hr0 (Filter.Eventually.of_forall fun x => mul_self_nonneg _)
      (by simpa only [mul_assoc] using hmassV)
  have hrhs : (∫⁻ x, ENNReal.ofReal (|f x| * v.toH1Function.toFun x)
      ∂(weightedMeasure rho).restrict U) = ENNReal.ofReal H := by
    simpa only [H, mul_assoc] using weighted_lintegral_ofReal_eq hU hrMeas
      (hfabs.aestronglyMeasurable.mul v.toH1Function.memL2.aestronglyMeasurable)
      hr0 (Filter.Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (hv0 x))
      (by simpa only [mul_assoc] using hmassAbs)
  have hbase : M + s * E ≤ H :=
    positivePart_mass_add_energy_le hs hk hrMeas hrAbs hr0 hf hvf hvg hu
  have habsorb := mass_add_energy_absorb hs hF hM hE hbase
  have hfac : 0 ≤ 1 + F / s := by positivity
  have hcoef : 0 ≤ A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p)) :=
    mul_nonneg hA (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  calc
    lpSq rho U p v.toH1Function.toFun ≤
        ENNReal.ofReal (A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p))) *
          (ENNReal.ofReal M + ENNReal.ofReal (F * E)) := by
      simpa only [hnorm] using hSob v
    _ = ENNReal.ofReal (A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p))) *
          ENNReal.ofReal (M + F * E) := by rw [ENNReal.ofReal_add hM (mul_nonneg hF hE)]
    _ ≤ ENNReal.ofReal (A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p))) *
          ENNReal.ofReal ((1 + F / s) * H) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal habsorb) _
    _ = _ := by rw [ENNReal.ofReal_mul hfac, ENNReal.ofReal_mul hcoef, hrhs, mul_assoc]


/-- The positive lower density bound transports `Lᵖ` data to volume. -/
theorem memLp_volume_restrict_of_weighted {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {rho f : Vec d → ℝ} (hr : CoefficientOn U rho)
    {p : ENNReal} (hf : MemLp f p ((weightedMeasure rho).restrict U)) :
    MemLp f p (volume.restrict U) := by
  obtain ⟨_, lo, hi, hlo, hb⟩ := hr
  have hlow := smul_volume_restrict_le_weightedMeasure_restrict hU lo
    (hb.mono fun _ hx => hx.1)
  have hne : ENNReal.ofReal lo ≠ 0 := by exact ne_of_gt (ENNReal.ofReal_pos.mpr hlo)
  have hinv : volume.restrict U ≤ (ENNReal.ofReal lo)⁻¹ • (weightedMeasure rho).restrict U := by
    apply Measure.le_iff.mpr
    intro S hS
    have h := Measure.le_iff.mp hlow S hS
    simp only [Measure.smul_apply, smul_eq_mul] at h ⊢
    calc
      volume.restrict U S = (ENNReal.ofReal lo)⁻¹ *
          (ENNReal.ofReal lo * volume.restrict U S) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
      _ ≤ _ := mul_le_mul_right h _
  exact hf.of_measure_le_smul (ENNReal.inv_ne_top.mpr hne) hinv

/-- Every killed resolvent datum has an `H¹₀` representative with all positive-level estimates. -/
theorem exists_killedResolvent_positivePart_lpSq_le {d : ℕ}
    {c rho : Vec d → ℝ} {law : ProbabilityTheory.Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {s p A F : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hSob : SobolevAssumption c rho U p A F) {f : Vec d → ℝ}
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    ∃ u : H10Function U,
      (∀ᵐ x ∂(weightedMeasure rho).restrict U,
        u.toH1Function.toFun x = killedResolvent law U s f x) ∧
      ∀ k : ℝ, 0 ≤ k → ∃ v : H10Function U,
        (∀ x, v.toH1Function.toFun x = max (u.toH1Function.toFun x-k) 0) ∧
        lpSq rho U p v.toH1Function.toFun ≤
          ENNReal.ofReal (A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p)) *
            (1 + F / s)) *
          ∫⁻ x, ENNReal.ofReal (|f x| * v.toH1Function.toFun x)
            ∂(weightedMeasure rho).restrict U := by
  have hUb := hU.isBoundedDomain.isBounded
  have hcpt := hD.2.1 (closure U) hUb.isCompact_closure
  have hc : CoefficientOn U c := coefficientOn_mono subset_closure hcpt.1
  have hr : CoefficientOn U rho := coefficientOn_mono subset_closure hcpt.2
  have hfvol : MemL2On U f := memLp_volume_restrict_of_weighted hU.isOpen.measurableSet hr hf
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU.isOpen hUb s hs f hf
  refine ⟨u, hueq, ?_⟩
  intro k hk
  obtain ⟨v, hvf, hvg⟩ := exists_h10_positivePart hU u hk
  exact ⟨v, hvf, positivePart_lpSq_le hU.isOpen.measurableSet hc hr hs hk hA hF hSob
    hfvol hvf hvg hu⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
