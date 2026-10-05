module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpperCore
public import SubdiffusiveProcess.Frozen.Section8.LocalResolventIteration

@[expose] public section

/-!
# The exit-time upper bound of the local resolvent
The Poincaré assumption gives the resolvent contraction,
which the exponential mixture comparison turns into geometric decay of the survival mass; the
continuous killed density of the resolvent iteration transfers that decay to every starting point,
and integrating the tail bounds the mean exit time.  Hölder's inequality between the exponents
`2` and `p₀` derives both assumptions from the homogeneous Sobolev inequality.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
open scoped ENNReal NNReal

noncomputable section

/-- The exponent-only constants of the exit-time upper bound. -/
def SubdiffusiveProcess.Providers.Section8.exitUpperConstant (p0 C1 : ℝ) : ℝ :=
  C1 * 2 ^ ((1 - 2 / p0)⁻¹) + C1 + 2


/-- Exponential exit-time tail and linear mean exit time for the local killed diffusion. -/

theorem SubdiffusiveProcess.Providers.Section8.local_resolvent_exit_upper (p0 : ℝ) (hp0 : 2 < p0) :
    ∃ c0 C : ℝ, 0 < c0 ∧ 0 < C ∧
      ∀ d : ℕ, ∀ _hd : 2 ≤ d, ∀ c rho : Vec d → ℝ, ∀ law : Kernel (Vec d) (Path d),
        LocalDiffusion c rho law → ∀ y : Vec d, ∀ side : ℝ, 0 < side →
        let U := Homogenization.axisCube y side
        ∀ A F : ℝ, 1 ≤ A → 0 < F →
          ((SobolevAssumption c rho U p0 A F ∧ PoincareAssumption c rho U A F) →
            ∀ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p →
              ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
                (Ioi 0 ×ˢ U ×ˢ U) →
              (∀ t : ℝ, 0 < t → ∀ x ∈ U,
                law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} ≤
                  ENNReal.ofReal (C * A ^ C * Real.exp (-c0 * t / (A * F)))) ∧
              (∀ x ∈ U, meanExit law U x ≤ ENNReal.ofReal (C * A ^ C * F))) ∧
          ((∀ f : H10Function U,
            lpSq rho U p0 f.toH1Function.toFun ≤
              ENNReal.ofReal (A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p0)) *
                F * energy c U f.toH1Function)) →
            SobolevAssumption c rho U p0 A F ∧ PoincareAssumption c rho U A F)

:= by
  obtain ⟨N0, C1, hN0, hC1, hiter⟩ := SubdiffusiveProcess.Frozen.Section8.local_resolvent_iteration p0 hp0
  have hthetapos : 0 < 1 - 2 / p0 := theta_pos hp0
  have htwopow : (0 : ℝ) < 2 ^ ((1 - 2 / p0)⁻¹) := Real.rpow_pos_of_pos (by norm_num) _
  set C0 : ℝ := SubdiffusiveProcess.Providers.Section8.exitUpperConstant p0 C1 with hC0def
  have hC0pos : 0 < C0 := by
    rw [hC0def, SubdiffusiveProcess.Providers.Section8.exitUpperConstant]
    positivity
  have hC02 : 2 ≤ C0 := by
    rw [hC0def, SubdiffusiveProcess.Providers.Section8.exitUpperConstant]
    nlinarith
  have hC0C1 : C1 ≤ C0 := by
    rw [hC0def, SubdiffusiveProcess.Providers.Section8.exitUpperConstant]
    nlinarith
  have hC0prod : C1 * 2 ^ ((1 - 2 / p0)⁻¹) ≤ C0 := by
    rw [hC0def, SubdiffusiveProcess.Providers.Section8.exitUpperConstant]
    nlinarith
  have hrate : 0 < rate := rate_pos
  refine ⟨rate, C0 / rate + C0 + 1, hrate, by positivity, ?_⟩
  set C : ℝ := C0 / rate + C0 + 1 with hCdef
  have hCC0 : C0 ≤ C := by rw [hCdef]; have : 0 < C0 / rate := by positivity
                           linarith
  have hCrate : C0 / rate ≤ C := by rw [hCdef]; linarith
  have hCsucc : C0 + 1 ≤ C := by
    rw [hCdef]
    have : 0 < C0 / rate := by positivity
    linarith
  intro d _hd c rho law hDiff y side hside U A F hA hF
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hAF : (0 : ℝ) < A * F := by positivity
  have hAC0 : (1 : ℝ) ≤ A ^ C0 := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hA (le_of_lt hC0pos)
    rwa [Real.one_rpow] at h
  have hACC : A ^ C0 ≤ A ^ C := Real.rpow_le_rpow_of_exponent_le hA hCC0
  have hMk : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hDiff
  have hrho : ∀ K : Set (Vec d), IsCompact K → CoefficientOn K rho :=
    fun K hK => (hDiff.2.1 K hK).2
  have hUdom : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_axisCube y side
  have hUopen : IsOpen U := hUdom.isOpen
  have hUb : Bornology.IsBounded U := hUdom.isBoundedDomain.isBounded
  have hm0 : (weightedMeasure rho) U ≠ 0 := (weightedMeasure_axisCube_pos hrho y side hside).ne'
  have hmtop : (weightedMeasure rho) U ≠ ∞ := (weightedMeasure_axisCube_lt_top hrho y side).ne
  have hmasspos : 0 < ((weightedMeasure rho) U).toReal := ENNReal.toReal_pos hm0 hmtop
  have hrhoU : CoefficientOn U rho := coefficientOn_axisCube hrho y side
  have hfin : IsFiniteMeasure ((weightedMeasure rho).restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hmtop⟩
  refine ⟨?_, fun hhom => assumptions_of_homogeneous hUopen hrhoU hm0 hmtop hp0 hA hhom⟩
  rintro ⟨hSob, hPoin⟩ p hp hcont
  obtain ⟨_, hdens⟩ := hiter d _hd c rho law hDiff y side hside A F hA hF hSob
  obtain ⟨hae, _⟩ := hdens p hp
  set D : ℝ := C1 * A ^ C1 / ((weightedMeasure rho) U).toReal *
    (1 + F / F) ^ ((1 - 2 / p0)⁻¹) with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    positivity
  have hslice : ContinuousOn (fun z : Vec d × Vec d => p F z.1 z.2) (U ×ˢ U) :=
    hcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun z hz => ⟨hF, hz⟩)
  have hpair : ∀ z ∈ U ×ˢ U, p F z.1 z.2 ≤ D :=
    continuousOn_le_of_ae_weightedMeasure_prod hUopen hrhoU _ hslice D (hae F hF)
  have hFF : (1 : ℝ) + F / F = 2 := by rw [div_self hF.ne']; norm_num
  have hDmass : D * ((weightedMeasure rho) U).toReal
      = C1 * A ^ C1 * 2 ^ ((1 - 2 / p0)⁻¹) := by
    rw [hDdef, hFF]
    field_simp
  -- the exponential tail with the intermediate constant
  have htail0 : ∀ t : ℝ, 0 < t → ∀ x ∈ U,
      law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} ≤
        ENNReal.ofReal (C0 * A ^ C0 * Real.exp (-rate * t / (A * F))) := by
    intro t ht x hx
    rcases le_or_gt (5 * (A * F)) t with hbig | hsmall
    · have hstep := survival_tail_le hDiff hUopen hUb hmtop hA hF hPoin hp hD0 hx
        (fun z hz => hpair (x, z) ⟨hx, hz⟩) hbig
      refine le_trans hstep (ENNReal.ofReal_le_ofReal ?_)
      have hAC1 : A ^ C1 ≤ A ^ C0 := Real.rpow_le_rpow_of_exponent_le hA hC0C1
      have hprod : D * ((weightedMeasure rho) U).toReal ≤ C0 * A ^ C0 := by
        rw [hDmass]
        calc C1 * A ^ C1 * 2 ^ ((1 - 2 / p0)⁻¹)
            = (C1 * 2 ^ ((1 - 2 / p0)⁻¹)) * A ^ C1 := by ring
          _ ≤ C0 * A ^ C0 :=
              mul_le_mul hC0prod hAC1 (by positivity) (le_of_lt hC0pos)
      exact mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    · have h1 : law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} ≤ 1 :=
        le_trans (measure_mono (Set.subset_univ _)) (le_of_eq (measure_univ))
      refine le_trans h1 ?_
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      refine ENNReal.ofReal_le_ofReal ?_
      have hrate5 : rate * 5 = Real.log (3 / 2) := by
        rw [rate]
        field_simp
      have hle : -(Real.log (3 / 2)) ≤ -rate * t / (A * F) := by
        rw [le_div_iff₀ hAF]
        nlinarith [mul_le_mul_of_nonneg_left hsmall.le hrate.le]
      have hexp : (2 : ℝ) / 3 ≤ Real.exp (-rate * t / (A * F)) := by
        have hmono := Real.exp_le_exp.mpr hle
        rwa [show Real.exp (-(Real.log (3 / 2))) = 2 / 3 by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num] at hmono
      have hfinal : (2 : ℝ) * 1 * (2 / 3) ≤ C0 * A ^ C0 * Real.exp (-rate * t / (A * F)) :=
        mul_le_mul (mul_le_mul hC02 hAC0 (by norm_num) (by linarith)) hexp (by norm_num)
          (by positivity)
      linarith
  refine ⟨fun t ht x hx => le_trans (htail0 t ht x hx) (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul hCC0 hACC (by positivity) (by linarith)) (Real.exp_pos _).le
  · intro x hx
    have hb : 0 < rate / (A * F) := by positivity
    have htail' : ∀ t : ℝ, 0 < t →
        law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} ≤
          ENNReal.ofReal (C0 * A ^ C0 * Real.exp (-(rate / (A * F) * t))) := by
      intro t ht
      have hstep := htail0 t ht x hx
      rwa [show -(rate / (A * F) * t) = -rate * t / (A * F) by ring]
    have hmean := meanExit_le_of_tail law hUopen x
      (by positivity : (0:ℝ) ≤ C0 * A ^ C0) hb htail'
    refine le_trans hmean (ENNReal.ofReal_le_ofReal ?_)
    have hA1 : A ^ C0 * A = A ^ (C0 + 1) := by
      rw [Real.rpow_add hA0, Real.rpow_one]
    have hAC : A ^ (C0 + 1) ≤ A ^ C := Real.rpow_le_rpow_of_exponent_le hA hCsucc
    calc C0 * A ^ C0 * (rate / (A * F))⁻¹
        = C0 / rate * (A ^ C0 * A) * F := by
          rw [inv_div]
          field_simp
      _ = C0 / rate * A ^ (C0 + 1) * F := by rw [hA1]
      _ ≤ C * A ^ C * F :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hCrate hAC (by positivity) (by linarith)) hF.le
