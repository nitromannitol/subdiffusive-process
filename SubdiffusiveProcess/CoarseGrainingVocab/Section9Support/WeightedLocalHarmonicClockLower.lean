module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicInterior

@[expose] public section

/-!
# The Sobolev clause forces the clock to dominate the square of the side

 v4's massive display is stated for `s` with
`cc * clock B.2 ≤ s`, and `clock : ℝ → ℝ` is an *arbitrary* function there.  Every
route to the display that is free of De Giorgi–Nash–Moser produces a correction term
of relative size `C · B.2² / s` which has to be absorbed, so such a route needs
`B.2² ≲ s` — that is, it needs `clock B.2 ≳ B.2²`, which the statement does not
say.

It is nevertheless **forced** by the hypotheses.  `LocalTorsionEstimates.sobolev`
asserts, for every `Q` of the family,

    ‖f‖²_{L^{p0}(a dx, Q)} ≤ CC · |Q|_a^{-(1-2/p0)} · clock(Q.2) · ∫_Q a |∇f|²

for every `f ∈ H¹₀(Q)`.  Testing it with one explicit cutoff — `1` on the ball of
radius `Q.2/8`, supported in the ball of radius `Q.2/6`, gradient at most
`C d / Q.2` — makes the left side a fixed fraction of `|Q|_a^{2/p0}` and the right
side `CC · clock(Q.2) · C²d²/Q.2² · |Q|_a^{2/p0}`, and the mass fraction is bounded
below by the per-cube ellipticity ratio `exp(√d √H)` of
`WeightedLocalHarmonicScaledContrast`.  The two `|Q|_a^{2/p0}` cancel and

    Q.2² ≤ clockLowerConstant d p0 CC H · clock(Q.2).

The constant depends only on `d, p0, CC, H`, all of which the statement binds
before `∃ C`.  Nothing here uses `law`, the diffusion, or any iteration.
-/

set_option autoImplicit false
open Homogenization hiding cubeSet
open MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab (normalizedL2On averageOn)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support (mem_centeredAxisCube)
open scoped ENNReal NNReal
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic

variable {d : ℕ}

/-! ## Two-sided mass bounds from a pointwise coefficient bound -/

theorem weightedMeasure_le_of_ae_le {a : Vec d → ℝ} {S : Set (Vec d)} {hi : ℝ}
    (hS : MeasurableSet S) (h : ∀ x ∈ S, a x ≤ hi) :
    weightedMeasure a S ≤ ENNReal.ofReal hi * volume S := by
  rw [weightedMeasure, withDensity_apply _ hS]
  calc ∫⁻ x in S, ENNReal.ofReal (a x) ∂volume
      ≤ ∫⁻ _ in S, ENNReal.ofReal hi ∂volume := by
        refine setLIntegral_mono' hS fun x hx => ?_
        exact ENNReal.ofReal_le_ofReal (h x hx)
    _ = ENNReal.ofReal hi * volume S := by
        rw [setLIntegral_const]

theorem le_weightedMeasure_of_ae_le {a : Vec d → ℝ} {S : Set (Vec d)} {lo : ℝ}
    (hS : MeasurableSet S) (h : ∀ x ∈ S, lo ≤ a x) :
    ENNReal.ofReal lo * volume S ≤ weightedMeasure a S := by
  rw [weightedMeasure, withDensity_apply _ hS]
  calc ENNReal.ofReal lo * volume S = ∫⁻ _ in S, ENNReal.ofReal lo ∂volume := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ x in S, ENNReal.ofReal (a x) ∂volume := by
        refine setLIntegral_mono' hS fun x hx => ?_
        exact ENNReal.ofReal_le_ofReal (h x hx)

/-! ## The explicit test cutoff -/

/-- The dimensional bound for `|∇η|²` of the canonical cutoff between the balls of
radii `L/8` and `L/6`, after clearing the scale `L`. -/
def cutoffGradSq (d : ℕ) : ℝ :=
  (d : ℝ) * (48 * (d : ℝ) * smoothTransitionProfile.derivBound) ^ 2

theorem cutoffGradSq_nonneg (d : ℕ) : 0 ≤ cutoffGradSq d := by
  unfold cutoffGradSq; positivity

theorem isOpen_cubeSet {Q : Cube d} : IsOpen (cubeSet Q) := isOpen_axisCube _ _

theorem euclideanBall_subset_cubeSet {Q : Cube d} {R : ℝ} (hR : 0 < R)
    (hRle : R ≤ Q.2 / 2) : euclideanBall Q.1 R ⊆ cubeSet Q := by
  intro y hy
  have hyx : ‖y - Q.1‖ < R := by
    have := euclideanBall_subset_metricBall hR hy
    rwa [mem_ball_iff_norm] at this
  show y ∈ centeredAxisCube Q.1 Q.2
  refine mem_centeredAxisCube.mpr fun i => ?_
  have hcoord := norm_le_pi_norm (y - Q.1) i
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoord
  linarith [hcoord.trans_lt hyx]

/-- One explicit admissible test function for the Sobolev clause: `1` on the ball of
radius `Q.2/8`, nonnegative, and with `|∇η|² ≤ cutoffGradSq d / Q.2²` everywhere. -/
theorem exists_cutoff_h10Function [NeZero d] {Q : Cube d} (hQ : 0 < Q.2) :
    ∃ f : H10Function (cubeSet Q),
      (∀ x ∈ euclideanBall Q.1 (Q.2 / 8), f.toH1Function.toFun x = 1) ∧
      (∀ x, 0 ≤ f.toH1Function.toFun x) ∧
      (∀ x, vecDot (f.toH1Function.grad x) (f.toH1Function.grad x) ≤
        cutoffGradSq d / Q.2 ^ 2) := by
  have hr : (0 : ℝ) < Q.2 / 8 := by positivity
  have hrs : Q.2 / 8 < Q.2 / 6 := by linarith
  have hsR : Q.2 / 6 < Q.2 / 4 := by linarith
  set phi : Vec d → ℝ := QuantitativeBallCutoff.canonicalFun Q.1 (Q.2 / 8) (Q.2 / 6) with hphi
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) phi :=
    QuantitativeBallCutoff.canonicalFun_smooth Q.1 hr hrs
  have hcs : HasCompactSupport phi :=
    QuantitativeBallCutoff.canonicalFun_hasCompactSupport Q.1 hr hrs
  have hsub : tsupport phi ⊆ cubeSet Q :=
    (QuantitativeBallCutoff.canonicalFun_tsupport_subset_euclideanBall Q.1 hr hrs hsR).trans
      (euclideanBall_subset_cubeSet (by positivity) (by linarith))
  set f : H10Function (cubeSet Q) :=
    H10Function.ofContDiff (isOpen_cubeSet) hsmooth hcs hsub with hf
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x hx
    exact QuantitativeBallCutoff.canonicalFun_eq_one_on_inner hr hrs hx
  · intro x
    exact QuantitativeBallCutoff.canonicalFun_nonneg Q.1 _ _ x
  · intro x
    have hfd : ‖fderiv ℝ phi x‖ ≤ 48 * (d : ℝ) * smoothTransitionProfile.derivBound / Q.2 := by
      have hb := QuantitativeBallCutoff.canonicalFun_gradient_bound Q.1 hr hrs x
      have heq : smoothTransitionProfile.derivBound * (2 * (d : ℝ) / (Q.2 / 6 - Q.2 / 8))
          = 48 * (d : ℝ) * smoothTransitionProfile.derivBound / Q.2 := by
        rw [show Q.2 / 6 - Q.2 / 8 = Q.2 / 24 by ring]
        field_simp
        ring
      rwa [heq] at hb
    have hcoord : ∀ i : Fin d,
        |f.toH1Function.grad x i| ≤ ‖fderiv ℝ phi x‖ := by
      intro i
      have hb : ‖basisVec (d := d) i‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
        rcases eq_or_ne j i with hij | hij <;> simp [basisVec_apply, hij]
      have := (fderiv ℝ phi x).le_opNorm (basisVec (d := d) i)
      calc |f.toH1Function.grad x i|
          = ‖(fderiv ℝ phi x) (basisVec i)‖ := by rw [Real.norm_eq_abs]; rfl
        _ ≤ ‖fderiv ℝ phi x‖ * ‖basisVec (d := d) i‖ := this
        _ ≤ ‖fderiv ℝ phi x‖ * 1 := by
            exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = ‖fderiv ℝ phi x‖ := mul_one _
    have hsum : vecDot (f.toH1Function.grad x) (f.toH1Function.grad x)
        ≤ (d : ℝ) * ‖fderiv ℝ phi x‖ ^ 2 := by
      rw [vecDot]
      calc ∑ i : Fin d, f.toH1Function.grad x i * f.toH1Function.grad x i
          ≤ ∑ _i : Fin d, ‖fderiv ℝ phi x‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 := hcoord i
            nlinarith [abs_nonneg (f.toH1Function.grad x i),
              sq_abs (f.toH1Function.grad x i), norm_nonneg (fderiv ℝ phi x)]
        _ = (d : ℝ) * ‖fderiv ℝ phi x‖ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine hsum.trans ?_
    have hQ2 : (0 : ℝ) < Q.2 ^ 2 := by positivity
    have hT : (0 : ℝ) ≤ 48 * (d : ℝ) * smoothTransitionProfile.derivBound := by
      have := smoothTransitionProfile.derivBound_nonneg
      positivity
    rw [cutoffGradSq, le_div_iff₀ hQ2]
    have h1 : ‖fderiv ℝ phi x‖ * Q.2 ≤ 48 * (d : ℝ) * smoothTransitionProfile.derivBound := by
      rw [← le_div_iff₀ hQ]
      exact hfd
    have h2 : (‖fderiv ℝ phi x‖ * Q.2) ^ 2 ≤
        (48 * (d : ℝ) * smoothTransitionProfile.derivBound) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc (d : ℝ) * ‖fderiv ℝ phi x‖ ^ 2 * Q.2 ^ 2
        = (d : ℝ) * (‖fderiv ℝ phi x‖ * Q.2) ^ 2 := by ring
      _ ≤ (d : ℝ) * (48 * (d : ℝ) * smoothTransitionProfile.derivBound) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d)

/-! ## The two sides of the tested Sobolev inequality -/

theorem vecDot_self_nonneg (v : Vec d) : 0 ≤ vecDot v v := by
  rw [vecDot]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- The energy of a test function with a uniform gradient bound, on a cube with a
uniformly bounded coefficient. -/
theorem energy_le_of_bounds {a : Vec d → ℝ} {Q : Cube d} {K hi : ℝ}
    (hQ : 0 < Q.2) (hhi : ∀ x ∈ cubeSet Q, a x ≤ hi)
    (hpos : ∀ x ∈ cubeSet Q, 0 < a x)
    (hameas : AEStronglyMeasurable a (volume.restrict (cubeSet Q)))
    (f : H10Function (cubeSet Q))
    (hgrad : ∀ x, vecDot (f.toH1Function.grad x) (f.toH1Function.grad x) ≤ K) :
    energy a (cubeSet Q) f.toH1Function ≤ hi * K * Q.2 ^ d := by
  have hQtop : volume (cubeSet Q) ≠ ⊤ := volume_cubeSet_ne_top
  have : IsFiniteMeasure (volume.restrict (cubeSet Q)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hQtop⟩
  have hGmeas : AEStronglyMeasurable
      (fun x => vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
      (volume.restrict (cubeSet Q)) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.integrableOn_vecDot_grad
      f.toH1Function f.toH1Function).1
  have hbound : ∀ᵐ x ∂(volume.restrict (cubeSet Q)),
      ‖a x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x)‖ ≤ hi * K := by
    filter_upwards [ae_restrict_mem (isOpen_cubeSet (Q := Q)).measurableSet] with x hx
    have h1 : 0 < a x := hpos x hx
    have h2 : a x ≤ hi := hhi x hx
    have h3 := vecDot_self_nonneg (f.toH1Function.grad x)
    have h4 := hgrad x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul h2 h4 h3 (by linarith)
  have hint : IntegrableOn
      (fun x => a x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
      (cubeSet Q) volume := by
    exact Integrable.mono' (integrable_const (hi * K)) (hameas.mul hGmeas) hbound
  have hconst : IntegrableOn (fun _ : Vec d => hi * K) (cubeSet Q) volume :=
    integrable_const (hi * K)
  have hmono : ∫ x in cubeSet Q,
      a x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x) ∂volume ≤
      ∫ _x in cubeSet Q, hi * K ∂volume := by
    refine setIntegral_mono_on hint hconst (isOpen_cubeSet (Q := Q)).measurableSet ?_
    intro x hx
    have h1 : 0 < a x := hpos x hx
    have h2 : a x ≤ hi := hhi x hx
    have h3 := vecDot_self_nonneg (f.toH1Function.grad x)
    have h4 := hgrad x
    exact mul_le_mul h2 h4 h3 (by linarith)
  calc energy a (cubeSet Q) f.toH1Function
      = ∫ x in cubeSet Q,
          a x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x) ∂volume := rfl
    _ ≤ ∫ _x in cubeSet Q, hi * K ∂volume := hmono
    _ = hi * K * Q.2 ^ d := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_cubeSet_toReal hQ.le]
        ring

/-- The tested Sobolev left side dominates the weighted mass of the set where the test
function equals one, raised to `2/p0`. -/
theorem weightedMeasure_rpow_le_lpSq {a : Vec d → ℝ} {Q : Cube d} {p0 : ℝ}
    (hp0 : 0 < p0) {S : Set (Vec d)} (hS : MeasurableSet S) (hSQ : S ⊆ cubeSet Q)
    (f : H10Function (cubeSet Q))
    (hone : ∀ x ∈ S, f.toH1Function.toFun x = 1) :
    weightedMeasure a S ^ (2 / p0) ≤ lpSq a (cubeSet Q) p0 f.toH1Function.toFun := by
  have hne0 : (ENNReal.ofReal p0) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hnetop : (ENNReal.ofReal p0) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p0).toReal = p0 := ENNReal.toReal_ofReal hp0.le
  have hrestrict : ((weightedMeasure a).restrict (cubeSet Q)) S = weightedMeasure a S := by
    rw [Measure.restrict_apply hS, Set.inter_eq_self_of_subset_left hSQ]
  have hindicator : AEStronglyMeasurable (S.indicator fun _ => (1 : ℝ))
      ((weightedMeasure a).restrict (cubeSet Q)) := aestronglyMeasurable_const.indicator hS
  have hind := eLpNorm_indicator_const (μ := (weightedMeasure a).restrict (cubeSet Q))
    (c := (1 : ℝ)) hS.nullMeasurableSet hne0 hnetop
  rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hindicator] at hind
  have hmono : SubdiffusiveProcess.RawLp.eLpNorm (S.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal p0)
      ((weightedMeasure a).restrict (cubeSet Q)) ≤
      SubdiffusiveProcess.RawLp.eLpNorm f.toH1Function.toFun (ENNReal.ofReal p0)
        ((weightedMeasure a).restrict (cubeSet Q)) := by
    refine SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, hone x hx]
    · rw [Set.indicator_of_notMem hx]
      simp
  rw [hind, hrestrict, htoReal] at hmono
  simp only [enorm_one, one_mul] at hmono
  calc weightedMeasure a S ^ (2 / p0)
      = (weightedMeasure a S ^ (1 / p0)) ^ (2 : ℕ) := by
        rw [← ENNReal.rpow_natCast (weightedMeasure a S ^ (1 / p0)) 2, ← ENNReal.rpow_mul]
        norm_num
        ring_nf
    _ ≤ (SubdiffusiveProcess.RawLp.eLpNorm f.toH1Function.toFun (ENNReal.ofReal p0)
          ((weightedMeasure a).restrict (cubeSet Q))) ^ (2 : ℕ) := by
        exact pow_le_pow_left' hmono 2
    _ = lpSq a (cubeSet Q) p0 f.toH1Function.toFun := rfl

/-! ## The clock lower bound -/

def cutoffMassFraction (d : ℕ) : ℝ :=
  min 1 ((volume (smallContrastUnitBall d)).toReal / 8 ^ d)

theorem cutoffMassFraction_pos (d : ℕ) [NeZero d] : 0 < cutoffMassFraction d := by
  have h := volume_smallContrastUnitBall_toReal_pos d
  have h2 : (0 : ℝ) < (volume (smallContrastUnitBall d)).toReal / 8 ^ d := by positivity
  unfold cutoffMassFraction
  exact lt_min one_pos h2

theorem min_one_le_rpow {x t : ℝ} (hx : 0 < x) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    min 1 x ≤ x ^ t := by
  rcases le_total x 1 with h | h
  · refine (min_le_right 1 x).trans ?_
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ t := Real.rpow_le_rpow_of_exponent_ge hx h ht1
  · refine (min_le_left 1 x).trans ?_
    calc (1 : ℝ) = x ^ (0 : ℝ) := (Real.rpow_zero x).symm
      _ ≤ x ^ t := Real.rpow_le_rpow_of_exponent_le h ht0.le

/-- The constant of the clock lower bound: it mentions only `d`, `CC` and `H`. -/
def clockLowerConstant (d : ℕ) (CC H : ℝ) : ℝ :=
  CC * Real.exp (2 * (Real.sqrt d * Real.sqrt H)) * cutoffGradSq d / cutoffMassFraction d

/-- **The Sobolev clause forces `clock(Q.2) ≳ Q.2²`.**

This is the fact that makes a De Giorgi-free route to the massive display possible:
every such route produces a correction of relative size `C·Q.2²/s`, and the display's
hypothesis `cc · clock Q.2 ≤ s` only controls that once `clock Q.2` dominates `Q.2²`. -/
theorem sq_side_le_clockLowerConstant_mul [NeZero d] {a : Vec d → ℝ}
    {H CC p0 clockQ : ℝ} {Q : Cube d}
    (hQ : 0 < Q.2) (hp0 : 2 < p0) (hCC : 0 ≤ CC)
    (hctrl : LogCoefficientControlOn a H Q)
    (hsob : ∀ f : H10Function (cubeSet Q),
      lpSq a (cubeSet Q) p0 f.toH1Function.toFun ≤
        ENNReal.ofReal CC * weightedMeasure a (cubeSet Q) ^ (-(1 - 2 / p0)) *
          ENNReal.ofReal (clockQ * energy a (cubeSet Q) f.toH1Function)) :
    Q.2 ^ 2 ≤ clockLowerConstant d CC H * clockQ := by
  classical
  have hQ1 : Q.1 ∈ cubeSet Q := by
    show Q.1 ∈ centeredAxisCube Q.1 Q.2
    refine mem_centeredAxisCube.mpr fun i => ?_
    simp only [sub_self, abs_zero]
    linarith
  obtain ⟨hposc, hcon⟩ := coefficientContrastOn_of_logCoefficientControlOn hQ hctrl
  set E : ℝ := Real.sqrt d * Real.sqrt H with hEdef
  set kappa : ℝ := a Q.1 with hkappa
  have hk : 0 < kappa := hposc Q.1 hQ1
  set lo : ℝ := Real.exp (-E) * kappa with hlodef
  set hi : ℝ := Real.exp E * kappa with hhidef
  have hlopos : 0 < lo := by rw [hlodef]; positivity
  have hhipos : 0 < hi := by rw [hhidef]; positivity
  have hhib : ∀ x ∈ cubeSet Q, a x ≤ hi := fun x hx => hcon x hx Q.1 hQ1
  have hlob : ∀ x ∈ cubeSet Q, lo ≤ a x := by
    intro x hx
    have h := hcon Q.1 hQ1 x hx
    have hex : 0 < Real.exp E := Real.exp_pos E
    have hrw : lo = kappa / Real.exp E := by
      rw [hlodef, Real.exp_neg]; field_simp
    rw [hrw, div_le_iff₀ hex]
    nlinarith [h]
  obtain ⟨f, hone, hnn, hgrad⟩ := exists_cutoff_h10Function (d := d) hQ
  set K : ℝ := cutoffGradSq d / Q.2 ^ 2 with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (cutoffGradSq_nonneg d) (by positivity)
  have hsub2B : cubeSet Q ⊆ centeredAxisCube Q.1 (2 * Q.2) := cubeSet_subset_double hQ.le
  have hacont : ContinuousOn a (cubeSet Q) :=
    (contDiffOn_of_logCoefficientControlOn hctrl).continuousOn.mono hsub2B
  have hameas : AEStronglyMeasurable a (volume.restrict (cubeSet Q)) :=
    hacont.aestronglyMeasurable (isOpen_cubeSet (Q := Q)).measurableSet
  have henergy : energy a (cubeSet Q) f.toH1Function ≤ hi * K * Q.2 ^ d :=
    energy_le_of_bounds hQ hhib (fun x hx => hposc x hx) hameas f hgrad
  have henergy0 : 0 ≤ energy a (cubeSet Q) f.toH1Function := by
    refine setIntegral_nonneg (isOpen_cubeSet (Q := Q)).measurableSet ?_
    intro x hx
    exact mul_nonneg (hposc x hx).le (vecDot_self_nonneg _)
  set omega : ℝ := (volume (smallContrastUnitBall d)).toReal with homegadef
  have homegapos : 0 < omega := volume_smallContrastUnitBall_toReal_pos d
  have hvolBall : volume (euclideanBall Q.1 (Q.2 / 8)) =
      ENNReal.ofReal (omega * (Q.2 / 8) ^ d) := by
    rw [homegadef, ← volume_euclideanBall_toReal_eq_unit_mul_pow Q.1
      (by positivity : (0 : ℝ) < Q.2 / 8)]
    exact (ENNReal.ofReal_toReal
      (Homogenization.Book.Ch01.volume_euclideanBall_ne_top _ _)).symm
  have hvolQ : volume (cubeSet Q) = ENNReal.ofReal (Q.2 ^ d) := by
    rw [← volume_cubeSet_toReal (B := Q) hQ.le]
    exact (ENNReal.ofReal_toReal volume_cubeSet_ne_top).symm
  set mB : ℝ := lo * (omega * (Q.2 / 8) ^ d) with hmBdef
  set mQ : ℝ := lo * Q.2 ^ d with hmQdef
  have hmBpos : 0 < mB := by rw [hmBdef]; positivity
  have hmQpos : 0 < mQ := by rw [hmQdef]; positivity
  have hBallQ : euclideanBall Q.1 (Q.2 / 8) ⊆ cubeSet Q :=
    euclideanBall_subset_cubeSet (by positivity) (by linarith)
  have hmassB : ENNReal.ofReal mB ≤ weightedMeasure a (euclideanBall Q.1 (Q.2 / 8)) := by
    have h := le_weightedMeasure_of_ae_le (a := a)
      (isOpen_euclideanBall Q.1 (Q.2 / 8)).measurableSet (fun x hx => hlob x (hBallQ hx))
    rwa [hvolBall, ← ENNReal.ofReal_mul hlopos.le] at h
  have hmassQ : ENNReal.ofReal mQ ≤ weightedMeasure a (cubeSet Q) := by
    have h := le_weightedMeasure_of_ae_le (a := a)
      (isOpen_cubeSet (Q := Q)).measurableSet hlob
    rwa [hvolQ, ← ENNReal.ofReal_mul hlopos.le] at h
  have hp0pos : (0 : ℝ) < p0 := by linarith
  have ht : (0 : ℝ) < 2 / p0 := by positivity
  have ht1 : 2 / p0 ≤ 1 := by rw [div_le_one hp0pos]; linarith
  have hkey : ENNReal.ofReal mB ^ (2 / p0) ≤
      lpSq a (cubeSet Q) p0 f.toH1Function.toFun := by
    refine (ENNReal.rpow_le_rpow hmassB ht.le).trans ?_
    exact weightedMeasure_rpow_le_lpSq hp0pos
      (isOpen_euclideanBall Q.1 (Q.2 / 8)).measurableSet hBallQ f hone
  have hsobf := hsob f
  rcases le_or_gt clockQ 0 with hcl | hcl
  · exfalso
    have hz : ENNReal.ofReal (clockQ * energy a (cubeSet Q) f.toH1Function) = 0 := by
      rw [ENNReal.ofReal_eq_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hcl henergy0
    rw [hz, mul_zero] at hsobf
    have hzero : ENNReal.ofReal mB ^ (2 / p0) = 0 :=
      le_antisymm (hkey.trans hsobf) zero_le
    rw [ENNReal.rpow_eq_zero_iff] at hzero
    rcases hzero with ⟨h0, _⟩ | ⟨_, h0⟩
    · rw [ENNReal.ofReal_eq_zero] at h0; linarith
    · linarith
  · have hgap : (0 : ℝ) ≤ 1 - 2 / p0 := by linarith
    have hrp : weightedMeasure a (cubeSet Q) ^ (-(1 - 2 / p0)) ≤
        ENNReal.ofReal mQ ^ (-(1 - 2 / p0)) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hmassQ hgap)
    have hen : ENNReal.ofReal (clockQ * energy a (cubeSet Q) f.toH1Function) ≤
        ENNReal.ofReal (clockQ * (hi * K * Q.2 ^ d)) :=
      ENNReal.ofReal_le_ofReal (by nlinarith [henergy, hcl])
    have hchain : ENNReal.ofReal mB ^ (2 / p0) ≤
        ENNReal.ofReal CC * ENNReal.ofReal mQ ^ (-(1 - 2 / p0)) *
          ENNReal.ofReal (clockQ * (hi * K * Q.2 ^ d)) := by
      refine hkey.trans (hsobf.trans ?_)
      exact mul_le_mul' (mul_le_mul' le_rfl hrp) hen
    have hXnn : (0 : ℝ) ≤ clockQ * (hi * K * Q.2 ^ d) := by positivity
    have hMnn : (0 : ℝ) ≤ mQ ^ (-(1 - 2 / p0)) := Real.rpow_nonneg hmQpos.le _
    rw [ENNReal.ofReal_rpow_of_pos hmBpos, ENNReal.ofReal_rpow_of_pos hmQpos,
      ← ENNReal.ofReal_mul hCC, ← ENNReal.ofReal_mul (by positivity)] at hchain
    have hreal : mB ^ (2 / p0) ≤
        CC * mQ ^ (-(1 - 2 / p0)) * (clockQ * (hi * K * Q.2 ^ d)) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
    -- real endgame
    have hmBeq : mB = mQ * (omega / 8 ^ d) := by
      rw [hmBdef, hmQdef, div_pow]; ring
    have h1 : mB ^ (2 / p0) = mQ ^ (2 / p0) * (omega / 8 ^ d) ^ (2 / p0) := by
      rw [hmBeq, Real.mul_rpow hmQpos.le (by positivity)]
    have h2 : mQ ^ (-(1 - 2 / p0)) = mQ ^ (2 / p0) / mQ := by
      rw [show -(1 - 2 / p0) = 2 / p0 - 1 by ring, Real.rpow_sub hmQpos, Real.rpow_one]
    have hmQt : 0 < mQ ^ (2 / p0) := Real.rpow_pos_of_pos hmQpos _
    have h3 : (omega / 8 ^ d) ^ (2 / p0) ≤ CC * clockQ * (hi * K) / lo := by
      have hstep : mQ ^ (2 / p0) * (omega / 8 ^ d) ^ (2 / p0) ≤
          mQ ^ (2 / p0) * (CC * clockQ * (hi * K) / lo) := by
        rw [← h1]
        refine hreal.trans (le_of_eq ?_)
        rw [h2, hmQdef]
        field_simp
      exact le_of_mul_le_mul_left (by linarith [hstep]) hmQt
    have hratio : hi / lo = Real.exp (2 * E) := by
      rw [hhidef, hlodef, Real.exp_neg]
      field_simp [Real.exp_ne_zero]
      rw [show (2 : ℝ) * E = E + E by ring, Real.exp_add]
      ring
    have h4 : (omega / 8 ^ d) ^ (2 / p0) * Q.2 ^ 2 ≤
        CC * Real.exp (2 * E) * cutoffGradSq d * clockQ := by
      have hQ2 : (0 : ℝ) < Q.2 ^ 2 := by positivity
      have hexp : CC * clockQ * (hi * K) / lo
          = CC * Real.exp (2 * E) * cutoffGradSq d * clockQ / Q.2 ^ 2 := by
        rw [hKdef, ← hratio]
        field_simp
      rw [hexp, le_div_iff₀ hQ2] at h3
      exact h3
    have h5 : cutoffMassFraction d ≤ (omega / 8 ^ d) ^ (2 / p0) :=
      min_one_le_rpow (by positivity) ht ht1
    have hcm : 0 < cutoffMassFraction d := cutoffMassFraction_pos d
    rw [clockLowerConstant, ← hEdef]
    rw [div_mul_eq_mul_div, le_div_iff₀ hcm]
    nlinarith [h4, h5, sq_nonneg Q.2, hcm]

theorem clockLowerConstant_nonneg (d : ℕ) [NeZero d] {CC H : ℝ} (hCC : 0 ≤ CC) :
    0 ≤ clockLowerConstant d CC H := by
  rw [clockLowerConstant]
  have h1 : 0 ≤ CC * Real.exp (2 * (Real.sqrt d * Real.sqrt H)) * cutoffGradSq d := by
    have := cutoffGradSq_nonneg d
    have h2 : (0 : ℝ) < Real.exp (2 * (Real.sqrt d * Real.sqrt H)) := Real.exp_pos _
    positivity
  exact div_nonneg h1 (cutoffMassFraction_pos d).le

/-- **The form.**  Under `LocalTorsionEstimates` and the family's scaled
coefficient control, the massive display's own hypothesis `cc * clock B.2 ≤ s` bounds
`B.2²/s` by a constant depending only on `d, p0, cc, CC, H` — all bound before `∃ C`.

This is precisely what a De Giorgi-free route to 
needs, and it is not visible in the statement: `clock` is an arbitrary function there,
and only the Sobolev clause ties it to the geometry. -/
theorem sq_side_le_of_localTorsionEstimates [NeZero d] {a : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} {clock : ℝ → ℝ} {p0 cc CC H s : ℝ}
    {U B : Cube d} {Qfam Afam : Set (Cube d)}
    (hp0 : 2 < p0) (hCC : 0 ≤ CC) (hcc : 0 < cc)
    (hBpos : 0 < B.2) (hB : B ∈ Qfam)
    (hH : FamilyLogCoefficientControl a H Qfam)
    (htor : LocalTorsionEstimates a law clock p0 cc CC U Qfam Afam)
    (hs : cc * clock B.2 ≤ s) :
    B.2 ^ 2 ≤ clockLowerConstant d CC H / cc * s := by
  have hmain := sq_side_le_clockLowerConstant_mul hBpos hp0 hCC (hH B hB) (htor.sobolev B hB)
  have hclock : clock B.2 ≤ s / cc := by
    rw [le_div_iff₀ hcc]
    linarith [hs]
  have hK0 : 0 ≤ clockLowerConstant d CC H := clockLowerConstant_nonneg d hCC
  calc B.2 ^ 2 ≤ clockLowerConstant d CC H * clock B.2 := hmain
    _ ≤ clockLowerConstant d CC H * (s / cc) := mul_le_mul_of_nonneg_left hclock hK0
    _ = clockLowerConstant d CC H / cc * s := by ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
