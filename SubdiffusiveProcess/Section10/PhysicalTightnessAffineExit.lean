import SubdiffusiveProcess.Section10.PhysicalTightnessAffineMoser
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceEstimatesUniqueness

/-! The common positive spatial scalars cancel from the every-start physical
exit bound. Local analytic estimates are consumed directly by the incoming
physical lifetime law; no transformed-law equality is assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped Pointwise ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- Pure scalar cancellation of the spatial Jacobian and common speed factor. -/
theorem affine_exit_constant {r c gamma : ℝ} (hr : 0 < r) (hc : 0 < c)
    (d : ℕ) (t Km Ke : ℝ) :
    4 * ((Km * Real.sqrt ((r ^ d * c)⁻¹)) *
      Real.sqrt (t * ((r ^ d * gamma * r⁻¹ * r⁻¹) * Ke))) =
      4 * (Km * Real.sqrt ((t / (r ^ 2 * c / gamma)) * Ke)) := by
  rw [mul_assoc Km, ← Real.sqrt_mul (by positivity : 0 ≤ (r ^ d * c)⁻¹)]
  congr 2
  field_simp [hr.ne', hc.ne', pow_ne_zero d hr.ne']

/-- Every-start early exit in the original physical law, obtained from the
actual local cutoff and weighted Moser estimates. The clock is `r^2*c/gamma`.
No local diffusion witness or caller path-law identification is required. -/
theorem exit_probability_le_of_affine_cutoff_moser {d : ℕ}
    {coefficient rho a b : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData coefficient rho law)
    (hcontinuous : Continuous coefficient) (hpositive : ∀ y, 0 < coefficient y)
    {r c gamma : ℝ} (hr : 0 < r) (hc : 0 < c) (hgamma : 0 < gamma) (z : Vec d)
    (hcoeff : ∀ x, coefficient (r • x + z) = gamma * a x)
    (hrho : ∀ x, rho (r • x + z) = c * b x)
    (R V W : ℝ) (hR : 0 < R) (hV : 0 < V) (hVR : V ≤ R) (hWV : W ≤ V)
    (chi : H10Function (Metric.ball (0 : Vec d) R))
    (hchi01 : ∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1)
    (hchi1 : ∀ x ∈ Metric.ball (0 : Vec d) V, chi.toFun x = 1)
    (Ke Km : ℝ) (hKe : 0 ≤ Ke) (hKm : 0 ≤ Km)
    (henergy : energy a (Metric.ball (0 : Vec d) R) chi.toH1Function ≤ Ke)
    (hmoser : ∀ w : H1Function (Metric.ball (0 : Vec d) V),
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec d) V), 0 ≤ w.toFun x) →
      (∃ Mw : ℝ, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec d) V), w.toFun x ≤ Mw) →
      IsWeakSubSolutionOn a (Metric.ball (0 : Vec d) V) w →
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec d) W),
        ENNReal.ofReal (w.toFun x) ≤ ENNReal.ofReal Km *
          (∫⁻ y in Metric.ball (0 : Vec d) V, ENNReal.ofReal (w.toFun y ^ 2 * b y)) ^ (1 / 2 : ℝ)) :
    ∀ t : ℝ, 0 < t → ∀ x ∈ Metric.ball z (r * W),
      law x {w | LifetimePath.exitTime (Metric.ball z (r * R)) w ≤ ENNReal.ofReal t} ≤
        ENNReal.ofReal (4 * (Km * Real.sqrt ((t / (r ^ 2 * c / gamma)) * Ke))) := by
  have hU := affine_ball_eq hr z R
  have hVe := affine_ball_eq hr z V
  have hWe := affine_ball_eq hr z W
  have hUopen : IsOpen (translateSet z (r • Metric.ball (0 : Vec d) R)) := by
    rw [hU]
    exact Metric.isOpen_ball
  have hUb : Bornology.IsBounded (translateSet z (r • Metric.ball (0 : Vec d) R)) := by
    rw [hU]
    exact Metric.isBounded_ball
  have hVopen : IsOpen (translateSet z (r • Metric.ball (0 : Vec d) V)) := by
    rw [hVe]
    exact Metric.isOpen_ball
  have hWopen : IsOpen (translateSet z (r • Metric.ball (0 : Vec d) W)) := by
    rw [hWe]
    exact Metric.isOpen_ball
  have hVU : translateSet z (r • Metric.ball (0 : Vec d) V) ⊆
      translateSet z (r • Metric.ball (0 : Vec d) R) := by
    rw [hVe, hU]
    exact Metric.ball_subset_ball (mul_le_mul_of_nonneg_left hVR hr.le)
  have hWV' : translateSet z (r • Metric.ball (0 : Vec d) W) ⊆
      translateSet z (r • Metric.ball (0 : Vec d) V) := by
    rw [hWe, hVe]
    exact Metric.ball_subset_ball (mul_le_mul_of_nonneg_left hWV hr.le)
  letI : IsFiniteMeasure (volumeMeasureOn (translateSet z (r • Metric.ball (0 : Vec d) V))) := by
    rw [hVe]
    exact (isOpenBoundedConvexDomain_ball z (mul_pos hr hV)).isFiniteMeasure_restrict_volume
  obtain ⟨lam, Lam, hEll, -⟩ :=
    exists_isEllipticFieldOn_ball_of_continuous_pos hcontinuous hpositive z (mul_pos hr hR)
  rw [← hU] at hEll
  have hchiP01 : ∀ y, 0 ≤ (affineH10Pushforward hr z chi).toFun y ∧
      (affineH10Pushforward hr z chi).toFun y ≤ 1 := by
    intro y
    simpa only [affineH10Pushforward_toFun] using hchi01 (r⁻¹ • (y - z))
  have hchiP1 : ∀ y ∈ translateSet z (r • Metric.ball (0 : Vec d) V),
      (affineH10Pushforward hr z chi).toFun y = 1 := by
    rintro y ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    rw [affineH10Pushforward_toFun, add_sub_cancel_right, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
    exact hchi1 x hx
  have hE : energy coefficient (translateSet z (r • Metric.ball (0 : Vec d) R))
      (affineH10Pushforward hr z chi).toH1Function ≤
        (r ^ d * gamma * r⁻¹ * r⁻¹) * Ke := by
    rw [energy_affine_pushforward hr z hcoeff]
    exact mul_le_mul_of_nonneg_left henergy (by positivity)
  have hm := moser_affine_transport hr hc hgamma hKm z hrho hcoeff hmoser
  have hfast := exit_probability_le_of_cutoff_moser hD hUopen hUb hVopen hVU hWopen hWV'
    hEll (Eventually.of_forall fun y => (hpositive y).le) (affineH10Pushforward hr z chi)
    hchiP01 hchiP1 ((r ^ d * gamma * r⁻¹ * r⁻¹) * Ke) (Km * Real.sqrt ((r ^ d * c)⁻¹))
    (by positivity) (mul_nonneg hKm (Real.sqrt_nonneg _)) hE hm
  simp_rw [hU, hWe, affine_exit_constant hr hc] at hfast
  exact hfast

end SubdiffusiveProcess.Section10.PhysicalTightness
