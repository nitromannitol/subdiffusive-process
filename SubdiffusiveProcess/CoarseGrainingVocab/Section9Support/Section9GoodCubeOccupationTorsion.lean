module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeZeroTraceLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerOccupationSolution

@[expose] public section

/-!
# A zero-trace occupation potential for good cubes

The occupation potential retains its zero-boundary carrier through the
massive resolvent limit. For constant forcing, its real representative is
the mean exit time. The finite upper exit bound is used when converting
that real equality back to an extended nonnegative equality.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The bounded occupation potential has a zero-trace Poisson representative. -/
theorem goodCube_exists_h10_occupationPotential
    {d : ℕ} [NeZero d]
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} (hD : LocalDiffusion c rho law)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    (hWconv : IsOpenBoundedConvexDomain W)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    {q : Vec d → ℝ} (hq : Measurable q) {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hqb : ∀ x ∈ W, |q x| ≤ K)
    (hmean : ∀ z ∈ W, meanExit law W z ≤ ENNReal.ofReal E) :
    ∃ v : H10Function W,
      (∀ᵐ x ∂(volume.restrict W), v.toH1Function.toFun x = occupationPotential law W q x) ∧
        IsMassiveWeakSolutionOn c rho 0 W v.toH1Function q := by
  classical
  have : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  have hWmeas : MeasurableSet W := hW.measurableSet
  have hrhoW : CoefficientOn W rho :=
    coefficientOn_mono subset_closure (hD.2.1 (closure W) hWb.isCompact_closure).2
  obtain ⟨hrhoMeas, lo, hi, hlo, hbnd⟩ := hrhoW
  have hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ hi := by
    filter_upwards [hbnd] with x hx
    rw [abs_of_nonneg (le_trans hlo.le hx.1)]
    exact hx.2
  have hrhoNonneg : ∀ᵐ x ∂(volume.restrict W), 0 ≤ rho x :=
    hbnd.mono fun x hx => le_trans hlo.le hx.1
  have hvolW : volume W < ∞ :=
    lt_of_le_of_lt (measure_mono subset_closure) hWb.isCompact_closure.measure_lt_top
  have hfinVol : IsFiniteMeasure (volumeMeasureOn W) := by
    refine ⟨?_⟩
    rwa [Measure.restrict_apply_univ]
  have hfinW : IsFiniteMeasure ((weightedMeasure rho).restrict W) :=
    isFiniteMeasure_restrict (weightedMeasure_ne_top_of_localDiffusion hD hW hWb)
  have hqbound : ∀ᵐ x ∂(volume.restrict W), ‖q x‖ ≤ K := by
    filter_upwards [ae_restrict_mem hWmeas] with x hx
    simpa only [Real.norm_eq_abs] using hqb x hx
  have hqL2 : MemL2On W q := MemLp.of_bound hq.aestronglyMeasurable K hqbound
  have hqL2w : MemLp q 2 ((weightedMeasure rho).restrict W) := by
    refine MemLp.of_bound hq.aestronglyMeasurable K ?_
    filter_upwards [ae_restrict_mem hWmeas] with x hx
    simpa only [Real.norm_eq_abs] using hqb x hx
  -- the resolvent family at the scales `s n = n + 1`
  set s : ℕ → ℝ := fun n => (n : ℝ) + 1 with hsdef
  have hspos : ∀ n, 0 < s n := fun n => by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [hsdef]
    linarith
  have hstop : Tendsto s atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  choose u hue hus using fun n : ℕ => hD.2.2 W hW hWb (s n) (hspos n) q hqL2w
  set U10 : ℕ → H10Function W := fun n => (s n) • (u n) with hU10
  set w : ℕ → H1Function W := fun n => (U10 n).toH1Function with hwdef
  have hsol : ∀ n, IsMassiveWeakSolutionOn c rho (s n)⁻¹ W (w n) q := by
    intro n
    have h := IsMassiveWeakSolutionOn.const_smul (s n) (hus n)
    have hfun : (fun x => s n * ((s n)⁻¹ * q x)) = q := by
      funext x
      rw [← mul_assoc, mul_inv_cancel₀ (hspos n).ne', one_mul]
    rw [hfun] at h
    exact h
  have hAc : volume.restrict W ≪ (weightedMeasure rho).restrict W :=
    volume_restrict_absolutelyContinuous_weightedMeasure_restrict hWmeas
      ⟨hrhoMeas, lo, hi, hlo, hbnd⟩
  have hid : ∀ n, ∀ᵐ x ∂(volume.restrict W),
      (w n).toFun x = s n * killedResolvent law W (s n) q x := by
    intro n
    filter_upwards [hAc.ae_le (hue n)] with x hx
    show s n * (u n).toH1Function.toFun x = _
    rw [hx]
  have hbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn W), |(w n).toFun x| ≤ K * E := by
    intro n
    filter_upwards [hid n, ae_restrict_mem hWmeas] with x hx hxW
    rw [hx]
    exact abs_mul_killedResolvent_le law hW hq hK hE hqb (hmean x hxW) (hspos n)
  have hpoint : ∀ᵐ x ∂(volumeMeasureOn W),
      Tendsto (fun n => (w n).toFun x) atTop (𝓝 (occupationPotential law W q x)) := by
    filter_upwards [ae_all_iff.2 hid, ae_restrict_mem hWmeas] with x hx hxW
    refine ((tendsto_mul_killedResolvent_occupationPotential law hW hq hqb
      (hmean x hxW)).comp hstop).congr ?_
    intro n
    exact (hx n).symm
  -- the uniform gradient bound: the mass term has a sign, so the energy identity suffices
  set B : ℝ := hi * K * (K * E) * (volume W).toReal with hBdef
  have hgradbound : ∀ n, ‖(w n).gradToHilbertVectorL2‖ ≤ Real.sqrt (B / lam) := by
    intro n
    have hcoercive : lam * ‖(w n).gradToHilbertVectorL2‖ ^ 2 ≤
        ∫ x in W, c x * vecNormSq ((w n).grad x) ∂volume := by
      have h := MassiveH1Hilbert.coeffGradientBilin_self_ge hEll
        (MassiveH1Hilbert.ofH1Function (w n))
      simpa only [MassiveH1Hilbert.gradient_ofH1Function,
        MassiveH1Hilbert.coeffGradientBilin_apply_ofH1Function,
        vecDot_smul_left, vecNormSq] using h
    have hen : ((s n)⁻¹ * ∫ x in W, rho x * (w n).toFun x * (w n).toFun x ∂volume) +
        ∫ x in W, c x * vecNormSq ((w n).grad x) ∂volume
        = ∫ x in W, rho x * q x * (w n).toFun x ∂volume :=
      massive_energy_identity_of_isMassiveWeakSolutionOn (u := U10 n) (hsol n)
    have hmassnn : 0 ≤ ∫ x in W, rho x * (w n).toFun x * (w n).toFun x ∂volume := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hrhoNonneg] with x hx
      simp only [Pi.zero_apply]
      have hz : rho x * (w n).toFun x * (w n).toFun x
          = rho x * ((w n).toFun x * (w n).toFun x) := by ring
      rw [hz]
      exact mul_nonneg hx (mul_self_nonneg _)
    have hint : IntegrableOn (fun x => rho x * q x * (w n).toFun x) W :=
      integrableOn_mass_term hrhoMeas hrhoBdd hqL2 (w n).memL2
    have hconst : IntegrableOn (fun _ : Vec d => hi * K * (K * E)) W := by
      simp only [IntegrableOn]
      exact integrable_const _
    have hrhs : (∫ x in W, rho x * q x * (w n).toFun x ∂volume) ≤ B := by
      have hmono : (∫ x in W, rho x * q x * (w n).toFun x ∂volume)
          ≤ ∫ _x in W, hi * K * (K * E) ∂volume := by
        refine integral_mono_ae hint hconst ?_
        filter_upwards [hrhoBdd, ae_restrict_mem hWmeas, hbound n] with x h1 hxW h3
        have h2 : |q x| ≤ K := hqb x hxW
        have hhi : (0:ℝ) ≤ hi := le_trans (abs_nonneg _) h1
        calc rho x * q x * (w n).toFun x ≤ |rho x * q x * (w n).toFun x| := le_abs_self _
          _ = |rho x| * |q x| * |(w n).toFun x| := by rw [abs_mul, abs_mul]
          _ ≤ hi * K * (K * E) := by
              refine mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hhi) h3 (abs_nonneg _)
                (mul_nonneg hhi hK)
      refine hmono.trans (le_of_eq ?_)
      rw [setIntegral_const, hBdef, smul_eq_mul, measureReal_def]
      ring
    have hsq : ‖(w n).gradToHilbertVectorL2‖ ^ 2 ≤ B / lam := by
      refine (le_div_iff₀ hlam).2 ?_
      have hinvnn : 0 ≤ (s n)⁻¹ * ∫ x in W, rho x * (w n).toFun x * (w n).toFun x ∂volume :=
        mul_nonneg (inv_nonneg.2 (hspos n).le) hmassnn
      calc ‖(w n).gradToHilbertVectorL2‖ ^ 2 * lam
          = lam * ‖(w n).gradToHilbertVectorL2‖ ^ 2 := by ring
        _ ≤ ∫ x in W, c x * vecNormSq ((w n).grad x) ∂volume := hcoercive
        _ ≤ ∫ x in W, rho x * q x * (w n).toFun x ∂volume := by linarith
        _ ≤ B := hrhs
    exact Real.le_sqrt_of_sq_le hsq
  have hmu : Tendsto (fun n => (s n)⁻¹) atTop (𝓝 0) := hstop.inv_tendsto_atTop
  -- pass to the H10 zero-mass limit on `U10`
  obtain ⟨v, hvae, hvsol⟩ :=
    goodCube_exists_h10_zero_mass_of_bounded_pointwise_limit hWconv hEll hrhoMeas hrhoBdd hqL2 U10
      hbound hpoint hgradbound hmu
      (fun n => hsol n)
  exact ⟨v, hvae, hvsol⟩

/-- The potential of the constant one is the real mean exit time. -/
theorem goodCube_occupationPotential_one_eq_meanExit_toReal
    {d : ℕ} (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {W : Set (Vec d)} (hW : IsOpen W) (x : Vec d) :
    occupationPotential law W (fun _ => 1) x = (meanExit law W x).toReal := by
  classical
  have hsurv_ne : ∀ t : ℝ,
      law x {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w} ≠ ∞ :=
    fun _ => measure_ne_top _ _
  have hEq : (∫ t in Ioi (0 : ℝ),
        (law x {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal)
      = (∫⁻ t in Ioi (0 : ℝ),
        law x {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal :=
    integral_toReal ((survival_antitone law W x).measurable.aemeasurable)
      (Eventually.of_forall fun t => lt_of_le_of_ne le_top (hsurv_ne t))
  have hinner : ∀ t : ℝ,
      ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}, (1 : ℝ) ∂law x
        = (law x {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal := by
    intro t
    rw [setIntegral_const]
    simp [Measure.real]
  have h0 : occupationPotential law W (fun _ => 1) x
      = ∫ t in Ioi (0 : ℝ),
          ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}, (1 : ℝ) ∂law x := rfl
  rw [h0]
  simp only [hinner]
  rw [hEq, SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper.meanExit_eq_lintegral_survival law hW x]

/-- Finite mean exit times have a bounded, nonnegative zero-trace torsion carrier. -/
theorem goodCube_exists_h10_meanExit
    {d : ℕ} [NeZero d] {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} (hD : LocalDiffusion c rho law)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    (hWconv : IsOpenBoundedConvexDomain W)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    {E : ℝ} (hE : 0 ≤ E)
    (hmean : ∀ x ∈ W, meanExit law W x ≤ ENNReal.ofReal E) :
    ∃ v : H10Function W,
      (∀ᵐ x ∂volume.restrict W, ENNReal.ofReal (v.toH1Function.toFun x) = meanExit law W x) ∧
      (∀ᵐ x ∂volume.restrict W, 0 ≤ v.toH1Function.toFun x ∧ v.toH1Function.toFun x ≤ E) ∧
      IsMassiveWeakSolutionOn c rho 0 W v.toH1Function (fun _ => 1) := by
  have hmk : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  obtain ⟨v, hv, hsol⟩ := goodCube_exists_h10_occupationPotential hD hW hWb hWconv hlam hEll
    (q := fun _ => (1 : ℝ)) measurable_const (K := 1) (E := E) zero_le_one hE
    (fun x _ => by simp) hmean
  have hEtop : ENNReal.ofReal E < ⊤ := by
    rw [ENNReal.ofReal]
    exact ENNReal.coe_lt_top
  have hne : ∀ x ∈ W, meanExit law W x ≠ ⊤ := fun x hx =>
    ne_of_lt (lt_of_le_of_lt (hmean x hx) hEtop)
  have hWmeas : MeasurableSet W := hW.measurableSet
  have hmem : ∀ᵐ x ∂(volume.restrict W), x ∈ W := ae_restrict_mem hWmeas
  refine ⟨v, ?_, ?_, hsol⟩
  · filter_upwards [hv, hmem] with x hxv hxm
    rw [hxv, goodCube_occupationPotential_one_eq_meanExit_toReal law hW x,
      ENNReal.ofReal_toReal (hne x hxm)]
  · filter_upwards [hv, hmem] with x hxv hx
    rw [hxv, goodCube_occupationPotential_one_eq_meanExit_toReal law hW x]
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmean x hx)).trans_eq
      (ENNReal.toReal_ofReal hE)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
