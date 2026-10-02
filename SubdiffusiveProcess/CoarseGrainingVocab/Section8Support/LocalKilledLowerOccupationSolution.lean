import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerOccupation
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveZeroMassLimit
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveContraction
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumRepresentative




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ}

/-! ### The occupation potential solves the Poisson problem -/



theorem exists_isMassiveWeakSolutionOn_zero_occupationPotential
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} (hD : LocalDiffusion c rho law)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    {q : Vec d → ℝ} (hq : Measurable q) {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hqb : ∀ x ∈ W, |q x| ≤ K)
    (hmean : ∀ z ∈ W, meanExit law W z ≤ ENNReal.ofReal E) :
    ∃ v : H1Function W,
      (∀ᵐ x ∂(volume.restrict W), v.toFun x = occupationPotential law W q x) ∧
        IsMassiveWeakSolutionOn c rho 0 W v q := by
  classical
  haveI : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
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
  haveI hfinVol : IsFiniteMeasure (volumeMeasureOn W) := by
    refine ⟨?_⟩
    rwa [Measure.restrict_apply_univ]
  haveI hfinW : IsFiniteMeasure ((weightedMeasure rho).restrict W) :=
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
  exact exists_isMassiveWeakSolutionOn_zero_of_bounded_pointwise_limit
    hEll hrhoMeas hrhoBdd hqL2 w hbound hpoint hgradbound hmu hsol

/-! ### The subtraction step -/



theorem weakHarmonic_sub_of_isMassiveWeakSolutionOn_zero
    {c rho : Vec d → ℝ} {lam Lam rhoMax : ℝ} {outer : Set (Vec d)} {h₁ h₂ f : Vec d → ℝ}
    (hEll : IsEllipticFieldOn lam Lam outer (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict outer))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict outer), |rho x| ≤ rhoMax)
    (hf : MemL2On outer f)
    (hcont : ContinuousOn (fun y => h₁ y - h₂ y) outer)
    (houter : IsOpen outer) {u₁ u₂ : H1Function outer}
    (hae₁ : ∀ᵐ x ∂(volume.restrict outer), u₁.toFun x = h₁ x)
    (hae₂ : ∀ᵐ x ∂(volume.restrict outer), u₂.toFun x = h₂ x)
    (hs₁ : IsMassiveWeakSolutionOn c rho 0 outer u₁ f)
    (hs₂ : IsMassiveWeakSolutionOn c rho 0 outer u₂ f) :
    WeakHarmonic c outer (fun y => h₁ y - h₂ y) := by
  refine ⟨hcont, fun W hW _ hclosure => ?_⟩
  have hWsub : W ⊆ outer := subset_closure.trans hclosure
  have hrestrict : volume.restrict W ≤ volume.restrict outer :=
    Measure.restrict_mono hWsub le_rfl
  have hEllW : IsEllipticFieldOn lam Lam W (scalarCoeffField c) :=
    hEll.mono hW.measurableSet hWsub
  have hrhoMeasW : AEStronglyMeasurable rho (volume.restrict W) :=
    hrhoMeas.mono_measure hrestrict
  have hrhoBddW : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax :=
    ae_mono hrestrict hrhoBdd
  have hfW : MemL2On W f := memL2On_mono hWsub hf
  have hr₁ := hs₁.restrict hW houter hWsub
  have hr₂ := hs₂.restrict hW houter hWsub
  have hdiff := IsMassiveWeakSolutionOn.sub hEllW hrhoMeasW hrhoBddW hfW hfW hr₁ hr₂
  refine ⟨u₁.restrict hW hWsub - u₂.restrict hW hWsub, ?_, ?_⟩
  · filter_upwards [ae_mono hrestrict hae₁, ae_mono hrestrict hae₂] with x hx₁ hx₂
    simp only [H1Function.sub_toFun, H1Function.restrict, hx₁, hx₂]
  · intro phi
    have h := hdiff phi
    simp only [Pi.sub_apply, sub_self, mul_zero, zero_mul, zero_add,
      MeasureTheory.integral_zero] at h
    simpa only [vecDot_smul_left] using h

/-! ### The reduction of the second conjunct of `KilledKernelTimeDerivative` -/

/-- **The Poisson correction of `l.local.killed.lower`, assuming the weak killed heat
equation and interior continuity.**

If `h` — in the application, `p_t^U(x,·)` — is almost everywhere equal to an `H¹(outer)`
weak solution of `-∇·(c∇h) = ρ q` on `outer`, and if the difference `h - v` between it and
the occupation potential of `q` is continuous on `outer`, then that difference is weakly
harmonic on `outer`: exactly the second conjunct of
`LocalKilledLowerHarmonic.KilledKernelTimeDerivative`.

Everything else the conjunct needs is proved here: the occupation potential really is a weak
solution of the same Poisson problem
(`exists_isMassiveWeakSolutionOn_zero_occupationPotential`), and the difference of two such
solutions is weakly harmonic (`weakHarmonic_sub_of_isMassiveWeakSolutionOn_zero`). -/
theorem weakHarmonic_sub_occupationPotential
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} (hD : LocalDiffusion c rho law)
    {outer : Set (Vec d)} (houter : IsOpen outer) (houterb : Bornology.IsBounded outer)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam outer (scalarCoeffField c))
    {q : Vec d → ℝ} (hq : Measurable q) {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hqb : ∀ x ∈ outer, |q x| ≤ K)
    (hmean : ∀ z ∈ outer, meanExit law outer z ≤ ENNReal.ofReal E)
    {h : Vec d → ℝ} {P : H1Function outer}
    (haeP : ∀ᵐ x ∂(volume.restrict outer), P.toFun x = h x)
    (hP : IsMassiveWeakSolutionOn c rho 0 outer P q)
    (hcont : ContinuousOn (fun y => h y - occupationPotential law outer q y) outer) :
    WeakHarmonic c outer (fun y => h y - occupationPotential law outer q y) := by
  classical
  have hrhoW : CoefficientOn outer rho :=
    coefficientOn_mono subset_closure (hD.2.1 (closure outer) houterb.isCompact_closure).2
  obtain ⟨hrhoMeas, lo, hi, hlo, hbnd⟩ := hrhoW
  have hrhoBdd : ∀ᵐ x ∂(volume.restrict outer), |rho x| ≤ hi := by
    filter_upwards [hbnd] with x hx
    rw [abs_of_nonneg (le_trans hlo.le hx.1)]
    exact hx.2
  have hqbound : ∀ᵐ x ∂(volume.restrict outer), ‖q x‖ ≤ K := by
    filter_upwards [ae_restrict_mem houter.measurableSet] with x hx
    simpa only [Real.norm_eq_abs] using hqb x hx
  haveI hfinVol : IsFiniteMeasure (volume.restrict outer) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono subset_closure)
      houterb.isCompact_closure.measure_lt_top
  have hqL2 : MemL2On outer q := MemLp.of_bound hq.aestronglyMeasurable K hqbound
  obtain ⟨v, hvae, hvsol⟩ :=
    exists_isMassiveWeakSolutionOn_zero_occupationPotential hD houter houterb hlam hEll hq
      hK hE hqb hmean
  exact weakHarmonic_sub_of_isMassiveWeakSolutionOn_zero hEll hrhoMeas hrhoBdd hqL2 hcont
    houter haeP hvae hP hvsol

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
