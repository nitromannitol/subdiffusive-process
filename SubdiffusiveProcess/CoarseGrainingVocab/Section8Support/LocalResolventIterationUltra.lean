module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationLevelEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationStampacchia
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationResolventOperator
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationScaling

@[expose] public section

/-!
# Ultracontractivity of a finite resolvent power

The Sobolev assumption of Section 8 gives, through the positive-level energy
estimates and the Stampacchia truncation iteration, an `L^q → L^∞` bound for a
single killed resolvent.  Duality and the geometric exponent iteration of
`LocalResolventIterationBootstrap` upgrade it to an `L¹ → L^∞` bound for a
fixed power of the resolvent, with the mass of the reference measure appearing
exactly once in the denominator.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationBootstrap
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationScaling
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra

theorem theta_pos {p0 : ℝ} (hp0 : 2 < p0) : 0 < 1 - 2 / p0 := by
  have h0 : 0 < p0 := by linarith
  have : 2 / p0 < 1 := (div_lt_one h0).mpr hp0
  simpa only [sub_pos] using this

theorem theta_lt_one {p0 : ℝ} (hp0 : 2 < p0) : 1 - 2 / p0 < 1 := by
  have h0 : 0 < p0 := by linarith
  have : 0 < 2 / p0 := by positivity
  linarith

/-- The high integrability exponent of the Stampacchia iteration. -/
def qExp (p0 : ℝ) : NNReal := Real.toNNReal (2 / (1 - 2 / p0))

/-- The exponent dual to `qExp`. -/
def rExp (p0 : ℝ) : NNReal := Real.toNNReal ((2 / (1 - 2 / p0)) / (2 / (1 - 2 / p0) - 1))

theorem two_lt_qReal {p0 : ℝ} (hp0 : 2 < p0) : 2 < 2 / (1 - 2 / p0) := by
  have h1 := theta_pos hp0
  have h2 := theta_lt_one hp0
  rw [lt_div_iff₀ h1]
  linarith

theorem coe_qExp {p0 : ℝ} (hp0 : 2 < p0) : ((qExp p0 : NNReal) : ℝ) = 2 / (1 - 2 / p0) :=
  Real.coe_toNNReal _ (by linarith [two_lt_qReal hp0])

theorem one_lt_qExp {p0 : ℝ} (hp0 : 2 < p0) : 1 < qExp p0 := by
  have := two_lt_qReal hp0
  have h : ((1 : NNReal) : ℝ) < ((qExp p0 : NNReal) : ℝ) := by
    rw [coe_qExp hp0]; simp only [NNReal.coe_one]; linarith
  exact_mod_cast h

theorem coe_rExp {p0 : ℝ} (hp0 : 2 < p0) :
    ((rExp p0 : NNReal) : ℝ) = (2 / (1 - 2 / p0)) / (2 / (1 - 2 / p0) - 1) := by
  refine Real.coe_toNNReal _ (le_of_lt (div_pos ?_ ?_)) <;> linarith [two_lt_qReal hp0]

theorem one_lt_rExp {p0 : ℝ} (hp0 : 2 < p0) : 1 < rExp p0 := by
  have hq := two_lt_qReal hp0
  have h : ((1 : NNReal) : ℝ) < ((rExp p0 : NNReal) : ℝ) := by
    rw [coe_rExp hp0]
    simp only [NNReal.coe_one]
    rw [lt_div_iff₀ (by linarith)]
    linarith
  exact_mod_cast h

theorem inv_add_inv_div_sub_one {q : ℝ} (hq : 1 < q) : q⁻¹ + (q / (q - 1))⁻¹ = 1 := by
  have h0 : q ≠ 0 := by linarith
  have h1 : q - 1 ≠ 0 := by linarith
  rw [inv_div]
  field_simp
  ring

theorem qExp_conjugate {p0 : ℝ} (hp0 : 2 < p0) :
    ((qExp p0 : NNReal) : ℝ)⁻¹ + ((rExp p0 : NNReal) : ℝ)⁻¹ = 1 := by
  rw [coe_qExp hp0, coe_rExp hp0]
  exact inv_add_inv_div_sub_one (by linarith [two_lt_qReal hp0])

/-- The exponent `qExp` as an extended-nonnegative exponent. -/
theorem coe_qExp_ennreal (p0 : ℝ) :
    ((qExp p0 : NNReal) : ℝ≥0∞) = ENNReal.ofReal (2 / (1 - 2 / p0)) := rfl



/-- The scalar identity behind the ultracontractivity constant. -/
theorem stampacchia_power_eq {S A m V th : ℝ} (hS : 0 ≤ S) (hA : 0 < A) (hm : 0 < m)
    (hV : 0 < V) (hth : 0 < th) :
    (S * Real.sqrt (A * m ^ (-th) * V)) ^ (2 / th)
      = S ^ (2 / th) * A ^ th⁻¹ / m * V ^ th⁻¹ := by
  have hth0 : th ≠ 0 := hth.ne'
  have hX : (0:ℝ) < A * m ^ (-th) * V := by positivity
  have hhalf : (1 / 2 : ℝ) * (2 / th) = th⁻¹ := by field_simp
  have hneg : (-th) * th⁻¹ = -1 := by field_simp
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hS (Real.rpow_nonneg hX.le _),
    ← Real.rpow_mul hX.le, hhalf,
    Real.mul_rpow (by positivity) hV.le,
    Real.mul_rpow hA.le (Real.rpow_nonneg hm.le _),
    ← Real.rpow_mul hm.le, hneg, Real.rpow_neg_one]
  field_simp

section Diffusion

variable {d : ℕ} {c rho : Vec d → ℝ} {law : ProbabilityTheory.Kernel (Vec d) (Path d)}

/-- A local diffusion law is a Markov kernel. -/
theorem isMarkovKernel_of_localDiffusion (hD : LocalDiffusion c rho law) :
    IsMarkovKernel law := ⟨fun x => ⟨hD.1.1 x⟩⟩

/-- The single-step `L^q → L^∞` estimate for the killed resolvent. -/
theorem eLpNorm_top_kernelIntegral_le
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    {p0 A F s : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hF : 0 < F) (hs : 0 < s)
    (hmass : 0 < ((weightedMeasure rho) U).toReal)
    (hSob : SobolevAssumption c rho U p0 A F)
    {g : Vec d → ℝ} (hg : MemLp g (qExp p0) ((weightedMeasure rho).restrict U)) :
    eLpNorm (kernelIntegral (resolventKernel law U hU.isOpen s hs) g) ∞
        ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal (stampacchiaConstant p0 *
        Real.sqrt (A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p0)) * (1 + F / s))) *
        eLpNorm g (qExp p0) ((weightedMeasure rho).restrict U) := by
  set mu := (weightedMeasure rho).restrict U with hmudef
  set kap := resolventKernel law U hU.isOpen s hs with hkapdef
  have hUb : Bornology.IsBounded U := hU.isBoundedDomain.isBounded
  have hksub : IsSubMarkovKernel kap := resolventKernel_subMarkov law U hU.isOpen s hs
  have hkmu : kap ∘ₘ mu ≤ mu := resolventKernel_subinvariant hD hU.isOpen hUb s hs
  have hq1 : (1 : NNReal) ≤ qExp p0 := (one_lt_qExp hp0).le
  have hq2 : (2 : ℝ≥0∞) ≤ (qExp p0 : ℝ≥0∞) := by
    have : ((2 : NNReal) : ℝ) ≤ ((qExp p0 : NNReal) : ℝ) := by
      rw [coe_qExp hp0]
      exact (two_lt_qReal hp0).le
    have h2 : (2 : NNReal) ≤ qExp p0 := by exact_mod_cast this
    exact_mod_cast h2
  set gg : Vec d → ℝ := fun x => |g x| with hggdef
  have hggq : MemLp gg (qExp p0) mu := by
    simpa only [hggdef, Real.norm_eq_abs] using hg.norm
  have hgg2 : MemLp gg 2 mu := hggq.mono_exponent hq2
  have hgg1 : MemLp gg 1 mu := hggq.mono_exponent (le_trans (by norm_num) hq2)
  have hggint : Integrable gg mu := memLp_one_iff_integrable.mp hgg1
  -- the `H¹₀` representative of the resolvent of `|g|`
  obtain ⟨uH, hueq, hlevel⟩ :=
    exists_killedResolvent_positivePart_lpSq_le hD hU hs (le_trans zero_le_one hA) hF.le hSob hgg2
  set uf : Vec d → ℝ := uH.toH1Function.toFun with hufdef
  -- the resolvent operator and the raw resolvent agree almost everywhere
  have hraw : kernelIntegral kap gg =ᵐ[mu] killedResolvent law U s gg :=
    resolventKernel_integral_ae law U hU.isOpen s hs mu hkmu gg hggint
  have hueq' : uf =ᵐ[mu] killedResolvent law U s gg := hueq
  have hufeq : uf =ᵐ[mu] kernelIntegral kap gg := hueq'.trans hraw.symm
  have hufq : MemLp uf (qExp p0) mu :=
    (memLp_congr_ae hufeq).mpr (MemLp.kernelIntegral hksub hkmu hq1 hggq)
  have hufcontract : eLpNorm uf (qExp p0) mu ≤ eLpNorm gg (qExp p0) mu := by
    rw [eLpNorm_congr_ae hufeq]
    exact eLpNorm_kernelIntegral_le hksub hkmu hq1 hggq
  -- the Stampacchia constant
  set B : ℝ := A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p0)) * (1 + F / s) with hBdef
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hBpos : 0 < B := by
    have h1 : 0 < (1 + F / s) := by positivity
    exact mul_pos (mul_pos hApos (Real.rpow_pos_of_pos hmass _)) h1
  have hstamp := ae_le_of_positive_level_estimates mu hp0 hBpos hufq hggq hufcontract
    (by
      intro k hk
      obtain ⟨v, hvval, hvbound⟩ := hlevel k hk
      have hvfun : (fun x => max (uf x - k) 0) = v.toH1Function.toFun :=
        funext fun x => (hvval x).symm
      have h2 : lpSq rho U p0 v.toH1Function.toFun
          = (eLpNorm (fun x => max (uf x - k) 0) (ENNReal.ofReal p0) mu) ^ 2 := by
        have hvmeas : AEStronglyMeasurable v.toH1Function.toFun mu := by
          rw [← hvfun]
          exact ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
            hufq.aestronglyMeasurable
        rw [hvfun, lpSq]
        have hraw : SubdiffusiveProcess.RawLp.eLpNorm v.toH1Function.toFun
            (ENNReal.ofReal p0)
            ((volume.withDensity (fun x => ENNReal.ofReal (rho x))).restrict U) =
            eLpNorm v.toH1Function.toFun (ENNReal.ofReal p0) mu := by
          simpa only using! SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hvmeas
        rw [hraw]
      have h3 : (∫⁻ x in U, ENNReal.ofReal (|gg x| * v.toH1Function.toFun x)
            ∂(weightedMeasure rho))
          = ∫⁻ x, ENNReal.ofReal (|gg x| * max (uf x - k) 0) ∂mu := by
        rw [hmudef]
        exact lintegral_congr fun x => by rw [hvval x]
      rw [h2, h3] at hvbound
      exact hvbound)
  -- transfer the bound to the resolvent operator
  have hbound : ∀ᵐ x ∂mu, ‖kernelIntegral kap g x‖ₑ ≤
      ENNReal.ofReal (stampacchiaConstant p0 * Real.sqrt B *
        (eLpNorm gg (qExp p0) mu).toReal) := by
    filter_upwards [hstamp, hufeq] with x hx hxeq
    have habs : |kernelIntegral kap g x| ≤ kernelIntegral kap gg x := by
      simpa only [hggdef] using! abs_integral_le_integral_abs (μ := kap x) (f := g)
    have : |kernelIntegral kap g x| ≤ stampacchiaConstant p0 * Real.sqrt B *
        (eLpNorm gg (qExp p0) mu).toReal := le_trans habs (by rw [← hxeq]; exact hx)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal this
  rw [eLpNorm_exponent_top
    (AEStronglyMeasurable.kernelIntegral hg.aestronglyMeasurable hkmu)]
  refine le_trans (eLpNormEssSup_le_of_ae_enorm_bound hbound) ?_
  have hfin : eLpNorm gg (qExp p0) mu ≠ ∞ := hggq.eLpNorm_ne_top
  have hggnorm : eLpNorm gg (qExp p0) mu = eLpNorm g (qExp p0) mu := by
    simp only [hggdef, ← Real.norm_eq_abs]
    exact eLpNorm_norm g hg.aestronglyMeasurable
  rw [ENNReal.ofReal_mul
    (mul_nonneg (stampacchiaConstant_pos p0).le (Real.sqrt_nonneg B)),
    ENNReal.ofReal_toReal hfin, hggnorm]


/-- The iterated raw resolvent agrees almost everywhere with the iterated kernel operator, and
the iterates stay integrable. -/
theorem iterate_killedResolvent_ae
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ}
    (hf : MemLp f 1 ((weightedMeasure rho).restrict U)) (n : ℕ) :
    (killedResolvent law U s)^[n] f
        =ᵐ[(weightedMeasure rho).restrict U]
      (kernelIntegral (resolventKernel law U hU s hs))^[n] f ∧
      MemLp ((kernelIntegral (resolventKernel law U hU s hs))^[n] f) 1
        ((weightedMeasure rho).restrict U) := by
  set mu := (weightedMeasure rho).restrict U with hmudef
  set kap := resolventKernel law U hU s hs with hkapdef
  have hksub : IsSubMarkovKernel kap := resolventKernel_subMarkov law U hU s hs
  have hkmu : kap ∘ₘ mu ≤ mu := resolventKernel_subinvariant hD hU hUb s hs
  induction n with
  | zero => exact ⟨Filter.EventuallyEq.refl _ _, hf⟩
  | succ n ih =>
    obtain ⟨iheq, ihmem⟩ := ih
    have hmemn : MemLp ((killedResolvent law U s)^[n] f) 1 mu :=
      (memLp_congr_ae iheq).mpr ihmem
    have hintn : Integrable ((killedResolvent law U s)^[n] f) mu :=
      memLp_one_iff_integrable.mp hmemn
    have hstep : killedResolvent law U s ((killedResolvent law U s)^[n] f)
        =ᵐ[mu] kernelIntegral kap ((killedResolvent law U s)^[n] f) :=
      (resolventKernel_integral_ae law U hU s hs mu hkmu _ hintn).symm
    have hcongr : kernelIntegral kap ((killedResolvent law U s)^[n] f)
        =ᵐ[mu] kernelIntegral kap ((kernelIntegral kap)^[n] f) :=
      kernelIntegral_congr_ae hkmu iheq
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hstep.trans hcongr
    · rw [Function.iterate_succ_apply']
      exact MemLp.kernelIntegral hksub hkmu (le_refl (1 : NNReal)) ihmem


/-- The exponent-only constant of the ultracontractivity estimate. -/
def ultraConstant (p0 : ℝ) : ℝ := stampacchiaConstant p0 ^ (2 / (1 - 2 / p0))

theorem ultraConstant_pos (p0 : ℝ) : 0 < ultraConstant p0 :=
  Real.rpow_pos_of_pos (stampacchiaConstant_pos p0) _

/-- A fixed power of the killed resolvent is ultracontractive for the normalised measure. -/
theorem iterate_eLpNorm_normalized_le
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A F s : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hF : 0 < F) (hs : 0 < s)
    (hSob : SobolevAssumption c rho U p0 A F)
    (k : ℕ) (hk : qExp p0 ≤ rExp p0 ^ k) {f : Vec d → ℝ}
    (hf : MemLp f 1 (LocalResolventIterationScaling.normalize
      ((weightedMeasure rho).restrict U))) :
    eLpNorm ((kernelIntegral (resolventKernel law U hU.isOpen s hs))^[k + 1] f) ∞
        (LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) ≤
      ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) *
          (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) *
        eLpNorm f 1 (LocalResolventIterationScaling.normalize
          ((weightedMeasure rho).restrict U)) := by
  set mu := (weightedMeasure rho).restrict U with hmudef
  have hmuniv : mu Set.univ = (weightedMeasure rho) U := by
    rw [hmudef, Measure.restrict_apply_univ]
  haveI hfinite : IsFiniteMeasure mu := ⟨by rw [hmuniv]; exact lt_of_le_of_ne le_top hmtop⟩
  have hm0' : mu Set.univ ≠ 0 := by rw [hmuniv]; exact hm0
  have hmtop' : mu Set.univ ≠ ∞ := by rw [hmuniv]; exact hmtop
  set m : ℝ≥0∞ := mu Set.univ with hmdef
  set nu := LocalResolventIterationScaling.normalize mu with hnudef
  haveI : IsProbabilityMeasure nu := isProbabilityMeasure_normalize hm0' hmtop'
  set kap := resolventKernel law U hU.isOpen s hs with hkapdef
  have hUb : Bornology.IsBounded U := hU.isBoundedDomain.isBounded
  have hksub : IsSubMarkovKernel kap := resolventKernel_subMarkov law U hU.isOpen s hs
  have hkmu : kap ∘ₘ mu ≤ mu := resolventKernel_subinvariant hD hU.isOpen hUb s hs
  have hknu : kap ∘ₘ nu ≤ nu := comp_smul_le _ hkmu
  have hrect := resolventKernel_rectangle_symmetry hD hU.isOpen hUb s hs
  have hrectnu : ∀ C D : Set (Vec d), MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, kap x D ∂nu) = ∫⁻ x in D, kap x C ∂nu :=
    rectangle_symmetry_smul _ hrect
  have hmass : 0 < (((weightedMeasure rho) U)).toReal := ENNReal.toReal_pos hm0 hmtop
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hth : 0 < 1 - 2 / p0 := theta_pos hp0
  set B : ℝ := A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p0)) * (1 + F / s) with hBdef
  have hVpos : (0:ℝ) < 1 + F / s := by positivity
  have hBpos : 0 < B := by
    rw [hBdef]
    exact mul_pos (mul_pos hApos (Real.rpow_pos_of_pos hmass _)) hVpos
  set SB : ℝ := stampacchiaConstant p0 * Real.sqrt B with hSBdef
  have hSBpos : 0 < SB := mul_pos (stampacchiaConstant_pos p0) (Real.sqrt_pos.mpr hBpos)
  set qE : ℝ≥0∞ := ((qExp p0 : NNReal) : ℝ≥0∞) with hqEdef
  have hqreal : ((qExp p0 : NNReal) : ℝ) = 2 / (1 - 2 / p0) := coe_qExp hp0
  have hqpos : (0:ℝ) < ((qExp p0 : NNReal) : ℝ) := by rw [hqreal]; positivity
  set t : ℝ := (1 / qE).toReal with htdef
  have htval : t = (((qExp p0 : NNReal) : ℝ))⁻¹ := by
    rw [htdef, hqEdef, one_div, ENNReal.toReal_inv, ENNReal.coe_toReal]
  have ht0 : 0 ≤ t := by rw [htval]; positivity
  have htq : t * ((qExp p0 : NNReal) : ℝ) = 1 := by
    rw [htval]
    field_simp
  have hmpow : m ^ t ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ht0 hmtop'
  set K : ℝ≥0∞ := ENNReal.ofReal SB * m ^ t with hKdef
  have hK : K ≠ ∞ := by
    rw [hKdef]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_ne le_top hmpow)).ne
  have hscale : ∀ g : Vec d → ℝ, eLpNorm g qE mu = m ^ t * eLpNorm g qE nu := by
    intro g
    rw [hnudef, LocalResolventIterationScaling.normalize, eLpNorm_smul_measure_of_ne_zero
      (ENNReal.inv_ne_zero.mpr hmtop') g qE mu, smul_eq_mul, ← mul_assoc,
      ← ENNReal.mul_rpow_of_nonneg _ _ ht0, ENNReal.mul_inv_cancel hm0' hmtop',
      ENNReal.one_rpow, one_mul]
  have hhigh : ∀ g : Vec d → ℝ, MemLp g (qExp p0) nu →
      eLpNorm (kernelIntegral kap g) ∞ nu ≤ K * eLpNorm g (qExp p0) nu := by
    intro g hg
    have hgmu : MemLp g (qExp p0) mu := (memLp_normalize_iff hm0' hmtop' _ g).mp hg
    have hstep := eLpNorm_top_kernelIntegral_le hD hU hp0 hA hF hs hmass hSob hgmu
    rw [eLpNorm_top_normalize hmtop']
    calc
      eLpNorm (kernelIntegral kap g) ∞ mu ≤ ENNReal.ofReal SB * eLpNorm g qE mu := hstep
      _ = ENNReal.ofReal SB * (m ^ t * eLpNorm g qE nu) := by rw [hscale g]
      _ = K * eLpNorm g qE nu := by rw [hKdef, mul_assoc]
  have hiter := iterate_bound hksub hknu hrectnu (qExp p0) (rExp p0) (one_lt_qExp hp0)
    (one_lt_rExp hp0) (qExp_conjugate hp0) k hk hK hhigh hf
  have hKpow : K ^ ((qExp p0 : NNReal) : ℝ) = ENNReal.ofReal (SB ^ (2 / (1 - 2 / p0))) * m := by
    rw [hKdef, ENNReal.mul_rpow_of_nonneg _ _ hqpos.le, ← ENNReal.rpow_mul, htq,
      ENNReal.rpow_one, ← ENNReal.ofReal_rpow_of_pos hSBpos, hqreal]
  have hUC : 0 < stampacchiaConstant p0 ^ (2 / (1 - 2 / p0)) :=
    Real.rpow_pos_of_pos (stampacchiaConstant_pos p0) _
  have hAp : 0 < A ^ ((1 - 2 / p0)⁻¹) := Real.rpow_pos_of_pos hApos _
  have hVp : 0 < (1 + F / s) ^ ((1 - 2 / p0)⁻¹) := Real.rpow_pos_of_pos hVpos _
  have hnonneg : (0:ℝ) ≤ stampacchiaConstant p0 ^ (2 / (1 - 2 / p0)) * A ^ ((1 - 2 / p0)⁻¹) /
      (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹) :=
    le_of_lt (mul_pos (div_pos (mul_pos hUC hAp) hmass) hVp)
  have hconst : ENNReal.ofReal (stampacchiaConstant p0 ^ (2 / (1 - 2 / p0)) *
        A ^ ((1 - 2 / p0)⁻¹) / (((weightedMeasure rho) U).toReal) *
        (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) * ((weightedMeasure rho) U)
      = ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) *
        (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) := by
    rw [show stampacchiaConstant p0 ^ (2 / (1 - 2 / p0)) * A ^ ((1 - 2 / p0)⁻¹) /
          (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)
        = (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) /
          (((weightedMeasure rho) U).toReal) from by
        rw [ultraConstant]; field_simp,
      ENNReal.ofReal_div_of_pos hmass, ENNReal.ofReal_toReal hmtop,
      ENNReal.div_mul_cancel hm0 hmtop]
  refine hiter.trans (mul_le_mul_left ?_ _)
  rw [hKpow, hSBdef, hBdef,
    stampacchia_power_eq (stampacchiaConstant_pos p0).le hApos hmass hVpos hth, hmuniv, hconst]

/-- A fixed power of the killed resolvent maps `L¹` to `L^∞` with the Sobolev constant. -/
theorem iterate_eLpNorm_le
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A F s : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hF : 0 < F) (hs : 0 < s)
    (hSob : SobolevAssumption c rho U p0 A F)
    (k : ℕ) (hk : qExp p0 ≤ rExp p0 ^ k) {f : Vec d → ℝ}
    (hf : MemLp f 1 ((weightedMeasure rho).restrict U)) :
    eLpNorm ((killedResolvent law U s)^[k + 1] f) ∞ ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
          (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) *
        eLpNorm f 1 ((weightedMeasure rho).restrict U) := by
  have hmuniv : ((weightedMeasure rho).restrict U) Set.univ = (weightedMeasure rho) U :=
    Measure.restrict_apply_univ _
  haveI hfinite : IsFiniteMeasure ((weightedMeasure rho).restrict U) :=
    ⟨by rw [hmuniv]; exact lt_of_le_of_ne le_top hmtop⟩
  have hm0' : ((weightedMeasure rho).restrict U) Set.univ ≠ 0 := by rw [hmuniv]; exact hm0
  have hmtop' : ((weightedMeasure rho).restrict U) Set.univ ≠ ∞ := by rw [hmuniv]; exact hmtop
  have hmass : 0 < (((weightedMeasure rho) U)).toReal := ENNReal.toReal_pos hm0 hmtop
  have hUb : Bornology.IsBounded U := hU.isBoundedDomain.isBounded
  have hfnu : MemLp f 1
      (LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) :=
    (memLp_normalize_iff hm0' hmtop' 1 f).mpr hf
  have hstep := iterate_eLpNorm_normalized_le hD hU hm0 hmtop hp0 hA hF hs hSob k hk hfnu
  have hiterae := (iterate_killedResolvent_ae hD hU.isOpen hUb hs hf (k + 1)).1
  have hconst : ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) *
        (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) * ((weightedMeasure rho) U)⁻¹
      = ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
        (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) := by
    rw [show ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) / (((weightedMeasure rho) U).toReal) *
          (1 + F / s) ^ ((1 - 2 / p0)⁻¹)
        = (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) /
          (((weightedMeasure rho) U).toReal) from by field_simp,
      ENNReal.ofReal_div_of_pos hmass, ENNReal.ofReal_toReal hmtop]
    exact (div_eq_mul_inv _ _).symm
  rw [eLpNorm_congr_ae hiterae, ← eLpNorm_top_normalize hmtop']
  refine hstep.trans ?_
  rw [eLpNorm_one_normalize, ← mul_assoc, hmuniv, hconst]

/-- A fixed power of the killed resolvent maps `L¹` to `L^∞`, with the power depending only on the
Sobolev exponent. -/
theorem exists_iterate_eLpNorm_le (p0 : ℝ) (hp0 : 2 < p0) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∃ k : ℕ, N0 = k + 1 ∧ qExp p0 ≤ rExp p0 ^ k := by
  obtain ⟨k, hk⟩ := iteration_count (qExp p0) (rExp p0) (one_lt_rExp hp0)
  exact ⟨k + 1, Nat.succ_pos k, k, rfl, hk⟩

end Diffusion

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
