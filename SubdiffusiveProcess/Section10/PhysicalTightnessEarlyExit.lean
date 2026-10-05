module

public import SubdiffusiveProcess.Section10.PhysicalTightnessVariational
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerPointwise

@[expose] public section

/-!
# Variational cutoff plus local Moser estimate gives every-start early exit

This is the deterministic analytic-to-stochastic step of the paper's §8 proof.
The law is the supplied lifetime law, with its actual coefficient and speed.
The cutoff and subharmonic estimates are explicit analytic inputs. Resolvent
identification is taken only from `LocalDiffusionData` and the exit bound is
proved at every start without nonexplosion or a Feller/FDD attachment premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- The actual killed weak-resolvent clause, a cutoff and a Moser estimate imply
an early-exit bound at every start in the interior set. -/
theorem exit_probability_le_of_cutoff_moser {d : ℕ}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U V W : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hW : IsOpen W) (hWV : W ⊆ V)
    [IsFiniteMeasure (volumeMeasureOn V)]
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c))
    (hc : ∀ᵐ x ∂volume.restrict U, 0 ≤ c x)
    (chi : H10Function U) (hchi01 : ∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1)
    (hchi1 : ∀ x ∈ V, chi.toFun x = 1)
    (Ke Km : ℝ) (hKe : 0 ≤ Ke) (hKm : 0 ≤ Km)
    (henergy : energy c U chi.toH1Function ≤ Ke)
    (hmoser : ∀ w : H1Function V,
      (∀ᵐ x ∂volume.restrict V, 0 ≤ w.toFun x) →
      (∃ Mw : ℝ, ∀ᵐ x ∂volume.restrict V, w.toFun x ≤ Mw) →
      IsWeakSubSolutionOn c V w →
      ∀ᵐ x ∂volume.restrict W,
        ENNReal.ofReal (w.toFun x) ≤ ENNReal.ofReal Km *
          (∫⁻ y in V, ENNReal.ofReal (w.toFun y ^ 2 * rho y)) ^ (1 / 2 : ℝ)) :
    ∀ t : ℝ, 0 < t → ∀ x ∈ W,
      law x {w | LifetimePath.exitTime U w ≤ ENNReal.ofReal t} ≤
        ENNReal.ofReal (4 * (Km * Real.sqrt (t * Ke))) := by
  have : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD.1
  have hrhoCoeff : CoefficientOn U rho := coefficientOn_of_localDiffusion hD.1 hUb
  obtain ⟨hrhoMeas, rhoLo, rhoMax, hrhoLo, hrhoHi⟩ := hrhoCoeff
  have hrho : ∀ᵐ x ∂volume.restrict U, 0 ≤ rho x := hrhoHi.mono fun x hx =>
    (hrhoLo.trans_le hx.1).le
  have hrhoBdd : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ rhoMax := by
    filter_upwards [hrhoHi] with x hx
    rw [abs_of_pos (hrhoLo.trans_le hx.1)]
    exact hx.2
  have hrhoCoeff' : CoefficientOn U rho := ⟨hrhoMeas, rhoLo, rhoMax, hrhoLo, hrhoHi⟩
  have hvolW : (volume.restrict U) ≪ (weightedMeasure rho).restrict U :=
    volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hrhoCoeff'
  have hWvol : ((weightedMeasure rho).restrict U) ≪ volume.restrict U :=
    weightedMeasure_restrict_absolutelyContinuous_volume_restrict hU.measurableSet
  have hchiMeas : AEMeasurable chi.toFun (volume.restrict U) :=
    chi.toH1Function.memL2.aestronglyMeasurable.aemeasurable
  let eta : Vec d → ℝ := fun x => max 0 (min 1 ((AEMeasurable.mk chi.toFun hchiMeas) x))
  have hetaMeas : Measurable eta := measurable_const.max
    (measurable_const.min hchiMeas.measurable_mk)
  have heta0 : ∀ x, 0 ≤ eta x := fun x => le_max_left _ _
  have heta1 : ∀ x, eta x ≤ 1 := fun x => max_le (by norm_num) (min_le_left _ _)
  have hetaAE : eta =ᵐ[volume.restrict U] chi.toFun := by
    filter_upwards [hchiMeas.ae_eq_mk.symm] with x hx
    dsimp only [eta]
    rw [hx, min_eq_right (hchi01 x).2, max_eq_right (hchi01 x).1]
  have hetaAEW : eta =ᵐ[(weightedMeasure rho).restrict U] chi.toFun := hWvol.ae_le hetaAE
  have hchiMem : MemLp chi.toFun 2 ((weightedMeasure rho).restrict U) :=
    memLp_weighted_of_volume_restrict hU.measurableSet hrhoCoeff' chi.toH1Function.memL2
  have hetaMem : MemLp eta 2 ((weightedMeasure rho).restrict U) :=
    (memLp_congr_ae hetaAEW).mpr hchiMem
  intro t ht
  obtain ⟨u, hueq, hu, hu01⟩ := weak_resolvent hD.1 U hU hUb t ht eta hetaMeas
    heta0 heta1 hetaMem
  have huChi : IsMassiveWeakSolutionOn c rho t⁻¹ U u.toH1Function
      (fun x => t⁻¹ * chi.toFun x) :=
    source_ae (hetaAE.mono fun x hx => congrArg (fun z : ℝ => t⁻¹ * z) hx) hu
  have hvar := variational_comparison hEll hc hrho hrhoMeas hrhoBdd ht u chi huChi
  have hresid : (∫ y in U, rho y * (u.toFun y - chi.toFun y) ^ 2) ≤ t * Ke :=
    hvar.trans (mul_le_mul_of_nonneg_left henergy ht.le)
  have hu01vol : ∀ᵐ x ∂volume.restrict U, 0 ≤ u.toFun x ∧ u.toFun x ≤ 1 :=
    hvolW.ae_le hu01
  let uV : H1Function V := u.toH1Function.restrict hV hVU
  let w : H1Function V := H1Function.const 1 - uV
  have hwfun : ∀ x, w.toFun x = 1 - u.toFun x := by
    intro x
    simp only [w, H1Function.sub_toFun, H1Function.const_apply]
    rfl
  have huV01 : ∀ᵐ x ∂volume.restrict V, 0 ≤ uV.toFun x ∧ uV.toFun x ≤ 1 :=
    ae_restrict_of_ae_restrict_of_subset hVU hu01vol
  have hw0 : ∀ᵐ x ∂volume.restrict V, 0 ≤ w.toFun x := by
    filter_upwards [huV01] with x hx
    simp only [w, H1Function.sub_toFun, H1Function.const_apply]
    exact sub_nonneg.mpr hx.2
  have hw1 : ∀ᵐ x ∂volume.restrict V, w.toFun x ≤ 1 := by
    filter_upwards [huV01] with x hx
    simp only [w, H1Function.sub_toFun, H1Function.const_apply]
    linarith only [hx.1]
  have huV := IsMassiveWeakSolutionOn.restrict hV hU hVU huChi
  have hsourceV : (fun x => t⁻¹ * chi.toFun x) =ᵐ[volume.restrict V]
      (fun _ => t⁻¹) := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [hchi1 x hx, mul_one]
  have huVconst := source_ae hsourceV huV
  have hrhoV : ∀ᵐ x ∂volume.restrict V, 0 ≤ rho x :=
    ae_restrict_of_ae_restrict_of_subset hVU hrho
  have hrhoVBdd : ∀ᵐ x ∂volume.restrict V, |rho x| ≤ rhoMax :=
    ae_restrict_of_ae_restrict_of_subset hVU hrhoBdd
  have hrhoVMeas : AEStronglyMeasurable rho (volume.restrict V) :=
    hrhoMeas.mono_measure (Measure.restrict_mono hVU le_rfl)
  have hwsub : IsWeakSubSolutionOn c V w := complement_subsolution
    (inv_nonneg.mpr ht.le) hrhoV hrhoVMeas hrhoVBdd uV huVconst
    (huV01.mono fun x hx => hx.2)
  have hmos := hmoser w hw0 ⟨1, hw1⟩ hwsub
  have hwInt : IntegrableOn (fun x => rho x * w.toFun x ^ 2) V := by
    have h := integrableOn_mass_term hrhoVMeas hrhoVBdd w.memL2 w.memL2
    simpa only [pow_two, mul_assoc] using h
  have hresidInt : IntegrableOn (fun x => rho x * (u.toFun x - chi.toFun x) ^ 2) U := by
    have h := integrableOn_mass_term hrhoMeas hrhoBdd
      (u.toH1Function - chi.toH1Function).memL2 (u.toH1Function - chi.toH1Function).memL2
    simpa only [H1Function.sub_toFun, pow_two, mul_assoc] using h
  have hresid0 : ∀ᵐ x ∂volume.restrict U,
      0 ≤ rho x * (u.toFun x - chi.toFun x) ^ 2 :=
    hrho.mono fun x hx => mul_nonneg hx (sq_nonneg _)
  have hwEq : ∀ᵐ x ∂volume.restrict V,
      rho x * w.toFun x ^ 2 = rho x * (u.toFun x - chi.toFun x) ^ 2 := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [hwfun x, hchi1 x hx]
    ring
  have hwBound : (∫ x in V, rho x * w.toFun x ^ 2) ≤ t * Ke := by
    rw [integral_congr_ae hwEq]
    exact (setIntegral_mono_set hresidInt hresid0
      (Eventually.of_forall fun x hx => hVU hx)).trans hresid
  have hwWeighted : (∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2 * rho x)) ≤
      ENNReal.ofReal (t * Ke) := by
    calc
      (∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2 * rho x)) =
          ENNReal.ofReal (∫ x in V, rho x * w.toFun x ^ 2) :=
        weighted_lintegral (g := fun x => w.toFun x ^ 2) hV.measurableSet hrhoVMeas
          (w.memL2.aestronglyMeasurable.pow 2) hrhoV
          (Eventually.of_forall fun x => sq_nonneg (w.toFun x)) hwInt
      _ ≤ ENNReal.ofReal (t * Ke) := ENNReal.ofReal_le_ofReal hwBound
  have hKnn : 0 ≤ Km * Real.sqrt (t * Ke) := mul_nonneg hKm (Real.sqrt_nonneg _)
  have hmosReal : ∀ᵐ x ∂volume.restrict W, 1 - u.toFun x ≤ Km * Real.sqrt (t * Ke) := by
    filter_upwards [hmos] with x hx
    have h : ENNReal.ofReal (w.toFun x) ≤ ENNReal.ofReal Km *
        ENNReal.ofReal (t * Ke) ^ (1 / 2 : ℝ) := hx.trans
      (mul_le_mul_right (ENNReal.rpow_le_rpow hwWeighted (by norm_num)) _)
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg ht.le hKe) (by norm_num),
      ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul hKm] at h
    rw [hwfun x] at h
    exact (ENNReal.ofReal_le_ofReal_iff hKnn).mp h
  have hueqVol : u.toFun =ᵐ[volume.restrict U] killedResolvent law U t eta :=
    hvolW.ae_le hueq
  have hdefectW : ∀ᵐ x ∂volume.restrict W,
      1 - killedResolvent law U t eta x ≤ Km * Real.sqrt (t * Ke) := by
    filter_upwards [hmosReal, ae_restrict_of_ae_restrict_of_subset (hWV.trans hVU) hueqVol]
      with x hx heq
    rwa [heq] at hx
  have hdefectU : ∀ᵐ x ∂volume.restrict U,
      x ∈ W → 1 - killedResolvent law U t eta x ≤ Km * Real.sqrt (t * Ke) :=
    (ae_restrict_iff' hW.measurableSet).mp (by
      rwa [Measure.restrict_restrict hW.measurableSet, inter_eq_left.mpr (hWV.trans hVU)])
  exact exit_probability_le_of_resolvent_defect_ae hD hU hUb hW (hWV.trans hVU)
    t ht eta hetaMeas heta0 heta1 (Km * Real.sqrt (t * Ke)) hKnn (hWvol.ae_le hdefectU)

end SubdiffusiveProcess.Section10.PhysicalTightness
