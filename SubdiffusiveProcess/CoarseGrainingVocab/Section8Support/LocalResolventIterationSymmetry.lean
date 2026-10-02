import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationLevelEnergy
/-!
# Reciprocity of the local killed resolvent

Cross-testing the H10 representatives supplied by LocalDiffusion gives the symmetric mass pairing.
Local coefficient bounds transport the representatives and L2 integrability between volume and the
weighted measure, yielding reciprocity for the raw killed resolvent and integrable pairings.
-/

open MeasureTheory Homogenization Set ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
/-- A constant factor in the forcing term factors out of the weighted mass integral. -/
theorem integral_mass_scaled_forcing {d : ℕ} (U : Set (Vec d)) (rho f v : Vec d → ℝ) (a : ℝ) : (∫ x in U, rho x * (a*f x) * v x) = a * ∫ x in U, rho x * f x * v x := by
  have h : ∀ x : Vec d, rho x * (a * f x) * v x = a * (rho x * f x * v x) := by
    intro x; ring
  simp only [h, integral_const_mul]

/-- The mass and scalar diffusion energy pairings are symmetric. -/
theorem mass_and_energy_pairing_comm {d : ℕ} (U : Set (Vec d)) (rho c u v : Vec d → ℝ) (du dv : Vec d → Vec d) : ((∫ x in U, rho x * u x * v x) = ∫ x in U, rho x * v x * u x) ∧ ((∫ x in U, vecDot (c x • du x) (dv x)) = ∫ x in U, vecDot (c x • dv x) (du x)) := by
  constructor
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [vecDot_smul_left, vecDot_smul_left, vecDot_comm]

/-- Integration against the restricted weighted measure equals the density-weighted volume integral. -/
theorem integral_weightedMeasure_restrict_eq {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (rho f : Vec d → ℝ) (hr : CoefficientOn U rho) : (∫ x, f x ∂(weightedMeasure rho).restrict U) = ∫ x in U, rho x * f x := by
  obtain ⟨lo, hi, hlo, hb⟩ := hr.2
  rw [weightedMeasure, restrict_withDensity hU,
    integral_withDensity_eq_integral_toReal_smul₀ hr.1.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  filter_upwards [hb] with x hx
  rw [ENNReal.toReal_ofReal (hlo.le.trans hx.1), smul_eq_mul]

/-- A local upper density bound transports every volume Lp function to the weighted measure. -/
theorem memLp_weighted_of_volume_restrict {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) {rho f : Vec d → ℝ} (hr : CoefficientOn U rho) {p : ENNReal} (hf : MemLp f p (volume.restrict U)) : MemLp f p ((weightedMeasure rho).restrict U) := by
  obtain ⟨_, lo, hi, hlo, hb⟩ := hr
  exact hf.of_measure_le_smul ENNReal.ofReal_ne_top
    (weightedMeasure_restrict_le_smul_volume_restrict hU hi (hb.mono fun _ hx => hx.2))

/-- The product of two real L2 functions is integrable. -/
theorem integrable_mul_of_memLp_two {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => f x*g x) μ := by
  exact hf.integrable_mul hg

/-- Testing two normalized weak massive solutions against each other gives reciprocity. -/
theorem massiveWeakSolution_mass_pairing_eq {d : ℕ} {U : Set (Vec d)}
    {c rho f g : Vec d → ℝ} {s : ℝ} (hs : 0 < s)
    {u v : H10Function U}
    (hu : IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function (fun x => s⁻¹ * f x))
    (hv : IsMassiveWeakSolutionOn c rho s⁻¹ U v.toH1Function (fun x => s⁻¹ * g x)) :
    (∫ x in U, rho x * f x * v.toH1Function.toFun x) =
      ∫ x in U, rho x * g x * u.toH1Function.toFun x := by
  have hsym := mass_and_energy_pairing_comm U rho c u.toH1Function.toFun v.toH1Function.toFun
    u.toH1Function.grad v.toH1Function.grad
  have h1 := hu v
  have h2 := hv u
  rw [integral_mass_scaled_forcing] at h1 h2
  rw [← hsym.1, ← hsym.2] at h2
  exact mul_left_cancel₀ (inv_ne_zero hs.ne') (h1.symm.trans h2)

/-- The raw killed resolvent of L2 data is in L2 for the restricted weighted measure. -/
theorem memLp_killedResolvent {d : ℕ} {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} (hD : LocalDiffusion c rho law)
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ}
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    MemLp (killedResolvent law U s f) 2 ((weightedMeasure rho).restrict U) := by
  have hr : CoefficientOn U rho := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).2
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU hUb s hs f hf
  exact (memLp_congr_ae hueq).mp (memLp_weighted_of_volume_restrict hU.measurableSet hr u.toH1Function.memL2)

/-- The product of L2 data with the killed resolvent of L2 data is integrable. -/
theorem integrable_mul_killedResolvent {d : ℕ} {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} (hD : LocalDiffusion c rho law)
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {s : ℝ} (hs : 0 < s) {f g : Vec d → ℝ}
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U))
    (hg : MemLp g 2 ((weightedMeasure rho).restrict U)) :
    Integrable (fun x => f x * killedResolvent law U s g x)
      ((weightedMeasure rho).restrict U) := by
  exact hf.integrable_mul (memLp_killedResolvent hD hU hUb hs hg)

/-- The raw killed resolvent has symmetric density-weighted volume pairings on bounded open sets. -/
theorem killedResolvent_mass_pairing_eq {d : ℕ} {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} (hD : LocalDiffusion c rho law)
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {s : ℝ} (hs : 0 < s) {f g : Vec d → ℝ}
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U))
    (hg : MemLp g 2 ((weightedMeasure rho).restrict U)) :
    (∫ x in U, rho x * f x * killedResolvent law U s g x) =
      ∫ x in U, rho x * g x * killedResolvent law U s f x := by
  have hr : CoefficientOn U rho := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).2
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU hUb s hs f hf
  obtain ⟨v, hveq, hv⟩ := hD.2.2 U hU hUb s hs g hg
  have hAc := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hr
  have huv := hueq.filter_mono hAc.ae_le
  have hvv := hveq.filter_mono hAc.ae_le
  calc
    _ = ∫ x in U, rho x * f x * v.toH1Function.toFun x := by
      apply integral_congr_ae
      exact hvv.mono fun x hx => by dsimp only; rw [hx]
    _ = ∫ x in U, rho x * g x * u.toH1Function.toFun x :=
      massiveWeakSolution_mass_pairing_eq hs hu hv
    _ = _ := by
      apply integral_congr_ae
      exact huv.mono fun x hx => by dsimp only; rw [hx]

/-- The raw killed resolvent has symmetric pairings in the restricted weighted measure. -/
theorem killedResolvent_pairing_eq {d : ℕ} {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} (hD : LocalDiffusion c rho law)
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {s : ℝ} (hs : 0 < s) {f g : Vec d → ℝ}
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U))
    (hg : MemLp g 2 ((weightedMeasure rho).restrict U)) :
    (∫ x, f x * killedResolvent law U s g x ∂(weightedMeasure rho).restrict U) =
      ∫ x, g x * killedResolvent law U s f x ∂(weightedMeasure rho).restrict U := by
  have hr : CoefficientOn U rho := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).2
  rw [integral_weightedMeasure_restrict_eq hU.measurableSet rho _ hr, integral_weightedMeasure_restrict_eq hU.measurableSet rho _ hr]
  simpa only [mul_assoc] using killedResolvent_mass_pairing_eq hD hU hUb hs hf hg

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
