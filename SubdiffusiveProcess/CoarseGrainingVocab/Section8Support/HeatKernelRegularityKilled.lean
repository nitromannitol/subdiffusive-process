import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}

/-! ## The killed kernel is carried by the domain -/

/-- A killed path is alive inside `U`, so the killed kernel gives no mass to the
complement of `U`. -/
theorem killedKernel_compl (law : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (t : NNReal) (x : Vec d) : killedKernel law U hU t x Uᶜ = 0 := by
  rw [killedKernel,
    map_restrict_apply law _ _ _ (position_fixed_measurable t) x Uᶜ hU.measurableSet.compl]
  have hempty : (position t ⁻¹' Uᶜ) ∩ {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w} = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun w hw => ?_
    exact hw.1 (position_mem_of_lt_exit U w t hw.2)
  rw [hempty, measure_empty]

/-- The killed kernel of a set is the killed kernel of its trace on `U`. -/
theorem killedKernel_inter (law : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (t : NNReal) (x : Vec d) {B : Set (Vec d)} :
    killedKernel law U hU t x B = killedKernel law U hU t x (B ∩ U) := by
  have hdiff : killedKernel law U hU t x (B \ U) = 0 :=
    measure_mono_null (fun y hy => hy.2) (killedKernel_compl law U hU t x)
  have hadd := measure_inter_add_diff (μ := killedKernel law U hU t x) B hU.measurableSet
  rw [hdiff, add_zero] at hadd
  exact hadd.symm

/-! ## Route 1: absolute continuity from continuity in the starting point -/



theorem killedLawAbsolutelyContinuousOn_of_continuousOn
    (hD : LocalDiffusion c rho law) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hsupp : FullSupportOn ((weightedMeasure rho).restrict U) U)
    (hcont : ∀ t : ℝ, 0 < t → ∀ B : Set (Vec d), MeasurableSet B →
      ContinuousOn (fun x => (killedKernel law U hU (Real.toNNReal t) x B).toReal) U) :
    KilledLawAbsolutelyContinuousOn law rho U := by
  haveI : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  haveI : IsFiniteMeasure ((weightedMeasure rho).restrict U) :=
    isFiniteMeasure_restrict (weightedMeasure_ne_top_of_localDiffusion hD hU hUb)
  intro t ht x hx B hB hBnull
  have hres : ((weightedMeasure rho).restrict U) B = 0 := by
    rwa [Measure.restrict_apply hB]
  have hae : ∀ᵐ y ∂((weightedMeasure rho).restrict U),
      y ∈ U → (killedKernel law U hU (Real.toNNReal t) y B).toReal ≤ 0 := by
    filter_upwards [killedKernel_ae_eq_zero hD hU hUb (Real.toNNReal t) hB hres] with y hy _
    rw [hy]
    simp
  have hle := le_of_ae_le hU hsupp (hcont t ht B hB) hae x hx
  have hzero : (killedKernel law U hU (Real.toNNReal t) x B).toReal = 0 :=
    le_antisymm hle ENNReal.toReal_nonneg
  have hone : killedKernel law U hU (Real.toNNReal t) x B ≤ 1 :=
    (killedKernel_subMarkov law U hU (Real.toNNReal t)).measure_le_one x B
  have : killedKernel law U hU (Real.toNNReal t) x B = 0 :=
    Or.resolve_right (ENNReal.toReal_eq_zero_iff _ |>.mp hzero)
      (ne_top_of_le_ne_top ENNReal.one_ne_top hone)
  rwa [killedKernel_apply_law law hU t x B hB] at this

/-! ## Route 2: the corollary from a resolvent-regularity datum -/



structure KilledHeatKernelDatum (rho : Vec d → ℝ) (law : Kernel (Vec d) (Path d))
    (U : Set (Vec d)) (hU : IsOpen U) where
  /-- Hypothesis (RRK) for the killed form on `L²(U, ρ dx)`. -/
  toDatum : ResolventRegularityDatum ((weightedMeasure rho).restrict U) U
  /-- The datum's semigroup is the killed transition semigroup. -/
  semigroup_eq_killed : ∀ t : ℝ, 0 < t → ∀ f : Vec d → ℝ,
    ∀ hf : MemLp f 2 ((weightedMeasure rho).restrict U),
      (fun x => (toDatum.semigroup t (hf.toLp f)) x)
        =ᵐ[(weightedMeasure rho).restrict U]
          fun x => ∫ y, f y ∂(killedKernel law U hU (Real.toNNReal t) x)
  /-- The killed transition probabilities depend continuously on the starting
  point inside `U`. -/
  continuousOn_killedKernel : ∀ t : ℝ, 0 < t → ∀ B : Set (Vec d), MeasurableSet B →
    ContinuousOn (fun x => (killedKernel law U hU (Real.toNNReal t) x B).toReal) U

namespace KilledHeatKernelDatum

variable {hU : IsOpen U} (K : KilledHeatKernelDatum rho law U hU)

/-- The killed kernel is a finite measure at every starting point. -/
instance isFiniteMeasure_killedKernel [IsMarkovKernel law] (t : NNReal) (x : Vec d) :
    IsFiniteMeasure (killedKernel law U hU t x) :=
  ⟨lt_of_le_of_lt ((killedKernel_subMarkov law U hU t).measure_le_one x univ) ENNReal.one_lt_top⟩

/-- **The killed transition mass is the integral of the kernel**, at *every*
starting point of `U`.  The almost-everywhere identity comes from
`semigroup_eq_killed` and the abstract lemma; continuity and full support raise
it to every point. -/
theorem killedKernel_toReal_eq [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U)
    {B : Set (Vec d)} (hB : MeasurableSet B) :
    (killedKernel law U hU (Real.toNNReal t) x B).toReal
      = ∫ z in B, K.toDatum.kernel t x z ∂((weightedMeasure rho).restrict U) := by
  set mu := (weightedMeasure rho).restrict U with hmu
  set f : Vec d → ℝ := B.indicator (fun _ => (1 : ℝ)) with hf
  have hmem : MemLp f 2 mu := (memLp_const (1 : ℝ)).indicator hB
  -- the two continuous functions of the starting point
  have hcont1 : ContinuousOn
      (fun y => (killedKernel law U hU (Real.toNNReal t) y B).toReal) U :=
    K.continuousOn_killedKernel t ht B hB
  have hcont2 : ContinuousOn (K.toDatum.pairing t (hmem.toLp f)) U :=
    K.toDatum.continuousOn_pairing t (hmem.toLp f)
  -- they agree almost everywhere
  have hint : ∀ y : Vec d, (∫ z, f z ∂(killedKernel law U hU (Real.toNNReal t) y))
      = (killedKernel law U hU (Real.toNNReal t) y B).toReal := by
    intro y
    rw [hf, integral_indicator_const, smul_eq_mul, mul_one]
    · rfl
    · exact hB
  have haegoal : ∀ᵐ y ∂mu, y ∈ U →
      (killedKernel law U hU (Real.toNNReal t) y B).toReal
        = K.toDatum.pairing t (hmem.toLp f) y := by
    filter_upwards [K.semigroup_eq_killed t ht f hmem,
      K.toDatum.pairing_ae_eq ht (hmem.toLp f)] with y hy hy' _
    rw [← hint y, ← hy, hy']
  have hEq := eqOn_of_ae_eq_of_fullSupport K.toDatum.isOpen_carrier K.toDatum.fullSupport
    hcont1 hcont2 haegoal hx
  rw [hEq, K.toDatum.pairing_eq_integral ht (hmem.toLp f) x]
  have hcoe : (fun z => K.toDatum.kernel t x z * (hmem.toLp f) z)
      =ᵐ[mu] fun z => K.toDatum.kernel t x z * f z := by
    filter_upwards [hmem.coeFn_toLp] with z hz
    rw [hz]
  rw [integral_congr_ae hcoe, hf]
  have hfun : (fun z => K.toDatum.kernel t x z * B.indicator (fun _ => (1 : ℝ)) z)
      = B.indicator (fun z => K.toDatum.kernel t x z) := by
    funext z
    by_cases hz : z ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [hfun, integral_indicator hB]



theorem killedKernel_eq_setLIntegral [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U)
    {B : Set (Vec d)} (hB : MeasurableSet B) :
    killedKernel law U hU (Real.toNNReal t) x B
      = ∫⁻ y in B ∩ U, ENNReal.ofReal (K.toDatum.kernel t x y) ∂(weightedMeasure rho) := by
  have hBU : MeasurableSet (B ∩ U) := hB.inter hU.measurableSet
  have hfin : killedKernel law U hU (Real.toNNReal t) x (B ∩ U) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((killedKernel_subMarkov law U hU (Real.toNNReal t)).measure_le_one x (B ∩ U))
  have hres : ((weightedMeasure rho).restrict U).restrict (B ∩ U)
      = (weightedMeasure rho).restrict (B ∩ U) := by
    rw [Measure.restrict_restrict hBU]
    congr 1
    rw [Set.inter_assoc, Set.inter_self]
  have htoReal : (killedKernel law U hU (Real.toNNReal t) x (B ∩ U)).toReal
      = ∫ z in B ∩ U, K.toDatum.kernel t x z ∂(weightedMeasure rho) := by
    rw [K.killedKernel_toReal_eq ht hx hBU]
    show (∫ z, K.toDatum.kernel t x z ∂(((weightedMeasure rho).restrict U).restrict (B ∩ U)))
      = ∫ z, K.toDatum.kernel t x z ∂((weightedMeasure rho).restrict (B ∩ U))
    rw [hres]
  have hnn : ∀ᵐ z ∂((weightedMeasure rho).restrict (B ∩ U)), 0 ≤ K.toDatum.kernel t x z := by
    rw [ae_restrict_iff' hBU]
    filter_upwards with z hz
    exact K.toDatum.kernel_nonneg ht hx hz.2
  have hintOn : IntegrableOn (fun z => K.toDatum.kernel t x z) (B ∩ U)
      (weightedMeasure rho) := by
    have hL2 : IntegrableOn (fun z => K.toDatum.kernel t x z) (B ∩ U)
        ((weightedMeasure rho).restrict U) := by
      refine (K.toDatum.integrableOn_resolvent_sq (t := t) x (s := B ∩ U)
        (measure_ne_top ((weightedMeasure rho).restrict U) (B ∩ U))).congr ?_
      filter_upwards [ae_restrict_of_ae (K.toDatum.kernel_ae_eq ht x)] with z hz
      exact hz
    have hL2' : Integrable (fun z => K.toDatum.kernel t x z)
        (((weightedMeasure rho).restrict U).restrict (B ∩ U)) := hL2
    rwa [hres] at hL2'
  rw [killedKernel_inter law U hU _ x, ← ENNReal.ofReal_toReal hfin, htoReal,
    ofReal_integral_eq_lintegral_ofReal hintOn hnn]

/-! ### The killed density -/

/-- **The killed transition density**: the abstract heat kernel of the datum,
extended by zero off `U × U` so that it is globally measurable, as
`IsKilledDensity` requires. -/
def density (t : ℝ) (x y : Vec d) : ℝ :=
  (U ×ˢ U).indicator (fun z : Vec d × Vec d => K.toDatum.kernel t z.1 z.2) (x, y)

theorem density_eq {t : ℝ} {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    K.density t x y = K.toDatum.kernel t x y :=
  Set.indicator_of_mem (Set.mk_mem_prod hx hy) _

theorem measurable_uncurry_density (t : ℝ) : Measurable (Function.uncurry (K.density t)) := by
  classical
  have hmeas : MeasurableSet (U ×ˢ U) := hU.measurableSet.prod hU.measurableSet
  have hpw := ContinuousOn.measurable_piecewise (K.toDatum.continuousOn_kernel_pair t)
    (continuous_zero.continuousOn (s := (U ×ˢ U)ᶜ)) hmeas
  rw [Set.piecewise_eq_indicator] at hpw
  exact hpw

/-- **`c.diffusion.heat.kernels` for the part form**: the killed law has the
datum's heat kernel as its transition density with respect to the weighted
measure, at **every** starting point of `U`. -/
theorem isKilledDensity_density [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] :
    IsKilledDensity law rho U K.density := by
  refine ⟨fun t _ => K.measurable_uncurry_density t, fun t ht x hx y hy => ?_,
    fun t ht x hx B hB => ?_⟩
  · rw [K.density_eq hx hy]
    exact K.toDatum.kernel_nonneg ht hx hy
  · rw [← killedKernel_apply_law law hU t x B hB, K.killedKernel_eq_setLIntegral ht hx hB]
    refine setLIntegral_congr_fun (hB.inter hU.measurableSet) (fun y hy => ?_)
    rw [K.density_eq hx hy.2]



theorem continuousOn_density :
    ContinuousOn (fun z : ℝ × Vec d × Vec d => K.density z.1 z.2.1 z.2.2)
      (Set.Ioi 0 ×ˢ U ×ˢ U) :=
  K.toDatum.continuousOn_kernel.congr fun _ hz => K.density_eq hz.2.1 hz.2.2

/-- **The killed density is symmetric.** -/
theorem density_symm {t : ℝ} {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    K.density t x y = K.density t y x := by
  rw [K.density_eq hx hy, K.density_eq hy hx, K.toDatum.kernel_symm]



theorem lintegral_density_le_one [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    (∫⁻ z in U, ENNReal.ofReal (K.density t x z) ∂(weightedMeasure rho)) ≤ 1 := by
  refine le_trans (le_of_eq ?_) (K.toDatum.lintegral_kernel_le_one ht hx)
  refine setLIntegral_congr_fun hU.measurableSet (fun z hz => ?_)
  rw [K.density_eq hx hz]



theorem density_chapmanKolmogorov [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    (∫ z in U, K.density t x z * K.density u z y ∂(weightedMeasure rho))
      = K.density (t + u) x y := by
  rw [K.density_eq hx hy, ← K.toDatum.chapmanKolmogorov ht hu x y]
  refine setIntegral_congr_ae hU.measurableSet (Filter.Eventually.of_forall fun z hz => ?_)
  rw [K.density_eq hx hz, K.density_eq hz hy]

include K in


theorem hasContinuousKilledDensityOn [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] :
    HasContinuousKilledDensityOn rho law U :=
  ⟨K.density, K.isKilledDensity_density, K.continuousOn_density⟩

include K in
/-- **`KilledLawAbsolutelyContinuousOn` is discharged**: by P-389's
`exists_isKilledDensity_iff` this is equivalent to the existence of a killed
density, and `isKilledDensity_density` supplies one. -/
theorem killedLawAbsolutelyContinuousOn [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] :
    KilledLawAbsolutelyContinuousOn law rho U :=
  killedLawAbsolutelyContinuousOn_of_isKilledDensity K.isKilledDensity_density

end KilledHeatKernelDatum

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled
