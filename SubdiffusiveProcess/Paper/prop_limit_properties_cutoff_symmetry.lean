module

public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.killed_generator_normalization
public import SubdiffusiveProcess.MultiplicativeChaos.TimeMarginal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKilledSymmetry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section10.WholeSpaceKilledDensity
public import SubdiffusiveProcess.Model.LifetimeProcess

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section10
open SubdiffusiveProcess.Model.LifetimeProcess

theorem aux_prop_limit_properties_cutoff_symmetry_killedKernel_mono
    {d : ℕ} {law : Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d)}
    {U V : Set (SpatialCoordinates d)} (hUV : U ⊆ V)
    (hU : IsOpen U) (hV : IsOpen V) (t : ℝ≥0)
    (x : SpatialCoordinates d) (B : Set (SpatialCoordinates d))
    (hB : MeasurableSet B) :
    killedKernel law U hU t x B ≤ killedKernel law V hV t x B := by
  rw [killed_apply law U hU t x B hB, killed_apply law V hV t x B hB]
  exact measure_mono fun w hw => ⟨hw.1, hw.2.trans_le (exitTime_mono_set hUV w)⟩

theorem aux_prop_limit_properties_cutoff_symmetry_killedKernel_global_rectangle
    {d : ℕ} {c rho : SpatialCoordinates d → ℝ}
    {law : Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    (C D : Set (SpatialCoordinates d)) (hC : MeasurableSet C)
    (hDset : MeasurableSet D) (t : ℝ≥0) :
    (∫⁻ x in C, killedKernel law Set.univ isOpen_univ t x D
        ∂weightedMeasure rho) =
      ∫⁻ x in D, killedKernel law Set.univ isOpen_univ t x C
        ∂weightedMeasure rho := by
  let μ : Measure (SpatialCoordinates d) := weightedMeasure rho
  let U : ℕ → Set (SpatialCoordinates d) := ballFamily d
  let K : ℕ → Kernel (SpatialCoordinates d) (SpatialCoordinates d) :=
    fun j => killedKernel law (U j) (isOpen_ballFamily j) t
  have hUmono : Monotone U := by
    exact monotone_ballFamily
  have hrect : ∀ j,
      (∫⁻ x in C ∩ U j, K j x D ∂(μ.restrict (U j))) =
        ∫⁻ x in D, K j x (C ∩ U j) ∂(μ.restrict (U j)) := by
    intro j
    let : IsFiniteMeasure (μ.restrict (U j)) :=
      isFiniteMeasure_restrict
        (weightedMeasure_ne_top_of_localDiffusion hD
          (isOpen_ballFamily j) (isBounded_ballFamily j))
    exact killedKernel_rectangle_symmetry hD (isOpen_ballFamily j)
      (isBounded_ballFamily j) t (C ∩ U j) D
      (hC.inter (isOpen_ballFamily j).measurableSet) hDset
  have hKinter : ∀ (j : ℕ) (x : SpatialCoordinates d),
      K j x (C ∩ U j) = K j x C := by
    intro j x
    rw [killed_apply law (U j) (isOpen_ballFamily j) t x (C ∩ U j)
      (hC.inter (isOpen_ballFamily j).measurableSet),
      killed_apply law (U j) (isOpen_ballFamily j) t x C hC]
    congr 1
    ext w
    constructor
    · intro hw
      exact ⟨hw.1.1, hw.2⟩
    · intro hw
      exact ⟨⟨hw.1, position_mem_of_lt_exit (U j) w t hw.2⟩, hw.2⟩
  have hKmono : ∀ i j (hij : i ≤ j) (x : SpatialCoordinates d)
      (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B),
      K i x B ≤ K j x B := by
    intro i j hij x B hB
    exact aux_prop_limit_properties_cutoff_symmetry_killedKernel_mono
      (hUmono hij) (isOpen_ballFamily i) (isOpen_ballFamily j) t x B hB
  let a : ℕ → SpatialCoordinates d → ℝ≥0∞ := fun j x =>
    (C ∩ U j).indicator (fun z => K j z D) x
  let b : ℕ → SpatialCoordinates d → ℝ≥0∞ := fun j x =>
    (U j).indicator (fun z => K j z C) x
  have ha_meas : ∀ j, Measurable (a j) := by
    intro j
    exact (K j).measurable_coe hDset |>.indicator
      (hC.inter (isOpen_ballFamily j).measurableSet)
  have hb_meas : ∀ j, Measurable (b j) := by
    intro j
    exact (K j).measurable_coe hC |>.indicator (isOpen_ballFamily j).measurableSet
  have ha_mono : Monotone a := by
    intro i j hij x
    change (C ∩ U i).indicator (fun z => K i z D) x ≤
      (C ∩ U j).indicator (fun z => K j z D) x
    by_cases hxC : x ∈ C
    · by_cases hxi : x ∈ U i
      · have hxj : x ∈ U j := hUmono hij hxi
        rw [Set.indicator_of_mem (Set.mem_inter hxC hxi),
          Set.indicator_of_mem (Set.mem_inter hxC hxj)]
        exact hKmono i j hij x D hDset
      · rw [Set.indicator_of_notMem (fun hx => hxi hx.2)]
        exact (zero_le)
    · rw [Set.indicator_of_notMem (fun hx => hxC hx.1),
        Set.indicator_of_notMem (fun hx => hxC hx.1)]
  have hb_mono : Monotone b := by
    intro i j hij x
    change (U i).indicator (fun z => K i z C) x ≤
      (U j).indicator (fun z => K j z C) x
    by_cases hxi : x ∈ U i
    · have hxj : x ∈ U j := hUmono hij hxi
      rw [Set.indicator_of_mem hxi, Set.indicator_of_mem hxj]
      exact hKmono i j hij x C hC
    · rw [Set.indicator_of_notMem hxi]
      exact zero_le
  have hmass (E : ℕ → Set (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (hEmono : Monotone E) (ν : Measure (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d)) :
      ν (⋃ j, E j) = ⨆ j, ν (E j) := by
    exact tendsto_nhds_unique (tendsto_measure_iUnion_atTop hEmono)
      (tendsto_atTop_iSup fun i j hij => measure_mono (hEmono hij))
  have hrow : ∀ x ∈ C,
      (⨆ j, a j x) = killedKernel law Set.univ isOpen_univ t x D := by
    intro x hxC
    let E : ℕ → Set (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d) :=
      fun j => {w | position t w ∈ D ∧ (t : ENNReal) < LifetimePath.exitTime (U j) w}
    have hEmono : Monotone E := by
      intro i j hij w hw
      exact ⟨hw.1, hw.2.trans_le (exitTime_mono_set (hUmono hij) w)⟩
    have hEunion : ⋃ j, E j =
        {w | position t w ∈ D ∧ (t : ENNReal) < LifetimePath.exitTime Set.univ w} := by
      ext w
      simp only [E, Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨hj.1, hj.2.trans_le (exitTime_mono_set (Set.subset_univ _) w)⟩
      · rintro ⟨hwB, hwT⟩
        rw [exitTime_univ_eq_lifetime,
          ← iSup_exitTime_eq_lifetime absorbsBounded_ballFamily w, lt_iSup_iff] at hwT
        obtain ⟨j, hj⟩ := hwT
        exact ⟨j, hwB, hj⟩
    have hmassE : law x (⋃ j, E j) = ⨆ j, law x (E j) :=
      hmass E hEmono (law x)
    obtain ⟨j0, hj0⟩ := absorbsBounded_ballFamily (d := d) {x}
      (Set.finite_singleton x).isBounded
    have hxj : ∀ j, j0 ≤ j → x ∈ U j := by
      intro j hj
      exact hUmono hj (hj0 rfl)
    have htail : ∀ j, j0 ≤ j → a j x = law x (E j) := by
      intro j hj
      dsimp [a]
      rw [Set.indicator_of_mem (Set.mem_inter hxC (hxj j hj)),
        killed_apply law (U j) (isOpen_ballFamily j) t x D hDset]
    rw [killed_apply law Set.univ isOpen_univ t x D hDset, ← hEunion, hmassE]
    exact iSup_eq_iSup_of_eventually_eq (f := fun j => a j x)
      (g := fun j => law x (E j)) (fun i j hij => ha_mono hij x)
      (fun i j hij => measure_mono (hEmono hij)) htail
  have hrow' : ∀ x, (⨆ j, b j x) = killedKernel law Set.univ isOpen_univ t x C := by
    intro x
    let E : ℕ → Set (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d) :=
      fun j => {w | position t w ∈ C ∧ (t : ENNReal) < LifetimePath.exitTime (U j) w}
    have hEmono : Monotone E := by
      intro i j hij w hw
      exact ⟨hw.1, hw.2.trans_le (exitTime_mono_set (hUmono hij) w)⟩
    have hEunion : ⋃ j, E j =
        {w | position t w ∈ C ∧ (t : ENNReal) < LifetimePath.exitTime Set.univ w} := by
      ext w
      simp only [E, Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨hj.1, hj.2.trans_le (exitTime_mono_set (Set.subset_univ _) w)⟩
      · rintro ⟨hwC, hwT⟩
        rw [exitTime_univ_eq_lifetime,
          ← iSup_exitTime_eq_lifetime absorbsBounded_ballFamily w, lt_iSup_iff] at hwT
        obtain ⟨j, hj⟩ := hwT
        exact ⟨j, hwC, hj⟩
    have hmassE : law x (⋃ j, E j) = ⨆ j, law x (E j) :=
      hmass E hEmono (law x)
    obtain ⟨j0, hj0⟩ := absorbsBounded_ballFamily (d := d) {x}
      (Set.finite_singleton x).isBounded
    have hxj : ∀ j, j0 ≤ j → x ∈ U j := by
      intro j hj
      exact hUmono hj (hj0 rfl)
    have htail : ∀ j, j0 ≤ j → b j x = law x (E j) := by
      intro j hj
      dsimp [b]
      rw [Set.indicator_of_mem (hxj j hj),
        killed_apply law (U j) (isOpen_ballFamily j) t x C hC]
    rw [killed_apply law Set.univ isOpen_univ t x C hC, ← hEunion, hmassE]
    exact iSup_eq_iSup_of_eventually_eq (f := fun j => b j x)
      (g := fun j => law x (E j)) (fun i j hij => hb_mono hij x)
      (fun i j hij => measure_mono (hEmono hij)) htail
  have hleft : ∀ j,
      (∫⁻ x in C, a j x ∂μ) = ∫⁻ x in C ∩ U j, K j x D ∂(μ.restrict (U j)) := by
    intro j
    rw [show a j = (C ∩ U j).indicator (fun x => K j x D) from rfl,
      lintegral_indicator (hC.inter (isOpen_ballFamily j).measurableSet)]
    rw [MeasureTheory.Measure.restrict_restrict
      (hC.inter (isOpen_ballFamily j).measurableSet),
      MeasureTheory.Measure.restrict_restrict
        (hC.inter (isOpen_ballFamily j).measurableSet)]
    have hset : (C ∩ ballFamily d j) ∩ C =
        (C ∩ ballFamily d j) ∩ U j := by
      simp [U, Set.inter_left_comm, Set.inter_comm]
    rw [hset]
  have hright : ∀ j,
      (∫⁻ x in D, b j x ∂μ) = ∫⁻ x in D, K j x (C ∩ U j) ∂(μ.restrict (U j)) := by
    intro j
    rw [show b j = (U j).indicator (fun x => K j x C) from rfl,
      lintegral_indicator (isOpen_ballFamily j).measurableSet]
    rw [MeasureTheory.Measure.restrict_restrict
      (isOpen_ballFamily j).measurableSet,
      MeasureTheory.Measure.restrict_restrict hDset]
    simp [U, Set.inter_comm]
    exact (lintegral_congr fun x => (hKinter j x).symm)
  calc
    (∫⁻ x in C, killedKernel law Set.univ isOpen_univ t x D ∂μ) =
        ∫⁻ x in C, (⨆ j, a j x) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hC] with x hx
          exact (hrow x hx).symm
    _ = ⨆ j, ∫⁻ x in C, a j x ∂μ :=
      lintegral_iSup ha_meas (fun i j hij x => ha_mono hij x)
    _ = ⨆ j, ∫⁻ x in C ∩ U j, K j x D ∂(μ.restrict (U j)) :=
      iSup_congr hleft
    _ = ⨆ j, ∫⁻ x in D, K j x (C ∩ U j) ∂(μ.restrict (U j)) :=
      iSup_congr hrect
    _ = ⨆ j, ∫⁻ x in D, b j x ∂μ :=
      iSup_congr (fun j => (hright j).symm)
    _ = ∫⁻ x in D, (⨆ j, b j x) ∂μ :=
      (lintegral_iSup hb_meas (fun i j hij x => hb_mono hij x)).symm
    _ = ∫⁻ x in D, killedKernel law Set.univ isOpen_univ t x C ∂μ := by
      apply lintegral_congr
      exact hrow'

theorem aux_prop_limit_properties_cutoff_symmetry_rectangle_to_measurable
    {d : ℕ} {μ : Measure (SpatialCoordinates d)}
    {κ : Kernel (SpatialCoordinates d) (SpatialCoordinates d)}
    (hsub : IsSubMarkovKernel κ)
    (hrect : ∀ C D : Set (SpatialCoordinates d), MeasurableSet C →
      MeasurableSet D →
      (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ)
    (U : ℕ → Set (SpatialCoordinates d))
    (hUmeas : ∀ j, MeasurableSet (U j))
    (hUcover : ⋃ j, U j = Set.univ)
    (hUfin : ∀ j, μ (U j) ≠ ∞)
    [SigmaFinite μ] :
    ∀ f g : SpatialCoordinates d → ℝ≥0∞, Measurable f → Measurable g →
      (∫⁻ x, f x * (∫⁻ y, g y ∂κ x) ∂μ) =
        ∫⁻ x, g x * (∫⁻ y, f y ∂κ x) ∂μ := by
  let : IsFiniteKernel κ := hsub.isFiniteKernel
  intro f g hf hg
  let ν : Measure (SpatialCoordinates d × SpatialCoordinates d) := μ.compProd κ
  have hν : ν = Measure.map Prod.swap ν := by
    apply Measure.ext_of_generateFrom_of_iUnion
      (Set.image2 (fun A B : Set (SpatialCoordinates d) => A ×ˢ B)
        {A | MeasurableSet A} {B | MeasurableSet B})
      (fun j => U j ×ˢ (Set.univ : Set (SpatialCoordinates d)))
      generateFrom_prod.symm isPiSystem_prod
    · ext z
      constructor
      · intro hz
        exact Set.mem_univ z
      · intro hz
        have hz' : z.1 ∈ ⋃ j, U j := by
          rw [hUcover]
          exact Set.mem_univ _
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hz'
        exact Set.mem_iUnion.2 ⟨j, ⟨hj, Set.mem_univ _⟩⟩
    · intro j
      refine ⟨U j, hUmeas j, Set.univ, ?_, rfl⟩
      change MeasurableSet (Set.univ : Set (SpatialCoordinates d))
      exact MeasurableSet.univ
    · intro j
      rw [Measure.compProd_apply_prod (hUmeas j) MeasurableSet.univ]
      refine ne_top_of_le_ne_top (hUfin j) ?_
      calc
        (∫⁻ x in U j, κ x Set.univ ∂μ) ≤
            ∫⁻ x in U j, (1 : ℝ≥0∞) ∂μ :=
          lintegral_mono fun x => hsub.measure_le_one x Set.univ
        _ = μ (U j) := by simp
    · rintro S ⟨A, hA, B, hB, rfl⟩
      change MeasurableSet A at hA
      change MeasurableSet B at hB
      rw [Measure.compProd_apply_prod hA hB,
        Measure.map_apply measurable_swap (hA.prod hB)]
      have hpre : Prod.swap ⁻¹' (A ×ˢ B) = B ×ˢ A := by
        ext z
        change (z.2 ∈ A ∧ z.1 ∈ B) ↔ (z.1 ∈ B ∧ z.2 ∈ A)
        exact and_comm
      rw [hpre, Measure.compProd_apply_prod hB hA]
      exact hrect A B hA hB
  let F : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ :=
    fun z => f z.1 * g z.2
  let G : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ :=
    fun z => g z.1 * f z.2
  have hF : Measurable F :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hG : Measurable G :=
    (hg.comp measurable_fst).mul (hf.comp measurable_snd)
  calc
    (∫⁻ x, f x * (∫⁻ y, g y ∂κ x) ∂μ) =
        ∫⁻ z, F z ∂ν := by
          rw [Measure.lintegral_compProd hF]
          apply lintegral_congr
          intro x
          dsimp [F]
          rw [lintegral_const_mul _ hg]
    _ = ∫⁻ z, F z ∂Measure.map Prod.swap ν :=
      congrArg (fun m => ∫⁻ z, F z ∂m) hν
    _ = ∫⁻ z, F (Prod.swap z) ∂ν :=
      lintegral_map hF measurable_swap
    _ = ∫⁻ z, G z ∂ν := by
      apply lintegral_congr
      intro z
      dsimp [F, G]
      rw [mul_comm]
    _ = ∫⁻ x, g x * (∫⁻ y, f y ∂κ x) ∂μ := by
      rw [Measure.lintegral_compProd hG]
      apply lintegral_congr
      intro x
      dsimp [G]
      rw [lintegral_const_mul _ hf]

theorem aux_prop_limit_properties_cutoff_symmetry_attached_killedKernel
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (L : Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (omega : BilateralField d) (x : SpatialCoordinates d)
    {t : ℝ≥0}
    (hL : Measure.map MarkovProcess.LifetimePath.ofContinuousPath
      (KN (omega, x)) = L x)
    (hFDD : (KN).map (ContinuousPath.finsetEvaluation ({t} : Finset ℝ≥0))
      (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) x)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B) :
    killedKernel L Set.univ isOpen_univ t x B = P.kernel t x B := by
  have hEval : Measurable
      (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d)
        ({t} : Finset ℝ≥0)) := by
    exact Measurable.of_eval fun s =>
      (continuous_eval_const (s : ℝ≥0)).measurable
  have hFDD' :
      Measure.map (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d)
        ({t} : Finset ℝ≥0)) (KN (omega, x)) =
        SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) x := by
    rw [← Kernel.map_apply _ hEval]
    exact hFDD
  have hmap :
      Measure.map (fun path : DiffusionPath d => path t) (KN (omega, x)) =
        P.kernel t x :=
    SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation P
      (KN (omega, x)) x t hFDD'
  have hmapL :
      Measure.map (position t) (L x) = P.kernel t x := by
    rw [← hL]
    rw [Measure.map_map (position_fixed_measurable t)
      LifetimePath.measurable_ofContinuousPath]
    simpa only [Function.comp_apply, position_ofContinuousPath] using! hmap
  have hA : MeasurableSet
      {w : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d |
        position t w ∈ B ∧ (t : ENNReal) <
          LifetimePath.exitTime Set.univ w} := by
    exact (hB.preimage (position_fixed_measurable t)).inter
      (measurableSet_lt measurable_const
        (LifetimePath.isStoppingTime_exitTime Set.univ isOpen_univ).measurable')
  rw [killed_apply L Set.univ isOpen_univ t x B hB, ← hL,
    Measure.map_apply LifetimePath.measurable_ofContinuousPath hA]
  have hpre :
      LifetimePath.ofContinuousPath ⁻¹'
          {w : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d |
            position t w ∈ B ∧ (t : ENNReal) <
              LifetimePath.exitTime Set.univ w} =
        (fun path : DiffusionPath d => path t) ⁻¹' B := by
    ext path
    simp [position_ofContinuousPath, exitTime_univ_eq_lifetime,
      LifetimePath.lifetime_ofContinuousPath]
  rw [hpre, ← Measure.map_apply (continuous_eval_const t).measurable hB, hmap]




theorem prop_limit_properties_cutoff_symmetry
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SemigroupSymmetric (PN N omega) (cutoffSpeedMeasure M H omega N) := by
  have hFDD_ae := hin.2.2
  filter_upwards [hLlocal, hFDD_ae] with omega hlocal hFDD
  intro N
  let c : SpatialCoordinates d → ℝ :=
    cutoffCoefficient M H omega N
  let rho : SpatialCoordinates d → ℝ :=
    cutoffSpeedDensity M H omega N
  let law : Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d) :=
    L N omega
  have hD : LocalDiffusion c rho law := by
    simpa [c, rho, law] using hlocal N
  let : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  have hfin : ∀ j, weightedMeasure rho (ballFamily d j) ≠ ∞ := by
    intro j
    exact weightedMeasure_ne_top_of_localDiffusion hD
      (isOpen_ballFamily j) (isBounded_ballFamily j)
  let : SigmaFinite (weightedMeasure rho) :=
    Measure.sigmaFinite_of_countable (Set.countable_range (ballFamily d))
      (by
        rintro s ⟨j, rfl⟩
        exact (hfin j).lt_top)
      (by
        simpa only [Set.sUnion_range] using (iUnion_ballFamily (d := d)))
  have hsym :
      ∀ t : ℝ≥0, ∀ f g : SpatialCoordinates d → ℝ≥0∞,
        Measurable f → Measurable g →
        (∫⁻ x, f x * (∫⁻ y, g y ∂killedKernel law Set.univ isOpen_univ t x)
            ∂weightedMeasure rho) =
          ∫⁻ x, g x * (∫⁻ y, f y ∂killedKernel law Set.univ isOpen_univ t x)
            ∂weightedMeasure rho := by
    intro t f g hf hg
    have hrect_t :
        ∀ C D : Set (SpatialCoordinates d), MeasurableSet C →
          MeasurableSet D →
          (∫⁻ x in C, killedKernel law Set.univ isOpen_univ t x D
              ∂weightedMeasure rho) =
            ∫⁻ x in D, killedKernel law Set.univ isOpen_univ t x C
              ∂weightedMeasure rho := by
      intro C D hC hD'
      exact aux_prop_limit_properties_cutoff_symmetry_killedKernel_global_rectangle
        hD C D hC hD' t
    exact aux_prop_limit_properties_cutoff_symmetry_rectangle_to_measurable
      (killedKernel_subMarkov law Set.univ isOpen_univ t) hrect_t
      (ballFamily d) (fun j => (isOpen_ballFamily j).measurableSet)
      (iUnion_ballFamily (d := d)) hfin f g hf hg
  have hkernel :
      PN N omega = fun t => killedKernel law Set.univ isOpen_univ t := by
    funext t
    apply Kernel.ext
    intro x
    apply Measure.ext
    intro B hB
    have hfdd_x := hFDD N ({t} : Finset ℝ≥0) x
    have hL_x :
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
            (KN N (omega, x)) = law x := by
      simpa [law] using hL N omega x
    have hFDD_x :
        (KN N).map (ContinuousPath.finsetEvaluation ({t} : Finset ℝ≥0))
            (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN N omega)
            ({t} : Finset ℝ≥0) x :=
      hFDD N ({t} : Finset ℝ≥0) x
    exact (aux_prop_limit_properties_cutoff_symmetry_attached_killedKernel
      (PN N omega) (KN N) law omega x hL_x hFDD_x B hB).symm
  have hμ :
      cutoffSpeedMeasure M H omega N = weightedMeasure rho := by
    rfl
  rw [hμ]
  unfold SemigroupSymmetric
  intro t f g hf hg
  rw [hkernel]
  exact hsym t f g hf hg

end SubdiffusiveProcess.Paper
