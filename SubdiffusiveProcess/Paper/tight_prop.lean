module

public import SubdiffusiveProcess.Paper.tight_fast_exit
public import SubdiffusiveProcess.Paper.tight_fixed_cutoff
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_timescale
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

lemma aux_tight_prop_tsum_geometric_half (eps : ℝ≥0∞) :
    (∑' n : ℕ, eps * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) = eps := by
  have hsplit : ∀ n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ =
      2⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    rw [pow_succ, ENNReal.mul_inv (by simp) (by simp), ← ENNReal.inv_pow]
    ring
  have hone : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    rw [← ENNReal.inv_two_add_inv_two, ENNReal.add_sub_cancel_left (by simp)]
  rw [ENNReal.tsum_mul_left]
  simp_rw [hsplit]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, hone, inv_inv,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

lemma aux_tight_prop_rho_eq (n : ℕ) :
    ((n + 1 : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
  have h : ENNReal.ofReal (n + 1 : ℝ) = (n + 1 : ℝ≥0∞) := by
    simpa [Nat.cast_add] using (ENNReal.ofReal_natCast (n + 1))
  exact congrArg (fun z : ℝ≥0∞ => z⁻¹) h.symm

lemma aux_tight_prop_modulus_mono
    {α : Type*} [PseudoEMetricSpace α]
    {T : ℝ≥0} {δ₁ δ₂ r : ℝ≥0∞} (hδ : δ₁ ≤ δ₂) :
    ContinuousPath.modulusSet (alpha := α) T δ₂ r ⊆
      ContinuousPath.modulusSet T δ₁ r := by
  intro path hpath s t hs ht hst
  exact hpath s t hs ht (hst.trans hδ)

lemma aux_tight_prop_measurable_majorant
    {Ω Z X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (P : Ω → Z → Measure X) (B : Set Z) (K : Set X)
    (f : Ω → ℝ≥0∞) {e : ℝ≥0∞}
    (hf : AEMeasurable f mu)
    (hpoint : ∀ᵐ omega ∂mu, ∀ z ∈ B, P omega z Kᶜ ≤ f omega)
    (hbound : ∫⁻ omega, f omega ∂mu ≤ e)
    (hprob : ∀ omega z, P omega z Set.univ ≤ 1) :
    ∃ G : Ω → ℝ≥0∞, Measurable G ∧
      (∀ omega, ∀ z ∈ B, P omega z Kᶜ ≤ G omega) ∧
      ∫⁻ omega, G omega ∂mu ≤ e := by
  classical
  let fm : Ω → ℝ≥0∞ := hf.mk f
  let bad₀ : Set Ω := {omega | ¬ ∀ z ∈ B, P omega z Kᶜ ≤ f omega}
  let neq : Set Ω := {omega | f omega ≠ fm omega}
  let bad : Set Ω := MeasureTheory.toMeasurable mu (bad₀ ∪ neq)
  have hbad : mu bad = 0 := by
    rw [MeasureTheory.measure_toMeasurable]
    apply measure_union_null
    · exact (ae_iff.mp hpoint)
    · exact (ae_iff.mp hf.ae_eq_mk)
  have hbad₀ : bad₀ ⊆ bad := by
    intro omega homega
    exact MeasureTheory.subset_toMeasurable mu (bad₀ ∪ neq) (Or.inl homega)
  have hneq : neq ⊆ bad := by
    intro omega homega
    exact MeasureTheory.subset_toMeasurable mu (bad₀ ∪ neq) (Or.inr homega)
  let G : Ω → ℝ≥0∞ := fun omega => if omega ∈ bad then 1 else fm omega
  have hGmeas : Measurable G := by
    exact Measurable.ite (MeasureTheory.measurableSet_toMeasurable mu (bad₀ ∪ neq))
      measurable_const hf.measurable_mk
  refine ⟨G, hGmeas, ?_, ?_⟩
  · intro omega z hz
    by_cases ho : omega ∈ bad
    · simp only [G, if_pos ho]
      exact (measure_mono (Set.subset_univ Kᶜ)).trans (hprob omega z)
    · simp only [G, if_neg ho]
      have hgood : ∀ z ∈ B, P omega z Kᶜ ≤ f omega := by
        intro z' hz'
        by_contra hfail
        exact ho (hbad₀ (fun hforall => hfail (hforall z' hz')))
      have heq : f omega = fm omega := by
        by_contra hne'
        exact ho (hneq hne')
      rw [← heq]
      exact hgood z hz
  · have hGfm : G =ᵐ[mu] fm := by
      have hnot : ∀ᵐ omega ∂mu, omega ∉ bad := by
        rw [ae_iff]
        simpa using hbad
      filter_upwards [hnot] with omega ho
      simp only [G, if_neg ho]
    calc
      (∫⁻ omega, G omega ∂mu) = ∫⁻ omega, fm omega ∂mu :=
        lintegral_congr_ae hGfm
      _ = ∫⁻ omega, f omega ∂mu :=
        (lintegral_congr_ae hf.ae_eq_mk).symm
      _ ≤ e := hbound

lemma aux_tight_prop_local_path_tightness
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ T : ℝ≥0, ∀ r : ℝ≥0∞, 0 < r → ∀ eta : ℝ≥0∞, 0 < eta →
          (∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ x ∈ B,
            ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
              ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
              (ContinuousPath.modulusSet T delta r)ᶜ ≤ eta) ∧
          (∃ K0 : Set (SpatialCoordinates d), IsCompact K0 ∧ ∀ x ∈ B,
            ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
              ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
              {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ T → path s ∈ K0}ᶜ ≤ eta)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧ ∀ x ∈ B,
          ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)) Ksetᶜ ≤
              ENNReal.ofReal eps := by
  filter_upwards [hlocal] with omega homega
  intro N B hB eps heps
  let e : ℝ≥0∞ := ENNReal.ofReal eps
  have he : 0 < e := ENNReal.ofReal_pos.mpr heps
  let a : ℝ≥0∞ := e * (2 : ℝ≥0∞)⁻¹
  have ha : 0 < a := ENNReal.mul_pos he.ne' (by simp)
  let rho : ℕ → ℝ≥0∞ := fun n ↦ (n : ℝ≥0∞)⁻¹
  have hrhopos : ∀ n : ℕ, 0 < rho n := by
    intro n
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n)
  have hrhotendsto : Tendsto rho atTop (nhds 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero
  have hmodulus : ∀ n : ℕ, ∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ x ∈ B,
      ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
        (ContinuousPath.modulusSet (n : ℝ≥0) delta (rho n))ᶜ ≤
          a * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
    intro n
    have hpos : 0 < a * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ :=
      ENNReal.mul_pos ha.ne' (by simp)
    exact (homega N B hB (n : ℝ≥0) (rho n) (hrhopos n)
      (a * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) hpos).1
  choose delta hdelta hdelta_measure using hmodulus
  obtain ⟨K0, hK0, hK0_measure⟩ :=
    (homega N B hB (0 : ℝ≥0) (1 : ℝ≥0∞) one_pos a ha).2
  let Kset : Set (DiffusionPath d) := ContinuousPath.moduliSet K0 delta rho
  refine ⟨Kset, ContinuousPath.isCompact_moduliSet hK0 hdelta hrhotendsto, ?_⟩
  intro x hx
  have hstart_subset : {path : DiffusionPath d | path 0 ∉ K0} ⊆
      {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ 0 → path s ∈ K0}ᶜ := by
    intro path hpath hpath0
    exact hpath (hpath0 0 le_rfl)
  have hstart : ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
      ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
      {path : DiffusionPath d | path 0 ∉ K0} ≤ a :=
    (measure_mono hstart_subset).trans (hK0_measure x hx)
  have hcompl : Ksetᶜ = {path : DiffusionPath d | path 0 ∉ K0} ∪
      ⋃ n : ℕ, (ContinuousPath.modulusSet (n : ℝ≥0) (delta n) (rho n))ᶜ := by
    ext path
    simp only [Kset, ContinuousPath.moduliSet, Set.mem_compl_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, not_and_or,
      not_forall]
  rw [hcompl]
  calc
    ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
        ({path : DiffusionPath d | path 0 ∉ K0} ∪
          ⋃ n : ℕ, (ContinuousPath.modulusSet (n : ℝ≥0) (delta n) (rho n))ᶜ)
        ≤ _ := measure_union_le _ _
    _ ≤ a + ∑' n : ℕ, a * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
      refine add_le_add hstart ?_
      exact (measure_iUnion_le _).trans
        (ENNReal.tsum_le_tsum fun n => hdelta_measure n x hx)
    _ = e := by
      rw [aux_tight_prop_tsum_geometric_half]
      dsimp [a]
      rw [← mul_add]
      simp [ENNReal.inv_two_add_inv_two]

lemma aux_tight_prop_start_continuity
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (hlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ T : ℝ≥0,
        ∀ r : ℝ≥0∞, 0 < r → ∀ eta : ℝ≥0∞, 0 < eta →
        (∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ x ∈ B,
          ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
            (ContinuousPath.modulusSet T delta r)ᶜ ≤ eta) ∧
        (∃ K0 : Set (SpatialCoordinates d), IsCompact K0 ∧ ∀ x ∈ B,
          ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
            {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ T → path s ∈ K0}ᶜ ≤ eta)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x) := by
  have hfdd := in_cutoff_fdd_start_continuity hd M H hH PN KN hin
  have htight := aux_tight_prop_local_path_tightness M H PN KN hKN hlocal
  filter_upwards [hfdd, htight] with omega homega htightomega
  intro N
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro F
  refine continuous_iff_continuousAt.mpr fun x0 ↦
    Metric.tendsto_nhds.mpr fun eps heps ↦ ?_
  set eps5 : ℝ := eps / 5 with heps5def
  have heps5 : 0 < eps5 := by positivity
  set Ctot : ℝ := ‖F‖ + (‖F‖ + eps5) with hCtotdef
  have hCtotpos : 0 < Ctot := by
    rw [hCtotdef]
    linarith [norm_nonneg F]
  set eta : ℝ := eps5 / Ctot with hetadef
  have hetapos : 0 < eta := div_pos heps5 hCtotpos
  obtain ⟨K0, hK0compact, hK0nhds⟩ := exists_compact_mem_nhds x0
  obtain ⟨Kp, hKpcompact, hKpmass⟩ :=
    htightomega N K0 hK0compact eta hetapos
  obtain ⟨G, hGcyl, hGnorm, hGapprox⟩ :=
    ContinuousPath.exists_boundedCylinder_approx F hKpcompact heps5
  have hKpmeas : MeasurableSet Kp := hKpcompact.isClosed.measurableSet
  have herror : ∀ x ∈ K0,
      |(∫ omega, F omega ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d))) -
        ∫ omega, G omega ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d))| ≤ 2 * eps5 := by
    intro x hx
    have hmass : ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)).real Kpᶜ ≤ eta := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hetapos.le (hKpmass x hx)
    have hbase := abs_integral_sub_le_of_approx_on
      ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)) F G
      hKpmeas heps5.le hGapprox
    have hFG : ‖F‖ + ‖G‖ ≤ Ctot := by rw [hCtotdef]; linarith [hGnorm]
    have hprod : (‖F‖ + ‖G‖) *
        ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)).real Kpᶜ ≤ eps5 := by
      calc
        _ ≤ Ctot * eta := mul_le_mul hFG hmass measureReal_nonneg hCtotpos.le
        _ = eps5 := by rw [hetadef]; field_simp
    linarith [hbase, hprod]
  have hcylinder : Continuous (fun x ↦
      ∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d))) := by
    obtain ⟨I, g, hg⟩ := hGcyl
    have h := homega N I g
    apply h.congr
    intro x
    rw [show (∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d))) =
        ∫ path, g (ContinuousPath.finsetEvaluation I path) ∂
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) by
      congr 1; funext path; exact hg path]
    rw [← integral_map (ContinuousPath.measurable_finsetEvaluation I).aemeasurable
      g.continuous.aestronglyMeasurable]
    change (∫ y, g y ∂((KN N).map (ContinuousPath.finsetEvaluation I) (omega, x))) =
      ∫ y, g y ∂Measure.map (ContinuousPath.finsetEvaluation I) (KN N (omega, x))
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
  have hnear : ∀ᶠ x in nhds x0,
      |(∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d))) -
        ∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
          ProbabilityMeasure (DiffusionPath d))| < eps5 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp
      (hcylinder.continuousAt (x := x0)) eps5 heps5)
  filter_upwards [hnear, hK0nhds] with x hxnear hxK0
  rw [Real.dist_eq]
  have h1 := herror x hxK0
  have h2' : |(∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
      ProbabilityMeasure (DiffusionPath d))) -
        ∫ path, F path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
          ProbabilityMeasure (DiffusionPath d))| ≤ 2 * eps5 := by
    rw [abs_sub_comm]
    exact herror x0 (mem_of_mem_nhds hK0nhds)
  have htri1 := abs_sub_le
    (∫ path, F path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
      ProbabilityMeasure (DiffusionPath d)))
    (∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
      ProbabilityMeasure (DiffusionPath d)))
    (∫ path, F path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
      ProbabilityMeasure (DiffusionPath d)))
  have htri2 := abs_sub_le
    (∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
      ProbabilityMeasure (DiffusionPath d)))
    (∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
      ProbabilityMeasure (DiffusionPath d)))
    (∫ path, F path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
      ProbabilityMeasure (DiffusionPath d)))
  rw [heps5def] at h1 h2' hxnear
  linarith [htri1, htri2, h1, h2', hxnear]

lemma aux_tight_prop_dense_sup
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [OpensMeasurableSpace β] [HasOuterApproxClosed β]
    {B D : Set α} {p : α → ProbabilityMeasure β} {G : Set β}
    (hp : Continuous p) (hD : B ⊆ closure D) (hG : IsOpen G) :
    (⨆ x ∈ B, ((p x : ProbabilityMeasure β) : Measure β) G) ≤
      ⨆ x : D, ((p x : ProbabilityMeasure β) : Measure β) G := by
  have hlsc : LowerSemicontinuous
      (fun x : α => ((p x : ProbabilityMeasure β) : Measure β) G) := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro x
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (hp.tendsto x) hG
  refine iSup₂_le fun x hx => ?_
  refine le_of_forall_lt fun c hcx => ?_
  have hopen : IsOpen {y : α | c < ((p y : ProbabilityMeasure β) : Measure β) G} := by
    simpa only [Set.preimage_setOf_eq, Set.mem_Ioi] using! hlsc.isOpen_preimage c
  have hne : ({y : α | c < ((p y : ProbabilityMeasure β) : Measure β) G} ∩ D).Nonempty :=
    (mem_closure_iff.mp (hD hx)) _ hopen hcx
  obtain ⟨y, hy, hyD⟩ := hne
  exact lt_of_lt_of_le hy (le_iSup (fun z : D => ((p z : ProbabilityMeasure β) : Measure β) G) ⟨y, hyD⟩)

lemma aux_tight_prop_finite_cutoff
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (hlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ T : ℝ≥0,
        ∀ r : ℝ≥0∞, 0 < r → ∀ eta : ℝ≥0∞, 0 < eta →
        (∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ x ∈ B,
          ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
            (ContinuousPath.modulusSet T delta r)ᶜ ≤ eta) ∧
        (∃ K0 : Set (SpatialCoordinates d), IsCompact K0 ∧ ∀ x ∈ B,
          ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
            {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ T → path s ∈ K0}ᶜ ≤ eta)) :
    ∀ (N : ℕ) (B : Set (SpatialCoordinates d)), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
        (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
          ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal eps := by
  intro N B hB eps heps
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : SpatialCoordinates d)).mp hB.isBounded
  let R₀ : ℝ := max R 0
  let K₀ : Set (SpatialCoordinates d) := Metric.closedBall 0 R₀
  have hBK₀ : B ⊆ K₀ := hR.trans (Metric.closedBall_subset_closedBall (le_max_left R 0))
  have hK₀ : IsCompact K₀ := isCompact_closedBall _ _
  obtain ⟨D, hDB, hDcount, hDdense⟩ := hB.isSeparable.exists_countable_dense_subset
  letI : Encodable D := hDcount.toEncodable
  have h_tightness := aux_tight_prop_local_path_tightness M H PN KN hKN hlocal
  have h_cont := aux_tight_prop_start_continuity hd M H hH PN KN hKN hin hlocal
  let startEvent : ℕ → Set (DiffusionPath d) := fun m =>
    {path | path 0 ∉ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ)}
  let modulusEvent : ℕ → ℕ → Set (DiffusionPath d) := fun n m =>
    (ContinuousPath.modulusSet (n : ℝ≥0)
      ((m + 1 : ℝ≥0∞)⁻¹) ((n + 1 : ℝ≥0∞)⁻¹))ᶜ
  have hstartEvent : ∀ m, MeasurableSet (startEvent m) := by
    intro m
    exact (Metric.isClosed_closedBall.measurableSet.compl.preimage
      (ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) 0))
  have hmodulusEvent : ∀ n m, MeasurableSet (modulusEvent n m) := by
    intro n m
    exact ContinuousPath.measurableSet_modulusSet _ _ _ |>.compl
  have hsup_open : ∀ (omega : BilateralField d) (G : Set (DiffusionPath d)),
      IsOpen G → Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x) →
      (⨆ x ∈ B, (KN N (omega, x)) G) =
        ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) G := by
    intro omega G hG hω
    have hle : (⨆ x ∈ B, (KN N (omega, x)) G) ≤
        ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) G := by
      simpa only [jointPathProbabilityMeasure] using!
        (aux_tight_prop_dense_sup (B := B) (D := D)
          (p := fun x => jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          hω hDdense hG)
    have hge : (⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) G) ≤
        ⨆ x ∈ B, (KN N (omega, x)) G := by
      refine iSup_le fun x => le_iSup_of_le (x : SpatialCoordinates d)
        (le_iSup_of_le (hDB x.property) le_rfl)
    exact le_antisymm hle hge
  let fstart : ℕ → BilateralField d → ℝ≥0∞ := fun m omega =>
    ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) (startEvent m)
  let fmod : ℕ → ℕ → BilateralField d → ℝ≥0∞ := fun n m omega =>
    ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) (modulusEvent n m)
  have hfstart_meas : ∀ m, Measurable (fstart m) := by
    intro m
    apply Measurable.iSup
    intro x
    change Measurable (fun omega => (KN N (omega, (x : SpatialCoordinates d)))
      (startEvent m))
    exact (Kernel.measurable_coe (KN N) (hstartEvent m)).comp measurable_prodMk_right
  have hfmod_meas : ∀ n m, Measurable (fmod n m) := by
    intro n m
    apply Measurable.iSup
    intro x
    change Measurable (fun omega => (KN N (omega, (x : SpatialCoordinates d)))
      (modulusEvent n m))
    exact (Kernel.measurable_coe (KN N) (hmodulusEvent n m)).comp measurable_prodMk_right
  have hfstart_le_one : ∀ m, ∀ omega, fstart m omega ≤ 1 := by
    intro m omega
    refine iSup_le fun x => ?_
    letI : IsProbabilityMeasure (KN N (omega, (x : SpatialCoordinates d))) :=
      (hKN N).isProbabilityMeasure _
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hfmod_le_one : ∀ n m, ∀ omega, fmod n m omega ≤ 1 := by
    intro n m omega
    refine iSup_le fun x => ?_
    letI : IsProbabilityMeasure (KN N (omega, (x : SpatialCoordinates d))) :=
      (hKN N).isProbabilityMeasure _
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hlim_start : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun m => fstart m omega) atTop (𝓝 0) := by
    filter_upwards [hlocal] with omega hω
    rw [ENNReal.tendsto_nhds_zero]
    intro eta heta
    obtain ⟨S, hScompact, hSbound⟩ :=
      (hω N B hB 0 1 (by simp) eta heta).2
    obtain ⟨R', hR'⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : SpatialCoordinates d)).mp hScompact.isBounded
    obtain ⟨k, hk⟩ := exists_nat_ge R'
    filter_upwards [eventually_ge_atTop k] with m hm
    refine iSup_le fun x => ?_
    have hmeasure := hSbound (x : SpatialCoordinates d) (hDB x.property)
    apply (measure_mono ?_).trans hmeasure
    intro path hpath
    change path 0 ∉ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) at hpath
    change ¬ (∀ s : ℝ≥0, s ≤ 0 → path s ∈ S)
    intro hpath0
    have h0S := hpath0 0 (by simp)
    have hSm : S ⊆ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) :=
      hR'.trans (Metric.closedBall_subset_closedBall (by
        exact le_trans hk (by exact_mod_cast hm)))
    exact hpath (hSm h0S)
  have hlim_mod : ∀ n, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun m => fmod n m omega) atTop (𝓝 0) := by
    intro n
    filter_upwards [hlocal] with omega hω
    rw [ENNReal.tendsto_nhds_zero]
    intro eta heta
    obtain ⟨delta, hdelta, hbound⟩ :=
      (hω N B hB (n : ℝ≥0) ((n + 1 : ℝ≥0∞)⁻¹)
        (by exact ENNReal.inv_pos.mpr (by simp)) eta heta).1
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hdelta.ne'
    filter_upwards [eventually_ge_atTop k] with m hm
    refine iSup_le fun x => ?_
    have hmeasure := hbound (x : SpatialCoordinates d) (hDB x.property)
    apply (measure_mono ?_).trans hmeasure
    intro path hpath
    change path ∉ ContinuousPath.modulusSet (n : ℝ≥0)
      ((m + 1 : ℝ≥0∞)⁻¹) ((n + 1 : ℝ≥0∞)⁻¹) at hpath
    change path ∉ ContinuousPath.modulusSet (n : ℝ≥0) delta
      ((n + 1 : ℝ≥0∞)⁻¹)
    intro hpathδ
    apply hpath
    have hkm : (k : ℝ≥0∞) ≤ (m + 1 : ℝ≥0∞) := by
      exact_mod_cast (Nat.le_succ_of_le hm)
    exact (aux_tight_prop_modulus_mono
      (δ₁ := (m + 1 : ℝ≥0∞)⁻¹) (δ₂ := delta)
      ((ENNReal.inv_le_inv.mpr hkm).trans hk.le)) hpathδ
  have hlim_start_int :
      Tendsto (fun m => ∫⁻ omega, fstart m omega ∂(chaosSampleLaw M).toMeasure)
        atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence
      (fun _ : BilateralField d => (1 : ℝ≥0∞)) hfstart_meas
      (fun m => Filter.Eventually.of_forall (hfstart_le_one m)) (by simp) hlim_start
  have hlim_mod_int : ∀ n,
      Tendsto (fun m => ∫⁻ omega, fmod n m omega ∂(chaosSampleLaw M).toMeasure)
        atTop (𝓝 0) := by
    intro n
    simpa using tendsto_lintegral_of_dominated_convergence
      (fun _ : BilateralField d => (1 : ℝ≥0∞)) (hfmod_meas n)
      (fun m => Filter.Eventually.of_forall (hfmod_le_one n m)) (by simp) (hlim_mod n)
  let a₀ : ℝ≥0∞ := ENNReal.ofReal eps * (2 : ℝ≥0∞)⁻¹
  have ha₀ : 0 < a₀ := ENNReal.mul_pos (ENNReal.ofReal_pos.mpr heps).ne' (by simp)
  obtain ⟨m₀, hm₀⟩ := (ENNReal.tendsto_nhds_zero.mp hlim_start_int a₀ ha₀).exists
  have hmod_exists : ∀ n : ℕ, ∃ m : ℕ,
      (∫⁻ omega, fmod n m omega ∂(chaosSampleLaw M).toMeasure) ≤
        ENNReal.ofReal eps * ((2 : ℝ≥0∞) ^ (n + 2))⁻¹ := by
    intro n
    let an : ℝ≥0∞ := ENNReal.ofReal eps * ((2 : ℝ≥0∞) ^ (n + 2))⁻¹
    have han : 0 < an := ENNReal.mul_pos (ENNReal.ofReal_pos.mpr heps).ne' (by simp)
    obtain ⟨m, hm⟩ := (ENNReal.tendsto_nhds_zero.mp (hlim_mod_int n) an han).exists
    exact ⟨m, by simpa [an] using hm⟩
  choose m hm using hmod_exists
  let δ : ℕ → ℝ≥0∞ := fun n => ((m n + 1 : ℝ≥0∞)⁻¹)
  let ρ : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℝ≥0∞)⁻¹)
  have hδ : ∀ n, 0 < δ n := by
    intro n; exact ENNReal.inv_pos.mpr (by simp [δ])
  have hρ : ∀ n, 0 < ρ n := by
    intro n; exact ENNReal.inv_pos.mpr (by simp [ρ])
  have hρtendsto : Tendsto ρ atTop (𝓝 0) := by
    simpa [ρ] using ((tendsto_add_atTop_iff_nat
      (f := fun n : ℕ => (n : ℝ≥0∞)⁻¹) (l := 𝓝 (0 : ℝ≥0∞)) 1).2
        ENNReal.tendsto_inv_nat_nhds_zero)
  let K₁ : Set (SpatialCoordinates d) := Metric.closedBall 0 (max R₀ (m₀ : ℝ))
  have hK₁ : IsCompact K₁ := isCompact_closedBall _ _
  have hBK₁ : B ⊆ K₁ := hR.trans (Metric.closedBall_subset_closedBall
    (le_trans (le_max_left R 0) (le_max_left R₀ (m₀ : ℝ))))
  let Kset : Set (DiffusionPath d) := ContinuousPath.moduliSet K₁ δ ρ
  have hKset : IsCompact Kset := ContinuousPath.isCompact_moduliSet hK₁ hδ hρtendsto
  have hKcompl : Ksetᶜ = {path : DiffusionPath d | path 0 ∉ K₁} ∪
      ⋃ n : ℕ, modulusEvent n (m n) := by
    ext path
    by_cases hp : path 0 ∈ K₁ <;>
      simp [Kset, startEvent, modulusEvent, ContinuousPath.moduliSet, δ, ρ, hp]
  have hsum_meas : Measurable (fun omega => ∑' n : ℕ, fmod n (m n) omega) :=
    Measurable.ennreal_tsum fun n => hfmod_meas n (m n)
  have hstart_dom : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x ∈ B, (KN N (omega, x)) {path : DiffusionPath d | path 0 ∉ K₁} ≤
        fstart m₀ omega := by
    filter_upwards [h_cont] with omega hω
    intro x hx
    have hs := hsup_open omega (startEvent m₀)
      (Metric.isClosed_closedBall.isOpen_compl.preimage
        (ContinuousPath.continuous_eval (alpha := SpatialCoordinates d) 0)) (hω N)
    have hle : (KN N (omega, x)) (startEvent m₀) ≤ fstart m₀ omega := by
      change (KN N (omega, x)) (startEvent m₀) ≤
        ⨆ z : D, (KN N (omega, (z : SpatialCoordinates d))) (startEvent m₀)
      rw [← hs]
      exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    exact (measure_mono (by
      intro path hp
      change path 0 ∉ K₁ at hp
      change path 0 ∉ Metric.closedBall (0 : SpatialCoordinates d) (m₀ : ℝ)
      intro hpath
      exact hp (Metric.closedBall_subset_closedBall
        (le_max_right R₀ (m₀ : ℝ)) hpath))).trans hle
  have hmod_dom : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ n, ∀ x ∈ B, (KN N (omega, x)) (modulusEvent n (m n)) ≤
        fmod n (m n) omega := by
    filter_upwards [h_cont] with omega hω
    intro n x hx
    have hs := hsup_open omega (modulusEvent n (m n))
      (ContinuousPath.isClosed_modulusSet _ _ _ |>.isOpen_compl) (hω N)
    change (KN N (omega, x)) (modulusEvent n (m n)) ≤
      ⨆ z : D, (KN N (omega, (z : SpatialCoordinates d))) (modulusEvent n (m n))
    rw [← hs]
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have hpoint : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ) ≤
        fstart m₀ omega + ∑' n : ℕ, fmod n (m n) omega := by
    filter_upwards [hstart_dom, hmod_dom] with omega hstart hmod
    refine iSup₂_le fun x hx => ?_
    rw [hKcompl]
    calc
      (KN N (omega, x)) ({path : DiffusionPath d | path 0 ∉ K₁} ∪
          ⋃ n : ℕ, modulusEvent n (m n)) ≤
        (KN N (omega, x)) {path : DiffusionPath d | path 0 ∉ K₁} +
          (KN N (omega, x)) (⋃ n : ℕ, modulusEvent n (m n)) := measure_union_le _ _
      _ ≤ fstart m₀ omega + ∑' n : ℕ, fmod n (m n) omega := by
        exact add_le_add (hstart x hx)
          ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun n => hmod n x hx))
  refine ⟨Kset, hKset, ?_⟩
  have hlin_tsum :
      (∫⁻ omega, ∑' n : ℕ, fmod n (m n) omega ∂(chaosSampleLaw M).toMeasure) =
        ∑' n : ℕ, ∫⁻ omega, fmod n (m n) omega ∂(chaosSampleLaw M).toMeasure :=
    lintegral_tsum fun n => (hfmod_meas n (m n)).aemeasurable
  have hgeom :
      (∑' n : ℕ, ENNReal.ofReal eps * ((2 : ℝ≥0∞) ^ (n + 2))⁻¹) =
        ENNReal.ofReal eps * (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.tsum_mul_left]
    have hterm : ∀ n : ℕ, ((2 : ℝ≥0∞) ^ (n + 2))⁻¹ =
        ((2 : ℝ≥0∞) ^ 2)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ n := by
      intro n
      rw [pow_add, ENNReal.mul_inv (by simp) (by simp), ← ENNReal.inv_pow]
      ac_rfl
    rw [tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    have hhalf : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
      rw [← ENNReal.inv_two_add_inv_two, ENNReal.add_sub_cancel_left (by simp)]
    rw [hhalf, inv_inv, pow_two, ENNReal.mul_inv (by simp) (by simp)]
    calc
      ENNReal.ofReal eps * ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ * 2) =
          ENNReal.ofReal eps * (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹ * 2) := by ac_rfl
      _ = ENNReal.ofReal eps * (2 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
  calc
    (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
        ∂(chaosSampleLaw M).toMeasure) ≤
        ∫⁻ omega, fstart m₀ omega + ∑' n : ℕ, fmod n (m n) omega
          ∂(chaosSampleLaw M).toMeasure := lintegral_mono_ae hpoint
    _ = (∫⁻ omega, fstart m₀ omega ∂(chaosSampleLaw M).toMeasure) +
        ∫⁻ omega, ∑' n : ℕ, fmod n (m n) omega ∂(chaosSampleLaw M).toMeasure :=
      lintegral_add_left (hfstart_meas m₀) _
    _ = (∫⁻ omega, fstart m₀ omega ∂(chaosSampleLaw M).toMeasure) +
        ∑' n : ℕ, ∫⁻ omega, fmod n (m n) omega ∂(chaosSampleLaw M).toMeasure :=
      congrArg (fun z => (∫⁻ omega, fstart m₀ omega ∂(chaosSampleLaw M).toMeasure) + z)
        hlin_tsum
    _ ≤ a₀ + ∑' n : ℕ,
        ENNReal.ofReal eps * ((2 : ℝ≥0∞) ^ (n + 2))⁻¹ := by
      exact add_le_add hm₀ (ENNReal.tsum_le_tsum fun n => hm n)
    _ = ENNReal.ofReal eps := by
      rw [hgeom]
      dsimp [a₀]
      rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

lemma aux_tight_prop_countable_assembly
    {I Omega Z X : Type*} [Countable I]
    [MeasurableSpace Omega] [MeasurableSpace X] [TopologicalSpace X]
    (mu : Measure Omega)
    (P : ℕ → Omega → Z → Measure X)
    (B : Set Z) (S : I → Set X) (a : I → ℝ≥0∞) (eta : ℝ≥0∞)
    (hcompact : IsCompact (⋂ i, S i))
    (hmeas : ∀ N i, AEMeasurable
      (fun omega => ⨆ x ∈ B, P N omega x (S i)ᶜ) mu)
    (hbound : ∀ N i,
      (∫⁻ omega, ⨆ x ∈ B, P N omega x (S i)ᶜ ∂mu) ≤ a i)
    (hbudget : (∑' i, a i) ≤ eta) :
    ∃ K : Set X, IsCompact K ∧
      ∀ N : ℕ, (∫⁻ omega, ⨆ x ∈ B, P N omega x Kᶜ ∂mu) ≤ eta := by
  classical
  have hset : (⋂ i, S i)ᶜ = ⋃ i, (S i)ᶜ := by
    ext x
    simp
  refine ⟨⋂ i, S i, hcompact, ?_⟩
  intro N
  calc
    (∫⁻ omega, ⨆ x ∈ B, P N omega x (⋂ i, S i)ᶜ ∂mu) ≤
        ∫⁻ omega, ∑' i, ⨆ x ∈ B, P N omega x (S i)ᶜ ∂mu := by
      apply lintegral_mono
      intro omega
      refine iSup_le fun x => iSup_le fun hx => ?_
      calc
        P N omega x (⋂ i, S i)ᶜ ≤ ∑' i, P N omega x (S i)ᶜ := by
          rw [hset]
          exact measure_iUnion_le _
        _ ≤ ∑' i, ⨆ y ∈ B, P N omega y (S i)ᶜ :=
          ENNReal.tsum_le_tsum fun i => le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    _ = ∑' i, ∫⁻ omega, ⨆ x ∈ B, P N omega x (S i)ᶜ ∂mu :=
      lintegral_tsum (hmeas N)
    _ ≤ ∑' i, a i := ENNReal.tsum_le_tsum (hbound N)
    _ ≤ eta := hbudget

lemma aux_tight_prop_random_laws
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (B : Set (SpatialCoordinates d))
    (hpath : ∀ eps : ℝ, 0 < eps →
      ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
        (∀ N : ℕ, ∃ G : BilateralField d → ℝ≥0∞, Measurable G ∧
          (∀ omega, ∀ x ∈ B, (KN N (omega, x)) Ksetᶜ ≤ G omega) ∧
          ∫⁻ omega, G omega ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps)) :
    ∀ eta : ℝ, 0 < eta →
      ∃ Keta : Set (ProbabilityMeasure (DiffusionPath d)), IsClosed Keta ∧
        (∀ eps : ℝ, 0 < eps → ∃ Kset' : Set (DiffusionPath d), IsCompact Kset' ∧
          ∀ Pm ∈ Keta, (Pm : Measure (DiffusionPath d)) Kset'ᶜ ≤ ENNReal.ofReal eps) ∧
        ∀ N : ℕ, (chaosSampleLaw M).toMeasure
            {omega : BilateralField d | ∃ x ∈ B,
              jointPathProbabilityMeasure (KN N) (hKN N) omega x ∉ Keta}
            ≤ ENNReal.ofReal eta := by
  intro eta heta
  let delta : ℕ → ℝ := fun k => eta * (1 / 2 : ℝ) ^ (k + 1)
  have hdelta : ∀ k, 0 < delta k := by
    intro k
    dsimp [delta]
    positivity
  choose Kk hKk hKkbound using fun k =>
    hpath ((delta k) ^ 2) (pow_pos (hdelta k) 2)
  let Keta : Set (ProbabilityMeasure (DiffusionPath d)) :=
    {mu : ProbabilityMeasure (DiffusionPath d) |
      ∀ k : ℕ, (mu : Measure (DiffusionPath d)) (Kk k)ᶜ ≤
        ENNReal.ofReal (delta k)}
  have hKeta_closed : IsClosed Keta := by
    refine IsSeqClosed.isClosed ?_
    intro u x hu hx k
    have hopen : IsOpen (Kk k)ᶜ := (hKk k).isClosed.isOpen_compl
    have hlim : (x : Measure (DiffusionPath d)) (Kk k)ᶜ ≤
        liminf (fun n => (u n : Measure (DiffusionPath d)) (Kk k)ᶜ) atTop :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hx hopen
    have hbound : liminf (fun n => (u n : Measure (DiffusionPath d)) (Kk k)ᶜ) atTop ≤
        ENNReal.ofReal (delta k) := by
      have hev : ∀ᶠ n in atTop,
          (u n : Measure (DiffusionPath d)) (Kk k)ᶜ ≤ ENNReal.ofReal (delta k) :=
        Eventually.of_forall (fun n => hu n k)
      exact (liminf_le_liminf hev).trans_eq (liminf_const _)
    exact hlim.trans hbound
  have hKeta_tight : ∀ eps : ℝ, 0 < eps →
      ∃ Kset' : Set (DiffusionPath d), IsCompact Kset' ∧
        ∀ Pm ∈ Keta, (Pm : Measure (DiffusionPath d)) Kset'ᶜ ≤ ENNReal.ofReal eps := by
    intro eps heps
    have hratio : 0 < eps / eta := div_pos heps heta
    have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hev : ∀ᶠ k : ℕ in atTop, (1 / 2 : ℝ) ^ k < eps / eta :=
      (tendsto_order.1 hpow).2 (eps / eta) hratio
    obtain ⟨k, hk⟩ := hev.exists
    have hpowmono : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ k := by
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
    have hdeltaeps : delta k ≤ eps := by
      dsimp [delta]
      exact le_of_lt (calc
        eta * (1 / 2 : ℝ) ^ (k + 1) ≤ eta * (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hpowmono heta.le
        _ < eta * (eps / eta) := mul_lt_mul_of_pos_left hk heta
        _ = eps := mul_div_cancel₀ eps heta.ne')
    exact ⟨Kk k, hKk k, fun Pm hPm =>
      (hPm k).trans (ENNReal.ofReal_le_ofReal hdeltaeps)⟩
  have hbad : ∀ N k : ℕ,
      (chaosSampleLaw M).toMeasure
          {omega : BilateralField d |
            ENNReal.ofReal (delta k) <
              ⨆ x ∈ B, (KN N (omega, x)) (Kk k)ᶜ} ≤
        ENNReal.ofReal (delta k) := by
    intro N k
    obtain ⟨G, hG, hpoint, hGint⟩ := hKkbound k N
    let μ := (chaosSampleLaw M).toMeasure
    have hsup : ∀ omega : BilateralField d,
        (⨆ x ∈ B, (KN N (omega, x)) (Kk k)ᶜ) ≤ G omega := by
      intro omega
      refine iSup₂_le fun x hx => ?_
      exact hpoint omega x hx
    have hsub : {omega : BilateralField d |
          ENNReal.ofReal (delta k) <
            ⨆ x ∈ B, (KN N (omega, x)) (Kk k)ᶜ} ⊆
        {omega : BilateralField d | ENNReal.ofReal (delta k) ≤ G omega} := by
      intro omega homega
      exact le_trans (le_of_lt homega) (hsup omega)
    have hmarkov : μ {omega : BilateralField d | ENNReal.ofReal (delta k) ≤ G omega} ≤
        (∫⁻ omega, G omega ∂μ) / ENNReal.ofReal (delta k) :=
      meas_ge_le_lintegral_div hG.aemeasurable
        (ENNReal.ofReal_pos.mpr (hdelta k)).ne' ENNReal.ofReal_ne_top
    have hprod : (∫⁻ omega, G omega ∂μ) ≤
        ENNReal.ofReal (delta k) * ENNReal.ofReal (delta k) := by
      calc
        (∫⁻ omega, G omega ∂μ) ≤ ENNReal.ofReal ((delta k) ^ 2) := hGint
        _ = ENNReal.ofReal (delta k) * ENNReal.ofReal (delta k) := by
          rw [pow_two, ENNReal.ofReal_mul (hdelta k).le]
    exact (measure_mono hsub).trans (hmarkov.trans (ENNReal.div_le_of_le_mul hprod))
  refine ⟨Keta, hKeta_closed, hKeta_tight, ?_⟩
  intro N
  have hsub : {omega : BilateralField d | ∃ x ∈ B,
        jointPathProbabilityMeasure (KN N) (hKN N) omega x ∉ Keta} ⊆
      ⋃ k : ℕ, {omega : BilateralField d |
        ENNReal.ofReal (delta k) <
          ⨆ x ∈ B, (KN N (omega, x)) (Kk k)ᶜ} := by
    intro omega homega
    obtain ⟨x, hxB, hxK⟩ := homega
    have hxK' : ¬ ∀ k : ℕ,
        ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)) (Kk k)ᶜ ≤
          ENNReal.ofReal (delta k) := by
      simpa [Keta] using hxK
    push_neg at hxK'
    obtain ⟨k, hk⟩ := hxK'
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    exact lt_of_lt_of_le hk (le_iSup₂_of_le x hxB le_rfl)
  calc
    (chaosSampleLaw M).toMeasure {omega : BilateralField d | ∃ x ∈ B,
        jointPathProbabilityMeasure (KN N) (hKN N) omega x ∉ Keta} ≤
      (chaosSampleLaw M).toMeasure (⋃ k : ℕ, {omega : BilateralField d |
        ENNReal.ofReal (delta k) <
          ⨆ x ∈ B, (KN N (omega, x)) (Kk k)ᶜ}) := measure_mono hsub
    _ ≤ ∑' k : ℕ,
        (chaosSampleLaw M).toMeasure {omega : BilateralField d |
          ENNReal.ofReal (delta k) <
            ⨆ x ∈ B, (KN N (omega, x)) (Kk k)ᶜ} :=
      measure_iUnion_le (μ := (chaosSampleLaw M).toMeasure) _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (delta k) :=
      ENNReal.tsum_le_tsum (fun k => hbad N k)
    _ = ENNReal.ofReal eta := by
      dsimp [delta]
      have hsumm : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
        simpa [pow_succ, mul_comm] using
          (summable_geometric_two.mul_left (1 / 2 : ℝ))
      have hsum : (∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1)) = 1 := by
        rw [tsum_congr (fun k => by rw [pow_succ]), tsum_mul_right,
          tsum_geometric_two]
        norm_num
      have hsumm' : Summable (fun k : ℕ => eta * (1 / 2 : ℝ) ^ (k + 1)) :=
        hsumm.mul_left eta
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm',
        tsum_mul_left, hsum, mul_one]

lemma aux_tight_prop_scale_lower
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k N : ℕ) (hkn : k ≤ N) :
    0 < (3 : ℝ) ^ (-(2 * (k : ℤ))) *
          (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)))⁻¹ ∧
      (3 : ℝ) ^ (-(2 * (k : ℤ))) *
          (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)))⁻¹ ≤
        (3 : ℝ) ^ (2 * (((N - k : ℕ) : ℤ) - (N : ℤ))) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) := by
  have hq := aux_in_timescale_triadic_ratio M (m := N - k) (n := N)
    (Nat.sub_le N k)
  have hNk : N - (N - k) = k := by omega
  rw [hNk] at hq
  have hq' :
      (3 : ℝ) ^ (2 * N) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤
        ((3 : ℝ) ^ (2 * k) *
          Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ))) *
          ((3 : ℝ) ^ (2 * (N-k)) /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k)) := by
    simpa only [Nat.cast_sub hkn] using hq
  let A : ℝ := (3 : ℝ) ^ (2 * k) *
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ))
  have hApos : 0 < A := by positivity
  have hqdiv :
      ((3 : ℝ) ^ (2 * N) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) / A ≤
        ((3 : ℝ) ^ (2 * (N-k)) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k)) := by
    apply (div_le_iff₀ hApos).2
    simpa [A, mul_comm] using hq'
  have hqpos : 0 < (3 : ℝ) ^ (2 * N) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    div_pos (by positivity) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  have hratio :
      1 / A ≤ ((3 : ℝ) ^ (2 * (N-k)) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k)) /
        ((3 : ℝ) ^ (2 * N) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := by
    apply (le_div_iff₀ hqpos).2
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hqdiv
  have hD_eq :
      (3 : ℝ) ^ (-(2 * (k : ℤ))) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) =
      ((3 : ℝ) ^ (2 * (N-k)) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k)) /
        ((3 : ℝ) ^ (2 * N) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := by
    have hp : (3 : ℝ) ^ (2 * N) =
        (3 : ℝ) ^ (2 * (N-k)) * (3 : ℝ) ^ (2*k) := by
      rw [show 2*N = 2*(N-k)+2*k by omega, pow_add]
    have hz : (3 : ℝ) ^ (-(2 * (k : ℤ))) =
        ((3 : ℝ) ^ (2*k))⁻¹ := by
      rw [zpow_neg]
      rw [show 2 * (k : ℤ) = ((2*k : ℕ) : ℤ) by omega]
      rw [zpow_natCast]
    rw [hz]
    field_simp [ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N),
      ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N-k))]
    rw [hp]
    ring
  have hAinv : 1 / A = (3 : ℝ) ^ (-(2 * (k : ℤ))) *
      (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)))⁻¹ := by
    rw [div_eq_mul_inv]
    dsimp [A]
    have hz : (3 : ℝ) ^ (-(2 * (k : ℤ))) =
        ((3 : ℝ) ^ (2*k))⁻¹ := by
      rw [zpow_neg]
      rw [show 2 * (k : ℤ) = ((2*k : ℕ) : ℤ) by omega]
      rw [zpow_natCast]
    rw [hz]
    field_simp
  constructor
  · positivity
  · have htarget :
        (3 : ℝ) ^ (2 * (((N - k : ℕ) : ℤ) - (N : ℤ))) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) =
          (3 : ℝ) ^ (-(2 * (k : ℤ))) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) := by
      congr 1
      congr 1
      simp only [Nat.cast_sub hkn]
      ring
    rw [htarget, hD_eq, ← hAinv]
    exact hratio

lemma aux_tight_prop_sqrt_scaled_bound
    {F0 Fi A M : ℝ} (hF0 : 0 < F0) (hF0Fi : F0 ≤ Fi)
    (hA : 0 < A) (hM : 0 < M) (p : ℕ) :
    Real.sqrt ((F0 * (A / (16 * ((p : ℝ) + 1) * M)) ^ 2) / Fi) ≤
      A / (16 * ((p : ℝ) + 1) * M) := by
  have hFi : 0 < Fi := lt_of_lt_of_le hF0 hF0Fi
  let s : ℝ := A / (16 * ((p : ℝ) + 1) * M)
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hsq : (F0 * s ^ 2) / Fi ≤ s ^ 2 := by
    apply (div_le_iff₀ hFi).2
    exact (mul_le_mul_of_nonneg_right hF0Fi (sq_nonneg s)).trans_eq (by ring)
  calc
    Real.sqrt ((F0 * (A / (16 * ((p : ℝ) + 1) * M)) ^ 2) / Fi) =
        Real.sqrt ((F0 * s ^ 2) / Fi) := by rfl
    _ ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hsq
    _ = s := Real.sqrt_sq hs
    _ = A / (16 * ((p : ℝ) + 1) * M) := by rfl

lemma aux_tight_prop_sqrt_small_bound
    {F0 Fi M : ℝ} (hF0 : 0 < F0) (hF0Fi : F0 ≤ Fi) (hM : 0 < M) :
    Real.sqrt ((F0 / (64 * M ^ 2)) / Fi) ≤ 1 / (8 * M) := by
  have hFi : 0 < Fi := lt_of_lt_of_le hF0 hF0Fi
  have hsq : (F0 / (64 * M ^ 2)) / Fi ≤ (1 / (8 * M)) ^ 2 := by
    apply (div_le_iff₀ hFi).2
    calc
      F0 / (64 * M ^ 2) ≤ Fi / (64 * M ^ 2) := by
        exact div_le_div_of_nonneg_right hF0Fi (by positivity)
      _ = (1 / (8 * M)) ^ 2 * Fi := by
        field_simp [ne_of_gt hM]
        ring
  exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))

lemma aux_tight_prop_half_pow (p : ℕ) :
    (1 / 2 : ℝ) ^ p = ((2 : ℝ) ^ p)⁻¹ := by
  rw [div_eq_mul_inv, one_mul, inv_pow]

lemma aux_tight_prop_exp_pow_bound {A T hh : ℝ} (hA : 0 < A)
    (hhpos : 0 < hh) (p : ℕ)
    (hp : 16 * Real.exp (T / hh) / A < (2 : ℝ) ^ p) :
    Real.exp (T / hh) * (1 / 2 : ℝ) ^ p ≤ A / 16 := by
  have hpow : 0 < (2 : ℝ) ^ p := by positivity
  rw [aux_tight_prop_half_pow]
  have hp' := (div_lt_iff₀ hA).mp hp
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
  have hp'' := mul_le_mul_of_nonneg_right hp'.le
    (le_of_lt (inv_pos.mpr hpow))
  field_simp [ne_of_gt hpow] at hp'' ⊢
  nlinarith

lemma aux_tight_prop_exp_ennreal_bound {A T hh : ℝ} (hA : 0 < A)
    (hhpos : 0 < hh) (p : ℕ)
    (hp : 16 * Real.exp (T / hh) / A < (2 : ℝ) ^ p) :
    ENNReal.ofReal (Real.exp (T / hh)) * ENNReal.ofReal (1 / 2 : ℝ) ^ p ≤
      ENNReal.ofReal (A / 16) := by
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal
    (aux_tight_prop_exp_pow_bound hA hhpos p hp)

lemma aux_tight_prop_tail_ennreal_bound {A : ℝ} (hA : 0 ≤ A) (p : ℕ) :
    (p : ℝ≥0∞) * ENNReal.ofReal (A / (16 * ((p : ℝ) + 1))) ≤
      ENNReal.ofReal (A / 16) := by
  have hp1 : 0 < (p : ℝ) + 1 := by positivity
  have hreal : (p : ℝ) * (A / (16 * ((p : ℝ) + 1))) ≤ A / 16 := by
    have hratio : (p : ℝ) / ((p : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hp1).2
      linarith
    have heq : (p : ℝ) * (A / (16 * ((p : ℝ) + 1))) =
        (A / 16) * ((p : ℝ) / ((p : ℝ) + 1)) := by
      field_simp [ne_of_gt hp1]
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hratio (by positivity)).trans_eq (mul_one _)
  rw [← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg p)]
  exact ENNReal.ofReal_le_ofReal hreal

lemma aux_tight_prop_four_quarters {a : ℝ≥0∞} (ha0 : a ≠ 0)
    (hatop : a ≠ ⊤) :
    ENNReal.ofReal (a.toReal / 16) + ENNReal.ofReal (a.toReal / 16) +
        ENNReal.ofReal (a.toReal / 16) + ENNReal.ofReal (a.toReal / 16) ≤ a := by
  have htr : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  calc
    _ = ENNReal.ofReal (a.toReal / 4) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1 <;> ring
    _ ≤ ENNReal.ofReal a.toReal := ENNReal.ofReal_le_ofReal (by linarith)
    _ = a := ENNReal.ofReal_toReal hatop

lemma aux_tight_prop_lintegral_ofReal_mul {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (f x * c) ∂μ) =
      ENNReal.ofReal c * (∫⁻ x, ENNReal.ofReal (f x) ∂μ) := by
  calc
    (∫⁻ x, ENNReal.ofReal (f x * c) ∂μ) =
        ∫⁻ x, ENNReal.ofReal c * ENNReal.ofReal (f x) ∂μ := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_mul' hc, mul_comm]
    _ = ENNReal.ofReal c * (∫⁻ x, ENNReal.ofReal (f x) ∂μ) := by
      exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hf)

lemma aux_tight_prop_card_bound {q C A : ℝ} (hq : 0 ≤ q)
    (hC : 0 < C) (hA : 0 < A) :
    q * C ≤ (16 * (q + 1) * C / A) * (A / 16) := by
  field_simp [ne_of_gt hA]
  nlinarith

lemma aux_tight_prop_mul_div_cancel {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    c * (a / (b * c)) = a / b := by
  field_simp [ne_of_gt hb, ne_of_gt hc]

lemma aux_tight_prop_mul_inv_cancel {c : ℝ} (hc : 0 < c) :
    c * (1 / (8 * c)) = 1 / 8 := by
  exact aux_tight_prop_mul_div_cancel (by norm_num) hc

lemma aux_tight_prop_cover_subtype {α : Type*} [PseudoMetricSpace α]
    {T S : Set α} {r : ℝ}
    (hcover : T ⊆ ⋃ x ∈ S, Metric.ball x r) :
    ∀ y ∈ T, ∃ i : {x // x ∈ S}, y ∈ Metric.ball (i : α) r := by
  intro y hy
  have h := hcover hy
  simp only [Set.mem_iUnion] at h
  rcases h with ⟨x, hx, hyx⟩
  exact ⟨⟨x, hx⟩, hyx⟩

structure aux_tight_prop_goodI {d : ℕ} [MeasurableSpace (BilateralField d × SpatialCoordinates d)]
    (ι : Type*)
    (center : ι → SpatialCoordinates d) (N : ℕ) (qk Fi : ℝ)
    (Ki : ι → BilateralField d → ℝ)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)) where
  bound : ∀ omega : BilateralField d, ∀ i : ι, ∀ t : ℝ, 0 < t →
    ∀ y ∈ Metric.ball (center i) (qk / 18),
      (KN N (omega, y))
        {path : DiffusionPath d |
          ContinuousPath.exitTime (Metric.ball (center i) (qk / 2)) path ≤
            ENNReal.ofReal t} ≤
        ENNReal.ofReal (Ki i omega * Real.sqrt (t / Fi))

structure aux_tight_prop_cover_data {α : Type*} [PseudoMetricSpace α]
    (ι : Type*) (T : Set α) (r : ℝ) (center : ι → α) where
  choose : ∀ y ∈ T, ∃ i : ι, y ∈ Metric.ball (center i) r

lemma aux_tight_prop_measure_chain {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {A B : Set α} {u v : ℝ≥0∞} (hsub : A ⊆ B) (hB : μ B ≤ u)
    (huv : u ≤ v) : μ A ≤ v :=
  (measure_mono hsub).trans (hB.trans huv)

lemma aux_tight_prop_kernel_chain {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (K : Kernel β α) {A B : Set α} {u v : ℝ≥0∞}
    (x : β) (hsub : A ⊆ B) (hB : (K x) B ≤ u) (huv : u ≤ v) :
    (K x) A ≤ v := by
  exact (measure_mono hsub).trans (hB.trans huv)

lemma aux_tight_prop_kernel_chain_ofReal {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (K : Kernel β α) (x : β) {A B : Set α}
    {r s : ℝ} (hsub : A ⊆ B) (hB : (K x) B ≤ ENNReal.ofReal r)
    (hrs : r ≤ s) : (K x) A ≤ ENNReal.ofReal s := by
  exact (measure_mono hsub).trans
    (hB.trans (ENNReal.ofReal_le_ofReal hrs))

lemma aux_tight_prop_markov_probability {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {K : Kernel β α} (hK : IsMarkovKernel K) (x : β) :
    IsProbabilityMeasure (K x) := by
  letI : IsMarkovKernel K := hK
  exact IsMarkovKernel.isProbabilityMeasure x

lemma aux_tight_prop_restart_wt_mono {α : Type*} [PseudoMetricSpace α]
    {hh : ℝ} (hhpos : 0 < hh)
    {U V : Set α} (hsub : V ⊆ U) (path : ContinuousPath α) :
    aux_tight_fixed_cutoff_restart_wt hh
        (ContinuousPath.exitTime U path) ≤
      aux_tight_fixed_cutoff_restart_wt hh
        (ContinuousPath.exitTime V path) := by
  by_cases htop : ContinuousPath.exitTime U path = ⊤
  · simp [htop, aux_tight_fixed_cutoff_restart_wt]
  · have hsmalltop : ContinuousPath.exitTime V path ≠ ⊤ := by
      intro hs
      exact htop (top_unique (by simpa [hs] using
        (ContinuousPath.exitTime_mono hsub path)))
    unfold aux_tight_fixed_cutoff_restart_wt
    rw [if_neg htop, if_neg hsmalltop]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (neg_le_neg (ENNReal.toReal_mono htop
        (ContinuousPath.exitTime_mono hsub path))) hhpos.le

lemma aux_tight_prop_restart_integral_bound {γ β : Type*}
    [PseudoMetricSpace γ] [MeasurableSpace (ContinuousPath γ)]
    [MeasurableSpace β]
    (K : Kernel β (ContinuousPath γ)) (x : β)
    (hprob : IsProbabilityMeasure (K x)) (U V : Set γ) (hh h1 : ℝ)
    (hhpos : 0 < hh)
    (hh1 : 0 ≤ h1)
    (hwt : ∀ path : ContinuousPath γ,
      aux_tight_fixed_cutoff_restart_wt hh
          (ContinuousPath.exitTime U path) ≤
        aux_tight_fixed_cutoff_restart_wt hh
          (ContinuousPath.exitTime V path))
    (hVm : Measurable (ContinuousPath.exitTime V :
      ContinuousPath γ → ℝ≥0∞))
    (hexp : Real.exp (-h1 / hh) ≤ 1 / 4)
    (hsmall : (K x) {path | ContinuousPath.exitTime V path ≤
      ENNReal.ofReal h1} ≤ ENNReal.ofReal (1 / 8)) :
    (∫⁻ path, aux_tight_fixed_cutoff_restart_wt hh
      (ContinuousPath.exitTime U path) ∂K x) ≤ ENNReal.ofReal (1 / 2) := by
  letI : IsProbabilityMeasure (K x) := hprob
  calc
    _ ≤ ∫⁻ path, aux_tight_fixed_cutoff_restart_wt hh
        (ContinuousPath.exitTime V path) ∂K x := lintegral_mono hwt
    _ ≤ ∫⁻ path, ({s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1}.indicator
          (1 : ℝ≥0∞ → ℝ≥0∞) (ContinuousPath.exitTime V path) +
        ENNReal.ofReal (Real.exp (-h1 / hh))) ∂K x :=
      lintegral_mono (fun path =>
        aux_tight_fixed_cutoff_restart_wt_le_split hhpos hh1 _)
    _ = (K x) {path | ContinuousPath.exitTime V path ≤
          (ENNReal.ofReal h1)} +
        ENNReal.ofReal (Real.exp (-h1 / hh)) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const,
        measure_univ, mul_one]
      congr 1
      have heq : (fun path => {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1}.indicator
          (1 : ℝ≥0∞ → ℝ≥0∞) (ContinuousPath.exitTime V path)) =
          {path : ContinuousPath γ |
            ContinuousPath.exitTime V path ≤ ENNReal.ofReal h1}.indicator
            (1 : ContinuousPath γ → ℝ≥0∞) := by
        funext path
        simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
      rw [heq, lintegral_indicator_one
        (measurableSet_le hVm measurable_const)]
    _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 4) := by
      refine add_le_add hsmall ?_
      apply ENNReal.ofReal_le_ofReal
      exact hexp
    _ ≤ ENNReal.ofReal (1 / 2) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      norm_num

lemma aux_tight_prop_exit_time_chain_ofReal
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    {β : Type*} [MeasurableSpace β]
    (K : Kernel β (DiffusionPath d)) (x : β)
    (U V : Set (SpatialCoordinates d)) (δ : ℝ≥0∞) (t r s : ℝ)
    (hsub : V ⊆ U) (hδ : δ = ENNReal.ofReal t)
    (hfast : (K x) {path : DiffusionPath d |
      ContinuousPath.exitTime V path ≤ ENNReal.ofReal t} ≤ ENNReal.ofReal r)
    (hrs : r ≤ s) :
    (K x) {path : DiffusionPath d |
      ContinuousPath.exitTime U path ≤ δ} ≤ ENNReal.ofReal s := by
  apply aux_tight_prop_kernel_chain_ofReal (K := K) x
    (A := {path : DiffusionPath d |
      ContinuousPath.exitTime U path ≤ δ})
    (B := {path : DiffusionPath d |
      ContinuousPath.exitTime V path ≤ ENNReal.ofReal t})
    (r := r) (s := s) ?_ hfast hrs
  intro path hp
  have hmono := ContinuousPath.exitTime_mono hsub path
  simpa only [hδ] using! hmono.trans hp

lemma aux_tight_prop_scaled_exit_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    {β : Type*} [MeasurableSpace β]
    (K : Kernel β (DiffusionPath d)) (x : β) (y z : SpatialCoordinates d)
    (rho qk : ℝ) (δ' : ℝ≥0∞) (F0 Fi A Mbig h2 : ℝ) (p : ℕ) (KiVal : ℝ)
    (hF0 : 0 < F0) (hFi : F0 ≤ Fi) (hA : 0 < A) (hMbig : 0 < Mbig)
    (hKiM : KiVal ≤ Mbig)
    (hh2eq : h2 = F0 * (A / (16 * ((p : ℝ) + 1) * Mbig)) ^ 2)
    (hball : Metric.ball z (qk / 2) ⊆ Metric.ball y rho)
    (hδ : δ' = ENNReal.ofReal h2)
    (hfast : (K x) {path : DiffusionPath d |
      ContinuousPath.exitTime (Metric.ball z (qk / 2)) path ≤
        ENNReal.ofReal h2} ≤
      ENNReal.ofReal (KiVal * Real.sqrt (h2 / Fi))) :
    (K x) {path : DiffusionPath d |
      ContinuousPath.exitTime (Metric.ball y rho) path ≤ δ'} ≤
      ENNReal.ofReal (A / (16 * ((p : ℝ) + 1))) := by
  have hp1 : 0 < (p : ℝ) + 1 := by positivity
  have hden : 0 < 16 * ((p : ℝ) + 1) := by positivity
  have hroot : Real.sqrt (h2 / Fi) ≤
      A / (16 * ((p : ℝ) + 1) * Mbig) := by
    rw [hh2eq]
    exact aux_tight_prop_sqrt_scaled_bound hF0 hFi hA hMbig p
  have hprod : KiVal * Real.sqrt (h2 / Fi) ≤
      A / (16 * ((p : ℝ) + 1)) := by
    calc
      _ ≤ Mbig * Real.sqrt (h2 / Fi) :=
        mul_le_mul_of_nonneg_right hKiM (Real.sqrt_nonneg _)
      _ ≤ Mbig * (A / (16 * ((p : ℝ) + 1) * Mbig)) :=
        mul_le_mul_of_nonneg_left hroot hMbig.le
      _ = A / (16 * ((p : ℝ) + 1)) :=
        aux_tight_prop_mul_div_cancel hden hMbig
  exact aux_tight_prop_exit_time_chain_ofReal K x
    (Metric.ball y rho) (Metric.ball z (qk / 2)) δ' h2
    (KiVal * Real.sqrt (h2 / Fi)) (A / (16 * ((p : ℝ) + 1)))
    hball hδ hfast hprod

lemma aux_tight_prop_exit_event_mono {α : Type*} [PseudoMetricSpace α]
    (U V : Set α) (t : ℝ≥0∞) (hsub : V ⊆ U) :
    {path : ContinuousPath α | ContinuousPath.exitTime U path ≤ t} ⊆
      {path : ContinuousPath α | ContinuousPath.exitTime V path ≤ t} := by
  intro path hp
  exact (ContinuousPath.exitTime_mono hsub path).trans hp

lemma aux_tight_prop_spatial_exit_event_mono {d : ℕ}
    (U V : Set (SpatialCoordinates d)) (t : ℝ≥0∞) (hsub : V ⊆ U) :
    {path : DiffusionPath d | ContinuousPath.exitTime U path ≤ t} ⊆
      {path : DiffusionPath d | ContinuousPath.exitTime V path ≤ t} := by
  exact aux_tight_prop_exit_event_mono U V t hsub

lemma aux_tight_prop_indicator_dom {α : Type*} (s : Set α)
    [DecidablePred (fun x : α => x ∈ s)]
    (u : α → ℝ≥0∞) (c₁ c₂ : ℝ≥0∞) (x : α) :
    (if x ∈ s then 1 else u x + c₁ + c₂) ≤
      s.indicator (fun _ => (1 : ℝ≥0∞)) x + u x + c₁ + c₂ := by
  by_cases hx : x ∈ s
  · rw [if_pos hx, Set.indicator_of_mem hx]
    simpa [add_assoc] using
      (le_add_of_nonneg_right (by positivity : 0 ≤ u x + c₁ + c₂) :
        (1 : ℝ≥0∞) ≤ 1 + (u x + c₁ + c₂))
  · simp [hx]

lemma aux_tight_prop_exp_half {h1 : ℝ} (h1pos : 0 < h1) :
    Real.exp (-h1 / (h1 / 2)) ≤ 1 / 4 := by
  have heq : -h1 / (h1 / 2) = (-2 : ℝ) := by
    field_simp
  rw [heq]
  exact aux_tight_fixed_cutoff_restart_exp_neg_two_le

lemma aux_tight_prop_measurable_exit_ball {d : ℕ}
    (y : SpatialCoordinates d) (r : ℝ) :
    Measurable (ContinuousPath.exitTime (Metric.ball y r) :
      DiffusionPath d → ℝ≥0∞) :=
  ContinuousPath.measurable_exitTime _ Metric.isOpen_ball

lemma aux_tight_prop_restart_integral_bound_ball
    {d : ℕ} {β : Type*} [MeasurableSpace β]
    (K : Kernel β (DiffusionPath d)) (x : β)
    (hprob : IsProbabilityMeasure (K x))
    (y z : SpatialCoordinates d) (rho q hh h1 : ℝ)
    (hhpos : 0 < hh) (h1pos : 0 ≤ h1)
    (hsub : Metric.ball z q ⊆ Metric.ball y rho)
    (hexp : Real.exp (-h1 / hh) ≤ 1 / 4) (v : ℝ)
    (hfast : (K x) {path : DiffusionPath d |
      ContinuousPath.exitTime (Metric.ball z q) path ≤ ENNReal.ofReal h1} ≤
      ENNReal.ofReal v) (hv : v ≤ 1 / 8) :
    (∫⁻ path, aux_tight_fixed_cutoff_restart_wt hh
      (ContinuousPath.exitTime (Metric.ball y rho) path) ∂K x) ≤
      ENNReal.ofReal (1 / 2) := by
  have hshort := hfast.trans (ENNReal.ofReal_le_ofReal hv)
  exact aux_tight_prop_restart_integral_bound K x hprob
    (Metric.ball y rho) (Metric.ball z q) hh h1 hhpos h1pos
    (fun path => aux_tight_prop_restart_wt_mono hhpos hsub path)
    (aux_tight_prop_measurable_exit_ball z q) hexp hshort

lemma aux_tight_prop_gamma_bound {d : ℕ}
    [MeasurableSpace (BilateralField d × SpatialCoordinates d)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (C : Set (SpatialCoordinates d))
    (centers : Type*) (center : centers → SpatialCoordinates d)
    (qk rho Fi hh h1 Mbig : ℝ) (Ki : centers → BilateralField d → ℝ)
    (hKN : IsMarkovKernel (KN N))
    (hcover : ∀ y ∈ C, ∃ i : centers,
      y ∈ Metric.ball (center i) (qk / 18))
    (hball : ∀ y (i : centers), y ∈ Metric.ball (center i) (qk / 18) →
      Metric.ball (center i) (qk / 2) ⊆ Metric.ball y rho)
    (hgood : ∀ (i : centers) (t : ℝ), 0 < t →
      ∀ y ∈ Metric.ball (center i) (qk / 18),
        (KN N (omega, y)) {path : DiffusionPath d |
          ContinuousPath.exitTime (Metric.ball (center i) (qk / 2)) path ≤
            ENNReal.ofReal t} ≤
          ENNReal.ofReal (Ki i omega * Real.sqrt (t / Fi)))
    (hexp : Real.exp (-h1 / hh) ≤ 1 / 4)
    (hMbig : 0 < Mbig)
    (hKiM : ∀ i : centers, Ki i omega ≤ Mbig)
    (hroot : Real.sqrt (h1 / Fi) ≤ 1 / (8 * Mbig))
    (hhpos : 0 < hh) (h1pos : 0 < h1) :
    ∀ y ∈ C, ∫⁻ path, aux_tight_fixed_cutoff_restart_wt hh
      (ContinuousPath.exitTime (Metric.ball y rho) path) ∂KN N (omega, y) ≤
      ENNReal.ofReal (1 / 2) := by
  intro y hy
  obtain ⟨i, hyi⟩ := hcover y hy
  have hfast := hgood i h1 h1pos y hyi
  have hshort : Ki i omega * Real.sqrt (h1 / Fi) ≤ 1 / 8 := by
    calc
      _ ≤ Mbig * Real.sqrt (h1 / Fi) :=
        mul_le_mul_of_nonneg_right (hKiM i) (Real.sqrt_nonneg _)
      _ ≤ Mbig * (1 / (8 * Mbig)) :=
        mul_le_mul_of_nonneg_left hroot hMbig.le
      _ = 1 / 8 := aux_tight_prop_mul_inv_cancel hMbig
  exact aux_tight_prop_restart_integral_bound_ball (KN N) (omega, y)
    (aux_tight_prop_markov_probability hKN (omega, y))
    y (center i) rho (qk / 2) hh h1 hhpos h1pos.le (hball y i hyi) hexp
    (Ki i omega * Real.sqrt (h1 / Fi)) hfast hshort

lemma aux_tight_prop_finite_sum_lintegral_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (Ki : ι → Ω → ℝ) (C : ℝ)
    (hmeas : ∀ i, Measurable (Ki i))
    (hbound : ∀ i, (∫⁻ omega, ENNReal.ofReal (Ki i omega) ∂μ) ≤
      ENNReal.ofReal C) :
    (∫⁻ omega, ∑ i : ι, ENNReal.ofReal (Ki i omega) ∂μ) ≤
      (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal C := by
  calc
    (∫⁻ omega, ∑ i : ι, ENNReal.ofReal (Ki i omega) ∂μ) =
        ∑ i : ι, ∫⁻ omega, ENNReal.ofReal (Ki i omega) ∂μ := by
      rw [lintegral_finset_sum]
      intro i hi
      exact ENNReal.measurable_ofReal.comp (hmeas i)
    _ ≤ ∑ i : ι, ENNReal.ofReal C := Finset.sum_le_sum (fun i hi => hbound i)
    _ = (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal C := by
      simp [nsmul_eq_mul]

lemma aux_tight_prop_finite_sum_lintegral_bound_field {d : ℕ} {ι : Type*}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] [Fintype ι]
    (μ : Measure (BilateralField d)) (Ki : ι → BilateralField d → ℝ)
    (C : ℝ) (hmeas : ∀ i, Measurable (Ki i))
    (hbound : ∀ i, (∫⁻ omega, ENNReal.ofReal (Ki i omega) ∂μ) ≤
      ENNReal.ofReal C) :
    (∫⁻ omega, ∑ i : ι, ENNReal.ofReal (Ki i omega) ∂μ) ≤
      (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal C := by
  exact aux_tight_prop_finite_sum_lintegral_bound μ Ki C hmeas hbound

lemma aux_tight_prop_exit_from_closedBall_complement {d : ℕ}
    (T r : ℝ) (hT : 0 < T) :
    {path : DiffusionPath d |
      ∃ s : ℝ≥0, s ≤ T ∧ path s ∉ Metric.closedBall
        (0 : SpatialCoordinates d) r} ⊆
      {path : DiffusionPath d |
        ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) r) path ≤
          ENNReal.ofReal T} := by
  intro path hp
  obtain ⟨s, hs, hnot⟩ := hp
  have hnotball : path s ∉ Metric.ball (0 : SpatialCoordinates d) r := by
    intro hsball
    exact hnot (Metric.ball_subset_closedBall hsball)
  have hle := ContinuousPath.exitTime_le_of_notMem
    (Metric.ball (0 : SpatialCoordinates d) r) path s hnotball
  have hs' : (s : ℝ≥0∞) ≤ ENNReal.ofReal T := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hs
  exact hle.trans hs'

lemma aux_tight_prop_fixed_modulus_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (B : Set (SpatialCoordinates d)) (hB : IsCompact B)
    (hlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ T : ℝ≥0,
        ∀ r : ℝ≥0∞, 0 < r → ∀ eta : ℝ≥0∞, 0 < eta →
          (∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ x ∈ B,
            ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
              ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
              (ContinuousPath.modulusSet T delta r)ᶜ ≤ eta) ∧
          (∃ K0 : Set (SpatialCoordinates d), IsCompact K0 ∧ ∀ x ∈ B,
            ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
              ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
              {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ T → path s ∈ K0}ᶜ ≤ eta))
    (hcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x)) :
    ∀ (N n : ℕ) (a : ℝ≥0∞), 0 < a →
      ∃ δ : ℝ≥0∞, 0 < δ ∧
        (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x))
          (ContinuousPath.modulusSet (n : ℝ≥0) δ
            (ENNReal.ofReal (1 / (n + 1 : ℝ))))ᶜ
          ∂(chaosSampleLaw M).toMeasure) ≤ a := by
  intro N n a ha
  obtain ⟨D, hDB, hDcount, hDdense⟩ := hB.isSeparable.exists_countable_dense_subset
  letI : Encodable D := hDcount.toEncodable
  let ev : ℕ → ℕ → Set (DiffusionPath d) := fun q m =>
    (ContinuousPath.modulusSet (q : ℝ≥0)
      ((m + 1 : ℝ≥0∞)⁻¹) (ENNReal.ofReal (1 / (q + 1 : ℝ))))ᶜ
  have hev_meas : ∀ q m, MeasurableSet (ev q m) := by
    intro q m
    exact ContinuousPath.measurableSet_modulusSet _ _ _ |>.compl
  let f : ℕ → BilateralField d → ℝ≥0∞ := fun m omega =>
    ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) (ev n m)
  have hfmeas : ∀ m, Measurable (f m) := by
    intro m
    apply Measurable.iSup
    intro x
    exact (Kernel.measurable_coe (KN N) (hev_meas n m)).comp measurable_prodMk_right
  have hf_le_one : ∀ m omega, f m omega ≤ 1 := by
    intro m omega
    refine iSup_le fun x => ?_
    letI : IsProbabilityMeasure (KN N (omega, (x : SpatialCoordinates d))) :=
      (hKN N).isProbabilityMeasure _
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun m => f m omega) atTop (𝓝 0) := by
    filter_upwards [hlocal, hcont] with omega hω hωcont
    rw [ENNReal.tendsto_nhds_zero]
    intro e he
    obtain ⟨δ, hδ, hδbound⟩ :=
      (hω N B hB (n : ℝ≥0) (ENNReal.ofReal (1 / (n + 1)) )
        (ENNReal.ofReal_pos.mpr (by positivity)) e he).1
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
    filter_upwards [eventually_ge_atTop k] with m hm
    have hsup := aux_tight_prop_dense_sup (B := B) (D := D)
      (p := fun x => jointPathProbabilityMeasure (KN N) (hKN N) omega x)
      (G := ev n m) (hωcont N) (by simpa using hDdense)
      (ContinuousPath.isClosed_modulusSet _ _ _).isOpen_compl
    have hsup' : (⨆ x ∈ B, (KN N (omega, x)) (ev n m)) ≤ f m omega := by
      simpa only [jointPathProbabilityMeasure, f, ev] using! hsup
    have hge : f m omega ≤ (⨆ x ∈ B, (KN N (omega, x)) (ev n m)) := by
      refine iSup_le fun x => le_iSup_of_le (x : SpatialCoordinates d)
        (le_iSup_of_le (hDB x.property) le_rfl)
    rw [← le_antisymm hsup' hge]
    refine iSup₂_le fun x hx => ?_
    have hmeas : (KN N (omega, x)) (ev n m) ≤
        (KN N (omega, x))
          (ContinuousPath.modulusSet (n : ℝ≥0) δ
            (ENNReal.ofReal (1 / (n + 1 : ℝ))))ᶜ := by
      apply measure_mono
      intro path hp
      change path ∉ ContinuousPath.modulusSet (n : ℝ≥0)
        ((m + 1 : ℝ≥0∞)⁻¹) (ENNReal.ofReal (1 / (n + 1 : ℝ))) at hp
      change path ∉ ContinuousPath.modulusSet (n : ℝ≥0) δ
        (ENNReal.ofReal (1 / (n + 1 : ℝ)))
      intro hpath
      apply hp
      exact aux_tight_prop_modulus_mono
        (δ₁ := (m + 1 : ℝ≥0∞)⁻¹) (δ₂ := δ)
        ((ENNReal.inv_le_inv.mpr (by
          exact_mod_cast Nat.le_succ_of_le hm)).trans hk.le) hpath
    exact hmeas.trans (hδbound x hx)
  have hlimint :
      Tendsto (fun m => ∫⁻ omega, f m omega ∂(chaosSampleLaw M).toMeasure)
        atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence
      (fun _ : BilateralField d => (1 : ℝ≥0∞)) hfmeas
      (fun m => Filter.Eventually.of_forall (hf_le_one m)) (by simp) hlim
  obtain ⟨m, hm⟩ := (ENNReal.tendsto_nhds_zero.mp hlimint a ha).exists
  refine ⟨(m + 1 : ℝ≥0∞)⁻¹, ENNReal.inv_pos.mpr (by simp), ?_⟩
  have hsup : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (⨆ x ∈ B, (KN N (omega, x))
        ((ContinuousPath.modulusSet (n : ℝ≥0) ((m + 1 : ℝ≥0∞)⁻¹)
          (ENNReal.ofReal (1 / (n + 1 : ℝ))))ᶜ)) ≤ f m omega := by
    filter_upwards [hcont] with omega hω
    have hs := aux_tight_prop_dense_sup (B := B) (D := D)
      (p := fun x => jointPathProbabilityMeasure (KN N) (hKN N) omega x)
      (G := ev n m) (hω N) (by simpa using hDdense)
        (ContinuousPath.isClosed_modulusSet _ _ _).isOpen_compl
    simpa only [jointPathProbabilityMeasure, f, ev] using! hs
  exact (lintegral_mono_ae hsup).trans (by simpa [f] using hm)

lemma aux_tight_prop_hmod_large
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N omega x,
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
        L N omega x)
    (hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
        (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (hfdd : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N I x,
      ((KN N).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
        ((PN N omega).finiteSetKernel I) x)
    (Cfast : ℝ) (hCfast : 0 < Cfast)
    (hfastN : ∀ (N m : ℕ) (y : SpatialCoordinates d),
      ∃ K : BilateralField d → ℝ, Measurable K ∧ (∀ omega, 0 ≤ K omega) ∧
        ∫⁻ omega, ENNReal.ofReal (K omega) ∂(chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal Cfast ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ t : ℝ, 0 < t →
          ∀ x ∈ Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 18),
            (KN N (omega, x))
                {path : DiffusionPath d |
                  ContinuousPath.exitTime
                    (Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 2)) path ≤
                    ENNReal.ofReal t} ≤
              ENNReal.ofReal (K omega * Real.sqrt (t /
                ((3 : ℝ) ^ (2 * ((m : ℤ) - (N : ℤ))) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))))
    (B : Set (SpatialCoordinates d)) (hB : IsCompact B) :
    ∀ (n : ℕ) (a : ℝ≥0∞), 0 < a →
      ∃ k : ℕ, ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ N : ℕ, k ≤ N →
        (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x))
          (ContinuousPath.modulusSet (n : ℝ≥0) δ
            (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ
          ∂(chaosSampleLaw M).toMeasure) ≤ a := by
  intro n a ha
  by_cases hatop : a = ⊤
  · exact ⟨0, 1, one_pos, fun N _ => by
      simpa [hatop] using
        (le_top : (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x))
          (ContinuousPath.modulusSet (n : ℝ≥0) 1
            (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ
          ∂(chaosSampleLaw M).toMeasure) ≤ (⊤ : ℝ≥0∞))⟩
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hatop' : a ≠ ⊤ := hatop
  let A : ℝ := a.toReal
  have hA : 0 < A := ENNReal.toReal_pos ha0 hatop'
  let r : ℝ := 1 / (n + 1 : ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨R, hBR⟩ := hB.isBounded.subset_closedBall (0 : SpatialCoordinates d)
  let R' : ℝ := max R 1
  have hBR' : B ⊆ Metric.closedBall (0 : SpatialCoordinates d) R' := by
    exact hBR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let Jbound : ℝ := max (18 * R' + 1)
      (16 * Cfast * Real.sqrt ((n + 1 : ℕ) : ℝ) / A + 1)
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt Jbound
    (by norm_num : (1 : ℝ) < 3)
  let qj : ℝ := (3 : ℝ) ^ j
  have hqj : 18 * R' < qj := by
    dsimp [qj]
    have hJ := le_max_left (18 * R' + 1)
      (16 * Cfast * Real.sqrt ((n + 1 : ℕ) : ℝ) / A + 1)
    linarith
  have hqjerr : 16 * Cfast * Real.sqrt ((n + 1 : ℕ) : ℝ) / A < qj := by
    dsimp [qj]
    have hJ := le_max_right (18 * R' + 1)
      (16 * Cfast * Real.sqrt ((n + 1 : ℕ) : ℝ) / A + 1)
    linarith
  have hBinner : B ⊆ Metric.ball (0 : SpatialCoordinates d) (qj / 18) := by
    intro x hx
    have hxR := hBR' hx
    rw [Metric.mem_closedBall] at hxR
    rw [Metric.mem_ball]
    linarith
  let CR : Set (SpatialCoordinates d) := Metric.closedBall 0 (qj / 2)
  have hCR : IsCompact CR := isCompact_closedBall _ _
  have hCRm : MeasurableSet CR := Metric.isClosed_closedBall.measurableSet
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (5 / (3 * r))
    (by norm_num : (1 : ℝ) < 3)
  let qk : ℝ := ((3 : ℝ)⁻¹) ^ k
  have hqkpos : 0 < qk := by dsimp [qk]; positivity
  have hqk : qk < 3 * r / 5 := by
    have hpow : 0 < (3 : ℝ) ^ k := by positivity
    have hmul : 5 < 3 * r * (3 : ℝ) ^ k := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * r)).mp hk
    dsimp [qk]
    rw [inv_pow]
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2
    have hmul' := mul_lt_mul_of_pos_right hmul (inv_pos.mpr hpow)
    convert hmul' using 1 <;> field_simp
  have hqkcover : 5 * qk / 9 < r / 3 := by linarith
  obtain ⟨centers, hcentSub, hcentFinite, hcentCover⟩ :=
    finite_cover_balls_of_compact hCR (by positivity : 0 < qk / 18)
  letI : Fintype centers := hcentFinite.fintype
  let F0 : ℝ := (3 : ℝ) ^ (-(2 * (k : ℤ))) *
    (Real.exp (2 * (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * k))⁻¹
  have hF0 : 0 < F0 := by
    dsimp [F0]
    positivity
  let card : ℝ := (Fintype.card centers : ℝ)
  let Mbig : ℝ := 16 * (card + 1) * Cfast / A
  have hMbig : 0 < Mbig := by
    dsimp [Mbig]
    positivity
  let h1 : ℝ := F0 / (64 * Mbig ^ 2)
  have hh1 : 0 < h1 := by
    dsimp [h1]
    positivity
  let hh : ℝ := h1 / 2
  have hhp : 0 < hh := by dsimp [hh]; positivity
  have hexp : Real.exp (-h1 / hh) ≤ 1 / 4 := by
    dsimp [hh]
    exact aux_tight_prop_exp_half hh1
  obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt
    (16 * Real.exp (((n + 1 : ℕ) : ℝ) / hh) / A)
    (by norm_num : (1 : ℝ) < 2)
  let h2 : ℝ := F0 * (A / (16 * ((p : ℝ) + 1) * Mbig)) ^ 2
  have hh2 : 0 < h2 := by
    dsimp [h2]
    positivity
  let δ : ℝ≥0∞ := ENNReal.ofReal h2
  let h2n : ℝ≥0 := ⟨h2, le_of_lt hh2⟩
  have hδn : (h2n : ℝ≥0∞) = ENNReal.ofReal h2 := by
    exact (ENNReal.ofReal_eq_coe_nnreal (le_of_lt hh2)).symm
  have hδeq : δ = (h2n : ℝ≥0∞) := by
    dsimp [δ]
    exact hδn.symm
  have hδ : 0 < δ := ENNReal.ofReal_pos.mpr hh2
  refine ⟨k, δ, hδ, by
    intro N hN
    obtain ⟨Kc, hKcmeas, hKcnonneg, hKcint, hKcae⟩ :=
      hfastN N (N + j) (0 : SpatialCoordinates d)
    choose Ki hKimeas hKinonneg hKiint hKiae using
      fun i : centers => hfastN N (N - k) (i : SpatialCoordinates d)
    have hscale := aux_tight_prop_scale_lower M k N hN
    have hF0le : F0 ≤
        (3 : ℝ) ^ (2 * (((N - k : ℕ) : ℤ) - (N : ℤ))) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) := by
      simpa [F0] using hscale.2
    let Fi : ℝ :=
      (3 : ℝ) ^ (2 * (((N - k : ℕ) : ℤ) - (N : ℤ))) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k)
    have hfastc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ t : ℝ, 0 < t →
          ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (qj / 18),
            (KN N (omega, x))
                {path : DiffusionPath d |
                  ContinuousPath.exitTime
                    (Metric.ball (0 : SpatialCoordinates d) (qj / 2)) path ≤
                    ENNReal.ofReal t} ≤
              ENNReal.ofReal
                (Kc omega * Real.sqrt (t /
                  ((3 : ℝ) ^ (2 * j) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j)))) := by
      have hexpj : ((N + j : ℕ) : ℤ) - (N : ℤ) = (j : ℤ) := by omega
      have hexp2j : 2 * (((N + j : ℕ) : ℤ) - (N : ℤ)) = 2 * (j : ℤ) := by omega
      simpa [qj, hexpj, hexp2j] using! hKcae
    have hfasti : ∀ i : centers, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ t : ℝ, 0 < t →
          ∀ x ∈ Metric.ball (i : SpatialCoordinates d) (qk / 18),
            (KN N (omega, x))
                {path : DiffusionPath d |
                  ContinuousPath.exitTime
                    (Metric.ball (i : SpatialCoordinates d) (qk / 2)) path ≤
                    ENNReal.ofReal t} ≤
              ENNReal.ofReal (Ki i omega * Real.sqrt (t / Fi)) := by
      intro i
      simpa [qk, Fi, show ((N - k : ℕ) : ℤ) - (N : ℤ) = -(k : ℤ) by omega] using
        hKiae i
    have hfasti_all : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ i : centers, ∀ t : ℝ, 0 < t →
          ∀ x ∈ Metric.ball (i : SpatialCoordinates d) (qk / 18),
            (KN N (omega, x))
                {path : DiffusionPath d |
                  ContinuousPath.exitTime
                    (Metric.ball (i : SpatialCoordinates d) (qk / 2)) path ≤
                    ENNReal.ofReal t} ≤
              ENNReal.ofReal (Ki i omega * Real.sqrt (t / Fi)) := by
      apply ae_all_iff.2
      intro i
      exact hfasti i
    have hfastall : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (∀ t : ℝ, 0 < t →
          ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (qj / 18),
            (KN N (omega, x))
                {path : DiffusionPath d |
                  ContinuousPath.exitTime
                    (Metric.ball (0 : SpatialCoordinates d) (qj / 2)) path ≤
                    ENNReal.ofReal t} ≤
              ENNReal.ofReal
                (Kc omega * Real.sqrt (t /
                  ((3 : ℝ) ^ (2 * j) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))))) ∧
        ∀ i : centers, ∀ t : ℝ, 0 < t →
          ∀ x ∈ Metric.ball (i : SpatialCoordinates d) (qk / 18),
            (KN N (omega, x))
                {path : DiffusionPath d |
                  ContinuousPath.exitTime
                    (Metric.ball (i : SpatialCoordinates d) (qk / 2)) path ≤
                    ENNReal.ofReal t} ≤
              ENNReal.ofReal (Ki i omega * Real.sqrt (t / Fi)) := by
      filter_upwards [hfastc, hfasti_all] with omega hc hi
      exact ⟨hc, hi⟩
    have hLD : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
            (L N omega) := by
      filter_upwards [hLloc] with omega hω
      exact hω N
    let Kω : BilateralField d → Kernel (SpatialCoordinates d)
        (ContinuousPath (SpatialCoordinates d)) := fun omega =>
      (KN N).comap (Prod.mk omega) measurable_prodMk_left
    have hKω : ∀ omega z, Kω omega z = KN N (omega, z) := by
      intro omega z
      rfl
    have hKωmarkov : ∀ omega, IsMarkovKernel (Kω omega) := by
      intro omega
      letI : IsMarkovKernel (KN N) := hKN N
      dsimp only [Kω]
      exact Kernel.IsMarkovKernel.comap _ measurable_prodMk_left
    have hprob_all : ∀ omega y, IsProbabilityMeasure (Kω omega y) := by
      intro omega y
      exact aux_tight_prop_markov_probability (hKωmarkov omega) y
    have hmap : ∀ omega : BilateralField d,
        (∀ I : Finset ℝ≥0, ∀ z : SpatialCoordinates d,
          ((KN N).map (ContinuousPath.finsetEvaluation I)) (omega, z) =
            ((PN N omega).finiteSetKernel I) z) →
        ∀ t : ℝ≥0, ∀ z : SpatialCoordinates d,
        Measure.map (ContinuousPath.eval t) (Kω omega z) = (PN N omega) t z := by
      intro omega hfd t z
      rw [hKω]
      simpa only [Kernel.map_apply] using!
        (SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
          (PN N omega) (KN N (omega, z)) z t
          (by
            have h := hfd ({t} : Finset ℝ≥0) z
            rw [Kernel.map_apply (KN N)
              (ContinuousPath.measurable_finsetEvaluation ({t} : Finset ℝ≥0))] at h
            exact h))
    have hLz : ∀ omega z, Measure.map MarkovProcess.LifetimePath.ofContinuousPath
        (Kω omega z) = L N omega z := by
      intro omega z
      rw [hKω]
      exact hL N omega z
    have h0 : ∀ omega
        (hfd : ∀ I : Finset ℝ≥0, ∀ z : SpatialCoordinates d,
          ((KN N).map (ContinuousPath.finsetEvaluation I)) (omega, z) =
            ((PN N omega).finiteSetKernel I) z)
        (z : SpatialCoordinates d),
        ∀ᵐ p ∂Kω omega z, p 0 = z := by
      intro omega hfd z
      exact aux_tight_fixed_cutoff_soft_start (PN N omega) (fun z => Kω omega z)
        (fun t z => hmap omega hfd t z) z
    have hscale_pos : 0 <
        (3 : ℝ) ^ (2 * (((N - k : ℕ) : ℤ) - (N : ℤ))) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) := by
      apply div_pos
      · exact mul_pos (zpow_pos (by norm_num) _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
      · exact SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k)
    let bad : Set (BilateralField d) :=
      {omega | ENNReal.ofReal Mbig ≤ ∑ i : centers, ENNReal.ofReal (Ki i omega)}
    let KS : BilateralField d → ℝ≥0∞ :=
      fun omega => ∑ i : centers, ENNReal.ofReal (Ki i omega)
    have hKSmeas : Measurable KS := by
      dsimp [KS]
      exact Finset.measurable_sum Finset.univ (fun i hi =>
        ENNReal.measurable_ofReal.comp (hKimeas i))
    have hKS_single : ∀ (i : centers) (omega : BilateralField d),
        ENNReal.ofReal (Ki i omega) ≤ KS omega := by
      intro i omega
      change ENNReal.ofReal (Ki i omega) ≤
        ∑ j : centers, ENNReal.ofReal (Ki j omega)
      exact Finset.single_le_sum (s := (Finset.univ : Finset centers))
        (f := fun j : centers => ENNReal.ofReal (Ki j omega))
        (fun j hj => bot_le) (Finset.mem_univ i)
    have hbadmeas : MeasurableSet bad := by
      dsimp [bad, KS]
      exact measurableSet_le measurable_const hKSmeas
    have hKiM_all : ∀ (omega : BilateralField d), omega ∉ bad →
        ∀ i : centers, Ki i omega ≤ Mbig := by
      intro omega hbad i
      apply (ENNReal.ofReal_le_ofReal_iff hMbig.le).mp
      exact (hKS_single i omega).trans (lt_of_not_ge hbad).le
    let T : ℝ := (n + 1 : ℕ)
    have hT : 0 < T := by dsimp [T]; positivity
    let Tn : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Aexit : Set (DiffusionPath d) :=
      {path | ∃ s : ℝ≥0, s ≤ Tn ∧ path s ∉ CR}
    let Fj : ℝ := (3 : ℝ) ^ (2 * j) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j)
    have hFj : 0 < Fj := by
      dsimp [Fj]
      exact div_pos (mul_pos (by positivity)
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + j))
    have hcontain_sqrt : Real.sqrt (T / Fj) ≤
        Real.sqrt T * qj⁻¹ := by
      have hahom : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) ≤
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ahom_le_ahom_of_le M
          (Nat.le_add_right N j)
      have hratio : 1 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) := by
        apply (le_div_iff₀ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + j))).2
        simpa using hahom
      have hqpow : qj ^ 2 = (3 : ℝ) ^ (2 * j) := by
        dsimp [qj]
        rw [← pow_mul]
        congr 1
        omega
      have hFjq : qj ^ 2 ≤ Fj := by
        calc
          qj ^ 2 = qj ^ 2 * 1 := by ring
          _ ≤ qj ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j)) :=
            mul_le_mul_of_nonneg_left hratio (sq_nonneg qj)
          _ = Fj := by
            rw [hqpow]
            dsimp [Fj]
            ring
      have hdiv : T / Fj ≤ T / qj ^ 2 := by
        exact div_le_div_of_nonneg_left (le_of_lt hT) (by positivity) hFjq
      calc
        Real.sqrt (T / Fj) ≤ Real.sqrt (T / qj ^ 2) :=
          Real.sqrt_le_sqrt hdiv
        _ = Real.sqrt T / Real.sqrt (qj ^ 2) := by
          rw [Real.sqrt_div (le_of_lt hT)]
        _ = Real.sqrt T * qj⁻¹ := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < qj),
            div_eq_mul_inv]
    have hcontain_bound :
        ENNReal.ofReal (Cfast * Real.sqrt (T / Fj)) ≤
          ENNReal.ofReal (A / 16) := by
      apply ENNReal.ofReal_le_ofReal
      have hqjpos : 0 < qj := by positivity
      have hsqrtT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hcontain_sqrt hCfast.le
      have hqjerr' : 16 * Cfast * Real.sqrt T / A < qj := by
        simpa [T] using hqjerr
      have hApos : 0 < A := hA
      have hlast : Cfast * (Real.sqrt T * qj⁻¹) ≤ A / 16 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
        have hineq : 16 * Cfast * Real.sqrt T < A * qj := by
          simpa [mul_comm] using (div_lt_iff₀ hApos).mp hqjerr'
        have hineq' := mul_lt_mul_of_pos_right hineq (inv_pos.mpr hqjpos)
        field_simp [ne_of_gt hqjpos] at hineq' ⊢
        nlinarith
      exact hmul.trans hlast
    have hroot_small_all : ∀ (Fi' : ℝ), F0 ≤ Fi' →
        Real.sqrt (h1 / Fi') ≤ 1 / (8 * Mbig) := by
      intro Fi' hFi'
      simpa only [h1] using
        aux_tight_prop_sqrt_small_bound hF0 hFi' hMbig
    let ρ : ℝ := 5 * qk / 9
    have hρ : 0 < ρ := by
      dsimp [ρ]
      positivity
    have h3ρ : 3 * ρ ≤ r := by
      dsimp [ρ]
      linarith [hqkcover]
    have hcover : ∀ y ∈ CR, ∃ i : centers,
        y ∈ Metric.ball (i : SpatialCoordinates d) (qk / 18) :=
      aux_tight_prop_cover_subtype hcentCover
    have hcoverData : aux_tight_prop_cover_data centers CR (qk / 18)
        (fun i : centers => (i : SpatialCoordinates d)) :=
      ⟨hcover⟩
    have hball : ∀ (y : SpatialCoordinates d) (i : centers),
        y ∈ Metric.ball (i : SpatialCoordinates d) (qk / 18) →
        Metric.ball (i : SpatialCoordinates d) (qk / 2) ⊆
          Metric.ball y ρ := by
      intro y i hy z hz
      rw [Metric.mem_ball] at hy hz ⊢
      calc
        dist z y ≤ dist z (i : SpatialCoordinates d) +
            dist (i : SpatialCoordinates d) y := dist_triangle _ _ _
        _ < qk / 2 + qk / 18 :=
          add_lt_add hz (by simpa [dist_comm] using hy)
        _ = ρ := by dsimp [ρ]; ring
    let U : BilateralField d → ℝ≥0∞ := fun omega =>
      ENNReal.ofReal (Kc omega * Real.sqrt (T / Fj))
    let Cexp : ℝ≥0∞ := ENNReal.ofReal (Real.exp (T / hh)) *
      (ENNReal.ofReal (1 / 2)) ^ p
    let Ctail : ℝ≥0∞ := (p : ℝ≥0∞) *
      ENNReal.ofReal (A / (16 * ((p : ℝ) + 1)))
    have hUmeas : Measurable U := by
      dsimp [U]
      exact ENNReal.measurable_ofReal.comp
        (hKcmeas.mul measurable_const)
    have hImeas : Measurable (bad.indicator (fun _ : BilateralField d =>
        (1 : ℝ≥0∞))) := measurable_const.indicator hbadmeas
    have hgood : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ x ∈ B, (KN N (omega, x))
          (ContinuousPath.modulusSet (n : ℝ≥0) δ
            (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ ≤
          (if omega ∈ bad then 1 else
            (KN N (omega, x)) Aexit +
              ENNReal.ofReal (Real.exp (T / hh)) *
                (ENNReal.ofReal (1 / 2)) ^ p +
              (p : ℝ≥0∞) * ENNReal.ofReal (A / (16 * ((p : ℝ) + 1)))) := by
      have hsmall_bound : ∀ (omega : BilateralField d),
          (∀ (i : centers) (t : ℝ), 0 < t →
            ∀ y ∈ Metric.ball (i : SpatialCoordinates d) (qk / 18),
              (KN N (omega, y)) {path : DiffusionPath d |
                ContinuousPath.exitTime
                  (Metric.ball (i : SpatialCoordinates d) (qk / 2)) path ≤
                ENNReal.ofReal t} ≤
              ENNReal.ofReal (Ki i omega * Real.sqrt (t / Fi))) →
          omega ∉ bad →
        ∀ (i : centers) (y : SpatialCoordinates d),
          y ∈ Metric.ball (i : SpatialCoordinates d) (qk / 18) →
          (KN N (omega, y)) {path | ContinuousPath.exitTime
            (Metric.ball y ρ) path ≤ (δ : ℝ≥0∞)} ≤
            ENNReal.ofReal (A / (16 * ((p : ℝ) + 1))) := by
        intro omega hfa hbad i y hy
        have hFi : F0 ≤ Fi := hF0le
        have hKiM : Ki i omega ≤ Mbig := hKiM_all omega hbad i
        have hfast : (Kω omega y) {path : DiffusionPath d |
            ContinuousPath.exitTime
              (Metric.ball (i : SpatialCoordinates d) (qk / 2)) path ≤
                ENNReal.ofReal h2} ≤
            ENNReal.ofReal (Ki i omega * Real.sqrt (h2 / Fi)) := by
          change (KN N (omega, y)) _ ≤ _
          exact hfa i h2 hh2 y hy
        exact aux_tight_prop_scaled_exit_bound (KN N) (omega, y) y
          (i : SpatialCoordinates d) ρ qk δ F0 Fi A Mbig h2 p (Ki i omega)
          hF0 hFi hA hMbig hKiM (by rfl) (hball y i hy) (by rfl) hfast
      have hgamma : ∀ (omega : BilateralField d),
          (∀ (i : centers) (t : ℝ), 0 < t →
            ∀ y ∈ Metric.ball (i : SpatialCoordinates d) (qk / 18),
              (KN N (omega, y)) {path : DiffusionPath d |
                ContinuousPath.exitTime
                  (Metric.ball (i : SpatialCoordinates d) (qk / 2)) path ≤
                ENNReal.ofReal t} ≤
              ENNReal.ofReal (Ki i omega * Real.sqrt (t / Fi))) →
          omega ∉ bad → ∀ y ∈ CR, ∫⁻ path, aux_tight_fixed_cutoff_restart_wt hh
          (ContinuousPath.exitTime (Metric.ball y ρ) path) ∂KN N (omega, y) ≤
          ENNReal.ofReal (1 / 2) := by
        intro omega hfa hbad
        exact aux_tight_prop_gamma_bound
          (d := d) (KN := KN) (N := N) (omega := omega) (C := CR)
          (centers := centers)
          (center := fun i : centers => (i : SpatialCoordinates d))
          (qk := qk) (rho := ρ) (Fi := Fi) (hh := hh) (h1 := h1)
          (Mbig := Mbig) (Ki := Ki) (hKN := hKN N)
          (hcover := hcoverData.choose) (hball := hball) (hgood := hfa)
          (hexp := hexp) (hMbig := hMbig)
          (hKiM := hKiM_all omega hbad)
          (hroot := hroot_small_all Fi hF0le) (hhpos := hhp) (h1pos := hh1)
      have hAexit : Aexit ⊆ {path : DiffusionPath d |
          ContinuousPath.exitTime
            (Metric.ball (0 : SpatialCoordinates d) (qj / 2)) path ≤
            ENNReal.ofReal T} := by
        dsimp [Aexit]
        exact aux_tight_prop_exit_from_closedBall_complement T (qj / 2) hT
      have hAE := hfastall.and (hLD.and hfdd)
      refine hAE.mono ?_
      intro omega hω
      have hfa := hω.1.1
      have hfa_i := hω.1.2
      have hLDomega := hω.2.1
      have hfdall := hω.2.2
      intro x hx
      by_cases hbad : omega ∈ bad
      · letI : IsMarkovKernel (KN N) := hKN N
        simp only [if_pos hbad]
        letI : IsProbabilityMeasure (KN N (omega, x)) :=
          (hKN N).isProbabilityMeasure _
        exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      · letI : IsMarkovKernel (KN N) := hKN N
        have hfd := hfdall N
        letI : IsMarkovKernel (Kω omega) := hKωmarkov omega
        have hgammaK : ∀ y ∈ CR, ∫⁻ path, aux_tight_fixed_cutoff_restart_wt hh
            (ContinuousPath.exitTime (Metric.ball y ρ) path) ∂Kω omega y ≤
            ENNReal.ofReal (1 / 2) := by
          intro y hy
          simpa only [hKω] using hgamma omega hfa_i hbad y hy
        have hsmallK : ∀ (i : centers) (y : SpatialCoordinates d),
            y ∈ Metric.ball (i : SpatialCoordinates d) (qk / 18) →
            (Kω omega y) {path | ContinuousPath.exitTime
              (Metric.ball y ρ) path ≤
                (h2n : ℝ≥0∞)} ≤
            ENNReal.ofReal (A / (16 * ((p : ℝ) + 1))) := by
          intro i y hy
          rw [hδn]
          exact hsmall_bound omega hfa_i hbad i y hy
        have hsmallAll : ∀ y ∈ CR,
            (Kω omega y) {path | ContinuousPath.exitTime
              (Metric.ball y ρ) path ≤ (h2n : ℝ≥0∞)} ≤
            ENNReal.ofReal (A / (16 * ((p : ℝ) + 1))) := by
          intro y hy
          obtain ⟨i, hyi⟩ := hcover y hy
          exact hsmallK i y hyi
        have hbound := aux_tight_fixed_cutoff_restart_modulus_bound
          (Kω omega) (L N omega) (hLz omega) hLDomega.1
          (h0 omega hfd) CR hCRm hρ Tn h2n hhp
          (ENNReal.ofReal (1 / 2))
          hgammaK
          (ENNReal.ofReal (A / (16 * ((p : ℝ) + 1))))
          hsmallAll p x
        have hmodsub : ContinuousPath.modulusSet (alpha := SpatialCoordinates d)
              Tn (h2n : ℝ≥0∞)
              (ENNReal.ofReal (3 * ρ)) ⊆
            ContinuousPath.modulusSet (alpha := SpatialCoordinates d) (n : ℝ≥0) δ
              (ENNReal.ofReal (1 / (n + 1 : ℕ))) := by
          have hnT : (n : ℝ≥0) ≤ Tn := by
            change (n : ℝ) ≤ T
            dsimp [T]
            norm_num
          have h3ρ' : 3 * ρ ≤ (1 / (n + 1 : ℕ) : ℝ) := by
            simpa [r] using h3ρ
          intro path hp s t hs ht hd
          have hd' : edist s t ≤ (h2n : ℝ≥0∞) := by
            simpa [hδeq] using hd
          exact (hp s t (hs.trans hnT) (ht.trans hnT) hd').trans
            (ENNReal.ofReal_le_ofReal h3ρ')
        have hmain := (measure_mono (by
          intro path hp
          change path ∉ ContinuousPath.modulusSet (n : ℝ≥0) δ
            (ENNReal.ofReal (1 / (n + 1 : ℕ))) at hp
          change path ∉ ContinuousPath.modulusSet (alpha := SpatialCoordinates d)
            Tn (h2n : ℝ≥0∞) (ENNReal.ofReal (3 * ρ))
          intro hsource
          exact hp (hmodsub hsource))).trans hbound
        have hrest : (KN N (omega, x))
              (ContinuousPath.modulusSet (n : ℝ≥0) δ
                (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ ≤
            (KN N (omega, x)) Aexit +
              ENNReal.ofReal (Real.exp (T / hh)) *
                (ENNReal.ofReal (1 / 2)) ^ p +
              (p : ℝ≥0∞) * ENNReal.ofReal (A / (16 * ((p : ℝ) + 1))) := by
          simpa only [hKω, Aexit] using! hmain
        rw [if_neg hbad]
        exact hrest
    have hAexit : Aexit ⊆ {path : DiffusionPath d |
        ContinuousPath.exitTime
          (Metric.ball (0 : SpatialCoordinates d) (qj / 2)) path ≤
          ENNReal.ofReal T} := by
      dsimp [Aexit]
      exact aux_tight_prop_exit_from_closedBall_complement T (qj / 2) hT
    have hAexit_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ x ∈ B, (KN N (omega, x)) Aexit ≤ U omega := by
      filter_upwards [hfastall] with omega hfa
      intro x hx
      have hfast : (KN N (omega, x)) {path : DiffusionPath d |
          ContinuousPath.exitTime
            (Metric.ball (0 : SpatialCoordinates d) (qj / 2)) path ≤
              ENNReal.ofReal T} ≤
          ENNReal.ofReal (Kc omega * Real.sqrt (T / Fj)) := by
        exact hfa.1 T hT x (hBinner hx)
      change (KN N (omega, x)) Aexit ≤
        ENNReal.ofReal (Kc omega * Real.sqrt (T / Fj))
      exact (measure_mono hAexit).trans hfast
    have hKSint :
        (∫⁻ omega, ∑ i : centers, ENNReal.ofReal (Ki i omega)
          ∂(chaosSampleLaw M).toMeasure) ≤
          (Fintype.card centers : ℝ≥0∞) * ENNReal.ofReal Cfast :=
      aux_tight_prop_finite_sum_lintegral_bound
        (chaosSampleLaw M).toMeasure Ki Cfast hKimeas hKiint
    have hbad_measure :
        (chaosSampleLaw M).toMeasure bad ≤ ENNReal.ofReal (A / 16) := by
      have hmark := MeasureTheory.mul_meas_ge_le_lintegral
        (μ := (chaosSampleLaw M).toMeasure) hKSmeas
        (ENNReal.ofReal Mbig)
      have hmark' : ENNReal.ofReal Mbig *
          (chaosSampleLaw M).toMeasure bad ≤
          ∫⁻ omega, KS omega ∂(chaosSampleLaw M).toMeasure := by
        simpa [bad] using hmark
      have hcardreal : (Fintype.card centers : ℝ) * Cfast ≤
          Mbig * (A / 16) := by
        exact aux_tight_prop_card_bound (by positivity) hCfast hA
      have hcard : (Fintype.card centers : ℝ≥0∞) * ENNReal.ofReal Cfast ≤
          ENNReal.ofReal Mbig * ENNReal.ofReal (A / 16) := by
        calc
          (Fintype.card centers : ℝ≥0∞) * ENNReal.ofReal Cfast =
              ENNReal.ofReal ((Fintype.card centers : ℝ) * Cfast) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
              (Nat.cast_nonneg (Fintype.card centers))]
          _ ≤ ENNReal.ofReal (Mbig * (A / 16)) :=
            ENNReal.ofReal_le_ofReal hcardreal
          _ = ENNReal.ofReal Mbig * ENNReal.ofReal (A / 16) := by
            rw [ENNReal.ofReal_mul hMbig.le]
      apply (ENNReal.mul_le_mul_iff_right
        (ENNReal.ofReal_pos.mpr hMbig).ne' ENNReal.ofReal_ne_top).mp
      exact hmark'.trans (hKSint.trans hcard)
    have hUintegral :
        (∫⁻ omega, U omega ∂(chaosSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (A / 16) := by
      calc
        (∫⁻ omega, U omega ∂(chaosSampleLaw M).toMeasure) =
            ENNReal.ofReal (Real.sqrt (T / Fj)) *
              (∫⁻ omega, ENNReal.ofReal (Kc omega)
                ∂(chaosSampleLaw M).toMeasure) := by
          dsimp [U]
          exact aux_tight_prop_lintegral_ofReal_mul
            (chaosSampleLaw M).toMeasure Kc (Real.sqrt (T / Fj))
            (Real.sqrt_nonneg _) hKcmeas
        _ ≤ ENNReal.ofReal (Real.sqrt (T / Fj)) *
            ENNReal.ofReal Cfast :=
          mul_le_mul_of_nonneg_left hKcint bot_le
        _ = ENNReal.ofReal (Cfast * Real.sqrt (T / Fj)) := by
          rw [ENNReal.ofReal_mul' (Real.sqrt_nonneg _), mul_comm]
        _ ≤ ENNReal.ofReal (A / 16) := hcontain_bound
    have hCexp_bound : Cexp ≤ ENNReal.ofReal (A / 16) := by
      change ENNReal.ofReal (Real.exp (T / hh)) * ENNReal.ofReal (1 / 2 : ℝ) ^ p ≤
        ENNReal.ofReal (A / 16)
      exact aux_tight_prop_exp_ennreal_bound hA hhp p hp
    have hCtail_bound : Ctail ≤ ENNReal.ofReal (A / 16) := by
      change (p : ℝ≥0∞) * ENNReal.ofReal (A / (16 * ((p : ℝ) + 1))) ≤
        ENNReal.ofReal (A / 16)
      exact aux_tight_prop_tail_ennreal_bound hA.le p
    have hmajor : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (⨆ x ∈ B, (KN N (omega, x))
          (ContinuousPath.modulusSet (n : ℝ≥0) δ
            (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ) ≤
          (bad.indicator (fun _ : BilateralField d => (1 : ℝ≥0∞))) omega +
            U omega + Cexp + Ctail := by
      filter_upwards [hgood, hAexit_ae] with omega hω hA
      refine iSup₂_le fun x hx => ?_
      have hxω := hω x hx
      by_cases hb : omega ∈ bad
      · simp only [Set.indicator_of_mem hb]
        simp only [if_pos hb] at hxω
        calc
          _ ≤ 1 := hxω
          _ ≤ 1 + U omega := by
            simpa only [add_zero] using
              (add_le_add_right (show (0 : ℝ≥0∞) ≤ U omega from bot_le) 1)
          _ ≤ (1 + U omega) + Cexp := by
            simpa only [add_zero] using
              (add_le_add_right (show (0 : ℝ≥0∞) ≤ Cexp from bot_le)
                (1 + U omega))
          _ ≤ ((1 + U omega) + Cexp) + Ctail := by
            simpa only [add_zero] using
              (add_le_add_right (show (0 : ℝ≥0∞) ≤ Ctail from bot_le)
                ((1 + U omega) + Cexp))
      · simp only [Set.indicator_of_notMem hb, zero_add]
        simp only [if_neg hb] at hxω
        change (KN N) (omega, x) _ ≤
          (KN N) (omega, x) Aexit + Cexp + Ctail at hxω
        have hrest : (KN N (omega, x)) Aexit + Cexp + Ctail ≤
            U omega + Cexp + Ctail :=
          add_le_add (add_le_add (hA x hx) (le_refl _)) (le_refl _)
        exact hxω.trans hrest
    have hpoint :
      (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x))
          (ContinuousPath.modulusSet (n : ℝ≥0) δ
            (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ
          ∂(chaosSampleLaw M).toMeasure) ≤ a := by
      calc
        (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x))
            (ContinuousPath.modulusSet (n : ℝ≥0) δ
              (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ
            ∂(chaosSampleLaw M).toMeasure) ≤
            ∫⁻ omega, (bad.indicator
              (fun _ : BilateralField d => (1 : ℝ≥0∞))) omega +
              U omega + Cexp + Ctail
              ∂(chaosSampleLaw M).toMeasure :=
          lintegral_mono_ae hmajor
        _ = (∫⁻ omega, (bad.indicator
              (fun _ : BilateralField d => (1 : ℝ≥0∞))) omega
              ∂(chaosSampleLaw M).toMeasure) +
              ∫⁻ omega, U omega ∂(chaosSampleLaw M).toMeasure + Cexp + Ctail := by
          erw [lintegral_add_left ((hImeas.add hUmeas).add measurable_const),
            lintegral_add_left (hImeas.add hUmeas),
            lintegral_add_left hImeas]
          rw [lintegral_const, lintegral_const]
          simp only [measure_univ, mul_one]
          rfl
        _ ≤ ENNReal.ofReal (A / 16) + ENNReal.ofReal (A / 16) +
              ENNReal.ofReal (A / 16) + ENNReal.ofReal (A / 16) := by
          exact add_le_add (add_le_add (add_le_add
            ((lintegral_indicator_one_le bad).trans hbad_measure)
            hUintegral) hCexp_bound) hCtail_bound
        _ ≤ a := by
          change ENNReal.ofReal (a.toReal / 16) + ENNReal.ofReal (a.toReal / 16) +
            ENNReal.ofReal (a.toReal / 16) + ENNReal.ofReal (a.toReal / 16) ≤ a
          exact aux_tight_prop_four_quarters ha0 hatop'
    exact hpoint⟩
/-- Proposition `tight:prop-tightness` (Tightness using only Sections 1–7), for the rescaled
untruncated cutoff processes of the common scale coupling (the paper's `3^{-L}X_{T_L t}`, the
family consumed by Theorem `mfd-convergence`).  The conclusion contains that of `lem_tightness`
(take `lintegral_mono` of the measurable majorant `G`), with the paper's `E[sup_{x∈B} …]` read as
a measurable majorant.  The process input is the heat-kernel-free `LocalDiffusion` package;
conservativeness is part of `in_crossing`.  The set of laws `Keta` is stated as closed and
uniformly tight — the paper's "closed and uniformly tight, hence compact": compactness is
Prokhorov's theorem, absent from the Mathlib pin, and follows for any consumer holding the
`hprokhorov` input of `lem_tightness`; the main theorem's cone never uses it. -/
theorem tight_prop
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : Lane4.SobolevFoundationalInput d hd) (W : Lane4.SmallPerturbationInput d)
    (Cp : Lane4.CampanatoInput d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N))
        (hin : in_crossing M H PN KN)
        (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
          (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
        (hL : ∀ N omega x,
          Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
            L N omega x)
        (hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
            (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega)),
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ epsilon : ℝ, 0 < epsilon →
          ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
            (∀ N : ℕ, ∃ G : BilateralField d → ℝ≥0∞, Measurable G ∧
              (∀ omega, ∀ x ∈ B, (KN N (omega, x)) Ksetᶜ ≤ G omega) ∧
              ∫⁻ omega, G omega ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal epsilon) ∧
            ∀ eta : ℝ, 0 < eta →
              ∃ Keta : Set (ProbabilityMeasure (DiffusionPath d)), IsClosed Keta ∧
                (∀ eps : ℝ, 0 < eps → ∃ Kset' : Set (DiffusionPath d), IsCompact Kset' ∧
                  ∀ Pm ∈ Keta, (Pm : Measure (DiffusionPath d)) Kset'ᶜ ≤ ENNReal.ofReal eps) ∧
                ∀ N : ℕ, (chaosSampleLaw M).toMeasure
                    {omega : BilateralField d | ∃ x ∈ B,
                      jointPathProbabilityMeasure (KN N) (hKN N) omega x ∉ Keta}
                  ≤ ENNReal.ofReal eta := by
  obtain ⟨delta0, hdelta0, hfast⟩ := tight_fast_exit hd Jc Pc Xc Sf W Cp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It hM
  intro H hH PN KN hKN hin L hL hLloc B hB epsilon hepsilon
  obtain ⟨Cfast, hCfast, hfastBase⟩ := hfast M Rm Sreg It hM
  have hfastN := hfastBase H hH PN KN hKN hin L hL hLloc
  obtain ⟨Tscale, Cscale, betaScale, hCscale, hbetaScale, hTscaleNat,
    hTscaleInterp, hTscalePos, hbetaScaleBound, hTscaleGrowth⟩ := in_timescale hd M
  have hlocal := tight_fixed_cutoff hd M H hH PN KN hKN hin L hL hLloc
  have hcont := aux_tight_prop_start_continuity hd M H hH PN KN hKN hin hlocal
  have hinParts := hin
  rcases hinParts with ⟨hres, hcons, hfdd⟩
  have hmod_fixed := aux_tight_prop_fixed_modulus_bound M KN hKN B hB hlocal hcont
  have hlarge : ∀ eps : ℝ, 0 < eps →
      ∃ N0 : ℕ, ∃ Klarge : Set (DiffusionPath d), IsCompact Klarge ∧
        ∀ N : ℕ, N0 ≤ N →
          (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Klargeᶜ
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal eps := by
    intro eps heps
    let e : ℝ≥0∞ := ENNReal.ofReal eps
    have he : 0 < e := ENNReal.ofReal_pos.mpr heps
    have hmin : ∀ (k : ℕ) (f : Fin k → ℝ≥0∞),
        (∀ i, 0 < f i) → ∃ q : ℝ≥0∞, 0 < q ∧ ∀ i, q ≤ f i := by
      intro k
      induction k with
      | zero =>
          intro f hf
          exact ⟨1, one_pos, fun i => Fin.elim0 i⟩
      | succ k ih =>
          intro f hf
          obtain ⟨q, hq, hqf⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
          refine ⟨min (f 0) q, lt_min (hf 0) hq, ?_⟩
          intro i
          refine Fin.cases (min_le_left _ _) (fun j => (min_le_right _ _).trans (hqf j)) i
    have hmod_large := aux_tight_prop_hmod_large M H PN KN hKN L hL hLloc hfdd
      Cfast hCfast hfastN B hB
    have hmod : ∀ (n : ℕ) (a : ℝ≥0∞), 0 < a →
        ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ N : ℕ,
          (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x))
            (ContinuousPath.modulusSet (n : ℝ≥0) δ
              (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ
            ∂(chaosSampleLaw M).toMeasure) ≤ a := by
      intro n a ha
      by_cases hatop : a = ⊤
      · exact ⟨1, one_pos, fun N => by
          simpa [hatop] using
            (le_top : (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x))
              (ContinuousPath.modulusSet (n : ℝ≥0) 1
                (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ
              ∂(chaosSampleLaw M).toMeasure) ≤ (⊤ : ℝ≥0∞))⟩
      obtain ⟨k, δL, hδL, hδLbound⟩ := hmod_large n a ha
      choose δN hδN hδNbound using fun i : Fin k => hmod_fixed i n a ha
      obtain ⟨δS, hδS, hδNS⟩ := hmin k δN hδN
      let δ := min δL δS
      have hδ : 0 < δ := lt_min hδL hδS
      refine ⟨δ, hδ, ?_⟩
      intro N
      by_cases hN : k ≤ N
      ·
        have hs : ContinuousPath.modulusSet (n : ℝ≥0) δL
            (ENNReal.ofReal (1 / (n + 1 : ℕ))) ⊆
            ContinuousPath.modulusSet (n : ℝ≥0) δ
              (ENNReal.ofReal (1 / (n + 1 : ℕ))) :=
          aux_tight_prop_modulus_mono (α := SpatialCoordinates d)
            (min_le_left _ _)
        exact (lintegral_mono (fun omega =>
          iSup₂_le fun x hx => (measure_mono (by
            intro path hp hpath
            change path ∉ ContinuousPath.modulusSet (n : ℝ≥0) δ
              (ENNReal.ofReal (1 / (n + 1 : ℕ))) at hp
            exact hp (hs (by simpa using hpath)))).trans
            (le_iSup_of_le x (le_iSup_of_le hx le_rfl)))).trans (hδLbound N hN)
      · have hNk : N < k := Nat.lt_of_not_ge hN
        let i : Fin k := ⟨N, hNk⟩
        have hs : ContinuousPath.modulusSet (n : ℝ≥0) (δN i)
              (ENNReal.ofReal (1 / (n + 1 : ℕ))) ⊆
            ContinuousPath.modulusSet (n : ℝ≥0) δ
              (ENNReal.ofReal (1 / (n + 1 : ℕ))) :=
          aux_tight_prop_modulus_mono (α := SpatialCoordinates d)
            ((min_le_right _ _).trans (hδNS i))
        exact (lintegral_mono (fun omega =>
          iSup₂_le fun x hx => (measure_mono (by
            intro path hp hpath
            change path ∉ ContinuousPath.modulusSet (n : ℝ≥0) δ
              (ENNReal.ofReal (1 / (n + 1 : ℕ))) at hp
            exact hp (hs (by simpa using hpath)))).trans
            (le_iSup_of_le x (le_iSup_of_le hx le_rfl)))).trans (hδNbound i)
    have hmod_all : ∀ n : ℕ, ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ N : ℕ,
        (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x))
          (ContinuousPath.modulusSet (n : ℝ≥0) δ
            (ENNReal.ofReal (1 / (n + 1 : ℕ))))ᶜ
          ∂(chaosSampleLaw M).toMeasure) ≤
          e * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
      intro n
      exact hmod n (e * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹)
        (ENNReal.mul_pos he.ne' (by simp))
    choose δ hδ hδbound using hmod_all
    let rho : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℝ≥0∞)⁻¹)
    have hrho_eq : ∀ n : ℕ, rho n = ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      intro n
      simpa [rho] using aux_tight_prop_rho_eq n
    have hrho : Tendsto rho atTop (𝓝 0) := by
      simpa [rho] using ((tendsto_add_atTop_iff_nat
        (f := fun n : ℕ => (n : ℝ≥0∞)⁻¹) (l := 𝓝 (0 : ℝ≥0∞)) 1).2
        ENNReal.tendsto_inv_nat_nhds_zero)
    let S : ℕ → Set (DiffusionPath d) := fun n =>
      {p | p 0 ∈ B} ∩ ContinuousPath.modulusSet (n : ℝ≥0) (δ n) (rho n)
    have hcompact : IsCompact (⋂ i, S i) := by
      have heq : (⋂ i, S i) = ContinuousPath.moduliSet B δ rho := by
        ext p
        simp only [S, ContinuousPath.moduliSet, Set.mem_iInter, Set.mem_inter_iff,
          Set.mem_setOf_eq]
        constructor
        · intro h
          exact ⟨h 0 |>.1, fun n => (h n).2⟩
        · rintro ⟨h0, hmod⟩ n
          exact ⟨h0, hmod n⟩
      rw [heq]
      exact ContinuousPath.isCompact_moduliSet hB hδ hrho
    have hstart : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
        ∀ x : SpatialCoordinates d, ∀ᵐ p ∂KN N (omega, x), p 0 = x := by
      filter_upwards [hfdd] with omega hfd
      intro N x
      have hmap : ∀ t : ℝ≥0, ∀ y : SpatialCoordinates d,
          Measure.map (ContinuousPath.eval t) (KN N (omega, y)) =
            (PN N omega) t y := by
        intro t y
        simpa only [Kernel.map_apply] using!
          (SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
            (PN N omega) (KN N (omega, y)) y t
            (by
              have h := hfd N ({t} : Finset ℝ≥0) y
              rw [Kernel.map_apply (KN N)
                (ContinuousPath.measurable_finsetEvaluation ({t} : Finset ℝ≥0))] at h
              exact h))
      exact aux_tight_fixed_cutoff_soft_start (PN N omega)
        (fun y => KN N (omega, y)) hmap x
    have hmeas : ∀ N n, AEMeasurable
        (fun omega => ⨆ x ∈ B, (KN N (omega, x)) (S n)ᶜ)
        (chaosSampleLaw M).toMeasure := by
      intro N n
      obtain ⟨D, hDB, hDcount, hDdense⟩ := hB.isSeparable.exists_countable_dense_subset
      letI : Encodable D := hDcount.toEncodable
      have hSn : IsClosed (S n) := by
        exact (hB.isClosed.preimage
          (ContinuousPath.continuous_eval (alpha := SpatialCoordinates d) 0)).inter
          (ContinuousPath.isClosed_modulusSet _ _ _)
      have hmeasD : Measurable (fun omega =>
          ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) (S n)ᶜ) := by
        apply Measurable.iSup
        intro x
        exact (Kernel.measurable_coe (KN N) hSn.measurableSet.compl).comp
          measurable_prodMk_right
      have heq : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (⨆ x ∈ B, (KN N (omega, x)) (S n)ᶜ) =
            ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) (S n)ᶜ := by
        filter_upwards [hcont] with omega hω
        have hs := aux_tight_prop_dense_sup (B := B) (D := D)
          (p := fun x => jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (G := (S n)ᶜ) (hω N) (by simpa using hDdense) hSn.isOpen_compl
        have hs' : (⨆ x ∈ B, (KN N (omega, x)) (S n)ᶜ) ≤
            ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) (S n)ᶜ := by
          simpa only [jointPathProbabilityMeasure] using! hs
        have hs'' : (⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) (S n)ᶜ) ≤
            ⨆ x ∈ B, (KN N (omega, x)) (S n)ᶜ := by
          refine iSup_le fun x => le_iSup_of_le (x : SpatialCoordinates d)
            (le_iSup_of_le (hDB x.property) le_rfl)
        exact le_antisymm hs' hs''
      have heq' : (fun omega =>
          ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) (S n)ᶜ) =ᵐ[
            (chaosSampleLaw M).toMeasure] (fun omega =>
          ⨆ x ∈ B, (KN N (omega, x)) (S n)ᶜ) := by
        filter_upwards [heq] with omega h
        exact h.symm
      exact hmeasD.aemeasurable.congr heq'
    have hstartzero : ∀ N, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (⨆ x ∈ B, (KN N (omega, x))
          {p : DiffusionPath d | p 0 ∉ B}) = 0 := by
      intro N
      filter_upwards [hstart] with omega hω
      apply le_antisymm
      · refine iSup₂_le fun x hx => ?_
        have hsub : {p : DiffusionPath d | p 0 ∉ B} ⊆
            {p : DiffusionPath d | p 0 ≠ x} := by
          intro p hp hp0
          exact hp (hp0 ▸ hx)
        exact (measure_mono hsub).trans (ae_iff.mp (hω N x)).le
      · exact bot_le
    have hbound : ∀ N n,
        (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) (S n)ᶜ
          ∂(chaosSampleLaw M).toMeasure) ≤
          e * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
      intro N n
      have hp : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (⨆ x ∈ B, (KN N (omega, x)) (S n)ᶜ) ≤
            ⨆ x ∈ B, (KN N (omega, x))
              (ContinuousPath.modulusSet (n : ℝ≥0) (δ n) (rho n))ᶜ := by
        filter_upwards [hstartzero N] with omega hzero
        refine iSup₂_le fun x hx => ?_
        have hsub : (S n)ᶜ ⊆
            {p : DiffusionPath d | p 0 ∉ B} ∪
              (ContinuousPath.modulusSet (n : ℝ≥0) (δ n) (rho n))ᶜ := by
          intro p hp
          change ¬ (p 0 ∈ B ∧ p ∈
            ContinuousPath.modulusSet (n : ℝ≥0) (δ n) (rho n)) at hp
          by_cases h0 : p 0 ∉ B
          · exact Or.inl h0
          · have h0' : p 0 ∈ B := not_not.mp h0
            exact Or.inr (by
              intro hm
              exact hp ⟨h0', hm⟩)
        exact (measure_mono hsub).trans ((measure_union_le _ _).trans (by
          have hle : (KN N (omega, x)) {p : DiffusionPath d | p 0 ∉ B} ≤
              (⨆ y : SpatialCoordinates d, ⨆ _ : y ∈ B,
                (KN N (omega, y)) {p : DiffusionPath d | p 0 ∉ B} ) :=
            le_iSup₂_of_le x hx le_rfl
          have h0 : (KN N (omega, x)) {p : DiffusionPath d | p 0 ∉ B} = 0 :=
            le_antisymm (hle.trans hzero.le)
              zero_le
          have hmodsup : (KN N (omega, x))
              (ContinuousPath.modulusSet (n : ℝ≥0) (δ n) (rho n))ᶜ ≤
              (⨆ y : SpatialCoordinates d, ⨆ _ : y ∈ B,
                (KN N (omega, y))
                  (ContinuousPath.modulusSet (n : ℝ≥0) (δ n) (rho n))ᶜ) :=
            le_iSup₂_of_le x hx le_rfl
          calc
            _ ≤ 0 + (⨆ y : SpatialCoordinates d, ⨆ _ : y ∈ B,
                (KN N (omega, y))
                  (ContinuousPath.modulusSet (n : ℝ≥0) (δ n) (rho n))ᶜ) :=
              add_le_add h0.le hmodsup
            _ = _ := zero_add _))
      exact (lintegral_mono_ae hp).trans (by
        simpa [hrho_eq n] using hδbound n N)
    let aa : ℕ → ℝ≥0∞ := fun n => e * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹
    have hbudget : (∑' i : ℕ, aa i) ≤ e := by
      exact le_of_eq (aux_tight_prop_tsum_geometric_half e)
    obtain ⟨Klarge, hKlarge, hKbound⟩ :=
      aux_tight_prop_countable_assembly
        (chaosSampleLaw M).toMeasure (fun N omega x => KN N (omega, x)) B S aa e
        hcompact hmeas hbound hbudget
    exact ⟨0, Klarge, hKlarge, fun N _ => hKbound N⟩
  have hpath_annealed : ∀ eps : ℝ, 0 < eps →
      ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
        (∀ N : ℕ, AEMeasurable
            (fun omega => ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ)
            (chaosSampleLaw M).toMeasure ∧
          ∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
            ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps) := by
    intro eps heps
    obtain ⟨N0, Klarge, hKlarge, hKlarge_bound⟩ := hlarge (eps / 2) (by positivity)
    choose Ksmall hKsmall hKsmall_bound using fun n : Fin N0 =>
      aux_tight_prop_finite_cutoff hd M H hH PN KN hKN hin hlocal n.1 B hB
        (eps / 2) (by positivity)
    let Kset : Set (DiffusionPath d) :=
      Klarge ∪ ⋃ n : Fin N0, Ksmall n
    have hKset : IsCompact Kset := by
      exact hKlarge.union (isCompact_iUnion fun n => hKsmall n)
    have hsup_meas : ∀ (K : Set (DiffusionPath d)), IsCompact K → ∀ N : ℕ,
        AEMeasurable (fun omega => ⨆ x ∈ B, (KN N (omega, x)) Kᶜ)
          (chaosSampleLaw M).toMeasure := by
      intro K hK N
      obtain ⟨D, hDB, hDcount, hDdense⟩ := hB.isSeparable.exists_countable_dense_subset
      letI : Encodable D := hDcount.toEncodable
      have hmeas : Measurable (fun omega =>
          ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) Kᶜ) := by
        apply Measurable.iSup
        intro x
        exact (Kernel.measurable_coe (KN N) hK.isClosed.measurableSet.compl).comp
          measurable_prodMk_right
      have heq : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (⨆ x ∈ B, (KN N (omega, x)) Kᶜ) =
            ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) Kᶜ := by
        filter_upwards [hcont] with omega hω
        have hωN := hω N
        have hs := aux_tight_prop_dense_sup (B := B) (D := D)
          (p := fun x => jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          hωN hDdense hK.isClosed.isOpen_compl
        have hs' : (⨆ x ∈ B, (KN N (omega, x)) Kᶜ) ≤
            ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) Kᶜ := by
          simpa only [jointPathProbabilityMeasure] using! hs
        have hs'' : (⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) Kᶜ) ≤
            ⨆ x ∈ B, (KN N (omega, x)) Kᶜ := by
          refine iSup_le fun x => le_iSup_of_le (x : SpatialCoordinates d)
            (le_iSup_of_le (hDB x.property) le_rfl)
        exact le_antisymm hs' hs''
      have heq' : (fun omega => ⨆ x : D, (KN N (omega, (x : SpatialCoordinates d))) Kᶜ) =ᵐ[
          (chaosSampleLaw M).toMeasure]
          (fun omega => ⨆ x ∈ B, (KN N (omega, x)) Kᶜ) := by
        filter_upwards [heq] with omega h
        exact h.symm
      exact hmeas.aemeasurable.congr heq'
    refine ⟨Kset, hKset, ?_⟩
    intro N
    refine ⟨hsup_meas Kset hKset N, ?_⟩
    by_cases hN : N0 ≤ N
    · have hsub : Klarge ⊆ Kset := Set.subset_union_left
      calc
        (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
            ∂(chaosSampleLaw M).toMeasure) ≤
          ∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Klargeᶜ
            ∂(chaosSampleLaw M).toMeasure := by
              apply lintegral_mono
              intro omega
              refine iSup₂_le fun x hx => ?_
              exact (measure_mono (by
                intro path hpath hKlarge
                exact hpath (hsub hKlarge))).trans
                (le_iSup_of_le x (le_iSup_of_le hx le_rfl))
        _ ≤ ENNReal.ofReal (eps / 2) := hKlarge_bound N hN
        _ ≤ ENNReal.ofReal eps := ENNReal.ofReal_le_ofReal (by linarith)
    · have hNlt : N < N0 := Nat.lt_of_not_ge hN
      let n : Fin N0 := ⟨N, hNlt⟩
      have hsub : Ksmall n ⊆ Kset :=
        Set.Subset.trans (Set.subset_iUnion (fun j : Fin N0 => Ksmall j) n)
          Set.subset_union_right
      calc
        (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
            ∂(chaosSampleLaw M).toMeasure) ≤
          ∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) (Ksmall n)ᶜ
            ∂(chaosSampleLaw M).toMeasure := by
              apply lintegral_mono
              intro omega
              refine iSup₂_le fun x hx => ?_
              exact (measure_mono (by
                intro path hpath hKsmall'
                exact hpath (hsub hKsmall'))).trans
                (le_iSup_of_le x (le_iSup_of_le hx le_rfl))
        _ ≤ ENNReal.ofReal (eps / 2) := hKsmall_bound n
        _ ≤ ENNReal.ofReal eps := ENNReal.ofReal_le_ofReal (by linarith)
  have hpath_all : ∀ eps : ℝ, 0 < eps →
      ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
        (∀ N : ℕ, ∃ G : BilateralField d → ℝ≥0∞, Measurable G ∧
          (∀ omega, ∀ x ∈ B, (KN N (omega, x)) Ksetᶜ ≤ G omega) ∧
          ∫⁻ omega, G omega ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps) := by
    intro eps heps
    obtain ⟨Kset, hKset, hKbound⟩ := hpath_annealed eps heps
    refine ⟨Kset, hKset, ?_⟩
    intro N
    let f : BilateralField d → ℝ≥0∞ := fun omega =>
      ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
    have hpoint : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ x ∈ B, (KN N (omega, x)) Ksetᶜ ≤ f omega :=
      Filter.Eventually.of_forall (fun omega x hx =>
        le_iSup_of_le x (le_iSup_of_le hx le_rfl))
    have hprob : ∀ omega x, (KN N (omega, x)) Set.univ ≤ 1 := by
      intro omega x
      letI : IsProbabilityMeasure (KN N (omega, x)) :=
        (hKN N).isProbabilityMeasure (omega, x)
      simp
    exact aux_tight_prop_measurable_majorant
      (chaosSampleLaw M).toMeasure (fun omega x => KN N (omega, x)) B Kset f
      (hKbound N).1 hpoint (hKbound N).2 hprob
  obtain ⟨Kset, hKset, hKbound⟩ := hpath_all epsilon hepsilon
  refine ⟨Kset, hKset, hKbound, ?_⟩
  exact aux_tight_prop_random_laws M KN hKN B hpath_all

end Paper

