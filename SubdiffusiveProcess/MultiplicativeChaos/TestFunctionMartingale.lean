module

public import SubdiffusiveProcess.MultiplicativeChaos.WeightedIndep
public import SubdiffusiveProcess.MultiplicativeChaos.TriadicGrid
public import Mathlib.Topology.ContinuousMap.CompactlySupported

@[expose] public section

/-!
# The test-function masses are martingales

`mfd:lem-chaos-moments` gives the martingale property of the cutoff measures
for CUBE masses.  Vague convergence is tested against compactly supported
continuous functions, so the same property is needed for those.  The cutoff
measure has the explicit density `exp (H omega ·) * fineDensity M N omega ·`,
whose pointwise martingale property is
`infraredWeightedFineDensity_martingale`; this file integrates that statement
in `x`, which is a Fubini step for the conditional expectation.
-/

open Filter MeasureTheory ProbabilityTheory Topology

open scoped CompactlySupported ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- The integral of a test function against the cutoff measure, written as a
Lebesgue integral against the weighted density. -/
theorem integral_weightedChaosCutoff_eq
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d) (f : SpatialCoordinates d → ℝ) :
    ∫ x, f x ∂(weightedChaosCutoff M H N omega)
      = ∫ x, (Real.exp (H omega x) * fineDensity M N omega x) * f x ∂volume := by
  have hcont : Continuous
      (fun x => Real.exp (H omega x) * fineDensity M N omega x) :=
    (Real.continuous_exp.comp (H omega).continuous).mul
      (continuous_fineDensity M N omega)
  have hmeas : Measurable (fun x =>
      ENNReal.ofReal (Real.exp (H omega x) * fineDensity M N omega x)) :=
    hcont.measurable.ennreal_ofReal
  have hfin : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
      ENNReal.ofReal (Real.exp (H omega x) * fineDensity M N omega x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [weightedChaosCutoff, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hnn : (0 : ℝ) ≤ Real.exp (H omega x) * fineDensity M N omega x :=
    (mul_pos (Real.exp_pos _) (fineDensity_pos M N omega x)).le
  show (ENNReal.ofReal (Real.exp (H omega x) * fineDensity M N omega x)).toReal • f x
    = Real.exp (H omega x) * fineDensity M N omega x * f x
  rw [ENNReal.toReal_ofReal hnn, smul_eq_mul]

/-- Adaptedness of the test-function masses to the fine filtration. -/
theorem weightedChaosCutoff_test_adapted
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (f : SpatialCoordinates d → ℝ) (hfc : Continuous f) :
    Adapted (conditionalFineFiltration H hH)
      (fun N omega ↦ ∫ x, f x ∂(weightedChaosCutoff M H N omega)) := by
  intro N
  let Φ : BilateralField d → (j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) :=
    fun omega j ↦ omega (-(Int.ofNat j))
  let Y : Type := C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))
  let Ψ : BilateralField d → Y := fun omega ↦ (H omega, Φ omega)
  let g : Y × SpatialCoordinates d → ℝ :=
    fun p ↦ Real.exp (p.1.1 p.2) * Real.exp ((∑ j : Fin (N + 1), p.1.2 j p.2) -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) * f p.2
  have hA : Measurable (fun p :
      (C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))) ×
        SpatialCoordinates d ↦ p.1.1 p.2) := by fun_prop
  have hB : Measurable (fun p :
      (C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))) ×
        SpatialCoordinates d ↦
      (∑ j : Fin (N + 1), p.1.2 j p.2) - (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    fun_prop
  have hg : StronglyMeasurable g := by
    have hgm : Measurable g := by
      unfold g
      exact ((hA.exp).mul (hB.exp)).mul (hfc.measurable.comp measurable_snd)
    exact hgm.stronglyMeasurable
  have hgmass : StronglyMeasurable (fun y : Y ↦ ∫ x, g (y, x)) :=
    hg.integral_prod_right'
  have hΦmeas : Measurable[(conditionalFineFiltration H hH) N] Φ := by
    have heq : (MeasurableSpace.comap Φ
        (inferInstance : MeasurableSpace ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)))) =
        ⨆ j : Fin (N + 1), MeasurableSpace.comap
          (fun omega : BilateralField d ↦ omega (-(Int.ofNat j))) inferInstance := by
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
        MeasurableSpace.comap_comp]
      rfl
    have hle : MeasurableSpace.comap Φ inferInstance ≤ (conditionalFineFiltration H hH) N := by
      change MeasurableSpace.comap Φ inferInstance ≤
        MeasurableSpace.comap H inferInstance ⊔
          ⨆ j : Fin (N + 1), MeasurableSpace.comap
            (fun omega : BilateralField d ↦ omega (-(Int.ofNat j))) inferInstance
      rw [heq]
      exact le_sup_right
    exact (comap_measurable Φ).mono hle le_rfl
  have hHmeas : Measurable[(conditionalFineFiltration H hH) N] H := by
    have hle : MeasurableSpace.comap H inferInstance ≤ (conditionalFineFiltration H hH) N := by
      change MeasurableSpace.comap H inferInstance ≤
        MeasurableSpace.comap H inferInstance ⊔
          ⨆ j : Fin (N + 1), MeasurableSpace.comap
            (fun omega : BilateralField d ↦ omega (-(Int.ofNat j))) inferInstance
      exact le_sup_left
    exact (comap_measurable H).mono hle le_rfl
  have hΨmeas : Measurable[(conditionalFineFiltration H hH) N] Ψ :=
    hHmeas.prodMk hΦmeas
  have hsum : ∀ (omega : BilateralField d) (x : SpatialCoordinates d),
      (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) x) =
        ∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x := by
    intro omega x
    refine Finset.sum_bij (s := Finset.range (N + 1))
      (t := (Finset.univ : Finset (Fin (N + 1))))
      (fun n hn ↦ ⟨n, by simpa using hn⟩) ?_ ?_ ?_ ?_
    · intro n hn
      simp
    · intro a ha b hb hab
      exact congrArg Fin.val hab
    · intro b hb
      exact ⟨b.1, by simpa using b.2, by simp⟩
    · intro n hn
      rfl
  have hfun : (fun omega : BilateralField d ↦
      ∫ x, f x ∂(weightedChaosCutoff M H N omega))
      = (fun omega ↦ ∫ x, g (Ψ omega, x)) := by
    funext omega
    rw [integral_weightedChaosCutoff_eq]
    apply integral_congr_ae
    filter_upwards with x
    simp only [g, Ψ, Φ, fineDensity, finePotential]
    rw [hsum omega x]
  change Measurable[(conditionalFineFiltration H hH) N]
    (fun omega : BilateralField d ↦ ∫ x, f x ∂(weightedChaosCutoff M H N omega))
  rw [hfun]
  exact (hgmass.comp_measurable hΨmeas).measurable

/-- The weighted density is integrable on any cube. -/
theorem weightedFineDensity_integrableOn_cube
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x => Real.exp (H omega x) * fineDensity M N omega x)
      (centeredCube z r hr : Set (SpatialCoordinates d)) volume := by
  have hcont : Continuous
      (fun x => Real.exp (H omega x) * fineDensity M N omega x) :=
    (Real.continuous_exp.comp (H omega).continuous).mul
      (continuous_fineDensity M N omega)
  have hK : IsCompact (Metric.closedBall z (r / 2)) := isCompact_closedBall z (r / 2)
  have hloc := (hcont.locallyIntegrable (μ := volume)).integrableOn_isCompact hK
  refine hloc.mono_set ?_
  rw [centeredCube_coe_eq_ball]
  exact Metric.ball_subset_closedBall

/-- The test-function masses are a martingale, for a test function supported in
a cube and bounded by `C`. -/
theorem weightedChaosCutoff_test_martingale
    {d : ℕ} (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (f : SpatialCoordinates d → ℝ) (hfc : Continuous f)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hsupp : ∀ x, x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) → f x = 0)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Martingale (fun N omega => ∫ x, f x ∂(weightedChaosCutoff M H N omega))
      (conditionalFineFiltration H hH.1) (chaosSampleLaw M).toMeasure := by
  classical
  set P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hP
  set Q : Set (SpatialCoordinates d) :=
    (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  have hfmble : AEStronglyMeasurable f volume := hfc.aestronglyMeasurable
  have hrestrict : ∀ (N : ℕ) (omega : BilateralField d),
      ∫ x, f x ∂(weightedChaosCutoff M H N omega)
        = ∫ x in Q, (Real.exp (H omega x) * fineDensity M N omega x) * f x ∂volume := by
    intro N omega
    rw [integral_weightedChaosCutoff_eq]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    rw [hsupp x hx, mul_zero]
  have hadp := weightedChaosCutoff_test_adapted M H hH.1 f hfc
  have hint : ∀ N : ℕ, Integrable
      (fun omega => ∫ x, f x ∂(weightedChaosCutoff M H N omega)) P := by
    intro N
    have hcube := weightedChaosCutoff_centeredCube_integrable hd M H hH N z r hr
    refine Integrable.mono' (hcube.const_mul C) ?_ ?_
    · exact ((hadp N).mono ((conditionalFineFiltration H hH.1).le N) le_rfl).aestronglyMeasurable
    · filter_upwards with omega
      rw [hrestrict N omega,
        weightedChaosCutoff_centeredCube_toReal_eq_integral M H N omega z r hr]
      have hdint := weightedFineDensity_integrableOn_cube M H N omega z r hr
      have hbnd : ∀ x, ‖(Real.exp (H omega x) * fineDensity M N omega x) * f x‖
          ≤ C * ‖Real.exp (H omega x) * fineDensity M N omega x‖ := by
        intro x
        rw [norm_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
      calc ‖∫ x in Q, (Real.exp (H omega x) * fineDensity M N omega x) * f x ∂volume‖
          ≤ ∫ x in Q, ‖(Real.exp (H omega x) * fineDensity M N omega x) * f x‖ ∂volume :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in Q, C * ‖Real.exp (H omega x) * fineDensity M N omega x‖ ∂volume := by
            have hprodmble : AEStronglyMeasurable
                (fun x => (Real.exp (H omega x) * fineDensity M N omega x) * f x)
                (volume.restrict Q) :=
              (hdint.aestronglyMeasurable).mul hfmble.restrict
            have hprod : IntegrableOn
                (fun x => (Real.exp (H omega x) * fineDensity M N omega x) * f x)
                Q volume :=
              Integrable.mono' (hdint.norm.const_mul C) hprodmble
                (Filter.Eventually.of_forall hbnd)
            exact integral_mono hprod.norm (hdint.norm.const_mul C) (fun x => hbnd x)
        _ = C * ∫ x in Q, ‖Real.exp (H omega x) * fineDensity M N omega x‖ ∂volume := by
            rw [integral_const_mul]
        _ = C * ∫ x in Q, Real.exp (H omega x) * fineDensity M N omega x ∂volume := by
            congr 1
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            exact Real.norm_of_nonneg
              (mul_pos (Real.exp_pos _) (fineDensity_pos M N omega x)).le
  refine martingale_of_setIntegral_eq_succ (fun N => (hadp N).stronglyMeasurable) hint ?_
  intro N S hS
  have hprodS : ∀ m : ℕ, Integrable
      (fun q : BilateralField d × SpatialCoordinates d =>
        (Real.exp (H q.1 q.2) * fineDensity M m q.1 q.2) * f q.2)
      ((P.restrict S).prod (volume.restrict Q)) := by
    intro m
    have hfull := weightedFineDensity_joint_integrable hd M H hH m z r hr
    have hQfull : Integrable
        (fun q : BilateralField d × SpatialCoordinates d =>
          Real.exp (H q.1 q.2) * fineDensity M m q.1 q.2)
        ((P.prod volume).restrict (Set.univ ×ˢ Q)) := by
      rw [← Measure.prod_restrict (Set.univ : Set (BilateralField d)) Q,
        Measure.restrict_univ]
      exact hfull
    have hSQ : Integrable
        (fun q : BilateralField d × SpatialCoordinates d =>
          Real.exp (H q.1 q.2) * fineDensity M m q.1 q.2)
        ((P.prod volume).restrict (S ×ˢ Q)) := by
      have hrestricted := hQfull.restrict (s := S ×ˢ Q)
      rw [Measure.restrict_restrict_of_subset] at hrestricted
      · exact hrestricted
      · intro q hq
        exact ⟨Set.mem_univ _, hq.2⟩
    rw [Measure.prod_restrict S Q]
    have hmblej : AEStronglyMeasurable
        (fun q : BilateralField d × SpatialCoordinates d =>
          (Real.exp (H q.1 q.2) * fineDensity M m q.1 q.2) * f q.2)
        ((P.prod volume).restrict (S ×ˢ Q)) :=
      hSQ.aestronglyMeasurable.mul
        (hfc.comp continuous_snd).aestronglyMeasurable
    refine Integrable.mono' (hSQ.norm.const_mul C) hmblej ?_
    refine Filter.Eventually.of_forall (fun q => ?_)
    rw [norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC q.2) (norm_nonneg _)
  have hswap : ∀ m : ℕ,
      (∫ omega in S, ∫ x in Q,
          (Real.exp (H omega x) * fineDensity M m omega x) * f x ∂volume ∂P) =
        ∫ x in Q, ∫ omega in S,
          (Real.exp (H omega x) * fineDensity M m omega x) * f x ∂P ∂volume := by
    intro m
    simpa using integral_integral_swap
      (f := fun omega x => (Real.exp (H omega x) * fineDensity M m omega x) * f x)
      (hprodS m)
  have hpoint : ∀ x : SpatialCoordinates d,
      (∫ omega in S, (Real.exp (H omega x) * fineDensity M N omega x) * f x ∂P) =
        ∫ omega in S,
          (Real.exp (H omega x) * fineDensity M (N + 1) omega x) * f x ∂P := by
    intro x
    rw [integral_mul_const, integral_mul_const]
    congr 1
    exact Martingale.setIntegral_eq
      (infraredWeightedFineDensity_martingale hd M H hH x) (Nat.le_succ N) hS
  have hspatial :
      (∫ x in Q, ∫ omega in S,
          (Real.exp (H omega x) * fineDensity M N omega x) * f x ∂P ∂volume) =
        ∫ x in Q, ∫ omega in S,
          (Real.exp (H omega x) * fineDensity M (N + 1) omega x) * f x ∂P ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => hpoint x)
  simp_rw [hrestrict N, hrestrict (N + 1)]
  rw [hswap N, hspatial, ← hswap (N + 1)]

/-- **The test-function masses are nonnegative martingales.**  This is the
form the vague-limit argument consumes. -/
theorem chaos_test_martingale
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (f : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    Martingale (fun N omega => ∫ x, f x ∂(weightedChaosCutoff M H N omega))
        (conditionalFineFiltration H hH.1) (chaosSampleLaw M).toMeasure ∧
      ∀ (N : ℕ) (omega : BilateralField d),
        0 ≤ ∫ x, f x ∂(weightedChaosCutoff M H N omega) := by
  classical
  refine ⟨?_, fun N omega => integral_nonneg (fun x => hf x)⟩
  have hcs : HasCompactSupport (f : SpatialCoordinates d → ℝ) := f.hasCompactSupport
  have hfc : Continuous (f : SpatialCoordinates d → ℝ) := map_continuous f
  obtain ⟨R0, hR0⟩ := hcs.isBounded.subset_closedBall (0 : SpatialCoordinates d)
  set R : ℝ := max R0 1 with hRdef
  have hR1 : (1 : ℝ) ≤ R := le_max_right _ _
  have hR : tsupport (f : SpatialCoordinates d → ℝ) ⊆
      Metric.closedBall (0 : SpatialCoordinates d) R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hrpos : (0 : ℝ) < 2 * (R + 1) := by linarith
  have hsupp : ∀ x, x ∉ (centeredCube (0 : SpatialCoordinates d) (2 * (R + 1)) hrpos :
      Set (SpatialCoordinates d)) → f x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport ?_
    intro hmem
    refine hx ?_
    rw [centeredCube_coe_eq_ball]
    have hdx : dist x (0 : SpatialCoordinates d) ≤ R :=
      Metric.mem_closedBall.mp (hR hmem)
    refine Metric.mem_ball.mpr ?_
    have hhalf : 2 * (R + 1) / 2 = R + 1 := by ring
    rw [hhalf]
    linarith
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hfc
  exact weightedChaosCutoff_test_martingale hd M H hH (f : SpatialCoordinates d → ℝ)
    hfc 0 (2 * (R + 1)) hrpos hsupp C hC

end SubdiffusiveProcess
