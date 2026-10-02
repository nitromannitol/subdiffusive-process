import SubdiffusiveProcess.Probability.FineDensityMartingale
import SubdiffusiveProcess.Main.ChaosCutoff
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

theorem aux_dedup_d079_cube_mass_toReal_eq_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ((chaosCutoff M N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        fineDensity M N omega x := by
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let f : SpatialCoordinates d → ℝ≥0∞ := ENNReal.ofReal ∘ fineDensity M N omega
  have hf : Measurable f := by
    dsimp [f]
    apply Measurable.ennreal_ofReal
    unfold fineDensity finePotential
    fun_prop
  have htop : ∀ᵐ x ∂(volume.restrict Q), f x < ∞ := by
    filter_upwards with x
    exact ENNReal.coe_lt_top
  have hset := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ := volume) hf htop (fun _ : SpatialCoordinates d => (1 : ℝ))
      (show MeasurableSet Q by
        dsimp [Q]
        exact (centeredCube z r hr).isOpen.measurableSet)
  change ((volume.withDensity f) Q).toReal = _
  have hconst : (∫ x in Q, (1 : ℝ) ∂volume.withDensity f) =
      ((volume.withDensity f) Q).toReal := by
    rw [setIntegral_const, Measure.real, smul_eq_mul, mul_one]
  rw [← hconst, hset]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [f]
  rw [ENNReal.toReal_ofReal]
  · simp
  · unfold fineDensity
    exact Real.exp_pos _ |>.le

private theorem cube_mass_toReal_eq_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ((chaosCutoff M N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        fineDensity M N omega x := by exact SubdiffusiveProcess.aux_dedup_d079_cube_mass_toReal_eq_integral (d := d) (M := M) (N := N) (omega := omega) (z := z) (r := r) (hr := hr)

private theorem cube_mass_integrable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Integrable
      (fun omega : BilateralField d =>
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          fineDensity M N omega x)
      (chaosSampleLaw M).toMeasure := by
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hjoint : StronglyMeasurable
      (fun p : BilateralField d × SpatialCoordinates d =>
        fineDensity M N p.1 p.2) := by
    unfold fineDensity finePotential
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun p : BilateralField d × SpatialCoordinates d =>
        fineDensity M N p.1 p.2) (P.prod (volume.restrict Q)) :=
    hjoint.aestronglyMeasurable
  have hpoint : ∀ x : SpatialCoordinates d,
      Integrable (fun omega : BilateralField d => fineDensity M N omega x) P := by
    intro x
    apply integrable_of_integral_eq_one
    exact integral_fineDensity_chaosSampleLaw M N x
  have hQfin : volume Q ≠ ∞ := by
    dsimp [Q]
    rw [centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hnorm : Integrable
      (fun x : SpatialCoordinates d =>
        ∫ omega : BilateralField d, ‖fineDensity M N omega x‖ ∂P)
      (volume.restrict Q) := by
    have heq : (fun x : SpatialCoordinates d =>
        ∫ omega : BilateralField d, ‖fineDensity M N omega x‖ ∂P) =ᵐ[volume.restrict Q]
        (fun _ => (1 : ℝ)) := by
      filter_upwards with x
      rw [← integral_fineDensity_chaosSampleLaw M N x]
      apply integral_congr_ae
      filter_upwards with omega
      exact Real.norm_of_nonneg (Real.exp_pos _ |>.le)
    exact (integrableOn_const hQfin).congr heq.symm
  have hprod : Integrable
      (fun p : BilateralField d × SpatialCoordinates d =>
        fineDensity M N p.1 p.2) (P.prod (volume.restrict Q)) := by
    rw [integrable_prod_iff' hmeas]
    exact ⟨ae_of_all _ hpoint, hnorm⟩
  have hmass := hprod.integral_prod_left
  simpa [Q] using hmass

private theorem cube_mass_adapted
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Adapted (conditionalFineFiltration (fun _ ↦ 0) measurable_const)
      (fun N omega ↦ ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
  intro N
  let Φ : BilateralField d → (j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) :=
    fun omega j ↦ omega (-(Int.ofNat j))
  let g : ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) ×
      SpatialCoordinates d → ℝ :=
    fun p ↦ Real.exp (∑ j : Fin (N + 1), p.1 j p.2 -
      (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hg : StronglyMeasurable g := by
    unfold g
    fun_prop
  have hgmass : StronglyMeasurable
      (fun y : (j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) =>
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g (y, x)) := by
    exact hg.integral_prod_right'
  have hΦ : Measurable Φ := by
    exact measurable_pi_lambda _ (fun j => measurable_pi_apply (-(Int.ofNat j)))
  have hfil : (conditionalFineFiltration (fun _ ↦ 0) measurable_const) N =
      (inferInstance : MeasurableSpace
        ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))).comap Φ := by
    change (MeasurableSpace.comap (fun _ : BilateralField d =>
      (0 : C(SpatialCoordinates d, ℝ))) inferInstance ⊔
        ⨆ j : Fin (N + 1), MeasurableSpace.comap
          (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance) = _
    rw [MeasurableSpace.comap_const, bot_sup_eq]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp]
    rfl
  have hfun : (fun omega : BilateralField d =>
      ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) =
      (fun omega => ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        g (Φ omega, x)) := by
    funext omega
    rw [cube_mass_toReal_eq_integral M N omega z r hr]
    apply integral_congr_ae
    filter_upwards with x
    simp only [g, Φ, fineDensity, finePotential]
    have hsum : (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) x) =
        ∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x := by
      refine Finset.sum_bij (s := Finset.range (N + 1))
        (t := (Finset.univ : Finset (Fin (N + 1))))
        (fun n hn => ⟨n, by simpa using hn⟩) ?_ ?_ ?_ ?_
      · intro n hn
        simp
      · intro a ha b hb hab
        exact congrArg Fin.val hab
      · intro b hb
        exact ⟨b.1, by simpa using b.2, by simp⟩
      · intro n hn
        rfl
    rw [hsum]
  change StronglyMeasurable[(conditionalFineFiltration (fun _ ↦ 0) measurable_const) N]
    (fun omega : BilateralField d => ((chaosCutoff M N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
  rw [hfil, hfun]
  exact (hgmass.comp_measurable (comap_measurable Φ))

private theorem cube_mass_joint_integrable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Integrable
      (fun p : BilateralField d × SpatialCoordinates d =>
        fineDensity M N p.1 p.2)
      ((chaosSampleLaw M).toMeasure.prod
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hjoint : StronglyMeasurable
      (fun p : BilateralField d × SpatialCoordinates d =>
        fineDensity M N p.1 p.2) := by
    unfold fineDensity finePotential
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun p : BilateralField d × SpatialCoordinates d =>
        fineDensity M N p.1 p.2) (P.prod (volume.restrict Q)) :=
    hjoint.aestronglyMeasurable
  have hpoint : ∀ x : SpatialCoordinates d,
      Integrable (fun omega : BilateralField d => fineDensity M N omega x) P := by
    intro x
    apply integrable_of_integral_eq_one
    exact integral_fineDensity_chaosSampleLaw M N x
  have hQfin : volume Q ≠ ∞ := by
    dsimp [Q]
    rw [centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hnorm : Integrable
      (fun x : SpatialCoordinates d =>
        ∫ omega : BilateralField d, ‖fineDensity M N omega x‖ ∂P)
      (volume.restrict Q) := by
    have heq : (fun x : SpatialCoordinates d =>
        ∫ omega : BilateralField d, ‖fineDensity M N omega x‖ ∂P) =ᵐ[volume.restrict Q]
        (fun _ => (1 : ℝ)) := by
      filter_upwards with x
      rw [← integral_fineDensity_chaosSampleLaw M N x]
      apply integral_congr_ae
      filter_upwards with omega
      exact Real.norm_of_nonneg (Real.exp_pos _ |>.le)
    exact (integrableOn_const hQfin).congr heq.symm
  rw [integrable_prod_iff' hmeas]
  exact ⟨ae_of_all _ hpoint, hnorm⟩

theorem chaosCutoff_centeredCube_martingale_nonnegative
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      Martingale
        (fun N omega ↦ ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
        (conditionalFineFiltration (fun _ ↦ 0) measurable_const)
        (chaosSampleLaw M).toMeasure ∧
      (∀ N omega, 0 ≤ ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
  intro z r hr
  have hadp := cube_mass_adapted M z r hr
  have hint : ∀ N, Integrable
      (fun omega : BilateralField d => ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
      (chaosSampleLaw M).toMeasure := by
    intro N
    rw [show (fun omega : BilateralField d => ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) =
      (fun omega => ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        fineDensity M N omega x) by
          funext omega; exact cube_mass_toReal_eq_integral M N omega z r hr]
    exact cube_mass_integrable M N z r hr
  have hm : Martingale
      (fun N omega ↦ ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
      (conditionalFineFiltration (fun _ ↦ 0) measurable_const)
      (chaosSampleLaw M).toMeasure := by
    apply martingale_of_setIntegral_eq_succ hadp hint
    intro N S hS
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    let Q : Set (SpatialCoordinates d) := centeredCube z r hr
    let f : BilateralField d × SpatialCoordinates d → ℝ :=
      fun p => fineDensity M N p.1 p.2
    have hprod : Integrable f (P.prod (volume.restrict Q)) := by
      simpa [f, P, Q] using cube_mass_joint_integrable M N z r hr
    have hprodQ : Integrable f
        ((P.prod volume).restrict (Set.univ ×ˢ Q)) := by
      rw [← Measure.prod_restrict (Set.univ : Set (BilateralField d)) Q,
        Measure.restrict_univ]
      exact hprod
    have hprodS' : Integrable f
        ((P.prod volume).restrict (S ×ˢ Q)) := by
      have hrestricted := hprodQ.restrict (s := S ×ˢ Q)
      rw [Measure.restrict_restrict_of_subset] at hrestricted
      · exact hrestricted
      · intro p hp
        exact ⟨Set.mem_univ _, hp.2⟩
    have hprodS : Integrable f ((P.restrict S).prod (volume.restrict Q)) := by
      rw [Measure.prod_restrict S Q]
      exact hprodS'
    have hswap := integral_integral_swap (f := fun omega x => f (omega, x)) hprodS
    have hpoint : ∀ x : SpatialCoordinates d,
        ∫ omega in S, fineDensity M N omega x ∂P =
          ∫ omega in S, fineDensity M (N + 1) omega x ∂P := by
      intro x
      exact (Martingale.setIntegral_eq
        (conditionalFineFiltration_zero_eq_restrict_and_fineDensity_martingale M x).2
        (Nat.le_succ N) hS)
    have hspatial :
        (∫ x in Q, ∫ omega in S, fineDensity M N omega x ∂P ∂volume) =
        ∫ x in Q, ∫ omega in S, fineDensity M (N + 1) omega x ∂P ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    have hswap' :
        (∫ omega in S, ∫ x in Q, fineDensity M N omega x ∂volume ∂P) =
        ∫ x in Q, ∫ omega in S, fineDensity M N omega x ∂P ∂volume := by
      simpa [f, P, Q] using hswap
    simp_rw [cube_mass_toReal_eq_integral M N _ z r hr,
      cube_mass_toReal_eq_integral M (N + 1) _ z r hr]
    rw [hswap', hspatial]
    have hprodS' : Integrable
        (fun p : BilateralField d × SpatialCoordinates d =>
          fineDensity M (N + 1) p.1 p.2)
        ((P.restrict S).prod (volume.restrict Q)) := by
      have hprodQ : Integrable
          (fun p : BilateralField d × SpatialCoordinates d =>
            fineDensity M (N + 1) p.1 p.2)
          ((P.prod volume).restrict (Set.univ ×ˢ Q)) := by
        rw [← Measure.prod_restrict (Set.univ : Set (BilateralField d)) Q,
          Measure.restrict_univ]
        simpa [f, P, Q] using cube_mass_joint_integrable M (N + 1) z r hr
      have hprodS'' : Integrable
          (fun p : BilateralField d × SpatialCoordinates d =>
            fineDensity M (N + 1) p.1 p.2)
          ((P.prod volume).restrict (S ×ˢ Q)) := by
        have hrestricted := hprodQ.restrict (s := S ×ˢ Q)
        rw [Measure.restrict_restrict_of_subset] at hrestricted
        · exact hrestricted
        · intro p hp
          exact ⟨Set.mem_univ _, hp.2⟩
      rw [Measure.prod_restrict S Q]
      exact hprodS''
    have hswap_succ := integral_integral_swap
      (f := fun omega x => fineDensity M (N + 1) omega x) hprodS'
    simpa [P, Q] using hswap_succ.symm
  refine ⟨hm, ?_⟩
  intro N omega
  exact ENNReal.toReal_nonneg

end SubdiffusiveProcess
