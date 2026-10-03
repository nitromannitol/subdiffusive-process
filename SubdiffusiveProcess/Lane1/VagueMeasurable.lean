module

public import SubdiffusiveProcess.Lane1.OpenExhaustion
public import SubdiffusiveProcess.Lane1.VagueRiesz
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.PiSystem

@[expose] public section

/-!
# Measurability of the vague limit family

Mathlib has no parametrized measurability for the Riesz construction.  The
mass of an OPEN set is a countable supremum of functional values -- the
Urysohn functions of `OpenExhaustion` -- hence measurable in the parameter;
open sets form a `pi`-system generating the Borel sets, so a Dynkin argument
carries measurability to every Borel set, after localising to balls to make
the measures finite.
-/

open Filter MeasureTheory Metric

open scoped CompactlySupported ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- Dynkin: a family of finite measures whose masses are measurable on a
generating `pi`-system is measurable. -/
theorem measurable_of_measurable_piSystem
    {X Om : Type*} [MeasurableSpace X] [MeasurableSpace Om]
    (mu : Om → Measure X) (hfin : ∀ w, IsFiniteMeasure (mu w))
    (Cs : Set (Set X))
    (hgen : (inferInstance : MeasurableSpace X) = MeasurableSpace.generateFrom Cs)
    (hpi : IsPiSystem Cs)
    (hbasic : ∀ t ∈ Cs, Measurable (fun w => mu w t))
    (huniv : Measurable (fun w => mu w Set.univ)) :
    Measurable mu := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro s hs
  induction s, hs using MeasurableSpace.induction_on_inter
    (h_eq := hgen) (h_inter := hpi) with
  | empty => simpa using measurable_const
  | basic t ht => exact hbasic t ht
  | compl t htm ih =>
      have heq : (fun w => mu w tᶜ) = fun w => mu w Set.univ - mu w t := by
        funext w
        haveI := hfin w
        exact measure_compl htm (measure_ne_top _ _)
      rw [heq]
      exact huniv.sub ih
  | iUnion f hdisj hfm ih =>
      have heq : (fun w => mu w (⋃ i, f i)) = fun w => ∑' i, mu w (f i) := by
        funext w
        exact measure_iUnion hdisj hfm
      rw [heq]
      exact Measurable.ennreal_tsum ih

/-- The mass of an open set is the supremum of the functional on the Urysohn
functions of its exhaustion. -/
theorem rieszMeasure_open_eq_iSup
    {d : ℕ} (Lam : C_c(SpatialCoordinates d, ℝ) →ₚ[ℝ] ℝ)
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    (f : ℕ → C_c(SpatialCoordinates d, ℝ))
    (hf01 : ∀ (n : ℕ) (x : SpatialCoordinates d), 0 ≤ f n x ∧ f n x ≤ 1)
    (hfK : ∀ (n : ℕ), ∀ x ∈ openPiece U n, f n x = 1)
    (hfU : ∀ n : ℕ, tsupport ((f n : SpatialCoordinates d → ℝ)) ⊆ U) :
    RealRMK.rieszMeasure Lam U = ⨆ n : ℕ, ENNReal.ofReal (Lam (f n)) := by
  refine le_antisymm ?_ ?_
  · rw [← iUnion_openPiece hU, (monotone_openPiece U).measure_iUnion]
    refine iSup_le fun n => le_iSup_of_le n ?_
    exact RealRMK.rieszMeasure_le_of_eq_one Lam (fun x => (hf01 n x).1)
      (isCompact_openPiece U n) (hfK n)
  · exact iSup_le fun n =>
      RealRMK.le_rieszMeasure_tsupport_subset Lam (hf01 n) (hfU n)

/-- **The Riesz measures of a measurable family of functionals form a
measurable family.** -/
theorem measurable_rieszMeasure_family
    {d : ℕ} {Om : Type*} [MeasurableSpace Om]
    (Lam : Om → C_c(SpatialCoordinates d, ℝ) →ₚ[ℝ] ℝ)
    (hmble : ∀ f : C_c(SpatialCoordinates d, ℝ), Measurable (fun w => Lam w f))
    (hloc : ∀ w, IsLocallyFiniteMeasure (RealRMK.rieszMeasure (Lam w))) :
    Measurable (fun w => RealRMK.rieszMeasure (Lam w)) := by
  classical
  -- masses of open sets are countable suprema of functional values
  have hopen : ∀ U : Set (SpatialCoordinates d), IsOpen U →
      Measurable (fun w => RealRMK.rieszMeasure (Lam w) U) := by
    intro U hU
    choose f hf01 hfK hfU using fun n => exists_urysohn_openPiece hU n
    have heq : (fun w => RealRMK.rieszMeasure (Lam w) U)
        = fun w => ⨆ n : ℕ, ENNReal.ofReal (Lam w (f n)) := by
      funext w
      exact rieszMeasure_open_eq_iSup (Lam w) hU f hf01 hfK hfU
    rw [heq]
    exact Measurable.iSup fun n => (hmble (f n)).ennreal_ofReal
  -- localise to balls to make the measures finite
  refine Measure.measurable_of_measurable_coe _ ?_
  intro s hs
  set nu : Om → ℕ → Measure (SpatialCoordinates d) :=
    fun w n => (RealRMK.rieszMeasure (Lam w)).restrict
      (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) with hnudef
  have hnufin : ∀ (w : Om) (n : ℕ), IsFiniteMeasure (nu w n) := by
    intro w n
    haveI := hloc w
    refine ⟨?_⟩
    rw [hnudef, Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hnumble : ∀ n : ℕ, Measurable (fun w => nu w n) := by
    intro n
    refine measurable_of_measurable_piSystem _ (fun w => hnufin w n)
      {U : Set (SpatialCoordinates d) | IsOpen U} ?_ isPiSystem_isOpen ?_ ?_
    · exact BorelSpace.measurable_eq
    · intro t ht
      have ht' : IsOpen t := ht
      have heq : (fun w => nu w n t)
          = fun w => RealRMK.rieszMeasure (Lam w)
            (t ∩ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) := by
        funext w
        rw [hnudef, Measure.restrict_apply ht'.measurableSet]
      rw [heq]
      exact hopen _ (ht'.inter Metric.isOpen_ball)
    · have heq : (fun w => nu w n Set.univ)
          = fun w => RealRMK.rieszMeasure (Lam w)
            (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) := by
        funext w
        rw [hnudef, Measure.restrict_apply_univ]
      rw [heq]
      exact hopen _ Metric.isOpen_ball
  have hlim : (fun w => RealRMK.rieszMeasure (Lam w) s)
      = fun w => ⨆ n : ℕ, nu w n s := by
    funext w
    have hmono : Monotone fun n : ℕ =>
        s ∩ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1) := by
      intro a b hab
      exact Set.inter_subset_inter_right _
        (Metric.ball_subset_ball (by exact_mod_cast Nat.succ_le_succ hab))
    have hunion : (⋃ n : ℕ, s ∩ Metric.ball (0 : SpatialCoordinates d)
        ((n : ℝ) + 1)) = s := by
      rw [← Set.inter_iUnion]
      refine Set.Subset.antisymm Set.inter_subset_left fun x hx => ⟨hx, ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (dist x (0 : SpatialCoordinates d))
      exact Set.mem_iUnion.mpr ⟨n, Metric.mem_ball.mpr (by linarith)⟩
    calc RealRMK.rieszMeasure (Lam w) s
        = RealRMK.rieszMeasure (Lam w) (⋃ n : ℕ, s ∩ Metric.ball
            (0 : SpatialCoordinates d) ((n : ℝ) + 1)) := by rw [hunion]
      _ = ⨆ n : ℕ, RealRMK.rieszMeasure (Lam w) (s ∩ Metric.ball
            (0 : SpatialCoordinates d) ((n : ℝ) + 1)) :=
          hmono.measure_iUnion
      _ = ⨆ n : ℕ, nu w n s := by
          refine iSup_congr fun n => ?_
          rw [hnudef, Measure.restrict_apply hs]
  rw [hlim]
  exact Measurable.iSup fun n => Measure.measurable_coe hs |>.comp (hnumble n)

/-- An open set's mass is approached from inside by test functions supported in
it: the inner-regularity input the portmanteau transfer needs. -/
theorem rieszMeasure_innerApprox {d : ℕ}
    (Lam : C_c(SpatialCoordinates d, ℝ) →ₚ[ℝ] ℝ)
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U) {c : ℝ≥0∞}
    (hc : c < RealRMK.rieszMeasure Lam U) :
    ∃ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      tsupport (f : SpatialCoordinates d → ℝ) ⊆ U ∧
      c < ENNReal.ofReal (∫ x, f x ∂(RealRMK.rieszMeasure Lam)) := by
  classical
  choose f hf01 hfK hfU using fun n => exists_urysohn_openPiece hU n
  rw [rieszMeasure_open_eq_iSup Lam hU f hf01 hfK hfU] at hc
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hc
  refine ⟨f n, hf01 n, hfU n, ?_⟩
  rwa [RealRMK.integral_rieszMeasure Lam (f n)]

end SubdiffusiveProcess
