import SubdiffusiveProcess.Section10.LimitMeasureRescaledLawVagueTopology
import SubdiffusiveProcess.Section10.LimitMeasureLawsRestrictionLocal

/-! Evaluation measurability for the literal vague topology. Open masses
are countable suprema of existing positive compact tests; finite-window
Giry generators then give every Borel mass, including unbounded sets. -/

open MeasureTheory SubdiffusiveProcess Filter Topology Set
open scoped CompactlySupported ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

theorem continuous_spatialVagueTest {d : ℕ} (f : C_c(SpatialCoordinates d, ℝ)) :
    Continuous (fun mu : LocallyFiniteSpatialMeasure d => ∫ x, f x ∂mu.val) := by
  have h : Continuous (fun mu : LocallyFiniteSpatialMeasure d =>
      fun g : C_c(SpatialCoordinates d, ℝ) => ∫ x, g x ∂mu.val) :=
    continuous_induced_dom
  exact (continuous_apply f).comp h

theorem measurable_spatialVagueTest {d : ℕ} (f : C_c(SpatialCoordinates d, ℝ)) :
    Measurable (fun mu : LocallyFiniteSpatialMeasure d => ∫ x, f x ∂mu.val) := by
  have hp : Measurable (fun mu : LocallyFiniteSpatialMeasure d =>
      ∫⁻ x, ENNReal.ofReal (f x) ∂mu.val) :=
    (Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal).comp
    measurable_subtype_coe
  have hn : Measurable (fun mu : LocallyFiniteSpatialMeasure d =>
      ∫⁻ x, ENNReal.ofReal (-f x) ∂mu.val) :=
    (Measure.measurable_lintegral f.continuous.measurable.neg.ennreal_ofReal).comp
    measurable_subtype_coe
  have heq : (fun mu : LocallyFiniteSpatialMeasure d => ∫ x, f x ∂mu.val) =
      fun mu => (∫⁻ x, ENNReal.ofReal (f x) ∂mu.val).toReal -
        (∫⁻ x, ENNReal.ofReal (-f x) ∂mu.val).toReal := by
    funext mu
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (integrable_spatialVagueTest mu f)
  rw [heq]
  exact hp.ennreal_toReal.sub hn.ennreal_toReal

theorem borel_measurable_spatial_open_mass {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) :
    @Measurable (LocallyFiniteSpatialMeasure d) ℝ≥0∞
      (@borel _ (spatialVagueTopology d)) inferInstance (fun mu => mu.val U) := by
  letI : MeasurableSpace (LocallyFiniteSpatialMeasure d) :=
    @borel _ (spatialVagueTopology d)
  letI : BorelSpace (LocallyFiniteSpatialMeasure d) := ⟨rfl⟩
  choose f hf hK hs using fun n => exists_urysohn_openPiece hU n
  have heq : (fun mu : LocallyFiniteSpatialMeasure d => mu.val U) =
      fun mu => ⨆ n, ENNReal.ofReal (∫ x, f n x ∂mu.val) := by
    funext mu
    rw [open_mass_eq_iSup_positive_tests mu.val U hU f hf hK hs]
    congr 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_spatialVagueTest mu (f n))
      (ae_of_all _ fun x => (hf n x).1)).symm
  rw [heq]
  exact Measurable.iSup fun n => (continuous_spatialVagueTest (f n)).measurable.ennreal_ofReal

/-- The inherited literal Giry structure is contained in the vague Borel
structure; finite restrictions and countable exhaustion handle all Borel sets. -/
theorem spatial_giry_le_vague_borel (d : ℕ) :
    (inferInstance : MeasurableSpace (LocallyFiniteSpatialMeasure d)) ≤
      @borel _ (spatialVagueTopology d) := by
  letI : MeasurableSpace (LocallyFiniteSpatialMeasure d) :=
    @borel _ (spatialVagueTopology d)
  have hopen := borel_measurable_spatial_open_mass (d := d)
  let W : ℕ → Set (SpatialCoordinates d) := fun n => Metric.ball 0 ((n : ℝ) + 1)
  let nu : ℕ → LocallyFiniteSpatialMeasure d → Measure (SpatialCoordinates d) :=
    fun n mu => mu.val.restrict (W n)
  have hfin (n : ℕ) (mu : LocallyFiniteSpatialMeasure d) : IsFiniteMeasure (nu n mu) := by
    letI := mu.property
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hnu (n : ℕ) : Measurable (nu n) := by
    letI := hfin n
    apply Measurable.measure_of_isPiSystem
      (BorelSpace.measurable_eq (α := SpatialCoordinates d)) isPiSystem_isOpen
    · intro U hU
      change IsOpen U at hU
      simpa only [nu, Measure.restrict_apply hU.measurableSet] using
        hopen (U ∩ W n) (hU.inter Metric.isOpen_ball)
    · simpa only [nu, Measure.restrict_apply_univ] using hopen (W n) Metric.isOpen_ball
  have hval : Measurable (Subtype.val : LocallyFiniteSpatialMeasure d →
      Measure (SpatialCoordinates d)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have heq : (fun mu : LocallyFiniteSpatialMeasure d => mu.val A) =
        fun mu => ⨆ n, nu n mu A := by
      funext mu
      have hmono : Monotone fun n => A ∩ W n := fun i j hij =>
        Set.inter_subset_inter_right _ (Metric.ball_subset_ball (by
          exact_mod_cast (Nat.add_le_add_right hij 1)))
      have hcover : (⋃ n, A ∩ W n) = A := by
        apply Set.Subset.antisymm (Set.iUnion_subset fun n => Set.inter_subset_left) ?_
        intro x hx
        obtain ⟨n, hn⟩ := exists_nat_gt (dist x (0 : SpatialCoordinates d))
        exact Set.mem_iUnion.mpr ⟨n, hx, Metric.mem_ball.mpr (by linarith)⟩
      calc mu.val A = mu.val (⋃ n, A ∩ W n) := by rw [hcover]
        _ = ⨆ n, mu.val (A ∩ W n) := hmono.measure_iUnion
        _ = ⨆ n, nu n mu A := by
          congr 1
          funext n
          exact (Measure.restrict_apply hA).symm
    rw [heq]
    exact Measurable.iSup fun n => (Measure.measurable_coe hA).comp (hnu n)
  change MeasurableSpace.comap
    (Subtype.val : LocallyFiniteSpatialMeasure d → Measure (SpatialCoordinates d))
    inferInstance ≤ _
  exact hval.comap_le

end SubdiffusiveProcess.Section10
