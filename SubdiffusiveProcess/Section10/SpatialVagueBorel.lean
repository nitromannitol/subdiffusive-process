module

public import SubdiffusiveProcess.Section10.SpatialVagueCountableTests

@[expose] public section

/-! The exact Giry/vague-Borel identity on the literal locally finite
spatial measure subtype. Countable supported tests generate the topology. -/

open MeasureTheory SubdiffusiveProcess Filter Topology Set TopologicalSpace
open scoped CompactlySupported ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

def spatialCountableTest (d : ℕ) : (ℕ × ℕ) ⊕ ℕ → C_c(SpatialCoordinates d, ℝ)
  | .inl (n, j) => spatialDenseTest d n j
  | .inr n => spatialMassTest d n

def spatialCountableReadout {d : ℕ} (mu : LocallyFiniteSpatialMeasure d) :
    (ℕ × ℕ) ⊕ ℕ → ℝ := fun i => ∫ x, spatialCountableTest d i x ∂mu.val

@[instance_reducible]
def spatialCountableTopology (d : ℕ) : TopologicalSpace (LocallyFiniteSpatialMeasure d) :=
  TopologicalSpace.induced spatialCountableReadout inferInstance

/-- The compact-mass control coordinate makes every real compact-test
integral continuous for the countably generated topology. -/
theorem continuous_test_for_spatialCountableTopology {d : ℕ}
    (f : C_c(SpatialCoordinates d, ℝ)) :
    @Continuous (LocallyFiniteSpatialMeasure d) ℝ (spatialCountableTopology d) inferInstance
      (fun mu => ∫ x, f x ∂mu.val) := by
  let := spatialCountableTopology d
  have hread : Continuous (spatialCountableReadout (d := d)) := continuous_induced_dom
  have ht (i : (ℕ × ℕ) ⊕ ℕ) :
      Continuous (fun mu : LocallyFiniteSpatialMeasure d =>
        ∫ x, spatialCountableTest d i x ∂mu.val) := (continuous_apply i).comp hread
  rw [Metric.continuous_iff']
  intro mu eps heps
  obtain ⟨n, hf⟩ := exists_spatialTestWindow_support f
  let C : ℝ := |∫ x, spatialMassTest d n x ∂mu.val| + 2
  have hC : 0 < C := by dsimp [C]; positivity
  let eta : ℝ := eps / (3 * C)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaC : eta * C = eps / 3 := by dsimp [eta]; field_simp
  obtain ⟨j, hj⟩ := exists_spatialDenseTest_approx f hf eta heta
  let g := spatialDenseTest d n j
  have hg : tsupport (g : SpatialCoordinates d → ℝ) ⊆ spatialTestWindow d n :=
    (denseSeq (SupportedSpatialTest d n) j).property
  have hem : ∀ᶠ nu in 𝓝 mu, dist (∫ x, spatialMassTest d n x ∂nu.val)
      (∫ x, spatialMassTest d n x ∂mu.val) < 1 :=
    (Metric.continuousAt_iff'.mp (ht (.inr n)).continuousAt) 1 zero_lt_one
  have heg : ∀ᶠ nu in 𝓝 mu, dist (∫ x, g x ∂nu.val) (∫ x, g x ∂mu.val) < eps / 3 :=
    (Metric.continuousAt_iff'.mp (ht (.inl (n, j))).continuousAt)
    (eps / 3) (by positivity)
  filter_upwards [hem, heg] with nu hmass htest
  change dist (∫ x, spatialMassTest d n x ∂nu.val)
    (∫ x, spatialMassTest d n x ∂mu.val) < 1 at hmass
  change dist (∫ x, g x ∂nu.val) (∫ x, g x ∂mu.val) < eps / 3 at htest
  have hmun : mu.val.real (spatialTestWindow d n) ≤ C :=
    (spatial_window_mass_le_test mu).trans (by
      dsimp [C]
      linarith [le_abs_self (∫ x, spatialMassTest d n x ∂mu.val)])
  have hnun : nu.val.real (spatialTestWindow d n) ≤ C :=
    (spatial_window_mass_le_test nu).trans (by
      rw [Real.dist_eq] at hmass
      dsimp [C]
      linarith [le_abs_self ((∫ x, spatialMassTest d n x ∂nu.val) -
        ∫ x, spatialMassTest d n x ∂mu.val),
        le_abs_self (∫ x, spatialMassTest d n x ∂mu.val)])
  have he (rho : LocallyFiniteSpatialMeasure d) :
      |(∫ x, f x ∂rho.val) - ∫ x, g x ∂rho.val| ≤
        eta * rho.val.real (spatialTestWindow d n) :=
    spatial_test_integral_error rho f g hf hg eta (fun x hx => by
      simpa only [abs_sub_comm] using (hj x hx).le)
  have henu : |(∫ x, f x ∂nu.val) - ∫ x, g x ∂nu.val| ≤ eps / 3 :=
    (he nu).trans (by simpa only [hetaC] using mul_le_mul_of_nonneg_left hnun heta.le)
  have hemu : |(∫ x, g x ∂mu.val) - ∫ x, f x ∂mu.val| ≤ eps / 3 := by
    rw [abs_sub_comm]
    exact (he mu).trans (by simpa only [hetaC] using mul_le_mul_of_nonneg_left hmun heta.le)
  have htri := abs_sub_le (∫ x, f x ∂nu.val) (∫ x, g x ∂nu.val) (∫ x, f x ∂mu.val)
  have htri' := abs_sub_le (∫ x, g x ∂nu.val) (∫ x, g x ∂mu.val) (∫ x, f x ∂mu.val)
  rw [Real.dist_eq] at htest ⊢
  linarith

theorem spatialCountableTopology_eq_vague (d : ℕ) :
    spatialCountableTopology d = spatialVagueTopology d := by
  have hfull : @Continuous (LocallyFiniteSpatialMeasure d)
      (C_c(SpatialCoordinates d, ℝ) → ℝ) (spatialCountableTopology d) inferInstance
      (fun mu f => ∫ x, f x ∂mu.val) := by
    let := spatialCountableTopology d
    exact continuous_pi fun f => continuous_test_for_spatialCountableTopology f
  have hcount : @Continuous (LocallyFiniteSpatialMeasure d) ((ℕ × ℕ) ⊕ ℕ → ℝ)
      (spatialVagueTopology d) inferInstance spatialCountableReadout :=
    continuous_pi fun i => continuous_spatialVagueTest (spatialCountableTest d i)
  exact le_antisymm hfull.le_induced hcount.le_induced

theorem spatialVagueTopology_secondCountable (d : ℕ) :
    @SecondCountableTopology (LocallyFiniteSpatialMeasure d) (spatialVagueTopology d) := by
  rw [← spatialCountableTopology_eq_vague d]
  exact secondCountableTopology_induced _ _ spatialCountableReadout

theorem spatial_vague_borel_le_giry (d : ℕ) :
    @borel (LocallyFiniteSpatialMeasure d) (spatialVagueTopology d) ≤
      (inferInstance : MeasurableSpace (LocallyFiniteSpatialMeasure d)) := by
  rw [← spatialCountableTopology_eq_vague d, spatialCountableTopology, borel_comap]
  have hm : Measurable (spatialCountableReadout (d := d)) :=
    measurable_pi_iff.mpr fun i => measurable_spatialVagueTest (spatialCountableTest d i)
  simpa only [BorelSpace.measurable_eq] using hm.comap_le

/-- P1, exactly the checked closed proposition: the inherited all-Borel
Giry sigma-algebra equals the Borel sigma-algebra of the literal real-test
vague topology, in every finite dimension including zero. -/
theorem spatialVagueTopology_borel_eq : ∀ d : ℕ,
    (inferInstance : MeasurableSpace (LocallyFiniteSpatialMeasure d)) =
      @borel (LocallyFiniteSpatialMeasure d) (spatialVagueTopology d) :=
  fun d => le_antisymm (spatial_giry_le_vague_borel d) (spatial_vague_borel_le_giry d)

end SubdiffusiveProcess.Section10
