module

public import SubdiffusiveProcess.Section10.LimitMeasureGrowthTransfer
public import SubdiffusiveProcess.MultiplicativeChaos.GrowthCutoff
public import SubdiffusiveProcess.Analysis.RpowMomentBound
public import SubdiffusiveProcess.Section10.ChaosNullCarrier

@[expose] public section

/-! The growth bank for the same limiting measure. The disorder threshold is
chosen before the model, infrared realization and bounded window. The random
constant is measurable and has every prescribed finite positive moment. -/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess Filter Topology TopologicalSpace Set
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The literal infrared-weighted version of the existing representative. -/
def infraredWeightedLimit {d : ℕ} (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (w : BilateralField d) :
    Measure (SpatialCoordinates d) :=
  (mu0 w).withDensity (fun x => ENNReal.ofReal (Real.exp (H w x)))

theorem infraredWeightedLimit_locallyFinite {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)) (w : BilateralField d) :
    IsLocallyFiniteMeasure (infraredWeightedLimit H mu0 w) := by
  have := hl w
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (Real.continuous_exp.comp (H w).continuous)

theorem infraredWeightedLimit_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)) :
    Measurable (infraredWeightedLimit H mu0) := by
  apply Measure.measurable_measure.mpr
  intro U hU
  have hj : Measurable (fun wx : BilateralField d × SpatialCoordinates d =>
      ENNReal.ofReal (Real.exp (H wx.1 wx.2))) :=
    (continuous_eval.measurable.comp
      ((hH.comp measurable_fst).prodMk measurable_snd)).exp.ennreal_ofReal
  let V : ℕ → Set (SpatialCoordinates d) :=
    fun n => U ∩ Metric.closedBall 0 ((n : ℝ) + 1)
  have hV (n : ℕ) : MeasurableSet (V n) := hU.inter Metric.isClosed_closedBall.measurableSet
  have hmono : Monotone V := by
    intro i j hij
    apply Set.inter_subset_inter_right
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hcov : (⋃ n, V n) = U := by
    apply Set.Subset.antisymm (Set.iUnion_subset fun n => Set.inter_subset_left) ?_
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (dist x (0 : SpatialCoordinates d))
    exact Set.mem_iUnion.mpr ⟨n, hx, Metric.mem_closedBall.mpr (by linarith)⟩
  have hf (n : ℕ) : Measurable (fun w => infraredWeightedLimit H mu0 w (V n)) := by
    have hfin (w : BilateralField d) : mu0 w (V n) ≠ ⊤ := by
      have := hl w
      exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
        (measure_mono Set.inter_subset_right)
    let k := _root_.SubdiffusiveProcess.Paper.aux_lim_measure_window_kernel mu0 hm (V n) (hV n)
    have : IsSFiniteKernel k :=
      _root_.SubdiffusiveProcess.Paper.aux_lim_measure_window_kernel_sfinite mu0 hm (V n) (hV n) hfin
    simpa only [infraredWeightedLimit, withDensity_apply _ (hV n)] using!
      hj.lintegral_kernel_prod_right' (κ := k)
  have heq : (fun w => infraredWeightedLimit H mu0 w U) =
      fun w => ⨆ n, infraredWeightedLimit H mu0 w (V n) := by
    funext w
    rw [← hcov, hmono.measure_iUnion]
  rw [heq]
  exact Measurable.iSup hf

theorem infraredWeightedLimit_same_vague {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (w : BilateralField d)
    (hc : MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w)) :
    MeasuresConvergeLocally (fun n => weightedChaosCutoff M H n w)
      (infraredWeightedLimit H mu0 w) := by
  let g : C(SpatialCoordinates d, ℝ) :=
    ⟨fun x => Real.exp (H w x), Real.continuous_exp.comp (H w).continuous⟩
  simpa only [_root_.SubdiffusiveProcess.Paper.aux_lim_measure_weighted_cutoff_eq] using!
    _root_.SubdiffusiveProcess.Paper.aux_lim_measure_vague_weight _ _ hc g (fun x => (Real.exp_pos _).le)

/-- The growth constant has the requested real moment order, uniformly over
all deterministic centers and radii in the fixed bounded window. -/
theorem same_limit_growth_moment_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (mu0 : BilateralField d → Measure (SpatialCoordinates d)),
        (∀ w, IsLocallyFiniteMeasure (mu0 w)) →
        (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w)) →
        ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ K : BilateralField d → ℝ, Measurable K ∧
            MemLp K (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
            (∀ w, 0 ≤ K w) ∧
            ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
              ∀ x ∈ R, ∀ r : ℝ, 0 < r → r ≤ 1 →
                mu0 w (Metric.ball x r) + infraredWeightedLimit H mu0 w (Metric.ball x r)
                  ≤ ENNReal.ofReal (K w * r ^ ((d : ℝ) - 1 / 2)) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (max (2 * p) (2 * (d : ℝ)))
  have hqp : 2 * p < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq
  have hqd : (d : ℝ) < (q : ℝ) * (1 / 2) := by
    have := lt_of_le_of_lt (le_max_right _ _) hq
    linarith
  obtain ⟨delta0, hd0, hcut⟩ := chaos_growth_cutoff hd (1 / 2) (by norm_num) q hqd
  refine ⟨delta0, hd0, ?_⟩
  intro M H hH hdelta mu0 hl hc R hR
  obtain ⟨Kc, hKc, hb⟩ := hcut M H hH hdelta R hR
  obtain ⟨a, ha⟩ := hR.subset_closedBall (0 : SpatialCoordinates d)
  let Q : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall (0 : SpatialCoordinates d) (a + 1), isCompact_closedBall _ _⟩
  have hQ (x : SpatialCoordinates d) (hx : x ∈ R) (r : ℝ) (hr : r ≤ 1) :
      Metric.ball x r ⊆ (Q : Set (SpatialCoordinates d)) := by
    intro y hy
    have hxy := Metric.mem_ball.mp hy
    have hx0 := Metric.mem_closedBall.mp (ha hx)
    exact Metric.mem_closedBall.mpr (by
      have := dist_triangle y x (0 : SpatialCoordinates d)
      linarith)
  let E : BilateralField d → ℝ :=
    fun w => Real.exp ‖(H w).restrict (Q : Set (SpatialCoordinates d))‖
  obtain ⟨C, _, hE⟩ := exp_H_compact_eLpNorm_uniform_bound hd
  have hElp : MemLp E (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure :=
    (hE M H hH Q (2 * p) (by positivity)).1
  have hKlp : MemLp Kc (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure :=
    hKc.mono_exponent (by
      have : ENNReal.ofReal (2 * p) ≤ ENNReal.ofReal (q : ℝ) :=
        ENNReal.ofReal_le_ofReal hqp.le
      simpa using this)
  have : ENNReal.HolderTriple (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal (2 * p)) (ENNReal.ofReal p) := ⟨by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.mul_inv (by left; norm_num) (by left; simp),
      ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]⟩
  let F : BilateralField d → ℝ := fun w => (E w + 1) * Kc w
  have hF : MemLp F (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure :=
    (hElp.add (memLp_const 1)).mul (r := ENNReal.ofReal p) hKlp
  let K : BilateralField d → ℝ := fun w => |hF.aestronglyMeasurable.mk F w|
  refine ⟨K, hF.aestronglyMeasurable.measurable_mk.abs,
    ((memLp_congr_ae hF.aestronglyMeasurable.ae_eq_mk).mp hF).norm,
    fun w => abs_nonneg _, ?_⟩
  filter_upwards [hc, hb, hF.aestronglyMeasurable.ae_eq_mk] with w hw hcB hmk
  have := hl w
  have := infraredWeightedLimit_locallyFinite H mu0 hl w
  have hFnonneg : 0 ≤ F w := mul_nonneg (by dsimp [E]; positivity) hcB.1
  have hKF : K w = F w := by dsimp [K]; rw [← hmk, abs_of_nonneg hFnonneg]
  have hwc := infraredWeightedLimit_same_vague M H mu0 w hw
  intro x hx r hr hr1
  have hKnonneg : 0 ≤ Kc w := hcB.1
  have hpow : 0 ≤ r ^ ((d : ℝ) - 1 / 2) := Real.rpow_nonneg hr.le _
  have hbmu := open_mass_le_of_same_vague_limit
    (fun n => weightedChaosCutoff M H n w) (infraredWeightedLimit H mu0 w)
    (fun n => weightedChaosCutoff_isLocallyFinite M H n w) hwc
    (Metric.ball x r) Metric.isOpen_ball _ (fun n => hcB.2 n x hx r hr hr1)
  have hb0 := mass_le_compact_envelope_mul_weighted (mu0 w) (H w) Q
    (Metric.ball x r) Metric.isOpen_ball.measurableSet (hQ x hx r hr1)
  change mu0 w (Metric.ball x r) ≤ ENNReal.ofReal (E w) *
    infraredWeightedLimit H mu0 w (Metric.ball x r) at hb0
  calc mu0 w (Metric.ball x r) + infraredWeightedLimit H mu0 w (Metric.ball x r)
      ≤ ENNReal.ofReal (E w) * ENNReal.ofReal (Kc w * r ^ ((d : ℝ) - 1 / 2)) +
          ENNReal.ofReal (Kc w * r ^ ((d : ℝ) - 1 / 2)) :=
        add_le_add (hb0.trans (by gcongr)) hbmu
    _ = ENNReal.ofReal (K w * r ^ ((d : ℝ) - 1 / 2)) := by
        rw [← ENNReal.ofReal_mul (by dsimp [E]; positivity),
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg hKnonneg hpow), hKF]
        congr 1
        dsimp [F]
        ring

end SubdiffusiveProcess.Section10
