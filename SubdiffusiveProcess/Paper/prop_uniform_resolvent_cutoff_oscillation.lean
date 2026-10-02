import SubdiffusiveProcess.Paper.conv_represented_sequence
import SubdiffusiveProcess.Paper.prop_chaos_growth
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.killed_zero_extension_bound
import SubdiffusiveProcess.Paper.finite_speed_resolvent_properties
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.cutoff_campanato_bound
import SubdiffusiveProcess.Analysis.GlobalTriadicAverageBound
import SubdiffusiveProcess.Analysis.GlobalTriadicPointwise
import SubdiffusiveProcess.Geometry.UpstreamCube

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace Paper

lemma aux_prop_uniform_resolvent_cutoff_oscillation_exponent
    {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2))) :
    1 / 4 < 1 / 2 - ((d : ℝ) + 2) * epsilon := by
  have hden : 0 < (8 : ℝ) * ((d : ℝ) + 2) := by positivity
  have hcross : epsilon * (8 * ((d : ℝ) + 2)) < 1 :=
    (lt_div_iff₀ hden).mp hepsilon'
  have hepsilon_nonneg : 0 ≤ epsilon := le_of_lt hepsilon
  nlinarith [hcross, hepsilon_nonneg]

lemma aux_prop_uniform_resolvent_cutoff_oscillation_bddAbove_range
    {ι : Type*} (c : ι → ℝ) (hc : BddAbove (Set.range c)) :
    ∃ C : ℝ, ∀ i : ι, c i ≤ C := by
  rcases hc with ⟨C, hC⟩
  exact ⟨C, fun i => hC ⟨i, rfl⟩⟩

lemma aux_prop_uniform_resolvent_cutoff_oscillation_common_constant_bound
    (c₁ c₂ : ℕ → ℝ)
    (h₁ : BddAbove (Set.range c₁))
    (h₂ : BddAbove (Set.range c₂)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, c₁ N ≤ C ∧ c₂ N ≤ C := by
  obtain ⟨C₁, hC₁⟩ :=
    aux_prop_uniform_resolvent_cutoff_oscillation_bddAbove_range c₁ h₁
  obtain ⟨C₂, hC₂⟩ :=
    aux_prop_uniform_resolvent_cutoff_oscillation_bddAbove_range c₂ h₂
  refine ⟨max 0 (max C₁ C₂), le_max_left 0 _, ?_⟩
  intro N
  constructor
  · exact (hC₁ N).trans ((le_max_left C₁ C₂).trans (le_max_right 0 _))
  · exact (hC₂ N).trans ((le_max_right C₁ C₂).trans (le_max_right 0 _))

lemma aux_prop_uniform_resolvent_cutoff_oscillation_ae_intersection
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {A B C D E F G : Ω → Prop}
    (hA : ∀ᵐ ω ∂P, A ω) (hB : ∀ᵐ ω ∂P, B ω)
    (hC : ∀ᵐ ω ∂P, C ω) (hD : ∀ᵐ ω ∂P, D ω)
    (hE : ∀ᵐ ω ∂P, E ω) (hF : ∀ᵐ ω ∂P, F ω)
    (hG : ∀ᵐ ω ∂P, G ω) :
    ∀ᵐ ω ∂P, A ω ∧ B ω ∧ C ω ∧ D ω ∧ E ω ∧ F ω ∧ G ω := by
  filter_upwards [hA, hB, hC, hD, hE, hF, hG] with ω hAω hBω hCω hDω hEω hFω hGω
  exact ⟨hAω, hBω, hCω, hDω, hEω, hFω, hGω⟩

lemma aux_prop_uniform_resolvent_cutoff_oscillation_source_square
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hsource : ∀ᵐ x ∂μ, |f x - g x| ≤ B) :
    ∀ᵐ x ∂μ, (f x - g x) ^ 2 ≤ B ^ 2 := by
  filter_upwards [hsource] with x hx
  nlinarith [sq_abs (f x - g x), abs_nonneg (f x - g x)]

lemma aux_prop_uniform_resolvent_cutoff_oscillation_mollified_scale
    {d : ℕ} (epsilon r : ℝ) (hr : 0 < r) :
    r ^ (1 / 2 : ℝ) * (r ^ ((d : ℝ) + 2)) ^ (-epsilon) =
      r ^ (1 / 2 - ((d : ℝ) + 2) * epsilon) := by
  rw [← Real.rpow_mul (le_of_lt hr)]
  rw [← Real.rpow_add hr]
  congr 1
  ring

lemma aux_prop_uniform_resolvent_cutoff_oscillation_error_scale
    {d : ℕ} (r : ℝ) (hr : 0 < r) :
    r ^ (-(d : ℝ) / 2) * (r ^ ((d : ℝ) + 2)) ^ (1 / 2 : ℝ) = r := by
  rw [← Real.rpow_mul (le_of_lt hr)]
  rw [← Real.rpow_add hr]
  have hexp : -(d : ℝ) / 2 + ((d : ℝ) + 2) * (1 / 2 : ℝ) = 1 := by ring
  rw [hexp, Real.rpow_one]

lemma aux_prop_uniform_resolvent_cutoff_oscillation_two_scale
    {d : ℕ} (epsilon r : ℝ) (hr : 0 < r) :
    r ^ (1 / 2 : ℝ) * (r ^ ((d : ℝ) + 2)) ^ (-epsilon) +
        r ^ (-(d : ℝ) / 2) * (r ^ ((d : ℝ) + 2)) ^ (1 / 2 : ℝ) =
      r ^ (1 / 2 - ((d : ℝ) + 2) * epsilon) + r := by
  rw [aux_prop_uniform_resolvent_cutoff_oscillation_mollified_scale epsilon r hr,
    aux_prop_uniform_resolvent_cutoff_oscillation_error_scale r hr]

lemma aux_prop_uniform_resolvent_cutoff_oscillation_killed_coercivity
    {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (v : killedSobolevGraph Ω) (K energy : ℝ)
    (hK : 0 ≤ K) (henergy : 0 ≤ energy)
    (hcoer : ‖(v : SobolevData Ω).1‖ ^ 2 ≤ K * energy) :
    ‖(v : SobolevData Ω).1‖ ≤ Real.sqrt (K * energy) := by
  have hprod : 0 ≤ K * energy := mul_nonneg hK henergy
  have hsqrt : (Real.sqrt (K * energy)) ^ 2 = K * energy := by
    simpa only [sq] using Real.sq_sqrt hprod
  have hsqrt_nonneg : 0 ≤ Real.sqrt (K * energy) := Real.sqrt_nonneg _
  nlinarith [norm_nonneg ((v : SobolevData Ω).1)]

lemma aux_prop_uniform_resolvent_cutoff_oscillation_form_nonneg
    {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (v : killedSobolevGraph Ω) :
    0 ≤ sobolevCoefficientForm a (v : SobolevData Ω) (v : SobolevData Ω) := by
  exact sobolevCoefficientForm_nonneg _ _

lemma aux_prop_uniform_resolvent_cutoff_oscillation_energy_nonneg
    {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω)
    (E : killedSobolevGraph Ω → killedSobolevGraph Ω → ℝ)
    (hE : ∀ v w, E v w =
      sobolevCoefficientForm a v.val w.val)
    (v : killedSobolevGraph Ω) : 0 ≤ E v v := by
  rw [hE]
  exact aux_prop_uniform_resolvent_cutoff_oscillation_form_nonneg a v

lemma aux_prop_uniform_resolvent_cutoff_oscillation_comparison_energy
    (energy A C : ℝ) (henergy : 0 ≤ energy)
    (hbound : energy ≤ A * C * Real.sqrt energy) :
    energy ≤ (A * C) ^ 2 := by
  have hsqrt : (Real.sqrt energy) ^ 2 = energy := by
    simpa only [sq] using Real.sq_sqrt henergy
  have hsqrt_nonneg : 0 ≤ Real.sqrt energy := Real.sqrt_nonneg _
  nlinarith

lemma aux_prop_uniform_resolvent_cutoff_oscillation_source_pairing
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g w : α → ℝ) (B : ℝ)
    (hsource : ∀ᵐ x ∂μ, |f x - g x| ≤ B)
    (hw : Integrable (fun x => |w x|) μ)
    (hprod : Integrable (fun x => (f x - g x) * w x) μ) :
    |∫ x, (f x - g x) * w x ∂μ| ≤ B * ∫ x, |w x| ∂μ := by
  have hprod_abs : Integrable (fun x => |(f x - g x) * w x|) μ := by
    simpa only [Real.norm_eq_abs] using hprod.norm
  have hdom : Integrable (fun x => B * |w x|) μ := by
    simpa only [smul_eq_mul] using hw.const_mul B
  calc
    |∫ x, (f x - g x) * w x ∂μ| ≤
        ∫ x, |(f x - g x) * w x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, B * |w x| ∂μ := by
      apply integral_mono_ae hprod_abs hdom
      filter_upwards [hsource] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = B * ∫ x, |w x| ∂μ := by rw [integral_const_mul]


/-- Coordinate hyperplanes are Lebesgue-null. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_volume_plane {d : ℕ} (i : Fin d) (c : ℝ) :
    volume {x : SpatialCoordinates d | x i = c} = 0 := by
  rw [MeasureTheory.volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i c

/-- A triadic cell average is the closed-ball average of the zero extension. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_cell_average_eq_closedBall {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (m : ℕ)
    (k : OddGridIndex d m) (f : SpatialCoordinates d → ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.averageOn (oddGridCell z r hr m k : Set (SpatialCoordinates d)) f =
      ⨍ y in Metric.closedBall (oddGridCenter z r m k) ((r / (2 * (m : ℝ) + 1)) / 2),
        (centeredCube z r hr : Set (SpatialCoordinates d)).indicator f y := by
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hℓ : 0 < r / (2 * (m : ℝ) + 1) := div_pos hr (by positivity)
  set c := oddGridCenter z r m k with hc
  set δ := (r / (2 * (m : ℝ) + 1)) / 2 with hδ
  have hcell : (oddGridCell z r hr m k : Set (SpatialCoordinates d)) = Metric.ball c δ := rfl
  have hsub : Metric.ball c δ ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [← hcell]; exact oddGridCell_subset z hr m k
  have hvol : volume (Metric.closedBall c δ) = volume (Metric.ball c δ) :=
    Measure.addHaar_closedBall_eq_addHaar_ball volume c δ
  have hae : Metric.ball c δ =ᵐ[volume] Metric.closedBall c δ := by
    apply ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall hvol.le
      measurableSet_ball.nullMeasurableSet
    rw [hvol]
    exact measure_ball_lt_top.ne
  rw [setAverage_eq, SubdiffusiveProcess.CoarseGrainingVocab.averageOn, Homogenization.volumeAverage, hcell, smul_eq_mul]
  have hint : (∫ y in Metric.closedBall c δ,
      (centeredCube z r hr : Set (SpatialCoordinates d)).indicator f y) =
      ∫ y in Metric.ball c δ, f y := by
    rw [← setIntegral_congr_set hae]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact Set.indicator_of_mem (hsub hy) f
  rw [hint, measureReal_def, hvol]

/-- The triadic averages of an integrable function converge to it at Lebesgue-almost every point of
the root cube (Lebesgue differentiation along the triadic cells containing the point). -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_triadic_tendsto_ae {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (f : SpatialCoordinates d → ℝ)
    (hf : IntegrableOn f (centeredCube z r hr : Set (SpatialCoordinates d)) volume) :
    ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
      x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      Tendsto (fun m => ∑ k : OddGridIndex d (triadicHalf m),
        (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
          (fun _ => SubdiffusiveProcess.CoarseGrainingVocab.averageOn
            (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x)
        atTop (𝓝 (f x)) := by
  classical
  set F : SpatialCoordinates d → ℝ :=
    (centeredCube z r hr : Set (SpatialCoordinates d)).indicator f with hFdef
  have hF : LocallyIntegrable F volume :=
    (hf.integrable_indicator (centeredCube z r hr).isOpen.measurableSet).locallyIntegrable
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average
    (volume : Measure (SpatialCoordinates d)) hF 1
  have hfaces : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)), ∀ m : ℕ,
      x ∉ ⋃ i : Fin d, ⋃ q : Fin (2 * triadicHalf m + 2),
        triadicFaceSet z r (triadicHalf m) i q := by
    apply ae_all_iff.2
    intro m
    apply ae_iff.2
    rw [show {x : SpatialCoordinates d |
        ¬ x ∉ ⋃ i : Fin d, ⋃ q : Fin (2 * triadicHalf m + 2),
          triadicFaceSet z r (triadicHalf m) i q} =
        ⋃ i : Fin d, ⋃ q : Fin (2 * triadicHalf m + 2),
          triadicFaceSet z r (triadicHalf m) i q by
      ext x
      simp]
    exact triadicFaceSet_union_null z hr (triadicHalf m) volume
      (fun i c => aux_prop_uniform_resolvent_cutoff_oscillation_volume_plane i c)
  filter_upwards [hleb, hfaces] with x hx hxf hxQ
  have hcells : ∀ m : ℕ, ∃ k : OddGridIndex d (triadicHalf m),
      x ∈ (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) := by
    intro m
    apply mem_triadicCell_of_mem_cube_of_not_face z hr (triadicHalf m) x hxQ
    intro i q hq
    exact hxf m (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨q, hq⟩⟩)
  choose k hk using hcells
  let w : ℕ → SpatialCoordinates d := fun m => oddGridCenter z r (triadicHalf m) (k m)
  let δ : ℕ → ℝ := fun m => (r / (2 * (triadicHalf m : ℝ) + 1)) / 2
  have hδeq : ∀ m, δ m = (r / 2) * ((1 : ℝ) / 3) ^ m := by
    intro m
    simp only [δ, triadic_denominator m, one_div, inv_pow]
    ring
  have hδpos : ∀ m, 0 < δ m := by
    intro m
    rw [hδeq]
    positivity
  have hδlim : Tendsto δ atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall hδpos⟩
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (1 : ℝ) / 3 < 1)).const_mul (r / 2)
    rw [mul_zero] at h
    exact h.congr (fun m => (hδeq m).symm)
  have hmem : ∀ᶠ m in atTop, x ∈ Metric.closedBall (w m) (1 * δ m) := by
    refine Eventually.of_forall (fun m => ?_)
    rw [one_mul]
    exact Metric.ball_subset_closedBall (hk m)
  have hlim := hx w δ hδlim hmem
  have hFx : F x = f x := Set.indicator_of_mem hxQ f
  rw [hFx] at hlim
  refine hlim.congr (fun m => ?_)
  rw [sum_indicator_triadicCell_eq z hr (triadicHalf m) x _ (k m) (hk m)]
  exact (aux_prop_uniform_resolvent_cutoff_oscillation_cell_average_eq_closedBall hd z hr (triadicHalf m) (k m) f).symm

/-- Fatou plus telescoping: geometric control of consecutive increments controls the distance to
an almost-everywhere limit. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_fatou_tail {α : Type*} {mα : MeasurableSpace α} (ν : Measure α)
    (g : ℕ → α → ℝ) (G : α → ℝ) (hg : ∀ m, AEStronglyMeasurable (g m) ν)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun m => g m x) atTop (𝓝 (G x)))
    (n : ℕ) (a q : ℝ) (ha : 0 ≤ a) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ m, n ≤ m →
      eLpNorm (fun x => g (m + 1) x - g m x) 2 ν ≤ ENNReal.ofReal (a * q ^ m)) :
    eLpNorm (fun x => G x - g n x) 2 ν ≤ ENNReal.ofReal (a * q ^ n / (1 - q)) := by
  have hpart : ∀ M, n ≤ M →
      eLpNorm (fun x => g M x - g n x) 2 ν ≤
        ENNReal.ofReal (a * ∑ j ∈ Finset.Ico n M, q ^ j) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hnM ih =>
      have hsplit : (fun x => g (M + 1) x - g n x) =
          (fun x => g M x - g n x) + (fun x => g (M + 1) x - g M x) := by
        funext x
        simp only [Pi.add_apply]
        ring
      rw [hsplit]
      calc eLpNorm ((fun x => g M x - g n x) + (fun x => g (M + 1) x - g M x)) 2 ν
          ≤ eLpNorm (fun x => g M x - g n x) 2 ν +
              eLpNorm (fun x => g (M + 1) x - g M x) 2 ν :=
            eLpNorm_add_le ((hg M).sub (hg n)) ((hg (M + 1)).sub (hg M)) (by norm_num)
        _ ≤ ENNReal.ofReal (a * ∑ j ∈ Finset.Ico n M, q ^ j) +
              ENNReal.ofReal (a * q ^ M) := add_le_add ih (hstep M hnM)
        _ = ENNReal.ofReal (a * ∑ j ∈ Finset.Ico n (M + 1), q ^ j) := by
            rw [← ENNReal.ofReal_add
              (mul_nonneg ha (Finset.sum_nonneg (fun j _ => pow_nonneg hq0 j)))
              (mul_nonneg ha (pow_nonneg hq0 M)),
              Finset.sum_Ico_succ_top hnM, mul_add]
  have hbound : ∀ M, n ≤ M →
      eLpNorm (fun x => g M x - g n x) 2 ν ≤ ENNReal.ofReal (a * q ^ n / (1 - q)) := by
    intro M hM
    refine (hpart M hM).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) ha
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (fun M => (hg M).sub (hg n)) (fun x => G x - g n x)
    (by
      filter_upwards [hlim] with x hx
      exact hx.sub_const (g n x))
  refine hfatou.trans ?_
  apply liminf_le_of_frequently_le'
  exact (Filter.eventually_atTop.2 ⟨n, fun M hM => hbound M hM⟩).frequently


/-- Exact value of the per-level triadic coefficient (the computation inside
`summable_triadicGrowthCoefficients`, recorded at a fixed level). -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_level_coeff {d : ℕ} (s t : ℝ) (hs : 0 < s) (m : ℕ) :
    ((s / (2 * (triadicHalf m : ℝ) + 1)) / 3) ^ t *
        (((s / (2 * (triadicHalf m : ℝ) + 1)) / 3) ^ d *
          (s / (2 * (triadicHalf m : ℝ) + 1)) ^ d)⁻¹ *
        (Real.sqrt (d : ℝ) * (s / (2 * (triadicHalf m : ℝ) + 1))) ^ ((d : ℝ) + 1) =
      (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) *
        (s / (3 : ℝ) ^ m) ^ (t - d + 1) := by
  rw [triadic_denominator m]
  have h3n_pos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hAn_pos : (0 : ℝ) < s / (3 : ℝ) ^ m := div_pos hs h3n_pos
  set A : ℝ := s / (3 : ℝ) ^ m with hAdef
  have hstep1 : ((A / 3) ^ d * A ^ d)⁻¹ = (3 : ℝ) ^ d / A ^ (2 * d) := by
    rw [div_pow, div_mul_eq_mul_div, ← pow_add, ← two_mul, inv_div]
  have hstep2 : (A / 3) ^ t = A ^ t * (3 : ℝ) ^ (-t) := by
    rw [div_eq_mul_inv, Real.mul_rpow hAn_pos.le (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹),
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have hstep3 : (Real.sqrt (d : ℝ) * A) ^ ((d : ℝ) + 1)
      = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * A ^ ((d : ℝ) + 1) :=
    Real.mul_rpow (Real.sqrt_nonneg _) hAn_pos.le
  have hpow_combine : A ^ t * (A ^ (2 * d))⁻¹ * A ^ ((d : ℝ) + 1) = A ^ (t - d + 1) := by
    rw [← Real.rpow_natCast A (2 * d), ← Real.rpow_neg hAn_pos.le,
      ← Real.rpow_add hAn_pos, ← Real.rpow_add hAn_pos]
    congr 1
    push_cast
    ring
  calc
    (A / 3) ^ t * ((A / 3) ^ d * A ^ d)⁻¹ * (Real.sqrt (d : ℝ) * A) ^ ((d : ℝ) + 1)
        = (A ^ t * (3 : ℝ) ^ (-t)) * ((3 : ℝ) ^ d / A ^ (2 * d)) *
            ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * A ^ ((d : ℝ) + 1)) := by
          rw [hstep1, hstep2, hstep3]
    _ = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * ((3 : ℝ) ^ (-t) * (3 : ℝ) ^ d) *
          (A ^ t * (A ^ (2 * d))⁻¹ * A ^ ((d : ℝ) + 1)) := by
          rw [div_eq_mul_inv]; ring
    _ = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) * A ^ (t - d + 1) := by
          rw [hpow_combine, ← Real.rpow_natCast (3 : ℝ) d,
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
            show (-t + (d : ℝ)) = (d : ℝ) - t from by ring]

/-- The level scale is geometric. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_level_scale_pow (s e : ℝ) (hs : 0 < s) (m : ℕ) :
    (s / (3 : ℝ) ^ m) ^ e = s ^ e * ((3 : ℝ) ^ (-e)) ^ m := by
  have hAform : s / (3 : ℝ) ^ m = s * (3 : ℝ) ^ (-(m : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_natCast (3 : ℝ) m,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hAform, Real.mul_rpow hs.le (Real.rpow_nonneg (by norm_num) _)]
  congr 1
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_natCast ((3 : ℝ) ^ (-e)) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- Square roots of an `ENNReal` square bound. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_ennreal_le_of_sq_le {x : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b)
    (h : x ^ (2 : ℕ) ≤ ENNReal.ofReal (b ^ 2)) : x ≤ ENNReal.ofReal b := by
  have hx : x ≠ ⊤ := by
    intro hx
    rw [hx] at h
    simp at h
  rw [← ENNReal.ofReal_toReal hx]
  apply ENNReal.ofReal_le_ofReal
  have h' : ENNReal.ofReal (x.toReal ^ 2) ≤ ENNReal.ofReal (b ^ 2) := by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
    exact h
  have h'' := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg b)).1 h'
  exact (sq_le_sq₀ ENNReal.toReal_nonneg hb).1 h''

/-- The triadic averages at level `m` of `f` on the root cube `centeredCube z s hs`. -/
def aux_prop_uniform_resolvent_cutoff_oscillation_E {d : ℕ} (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (f : SpatialCoordinates d → ℝ) (m : ℕ) (x : SpatialCoordinates d) : ℝ :=
  ∑ k : OddGridIndex d (triadicHalf m),
    (oddGridCell z s hs (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
      (fun _ => SubdiffusiveProcess.CoarseGrainingVocab.averageOn (oddGridCell z s hs (triadicHalf m) k : Set (SpatialCoordinates d)) f) x

/-- The order-`1/2` Gagliardo kernel of `f` on the root cube (the one used by the triadic
increment estimate). -/
def aux_prop_uniform_resolvent_cutoff_oscillation_I {d : ℕ} (U : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ y in U, ∫⁻ x in U, ENNReal.ofReal ((f y - f x) ^ 2) /
    (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)

/-- The level-`m` cell-averaged (mollified) source of the signed measure `h ν`. -/
def aux_prop_uniform_resolvent_cutoff_oscillation_source {d : ℕ} (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (ν : Measure (SpatialCoordinates d)) (h : SpatialCoordinates d → ℝ) (m : ℕ)
    (y : SpatialCoordinates d) : ℝ :=
  ∑ k : OddGridIndex d (triadicHalf m),
    (oddGridCell z s hs (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
      (fun _ => (∫ x in (oddGridCell z s hs (triadicHalf m) k : Set (SpatialCoordinates d)),
          h x ∂ν) /
        volume.real (oddGridCell z s hs (triadicHalf m) k : Set (SpatialCoordinates d))) y

/-- One triadic increment in `L²(ν)`, in geometric form. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_level_bound {d : ℕ} (hd : 2 ≤ d) (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (Homogenization.openCubeSet Qtri))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Qtri), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
    (V Ir : ℝ) (hV : ν.real univ ≤ V) (hIr : 0 ≤ Ir)
    (hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) f ≤
        ENNReal.ofReal Ir)
    (m : ℕ) :
    eLpNorm (fun x => aux_prop_uniform_resolvent_cutoff_oscillation_E (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr f (m + 1) x -
      aux_prop_uniform_resolvent_cutoff_oscillation_E (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr f m x) 2 ν ≤
      ENNReal.ofReal (Real.sqrt ((K + V) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * (Homogenization.cubeScaleFactor Qtri) ^ (t - d + 1) * Ir) *
        (Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ m) := by
  set s := Homogenization.cubeScaleFactor Qtri with hsdef
  have hroot : (centeredCube (Homogenization.cubeCenter Qtri) s hr :
      Set (SpatialCoordinates d)) ⊆ closure (Homogenization.openCubeSet Qtri) := by
    rw [centeredCube_eq_openCubeSet Qtri hr]
    exact subset_closure
  have hinc := globalTriadicAverages_memLp_and_increment_bound hd Qtri
    (Homogenization.cubeCenter Qtri) hr hroot K t hK ht m ν inferInstance hsupp hgrowth f hf
  dsimp only at hinc
  have hsq := hinc.2.2
  have hα : 0 < t - d + 1 := by linarith
  set C0 : ℝ := (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) with hC0
  have hC0nn : 0 ≤ C0 := by positivity
  have hcoef := aux_prop_uniform_resolvent_cutoff_oscillation_level_coeff (d := d) s t hr m
  have hscale := aux_prop_uniform_resolvent_cutoff_oscillation_level_scale_pow s (t - d + 1) hr m
  set ell : ℝ := s / (2 * (triadicHalf m : ℝ) + 1) with hell
  have hellpos : 0 < ell := by rw [hell]; positivity
  have hVnn : 0 ≤ ν.real univ := measureReal_nonneg
  have hq0 : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  set q : ℝ := Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) with hqdef
  have hq2 : q ^ 2 = (3 : ℝ) ^ (-(t - d + 1)) := Real.sq_sqrt hq0
  set X : ℝ := (K + V) * C0 * s ^ (t - d + 1) * Ir with hX
  have hXnn : 0 ≤ X := by
    have : 0 ≤ K + V := by linarith
    positivity
  apply aux_prop_uniform_resolvent_cutoff_oscillation_ennreal_le_of_sq_le (by positivity)
  refine hsq.trans ?_
  have hsqrtd : 0 ≤ Real.sqrt (d : ℝ) * ell := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hsqrtd (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal ((K + ν.real univ) * (ell / 3) ^ t * ((ell / 3) ^ d * ell ^ d)⁻¹ *
          (Real.sqrt (d : ℝ) * ell) ^ ((d : ℝ) + 1)) *
        aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube (Homogenization.cubeCenter Qtri) s hr :
          Set (SpatialCoordinates d)) f
      ≤ ENNReal.ofReal ((K + ν.real univ) * (ell / 3) ^ t * ((ell / 3) ^ d * ell ^ d)⁻¹ *
          (Real.sqrt (d : ℝ) * ell) ^ ((d : ℝ) + 1)) * ENNReal.ofReal Ir := by
        gcongr
    _ = ENNReal.ofReal ((K + ν.real univ) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m))
          * Ir) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_assoc (K + ν.real univ), mul_assoc (K + ν.real univ), hell, hcoef, hscale]
    _ ≤ ENNReal.ofReal ((Real.sqrt X * q ^ m) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow, Real.sq_sqrt hXnn, ← pow_mul, mul_comm m 2, pow_mul, hq2, hX]
        have hA : 0 ≤ C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m) := by positivity
        have hB : K + ν.real univ ≤ K + V := by linarith
        calc (K + ν.real univ) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m)) * Ir
            ≤ (K + V) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m)) * Ir := by
              gcongr
          _ = (K + V) * C0 * s ^ (t - d + 1) * Ir * ((3 : ℝ) ^ (-(t - d + 1))) ^ m := by ring

/-- Pairing identity: the Lebesgue pairing with the cell-averaged source equals the `h ν`
pairing with the cell averages. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_pairing {d : ℕ} (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s) (m : ℕ)
    (ν : Measure (SpatialCoordinates d))
    (h : SpatialCoordinates d → ℝ) (hh : Integrable h ν)
    (ψ : SpatialCoordinates d → ℝ)
    (hψ : IntegrableOn ψ (centeredCube z s hs : Set (SpatialCoordinates d)) volume) :
    ∫ y in (centeredCube z s hs : Set (SpatialCoordinates d)),
        aux_prop_uniform_resolvent_cutoff_oscillation_source z s hs ν h m y * ψ y =
      ∫ x, h x * aux_prop_uniform_resolvent_cutoff_oscillation_E z s hs ψ m x ∂ν := by
  classical
  set C : OddGridIndex d (triadicHalf m) → Set (SpatialCoordinates d) :=
    fun k => (oddGridCell z s hs (triadicHalf m) k : Set (SpatialCoordinates d)) with hCdef
  have hCm : ∀ k, MeasurableSet (C k) :=
    fun k => (oddGridCell z s hs (triadicHalf m) k).isOpen.measurableSet
  have hCsub : ∀ k, C k ⊆ (centeredCube z s hs : Set (SpatialCoordinates d)) :=
    fun k => oddGridCell_subset z hs (triadicHalf m) k
  have hL : ∀ y, aux_prop_uniform_resolvent_cutoff_oscillation_source z s hs ν h m y * ψ y =
      ∑ k, (C k).indicator
        (fun y => ((∫ x in C k, h x ∂ν) / volume.real (C k)) * ψ y) y := by
    intro y
    simp only [aux_prop_uniform_resolvent_cutoff_oscillation_source, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hy : y ∈ C k
    · simp only [hCdef] at hy ⊢
      simp [hy]
    · simp only [hCdef] at hy ⊢
      simp [hy]
  have hR : ∀ x, h x * aux_prop_uniform_resolvent_cutoff_oscillation_E z s hs ψ m x =
      ∑ k, (C k).indicator (fun x => SubdiffusiveProcess.CoarseGrainingVocab.averageOn (C k) ψ * h x) x := by
    intro x
    simp only [aux_prop_uniform_resolvent_cutoff_oscillation_E, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hx : x ∈ C k
    · simp only [hCdef] at hx ⊢
      simp [hx, mul_comm]
    · simp only [hCdef] at hx ⊢
      simp [hx]
  rw [integral_congr_ae (ae_of_all _ hL), integral_congr_ae (ae_of_all _ hR)]
  rw [integral_finset_sum _ (fun k _ => ((hψ.const_mul _).indicator (hCm k))),
    integral_finset_sum _ (fun k _ => ((hh.const_mul _).indicator (hCm k)))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_indicator (hCm k), integral_indicator (hCm k),
    Measure.restrict_restrict (hCm k), Set.inter_eq_left.2 (hCsub k),
    integral_const_mul, integral_const_mul, SubdiffusiveProcess.CoarseGrainingVocab.averageOn, Homogenization.volumeAverage,
    measureReal_def]
  ring


/-- Bounded-density pairing against an `L²(ν)`-small difference. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_pair_diff_bound {α : Type*} {mα : MeasurableSpace α}
    (ν : Measure α) [IsFiniteMeasure ν]
    (h W P : α → ℝ) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hh : AEStronglyMeasurable h ν) (hbound : ∀ᵐ x ∂ν, |h x| ≤ B)
    (hW : AEStronglyMeasurable W ν) (hP : MemLp P 2 ν)
    (hD : eLpNorm (fun x => W x - P x) 2 ν ≤ ENNReal.ofReal T) :
    Integrable (fun x => h x * W x) ν ∧ Integrable (fun x => h x * P x) ν ∧
      ∫ x, h x * W x ∂ν - ∫ x, h x * P x ∂ν ≤ B * Real.sqrt (ν.real univ) * T := by
  have hDm : MemLp (fun x => W x - P x) 2 ν :=
    ⟨hW.sub hP.1, hD.trans_lt ENNReal.ofReal_lt_top⟩
  have hWm : MemLp W 2 ν := by
    have := hDm.add hP
    refine this.congr_norm hW (Eventually.of_forall (fun x => ?_))
    simp
  have hbound' : ∀ᵐ x ∂ν, ‖h x‖ ≤ B := by
    filter_upwards [hbound] with x hx
    simpa [Real.norm_eq_abs] using hx
  have hWi : Integrable W ν := hWm.integrable one_le_two
  have hPi : Integrable P ν := hP.integrable one_le_two
  have hDi : Integrable (fun x => W x - P x) ν := hDm.integrable one_le_two
  have hhW : Integrable (fun x => h x * W x) ν := hWi.bdd_mul hh hbound'
  have hhP : Integrable (fun x => h x * P x) ν := hPi.bdd_mul hh hbound'
  refine ⟨hhW, hhP, ?_⟩
  have hhD : Integrable (fun x => h x * (W x - P x)) ν := hDi.bdd_mul hh hbound'
  rw [← integral_sub hhW hhP]
  have hstep1 : ∫ x, (h x * W x - h x * P x) ∂ν ≤ ∫ x, B * ‖W x - P x‖ ∂ν := by
    apply integral_mono_ae (hhW.sub hhP) (hDi.norm.const_mul B)
    filter_upwards [hbound'] with x hx
    have : h x * W x - h x * P x = h x * (W x - P x) := by ring
    simp only [Pi.sub_apply]
    rw [this]
    calc h x * (W x - P x) ≤ |h x * (W x - P x)| := le_abs_self _
      _ = ‖h x‖ * ‖W x - P x‖ := by rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ B * ‖W x - P x‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  refine hstep1.trans ?_
  rw [integral_const_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hB
  have hmeasD : AEStronglyMeasurable (fun x => W x - P x) ν := hW.sub hP.1
  have hone := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := ν)
    (by norm_num) hmeasD
  rw [integral_norm_eq_lintegral_enorm hmeasD, ← eLpNorm_one_eq_lintegral_enorm]
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [hexp] at hone
  have hmu : ν univ ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (ν.real univ)) := by
    rw [← ofReal_measureReal (measure_ne_top ν univ),
      ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg (by norm_num), Real.sqrt_eq_rpow]
  rw [hmu] at hone
  have hfin : ENNReal.ofReal T * ENNReal.ofReal (Real.sqrt (ν.real univ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h2 : eLpNorm (fun x => W x - P x) 1 ν ≤
      ENNReal.ofReal T * ENNReal.ofReal (Real.sqrt (ν.real univ)) :=
    hone.trans (by gcongr)
  calc (eLpNorm (fun x => W x - P x) 1 ν).toReal
      ≤ (ENNReal.ofReal T * ENNReal.ofReal (Real.sqrt (ν.real univ))).toReal :=
        ENNReal.toReal_mono hfin h2
    _ = Real.sqrt (ν.real univ) * T := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hT,
          ENNReal.toReal_ofReal (Real.sqrt_nonneg _), mul_comm]

/-- Comparison of the order-`1/2` cube kernel with the global order-`3/4` Gagliardo norm of the
zero extension. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_kernel_compare {d : ℕ} (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (φ : SpatialCoordinates d → ℝ) (hφ : Measurable φ) :
    aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube z s hs : Set (SpatialCoordinates d)) φ ≤
      ENNReal.ofReal ((Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) *
        globalFractionalSqNorm (3 / 4)
          ((centeredCube z s hs : Set (SpatialCoordinates d)).indicator φ) := by
  set U : Set (SpatialCoordinates d) := (centeredCube z s hs : Set (SpatialCoordinates d))
    with hUdef
  have hUm : MeasurableSet U := (centeredCube z s hs).isOpen.measurableSet
  set v : SpatialCoordinates d → ℝ := U.indicator φ with hvdef
  have hvm : Measurable v := hφ.indicator hUm
  set c : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) with hcdef
  set K2 : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((v q.1 - v q.2) ^ 2) /
      ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4))
    with hK2def
  have hK2m : Measurable K2 := by
    have h1 : Measurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        ENNReal.ofReal ((v q.1 - v q.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp
        (((hvm.comp measurable_fst).sub (hvm.comp measurable_snd)).pow_const 2)
    have h2 : Measurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^
          ((d : ℝ) + 2 * (3 / 4))) := by
      apply Measurable.pow_const
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.sqrt
      apply Finset.measurable_sum
      intro j _
      exact (((measurable_pi_apply j).comp measurable_fst).sub
        ((measurable_pi_apply j).comp measurable_snd)).pow_const 2
    exact h1.div h2
  have hpt : ∀ y ∈ U, ∀ x ∈ U,
      ENNReal.ofReal ((φ y - φ x) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1) ≤
        c * K2 (y, x) := by
    intro y hy x hx
    have hvy : v y = φ y := Set.indicator_of_mem hy φ
    have hvx : v x = φ x := Set.indicator_of_mem hx φ
    simp only [hK2def, hvy, hvx]
    set D : ℝ := Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2) with hDdef
    set a : ℝ≥0∞ := ENNReal.ofReal ((φ y - φ x) ^ 2) with hadef
    by_cases hD0 : D = 0
    · have hsum : ∑ i : Fin d, (y i - x i) ^ 2 = 0 := by
        have hnn : 0 ≤ ∑ i : Fin d, (y i - x i) ^ 2 :=
          Finset.sum_nonneg (fun i _ => sq_nonneg _)
        have := Real.sqrt_eq_zero hnn
        exact this.1 hD0
      have hyx : y = x := by
        funext i
        have hnn : ∀ j ∈ (Finset.univ : Finset (Fin d)), 0 ≤ (y j - x j) ^ 2 :=
          fun j _ => sq_nonneg _
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ i)
        have : y i - x i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        linarith
      have ha0 : a = 0 := by rw [hadef, hyx]; simp
      rw [ha0, ENNReal.zero_div]
      exact zero_le _
    · have hDpos : 0 < D := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hD0)
      have hDle : D ≤ Real.sqrt (d : ℝ) * s := by
        have hcoord : ∀ i : Fin d, (y i - x i) ^ 2 ≤ s ^ 2 := by
          intro i
          have hyz : dist y z < s / 2 := hy
          have hxz : dist x z < s / 2 := hx
          have hyx : dist y x < s := by
            calc dist y x ≤ dist y z + dist z x := dist_triangle y z x
              _ < s / 2 + s / 2 := by rw [dist_comm z x]; exact add_lt_add hyz hxz
              _ = s := by ring
          have hi : dist (y i) (x i) ≤ dist y x := dist_le_pi_dist y x i
          rw [Real.dist_eq] at hi
          have habs : |y i - x i| ≤ s := by linarith
          have := sq_le_sq' (neg_le_of_abs_le habs) (le_of_abs_le habs)
          simpa using this
        have hsum : ∑ i : Fin d, (y i - x i) ^ 2 ≤ (d : ℝ) * s ^ 2 := by
          calc ∑ i : Fin d, (y i - x i) ^ 2 ≤ ∑ _i : Fin d, s ^ 2 :=
                Finset.sum_le_sum (fun i _ => hcoord i)
            _ = (d : ℝ) * s ^ 2 := by simp
        calc D ≤ Real.sqrt ((d : ℝ) * s ^ 2) := Real.sqrt_le_sqrt hsum
          _ = Real.sqrt (d : ℝ) * s := by
              rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hs.le]
      set X : ℝ≥0∞ := ENNReal.ofReal D ^ ((d : ℝ) + 1) with hXdef
      set Y : ℝ≥0∞ := ENNReal.ofReal D ^ (1 / 2 : ℝ) with hYdef
      have hDne : ENNReal.ofReal D ≠ 0 := by
        simpa [ENNReal.ofReal_eq_zero, not_le] using hDpos
      have hX0 : X ≠ 0 := by
        rw [hXdef]; exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 hDne) ENNReal.ofReal_ne_top).ne'
      have hXt : X ≠ ⊤ := by
        rw [hXdef]; exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
      have hY0 : Y ≠ 0 := by
        rw [hYdef]; exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 hDne) ENNReal.ofReal_ne_top).ne'
      have hYt : Y ≠ ⊤ := by
        rw [hYdef]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
      have hsplit : ENNReal.ofReal D ^ ((d : ℝ) + 2 * (3 / 4)) = X * Y := by
        rw [hXdef, hYdef, ← ENNReal.rpow_add _ _ hDne ENNReal.ofReal_ne_top]
        congr 1
        ring
      have hYc : Y ≤ c := by
        rw [hYdef, hcdef, ENNReal.ofReal_rpow_of_nonneg hDpos.le (by norm_num)]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow hDpos.le hDle (by norm_num))
      rw [hsplit]
      calc a / X = Y * (a / (X * Y)) := by
            rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
              ENNReal.mul_inv (Or.inl hX0) (Or.inl hXt)]
            calc X⁻¹ * a = X⁻¹ * a * (Y * Y⁻¹) := by
                  rw [ENNReal.mul_inv_cancel hY0 hYt, mul_one]
              _ = Y * (X⁻¹ * Y⁻¹ * a) := by ring
        _ ≤ c * (a / (X * Y)) := by gcongr
  calc aux_prop_uniform_resolvent_cutoff_oscillation_I U φ
      = ∫⁻ y in U, ∫⁻ x in U, ENNReal.ofReal ((φ y - φ x) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1) := rfl
    _ ≤ ∫⁻ y in U, ∫⁻ x in U, c * K2 (y, x) := by
        apply setLIntegral_mono' hUm
        intro y hy
        exact setLIntegral_mono' hUm (fun x hx => hpt y hy x hx)
    _ ≤ ∫⁻ y, ∫⁻ x, c * K2 (y, x) := by
        refine (setLIntegral_le_lintegral U _).trans ?_
        exact lintegral_mono (fun y => setLIntegral_le_lintegral U _)
    _ = c * ∫⁻ y, ∫⁻ x, K2 (y, x) := by
        rw [← lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
        congr 1
        funext y
        rw [lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
    _ = c * ∫⁻ q, K2 q := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hK2m.aemeasurable]
    _ ≤ c * globalFractionalSqNorm (3 / 4) v := by
        gcongr
        unfold globalFractionalSqNorm
        exact le_add_self

/-- A segment from a point of an open set to a point outside it meets the frontier no farther
than the far endpoint. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_frontier_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (x y : E) (hx : x ∈ U) (hy : y ∉ U) :
    ∃ z, z ∈ closure U ∧ z ∉ U ∧ dist x z ≤ dist x y := by
  by_contra hcon
  push_neg at hcon
  set S : Set E := segment ℝ x y with hSdef
  have hSsub : S ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · right
      intro hzc
      have hdist : dist x z ≤ dist x y := by
        have hz' : z ∈ segment ℝ x y := hz
        rw [segment_eq_image'] at hz'
        obtain ⟨θ, hθ, rfl⟩ := hz'
        rw [dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hθ.1, ← norm_neg (x - y), neg_sub]
        calc θ * ‖y - x‖ ≤ 1 * ‖y - x‖ :=
              mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
          _ = ‖y - x‖ := one_mul _
      exact absurd hdist (not_le.2 (hcon z hzc hzU))
  have hpre : IsPreconnected S := (convex_segment x y).isPreconnected
  have hdisj : Disjoint U (closure U)ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 subset_closure
  rcases hpre.subset_or_subset hU isClosed_closure.isOpen_compl hdisj hSsub with h | h
  · exact hy (h (right_mem_segment ℝ x y))
  · exact h (left_mem_segment ℝ x y) (subset_closure hx)

/-- A function vanishing off an open set and `1/2`-Hölder on its closure is globally
`1/2`-Hölder with the same constant. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_holder_global {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (v : E → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hzero : ∀ x ∉ U, v x = 0)
    (hhol : ∀ x ∈ closure U, ∀ y ∈ closure U,
      |v x - v y| ≤ C * dist x y ^ (1 / 2 : ℝ)) :
    ∀ x y, |v x - v y| ≤ C * dist x y ^ (1 / 2 : ℝ) := by
  have hone : ∀ x y, x ∈ U → y ∉ U → |v x - v y| ≤ C * dist x y ^ (1 / 2 : ℝ) := by
    intro x y hx hy
    obtain ⟨z, hzc, hzU, hzd⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_frontier_point U hU x y hx hy
    rw [hzero y hy, ← hzero z hzU]
    calc |v x - v z| ≤ C * dist x z ^ (1 / 2 : ℝ) := hhol x (subset_closure hx) z hzc
      _ ≤ C * dist x y ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact Real.rpow_le_rpow dist_nonneg hzd (by norm_num)
  intro x y
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · exact hhol x (subset_closure hx) y (subset_closure hy)
    · exact hone x y hx hy
  · by_cases hy : y ∈ U
    · rw [abs_sub_comm, dist_comm]
      exact hone y x hy hx
    · rw [hzero x hx, hzero y hy, sub_self, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg dist_nonneg _)

/-- The mean minimizes the square deviation. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_variance_le {α : Type*} {mα : MeasurableSpace α}
    (μ : Measure α) [IsFiniteMeasure μ]
    (g : α → ℝ) (hg : MemLp g 2 μ) (c : ℝ) :
    ∫ x, (g x - (μ.real univ)⁻¹ * ∫ y, g y ∂μ) ^ 2 ∂μ ≤ ∫ x, (g x - c) ^ 2 ∂μ := by
  set V : ℝ := μ.real univ with hV
  set m : ℝ := V⁻¹ * ∫ y, g y ∂μ with hm
  by_cases hV0 : V = 0
  · have hμ : μ = 0 := by
      have : μ univ = 0 := by
        rw [← ofReal_measureReal (measure_ne_top μ univ)]
        simp [← hV, hV0]
      exact Measure.measure_univ_eq_zero.1 this
    subst hμ
    simp
  have hgi : Integrable g μ := hg.integrable one_le_two
  have hsq : Integrable (fun x => (g x - m) ^ 2) μ := (hg.sub (memLp_const m)).integrable_sq
  have hlin : Integrable (fun x => 2 * (m - c) * (g x - m)) μ :=
    (hgi.sub (integrable_const m)).const_mul _
  have hpt : ∀ x, (g x - c) ^ 2 = (g x - m) ^ 2 + 2 * (m - c) * (g x - m) + (m - c) ^ 2 := by
    intro x; ring
  have hmean : ∫ x, (g x - m) ∂μ = 0 := by
    rw [integral_sub hgi (integrable_const m), integral_const, smul_eq_mul, hm, ← hV]
    field_simp
    ring
  have hsl : Integrable (fun x => (g x - m) ^ 2 + 2 * (m - c) * (g x - m)) μ := hsq.add hlin
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add hsl (integrable_const _),
    integral_add hsq hlin, integral_const_mul, hmean, integral_const, smul_eq_mul, ← hV]
  have : 0 ≤ V * (m - c) ^ 2 := mul_nonneg measureReal_nonneg (sq_nonneg _)
  linarith

/-- A bounded Lebesgue source has a killed comparison solution (Lax--Milgram with the
coercivity supplied by `hcoer`). -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_comparison_exists {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (Kc : ℝ)
    (hcoer : ∀ v : killedSobolevGraph Ω,
      ‖(v : SobolevData Ω).1‖ ^ 2 ≤ Kc * sobolevCoefficientForm a v.val v.val)
    (F0 : SpatialCoordinates d → ℝ)
    (hF0 : MemLp F0 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    ∃ v : killedSobolevGraph Ω, ∀ w : killedSobolevGraph Ω,
      sobolevCoefficientForm a v.val w.val =
        ∫ x in (Ω : Set (SpatialCoordinates d)), F0 x * (w : SobolevData Ω).1 x := by
  obtain ⟨c, hc, ha⟩ := a.property
  set Wf := weightedGradientForm a.val with hWf
  have hform : ∀ u v : killedSobolevGraph Ω, sobolevCoefficientForm a u.val v.val =
      Wf (subspaceGradient (killedSobolevGraph Ω) u)
        (subspaceGradient (killedSobolevGraph Ω) v) := fun u v => rfl
  set K0 : ℝ := Real.sqrt (max Kc 0 * ‖Wf‖) with hK0
  have hP : ∀ z : killedSobolevGraph Ω, ‖(z : SobolevData Ω).1‖ ≤
      (Real.toNNReal K0 : ℝ) * ‖subspaceGradient (killedSobolevGraph Ω) z‖ := by
    intro z
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    set g := subspaceGradient (killedSobolevGraph Ω) z
    have hE0 : 0 ≤ sobolevCoefficientForm a z.val z.val := sobolevCoefficientForm_nonneg a _
    have hEle : sobolevCoefficientForm a z.val z.val ≤ ‖Wf‖ * ‖g‖ * ‖g‖ := by
      rw [hform]
      exact (le_abs_self _).trans (by
        have := Wf.le_opNorm₂ g g
        rwa [Real.norm_eq_abs] at this)
    have h1 : ‖(z : SobolevData Ω).1‖ ^ 2 ≤ (K0 * ‖g‖) ^ 2 := by
      rw [mul_pow, hK0, Real.sq_sqrt (mul_nonneg (le_max_right Kc 0) (norm_nonneg Wf))]
      calc ‖(z : SobolevData Ω).1‖ ^ 2 ≤ Kc * sobolevCoefficientForm a z.val z.val := hcoer z
        _ ≤ max Kc 0 * sobolevCoefficientForm a z.val z.val :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hE0
        _ ≤ max Kc 0 * (‖Wf‖ * ‖g‖ * ‖g‖) :=
            mul_le_mul_of_nonneg_left hEle (le_max_right _ _)
        _ = max Kc 0 * ‖Wf‖ * ‖g‖ ^ 2 := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 h1
  let L : killedSobolevGraph Ω →L[ℝ] ℝ :=
    (innerSL ℝ (hF0.toLp F0)).comp
      ((ContinuousLinearMap.fst ℝ (DomainL2 Ω) (Fin d → DomainL2 Ω)).comp
        (killedSobolevGraph Ω).subtypeL)
  obtain ⟨u, hu, -⟩ := existsUnique_gradient_subspace_solution (killedSobolevGraph Ω)
    isClosed_killedSobolevGraph (Real.toNNReal K0) hP a.val hc ha L
  refine ⟨u, fun w => ?_⟩
  rw [hform, hu w]
  change inner ℝ (hF0.toLp F0) ((w : SobolevData Ω).1) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hF0] with x hx
  rw [hx]
  simp [mul_comm]


/-- The `L²` norm square is the integral of the square. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_L2_norm_sq {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    (f : Lp ℝ 2 μ) : ∫ a, (f a) ^ 2 ∂μ = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext a
  simp [sq]

/-- A triadic level whose side lies between `min s (1/3) * R` and `R`. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_level_choice (s R : ℝ) (hs : 0 < s) (hR : 0 < R) (hR1 : R ≤ 1) :
    ∃ n : ℕ, s / (3 : ℝ) ^ n ≤ R ∧ min s (1 / 3) * R ≤ s / (3 : ℝ) ^ n := by
  classical
  have hex : ∃ n : ℕ, s / (3 : ℝ) ^ n ≤ R := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / R) (by norm_num : (1 : ℝ) < 3)
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hR] at hn
    linarith [mul_comm R ((3 : ℝ) ^ n)]
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  have hmin_s : min s (1 / 3) ≤ s := min_le_left _ _
  have hmin_t : min s (1 / 3) ≤ 1 / 3 := min_le_right _ _
  have hmin_pos : 0 < min s (1 / 3) := lt_min hs (by norm_num)
  cases hk : Nat.find hex with
  | zero =>
    simp only [pow_zero, div_one]
    calc min s (1 / 3) * R ≤ s * 1 := mul_le_mul hmin_s hR1 hR.le hs.le
      _ = s := mul_one s
  | succ k =>
    have hlt : k < Nat.find hex := by omega
    have hnot := Nat.find_min hex hlt
    push_neg at hnot
    rw [pow_succ, ← div_div]
    have : R / 3 < s / (3 : ℝ) ^ k / 3 := by linarith
    calc min s (1 / 3) * R ≤ (1 / 3) * R := mul_le_mul_of_nonneg_right hmin_t hR.le
      _ = R / 3 := by ring
      _ ≤ s / (3 : ℝ) ^ k / 3 := this.le

/-- The triadic averages are measurable. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_E_measurable {d : ℕ} (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (f : SpatialCoordinates d → ℝ) (m : ℕ) : Measurable (aux_prop_uniform_resolvent_cutoff_oscillation_E z s hs f m) := by
  unfold aux_prop_uniform_resolvent_cutoff_oscillation_E
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact measurable_const.indicator (oddGridCell z s hs (triadicHalf m) k).isOpen.measurableSet

/-- The triadic averages are square integrable for any finite measure. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_E_memLp {d : ℕ} (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (f : SpatialCoordinates d → ℝ) (m : ℕ) (ν : Measure (SpatialCoordinates d))
    [IsFiniteMeasure ν] : MemLp (aux_prop_uniform_resolvent_cutoff_oscillation_E z s hs f m) 2 ν := by
  unfold aux_prop_uniform_resolvent_cutoff_oscillation_E
  refine memLp_finset_sum _ (fun k _ => ?_)
  exact (memLp_const _).indicator (oddGridCell z s hs (triadicHalf m) k).isOpen.measurableSet

/-- The cell-averaged source is measurable. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_source_measurable {d : ℕ} (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (ν : Measure (SpatialCoordinates d)) (h : SpatialCoordinates d → ℝ) (m : ℕ) :
    Measurable (aux_prop_uniform_resolvent_cutoff_oscillation_source z s hs ν h m) := by
  unfold aux_prop_uniform_resolvent_cutoff_oscillation_source
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact measurable_const.indicator (oddGridCell z s hs (triadicHalf m) k).isOpen.measurableSet

/-- Pointwise size of the cell-averaged source from the upper mass growth. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_source_bound {d : ℕ} (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (μ : Measure (SpatialCoordinates d))
    (h : SpatialCoordinates d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂(μ.restrict (centeredCube z s hs : Set (SpatialCoordinates d))), |h x| ≤ B)
    (Km t : ℝ) (hKm : 0 ≤ Km) (ht : 0 < t)
    (hgrowth : ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t))
    (n : ℕ) (hℓ : s / (3 : ℝ) ^ n ≤ 2) (y : SpatialCoordinates d) :
    |aux_prop_uniform_resolvent_cutoff_oscillation_source z s hs (μ.restrict (centeredCube z s hs : Set (SpatialCoordinates d))) h n y|
      ≤ B * Km * (s / (3 : ℝ) ^ n) ^ t / (s / (3 : ℝ) ^ n) ^ d := by
  classical
  set Q : Set (SpatialCoordinates d) := (centeredCube z s hs : Set (SpatialCoordinates d))
    with hQdef
  set ν := μ.restrict Q with hνdef
  set ℓ : ℝ := s / (3 : ℝ) ^ n with hℓdef
  have hℓpos : 0 < ℓ := by positivity
  have hrhs : 0 ≤ B * Km * ℓ ^ t / ℓ ^ d := by positivity
  by_cases hy : ∃ k : OddGridIndex d (triadicHalf n),
      y ∈ (oddGridCell z s hs (triadicHalf n) k : Set (SpatialCoordinates d))
  · obtain ⟨k, hk⟩ := hy
    rw [aux_prop_uniform_resolvent_cutoff_oscillation_source, sum_indicator_triadicCell_eq z hs (triadicHalf n) y _ k hk]
    set C : Set (SpatialCoordinates d) :=
      (oddGridCell z s hs (triadicHalf n) k : Set (SpatialCoordinates d)) with hCdef
    have hCm : MeasurableSet C := (oddGridCell z s hs (triadicHalf n) k).isOpen.measurableSet
    have hCsub : C ⊆ Q := oddGridCell_subset z hs (triadicHalf n) k
    have hside : s / (2 * (triadicHalf n : ℝ) + 1) = ℓ := by rw [triadic_denominator n]
    have hvol : volume.real C = ℓ ^ d := by
      rw [hCdef, oddGridCell_volume_real, hside]
    set c := oddGridCenter z s (triadicHalf n) k with hcdef
    have hCball : C = Metric.ball c (ℓ / 2) := by
      rw [hCdef, ← hside]; rfl
    have hcQ : c ∈ closure Q := by
      apply subset_closure
      apply hCsub
      rw [hCball]
      exact Metric.mem_ball_self (by positivity)
    have hνC : ν C ≤ ENNReal.ofReal (Km * ℓ ^ t) := by
      rw [hνdef, Measure.restrict_apply hCm, Set.inter_eq_left.2 hCsub, hCball]
      refine (hgrowth c hcQ (ℓ / 2) (by positivity) (by linarith)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hKm
      exact Real.rpow_le_rpow (by positivity) (by linarith) ht.le
    have hνCfin : ν C < ⊤ := hνC.trans_lt ENNReal.ofReal_lt_top
    have hνCreal : ν.real C ≤ Km * ℓ ^ t :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hνC
    have hint : ‖∫ x in C, h x ∂ν‖ ≤ B * ν.real C := by
      apply norm_setIntegral_le_of_norm_le_const_ae hνCfin
      filter_upwards [ae_restrict_of_ae hbound] with x hx
      simpa [Real.norm_eq_abs] using hx
    rw [hvol, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ℓ ^ d)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← Real.norm_eq_abs]
    calc ‖∫ x in C, h x ∂ν‖ ≤ B * ν.real C := hint
      _ ≤ B * (Km * ℓ ^ t) := mul_le_mul_of_nonneg_left hνCreal hB
      _ = B * Km * ℓ ^ t := by ring
  · push_neg at hy
    have hzero : aux_prop_uniform_resolvent_cutoff_oscillation_source z s hs ν h n y = 0 := by
      unfold aux_prop_uniform_resolvent_cutoff_oscillation_source
      apply Finset.sum_eq_zero
      intro k _
      exact Set.indicator_of_notMem (hy k) _
    rw [hzero, abs_zero]
    exact hrhs

/-- Distance in `L²(μ|_Q)` from a square-integrable function to its level-`n` triadic averages,
for an absolutely continuous upper-growth measure. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_trace_diff {d : ℕ} (hd : 2 ≤ d) (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0)
    (hgrowth : ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t))
    (hV : μ (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal V0)
    (φ : SpatialCoordinates d → ℝ)
    (hφ : MemLp φ 2 (volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
    (Ir : ℝ) (hIr : 0 ≤ Ir)
    (hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) φ ≤
        ENNReal.ofReal Ir)
    (n : ℕ) :
    eLpNorm (fun x => φ x - aux_prop_uniform_resolvent_cutoff_oscillation_E (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr φ n x) 2
      (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ≤
      ENNReal.ofReal (Real.sqrt ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * (Homogenization.cubeScaleFactor Qtri) ^ (t - d + 1) * Ir) *
        (Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ n /
          (1 - Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))))) := by
  set z := Homogenization.cubeCenter Qtri with hzdef
  set s := Homogenization.cubeScaleFactor Qtri with hsdef
  set Q : Set (SpatialCoordinates d) := (centeredCube z s hr : Set (SpatialCoordinates d))
    with hQdef
  set ν := μ.restrict Q with hνdef
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  have hQeq : Q = Homogenization.openCubeSet Qtri := centeredCube_eq_openCubeSet Qtri hr
  have hsupp : ν (closure (Homogenization.openCubeSet Qtri))ᶜ = 0 := by
    rw [← hQeq, hνdef, Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
    have : (closure Q)ᶜ ∩ Q = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hx.1 (subset_closure hx.2)
    rw [this, measure_empty]
  have hgrowthν : ∀ x ∈ closure (Homogenization.openCubeSet Qtri), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t) := by
    intro x hx ρ hρ hρ1
    rw [← hQeq] at hx
    exact (Measure.restrict_apply_le Q _).trans (hgrowth x hx ρ hρ hρ1)
  have hVr : ν.real univ ≤ V0 := by
    rw [measureReal_def, hνdef, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  have hα : 0 < t - d + 1 := by linarith
  have hq0' : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  have hq1' : (3 : ℝ) ^ (-(t - d + 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set q : ℝ := Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [hqdef, Real.sqrt_lt' one_pos, one_pow]
    exact hq1'
  have hstep : ∀ m, n ≤ m →
      eLpNorm (fun x => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ (m + 1) x - aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m x) 2 ν ≤
        ENNReal.ofReal (Real.sqrt ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * s ^ (t - d + 1) * Ir) * q ^ m) :=
    fun m _ => aux_prop_uniform_resolvent_cutoff_oscillation_level_bound hd Qtri hr Km t hKm ht ν hsupp hgrowthν φ hφ V0 Ir hVr hIr
      hI m
  have hint : IntegrableOn φ Q volume := hφ.integrable one_le_two
  have hleb := aux_prop_uniform_resolvent_cutoff_oscillation_triadic_tendsto_ae hd z hr φ hint
  have hνac : ν ≪ volume := hac
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun m => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m x) atTop (𝓝 (φ x)) := by
    filter_upwards [hνac.ae_le hleb, ae_restrict_mem (centeredCube z s hr).isOpen.measurableSet]
      with x hx hxQ
    exact hx hxQ
  exact aux_prop_uniform_resolvent_cutoff_oscillation_fatou_tail ν (fun m => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m) φ
    (fun m => (aux_prop_uniform_resolvent_cutoff_oscillation_E_measurable z hr φ m).aestronglyMeasurable) hlim n _ q
    (Real.sqrt_nonneg _) hq0 hq1 hstep

/-- `E ≤ A √E` forces `E ≤ A²`. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_sqrt_absorb (E A : ℝ) (hE : 0 ≤ E) (hEA : E ≤ A * Real.sqrt E) :
    E ≤ A ^ 2 := by
  by_cases hE0 : E = 0
  · rw [hE0]; exact sq_nonneg A
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 (lt_of_le_of_ne hE (Ne.symm hE0))
  have hsq : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt hE
  have hle : Real.sqrt E ≤ A := by
    have : Real.sqrt E * Real.sqrt E ≤ A * Real.sqrt E := by rw [hsq]; exact hEA
    exact le_of_mul_le_mul_right this hs
  calc E = Real.sqrt E ^ 2 := (Real.sq_sqrt hE).symm
    _ ≤ A ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

/-- Energy estimate for the difference `w = u_N - v` of the measure-source solution and the
cell-averaged comparison solution. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_w_bound {d : ℕ} (hd : 2 ≤ d) (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 Kc B : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0) (hKc : 0 ≤ Kc) (hB : 0 ≤ B)
    (hgrowth : ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t))
    (hV : μ (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal V0)
    (a : PositiveCoefficient (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr))
    (w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr))
    (hcw1 : ‖(w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
      Kc * sobolevCoefficientForm a w.val w.val)
    (hcw2 : globalFractionalSqNorm (3 / 4)
        (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
          (fun x => (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
      ENNReal.ofReal (Kc * sobolevCoefficientForm a w.val w.val))
    (h : SpatialCoordinates d → ℝ)
    (hh : AEStronglyMeasurable h (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
    (hbound : ∀ᵐ x ∂(μ.restrict (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))), |h x| ≤ B)
    (n : ℕ)
    (hEw : sobolevCoefficientForm a w.val w.val =
      (∫ x in (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
        h x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂μ) -
      ∫ x, h x * aux_prop_uniform_resolvent_cutoff_oscillation_E (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr
          (fun y => (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 y) n x
        ∂(μ.restrict (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) :
    ‖(w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
      Kc ^ 2 * V0 * ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) *
          (Real.sqrt (d : ℝ) * Homogenization.cubeScaleFactor Qtri) ^ (1 / 2 : ℝ)) /
        (1 - Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ 2 * B ^ 2 *
        (Homogenization.cubeScaleFactor Qtri / (3 : ℝ) ^ n) ^ (t - d + 1) := by
  haveI : IsFiniteMeasure (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = sobolevCoefficientForm a w.val w.val := ⟨_, rfl⟩
  rw [← hEdef] at hcw1 hcw2 hEw
  have hE0 : 0 ≤ E := by rw [hEdef]; exact sobolevCoefficientForm_nonneg a _
  have hφ2 : MemLp (fun y => (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr)).1 y) 2
      (volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) := Lp.memLp _
  have hφs : StronglyMeasurable (fun y => (w : SobolevData (centeredCube
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 y) :=
    Lp.stronglyMeasurable _
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ,
      cs = (Real.sqrt (d : ℝ) * Homogenization.cubeScaleFactor Qtri) ^ (1 / 2 : ℝ) :=
    ⟨_, rfl⟩
  have hcs0 : 0 ≤ cs := by rw [hcsdef]; positivity
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ,
      C0 = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) := ⟨_, rfl⟩
  have hC00 : 0 ≤ C0 := by rw [hC0def]; positivity
  have hIr0 : 0 ≤ cs * (Kc * E) := by positivity
  have hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))
      (fun y => (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)).1 y) ≤ ENNReal.ofReal (cs * (Kc * E)) := by
    refine (aux_prop_uniform_resolvent_cutoff_oscillation_kernel_compare _ hr _ hφs.measurable).trans ?_
    rw [ENNReal.ofReal_mul hcs0, ← hcsdef]
    gcongr
  have hT := aux_prop_uniform_resolvent_cutoff_oscillation_trace_diff hd Qtri hr t ht μ hac Km V0 hKm hV0 hgrowth hV _ hφ2
    (cs * (Kc * E)) hIr0 hI n
  rw [← hC0def] at hT
  have hα : 0 < t - d + 1 := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) := ⟨_, rfl⟩
  rw [← hqdef] at hT ⊢
  have hq0' : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  have hq1 : q < 1 := by
    rw [hqdef, Real.sqrt_lt' one_pos, one_pow]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 ≤ q := by rw [hqdef]; exact Real.sqrt_nonneg _
  have h1q : 0 < 1 - q := by linarith
  have hT0 : 0 ≤ Real.sqrt ((Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) * (cs * (Kc * E))) * q ^ n /
      (1 - q) := by positivity
  have hpair := aux_prop_uniform_resolvent_cutoff_oscillation_pair_diff_bound _ h _ _ B _ hB hT0 hh hbound hφs.aestronglyMeasurable
    (aux_prop_uniform_resolvent_cutoff_oscillation_E_memLp _ hr _ n _) hT
  have hVr : Real.sqrt ((μ.restrict (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))).real univ) ≤
      Real.sqrt V0 := by
    apply Real.sqrt_le_sqrt
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = B * Real.sqrt V0 *
      (Real.sqrt ((Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q)) := ⟨_, rfl⟩
  have hEA : E ≤ A * Real.sqrt E := by
    have h1 := hpair.2.2
    rw [← hEw] at h1
    have h3 : Real.sqrt ((Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) * (cs * (Kc * E))) * q ^ n /
        (1 - q) = Real.sqrt ((Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
        Real.sqrt E := by
      rw [show (Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) * (cs * (Kc * E)) =
        ((Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) * (cs * Kc)) * E by ring,
        Real.sqrt_mul' _ hE0]
      ring
    rw [h3] at h1
    calc E ≤ B * Real.sqrt ((μ.restrict (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))).real univ) *
          (Real.sqrt ((Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
            Real.sqrt E) := h1
      _ ≤ B * Real.sqrt V0 *
          (Real.sqrt ((Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
            Real.sqrt E) := by gcongr
      _ = A * Real.sqrt E := by rw [hAdef]; ring
  have hEA2 := aux_prop_uniform_resolvent_cutoff_oscillation_sqrt_absorb E A hE0 hEA
  have hKmV : 0 ≤ Km + V0 := by linarith
  have hscale := aux_prop_uniform_resolvent_cutoff_oscillation_level_scale_pow _ (t - d + 1) hr n
  have hq2 : q ^ 2 = (3 : ℝ) ^ (-(t - d + 1)) := by rw [hqdef]; exact Real.sq_sqrt hq0'
  rw [← hC0def, ← hcsdef]
  calc _ ≤ Kc * E := hcw1
    _ ≤ Kc * A ^ 2 := mul_le_mul_of_nonneg_left hEA2 hKc
    _ = Kc ^ 2 * V0 * ((Km + V0) * C0 * cs) / (1 - q) ^ 2 * B ^ 2 *
          (Homogenization.cubeScaleFactor Qtri / (3 : ℝ) ^ n) ^ (t - d + 1) := by
        have hsq1 : Real.sqrt V0 ^ 2 = V0 := Real.sq_sqrt hV0
        have hsq2 : Real.sqrt ((Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) *
            (cs * Kc)) ^ 2 = (Km + V0) * C0 * Homogenization.cubeScaleFactor Qtri ^ (t - d + 1) *
            (cs * Kc) := Real.sq_sqrt (by positivity)
        have hq2n : (q ^ n) ^ 2 = ((3 : ℝ) ^ (-(t - d + 1))) ^ n := by
          rw [← pow_mul, mul_comm n 2, pow_mul, hq2]
        rw [hscale, hAdef, mul_pow, mul_pow, div_pow, mul_pow, hsq1, hsq2, hq2n]
        field_simp


/-- Square-mean oscillation of `vc + ψ` on a ball, for `vc` globally `1/2`-Hölder and `ψ`
supported in `U` with controlled `L²` norm. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_campanato_assembly {d : ℕ} (U : Set (SpatialCoordinates d))
    (hUm : MeasurableSet U)
    (u0 vc ψ : SpatialCoordinates d → ℝ) (hvc : Continuous vc) (C : ℝ) (hC : 0 ≤ C)
    (hvcHol : ∀ x y, |vc x - vc y| ≤ C * dist x y ^ (1 / 2 : ℝ))
    (hdecomp : u0 =ᵐ[volume] fun y => vc y + U.indicator ψ y)
    (hψ : MemLp ψ 2 (volume.restrict U)) (W2 : ℝ) (hW2 : ∫ y in U, ψ y ^ 2 ≤ W2)
    (x : SpatialCoordinates d) (r : ℝ) :
    ∫ y in Metric.ball x r,
        (u0 y - (volume.real (Metric.ball x r))⁻¹ * ∫ w in Metric.ball x r, u0 w) ^ 2 ≤
      2 * volume.real (Metric.ball x r) * C ^ 2 * r + 2 * W2 := by
  set μB : Measure (SpatialCoordinates d) := volume.restrict (Metric.ball x r) with hμB
  haveI : IsFiniteMeasure μB := by
    refine ⟨?_⟩
    rw [hμB, Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hvolB : volume.real (Metric.ball x r) = μB.real univ := by
    rw [hμB, measureReal_restrict_apply_univ]
  have hψind : MemLp (U.indicator ψ) 2 volume := (memLp_indicator_iff_restrict hUm).2 hψ
  have hvcbd : ∀ᵐ y ∂μB, ‖vc y‖ ≤ |vc x| + C * r ^ (1 / 2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [Real.norm_eq_abs]
    have h1 := hvcHol y x
    have h2 : dist y x ^ (1 / 2 : ℝ) ≤ r ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow dist_nonneg (le_of_lt hy) (by norm_num)
    calc |vc y| = |(vc y - vc x) + vc x| := by ring_nf
      _ ≤ |vc y - vc x| + |vc x| := abs_add_le _ _
      _ ≤ C * r ^ (1 / 2 : ℝ) + |vc x| := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 hC)
      _ = |vc x| + C * r ^ (1 / 2 : ℝ) := by ring
  have hvcL2 : MemLp vc 2 μB := MemLp.of_bound hvc.aestronglyMeasurable _ hvcbd
  have hsumL2 : MemLp (fun y => vc y + U.indicator ψ y) 2 μB :=
    hvcL2.add (hψind.restrict _)
  have hdecB : (fun y => vc y + U.indicator ψ y) =ᵐ[μB] u0 :=
    Filter.EventuallyEq.symm (ae_restrict_of_ae hdecomp)
  have hu0L2 : MemLp u0 2 μB := hsumL2.ae_eq hdecB
  have hvar := aux_prop_uniform_resolvent_cutoff_oscillation_variance_le μB u0 hu0L2 (vc x)
  rw [← hvolB] at hvar
  refine hvar.trans ?_
  have hint1 : Integrable (fun y => (u0 y - vc x) ^ 2) μB :=
    (hu0L2.sub (memLp_const (vc x))).integrable_sq
  have hint2 : Integrable (fun y => (vc y - vc x) ^ 2) μB :=
    (hvcL2.sub (memLp_const (vc x))).integrable_sq
  have hint3 : Integrable (fun y => (U.indicator ψ y) ^ 2) μB :=
    (hψind.restrict _).integrable_sq
  have hint3' : Integrable (fun y => (U.indicator ψ y) ^ 2) volume := hψind.integrable_sq
  have hstep1 : ∫ y, (u0 y - vc x) ^ 2 ∂μB ≤
      ∫ y, (2 * (vc y - vc x) ^ 2 + 2 * (U.indicator ψ y) ^ 2) ∂μB := by
    apply integral_mono_ae hint1 ((hint2.const_mul 2).add (hint3.const_mul 2))
    filter_upwards [ae_restrict_of_ae hdecomp] with y hy
    simp only [Pi.add_apply]
    rw [hy]
    nlinarith [sq_nonneg (vc y - vc x - U.indicator ψ y)]
  have hstep2 : ∫ y, (vc y - vc x) ^ 2 ∂μB ≤ C ^ 2 * r * μB.real univ := by
    have : ∫ y, (vc y - vc x) ^ 2 ∂μB ≤ ∫ _y, C ^ 2 * r ∂μB := by
      apply integral_mono_ae hint2 (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have h1 := hvcHol y x
      have hd : dist y x ^ (1 / 2 : ℝ) = Real.sqrt (dist y x) := (Real.sqrt_eq_rpow _).symm
      rw [hd] at h1
      have h1' : (vc y - vc x) ^ 2 ≤ (C * Real.sqrt (dist y x)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [mul_pow, Real.sq_sqrt dist_nonneg] at h1'
      exact h1'.trans (mul_le_mul_of_nonneg_left (le_of_lt hy) (sq_nonneg C))
    rw [integral_const, smul_eq_mul] at this
    linarith
  have hstep3 : ∫ y, (U.indicator ψ y) ^ 2 ∂μB ≤ W2 := by
    have hle : ∫ y, (U.indicator ψ y) ^ 2 ∂μB ≤ ∫ y, (U.indicator ψ y) ^ 2 :=
      setIntegral_le_integral hint3' (Eventually.of_forall (fun y => sq_nonneg _))
    have heq : ∫ y, (U.indicator ψ y) ^ 2 = ∫ y in U, ψ y ^ 2 := by
      rw [← integral_indicator hUm]
      congr 1
      funext y
      by_cases hy : y ∈ U <;> simp [hy]
    linarith
  have hsplit : ∫ y, (2 * (vc y - vc x) ^ 2 + 2 * (U.indicator ψ y) ^ 2) ∂μB =
      2 * ∫ y, (vc y - vc x) ^ 2 ∂μB + 2 * ∫ y, (U.indicator ψ y) ^ 2 ∂μB := by
    rw [integral_add (hint2.const_mul 2) (hint3.const_mul 2), integral_const_mul,
      integral_const_mul]
  rw [hsplit] at hstep1
  rw [hvolB]
  calc ∫ y, (u0 y - vc x) ^ 2 ∂μB
      ≤ 2 * ∫ y, (vc y - vc x) ^ 2 ∂μB + 2 * ∫ y, (U.indicator ψ y) ^ 2 ∂μB := hstep1
    _ ≤ 2 * (C ^ 2 * r * μB.real univ) + 2 * W2 := by linarith
    _ = 2 * μB.real univ * C ^ 2 * r + 2 * W2 := by ring

/-- Final exponent bookkeeping for the two Campanato terms. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_final_algebra {d : ℕ} (ε r ℓ σ B Km Kh Cw : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hσ : 0 < σ) (hCw : 0 ≤ Cw)
    (hℓR : ℓ ≤ r ^ ((d : ℝ) + 2)) (hℓσ : σ * r ^ ((d : ℝ) + 2) ≤ ℓ) :
    2 * (2 * r) ^ d * (Kh * (B * Km * ℓ ^ ((d : ℝ) - ε) / ℓ ^ d)) ^ 2 * r +
        2 * (Cw * B ^ 2 * ℓ ^ ((d : ℝ) - ε - d + 1)) ≤
      (Real.sqrt (2 * Kh ^ 2 * Km ^ 2 * σ ^ (-2 * ε) + 2 * Cw / 2 ^ d) * B) ^ 2 *
        (2 * r) ^ d * r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * ε)) := by
  have hR : 0 < r ^ ((d : ℝ) + 2) := Real.rpow_pos_of_pos hr0 _
  have hℓ : 0 < ℓ := lt_of_lt_of_le (mul_pos hσ hR) hℓσ
  -- first term
  have hratio : ℓ ^ ((d : ℝ) - ε) / ℓ ^ d = ℓ ^ (-ε) := by
    rw [← Real.rpow_natCast ℓ d, ← Real.rpow_sub hℓ]
    ring_nf
  have hneg : ℓ ^ (-ε) ≤ σ ^ (-ε) * r ^ (-(((d : ℝ) + 2) * ε)) := by
    calc ℓ ^ (-ε) ≤ (σ * r ^ ((d : ℝ) + 2)) ^ (-ε) :=
          Real.rpow_le_rpow_of_nonpos (mul_pos hσ hR) hℓσ (by linarith)
      _ = σ ^ (-ε) * r ^ (-(((d : ℝ) + 2) * ε)) := by
          rw [Real.mul_rpow hσ.le hR.le, ← Real.rpow_mul hr0.le]
          ring_nf
  have hneg2 : (ℓ ^ (-ε)) ^ 2 ≤ σ ^ (-2 * ε) * r ^ (-(2 * ((d : ℝ) + 2) * ε)) := by
    calc (ℓ ^ (-ε)) ^ 2 ≤ (σ ^ (-ε) * r ^ (-(((d : ℝ) + 2) * ε))) ^ 2 :=
          pow_le_pow_left₀ (Real.rpow_nonneg hℓ.le _) hneg 2
      _ = σ ^ (-2 * ε) * r ^ (-(2 * ((d : ℝ) + 2) * ε)) := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (r ^ _),
            ← Real.rpow_mul hσ.le, ← Real.rpow_mul hr0.le]
          ring_nf
  have hexp1 : r ^ (-(2 * ((d : ℝ) + 2) * ε)) * r = r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * ε)) := by
    rw [← Real.rpow_add_one hr0.ne']
    congr 1
    ring
  -- second term
  have hsec : ℓ ^ ((d : ℝ) - ε - d + 1) ≤ r ^ (d : ℝ) * r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * ε)) := by
    have hα : (d : ℝ) - ε - d + 1 = 1 - ε := by ring
    rw [hα]
    calc ℓ ^ (1 - ε) ≤ (r ^ ((d : ℝ) + 2)) ^ (1 - ε) :=
          Real.rpow_le_rpow hℓ.le hℓR (by linarith)
      _ = r ^ (((d : ℝ) + 2) * (1 - ε)) := by rw [← Real.rpow_mul hr0.le]
      _ ≤ r ^ ((d : ℝ) + 2 * (1 / 2 - ((d : ℝ) + 2) * ε)) := by
          apply Real.rpow_le_rpow_of_exponent_ge hr0 hr1
          have : 0 ≤ ((d : ℝ) + 2) * ε := by positivity
          nlinarith
      _ = r ^ (d : ℝ) * r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * ε)) := Real.rpow_add hr0 _ _
  have hrd : r ^ (d : ℝ) = (2 * r) ^ d / 2 ^ d := by
    rw [Real.rpow_natCast, mul_pow]
    field_simp
  have hP : 0 ≤ 2 * Kh ^ 2 * Km ^ 2 * σ ^ (-2 * ε) + 2 * Cw / 2 ^ d := by positivity
  rw [mul_pow (Real.sqrt _) B 2, Real.sq_sqrt hP, mul_div_assoc (B * Km), hratio]
  set β := r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * ε)) with hβ
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have h2r : 0 ≤ (2 * r) ^ d := by positivity
  have hT1 : 2 * (2 * r) ^ d * (Kh * (B * Km * ℓ ^ (-ε))) ^ 2 * r ≤
      2 * Kh ^ 2 * Km ^ 2 * σ ^ (-2 * ε) * B ^ 2 * (2 * r) ^ d * β := by
    have : (Kh * (B * Km * ℓ ^ (-ε))) ^ 2 * r = Kh ^ 2 * B ^ 2 * Km ^ 2 * ((ℓ ^ (-ε)) ^ 2 * r) := by
      ring
    have h' : (ℓ ^ (-ε)) ^ 2 * r ≤ σ ^ (-2 * ε) * β := by
      calc (ℓ ^ (-ε)) ^ 2 * r ≤ σ ^ (-2 * ε) * r ^ (-(2 * ((d : ℝ) + 2) * ε)) * r :=
            mul_le_mul_of_nonneg_right hneg2 hr0.le
        _ = σ ^ (-2 * ε) * β := by rw [mul_assoc, hexp1]
    calc 2 * (2 * r) ^ d * (Kh * (B * Km * ℓ ^ (-ε))) ^ 2 * r
        = 2 * (2 * r) ^ d * (Kh ^ 2 * B ^ 2 * Km ^ 2) * ((ℓ ^ (-ε)) ^ 2 * r) := by
          rw [mul_assoc (2 * (2 * r) ^ d), this]; ring
      _ ≤ 2 * (2 * r) ^ d * (Kh ^ 2 * B ^ 2 * Km ^ 2) * (σ ^ (-2 * ε) * β) := by
          gcongr
      _ = 2 * Kh ^ 2 * Km ^ 2 * σ ^ (-2 * ε) * B ^ 2 * (2 * r) ^ d * β := by ring
  have hT2 : 2 * (Cw * B ^ 2 * ℓ ^ ((d : ℝ) - ε - d + 1)) ≤
      2 * Cw / 2 ^ d * B ^ 2 * (2 * r) ^ d * β := by
    have h' := mul_le_mul_of_nonneg_left hsec (by positivity : 0 ≤ 2 * (Cw * B ^ 2))
    rw [hrd] at h'
    calc 2 * (Cw * B ^ 2 * ℓ ^ ((d : ℝ) - ε - d + 1))
        = 2 * (Cw * B ^ 2) * ℓ ^ ((d : ℝ) - ε - d + 1) := by ring
      _ ≤ 2 * (Cw * B ^ 2) * ((2 * r) ^ d / 2 ^ d * β) := h'
      _ = 2 * Cw / 2 ^ d * B ^ 2 * (2 * r) ^ d * β := by ring
  calc _ ≤ 2 * Kh ^ 2 * Km ^ 2 * σ ^ (-2 * ε) * B ^ 2 * (2 * r) ^ d * β +
        2 * Cw / 2 ^ d * B ^ 2 * (2 * r) ^ d * β := add_le_add hT1 hT2
    _ = _ := by ring


/-- The explicit sample constant of the oscillation estimate. -/
def aux_prop_uniform_resolvent_cutoff_oscillation_Kinst (d : ℕ) (epsilon s Km V0 Kc Kh : ℝ) : ℝ :=
  Real.sqrt (2 * Kh ^ 2 * Km ^ 2 * (min s (1 / 3)) ^ (-2 * epsilon) +
    2 * (Kc ^ 2 * V0 * ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
        (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - epsilon))) * (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) /
      (1 - Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) - epsilon - d + 1)))) ^ 2) / 2 ^ d)

/-- The difference of two killed functions has the difference representative. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_sub_coe {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (u v : killedSobolevGraph Ω) :
    (((u - v : killedSobolevGraph Ω) : SobolevData Ω).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))]
      fun y => (u : SobolevData Ω).1 y - (v : SobolevData Ω).1 y := by
  have h : ((u - v : killedSobolevGraph Ω) : SobolevData Ω).1 =
      (u : SobolevData Ω).1 - (v : SobolevData Ω).1 := by
    rw [Submodule.coe_sub, Prod.fst_sub]
  rw [h]
  exact Lp.coeFn_sub _ _

/-- Bilinearity of the coefficient form in the first slot. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_form_sub {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (u v w : killedSobolevGraph Ω) :
    sobolevCoefficientForm a (u - v : killedSobolevGraph Ω).val w.val =
      sobolevCoefficientForm a u.val w.val - sobolevCoefficientForm a v.val w.val := by
  rw [Submodule.coe_sub, map_sub, ContinuousLinearMap.sub_apply]

/-- Zero extension of the measure-source solution splits into the continuous comparison
solution and the zero extension of the difference. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_decomp {d : ℕ} (U : TopologicalSpace.Opens (SpatialCoordinates d))
    (u v : killedSobolevGraph U) (vc : SpatialCoordinates d → ℝ)
    (hvcae : (((v : SobolevData U).1 : SpatialCoordinates d → ℝ)) =ᵐ[
      volume.restrict (U : Set (SpatialCoordinates d))] vc)
    (hvc0 : ∀ x ∉ (U : Set (SpatialCoordinates d)), vc x = 0)
    (u0 : SpatialCoordinates d → ℝ)
    (hzero : ∀ x, u0 x = Set.indicator (U : Set (SpatialCoordinates d))
      (fun y => (u : SobolevData U).1 y) x) :
    u0 =ᵐ[volume] fun y => vc y + Set.indicator (U : Set (SpatialCoordinates d))
      (fun z => ((u - v : killedSobolevGraph U) : SobolevData U).1 z) y := by
  have hUm : MeasurableSet (U : Set (SpatialCoordinates d)) := U.isOpen.measurableSet
  have h1 := (ae_restrict_iff' hUm).1 hvcae
  have h2 := (ae_restrict_iff' hUm).1 (aux_prop_uniform_resolvent_cutoff_oscillation_sub_coe u v)
  filter_upwards [h1, h2] with y hy1 hy2
  rw [hzero y]
  by_cases hy : y ∈ (U : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hy2 hy, ← hy1 hy]
    ring
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, hvc0 y hy]
    ring

/-- The oscillation estimate for one sample, cutoff, source, centre and radius, with explicit
constants. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_instance {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon < 1)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 Kc Kh : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0) (hKc : 0 ≤ Kc) (hKh : 0 ≤ Kh)
    (hgrowth : ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ ((d : ℝ) - epsilon)))
    (hV : μ (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal V0)
    (a : PositiveCoefficient (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    (hcoer : ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤ Kc * sobolevCoefficientForm a v.val v.val ∧
      globalFractionalSqNorm (3 / 4)
        (Set.indicator (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
        ENNReal.ofReal (Kc * sobolevCoefficientForm a v.val v.val))
    (hHol : ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 → ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), |F0 x| ≤ MF) → ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), sobolevCoefficientForm a v.val w.val =
          ∫ x in (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
            |vc x - vc y| ≤ Kh * MF * dist x y ^ (1 / 2 : ℝ)))
    (u : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (h : SpatialCoordinates d → ℝ)
    (hh : AEStronglyMeasurable h (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂(μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))), |h x| ≤ B)
    (hfin : ∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), sobolevCoefficientForm a u.val w.val =
      ∫ x in (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), h x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂μ)
    (u0 : SpatialCoordinates d → ℝ)
    (hzero : ∀ x, u0 x = Set.indicator (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) (fun y => (u : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 y) x)
    (x : SpatialCoordinates d) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ y in Metric.ball x r,
        (u0 y - (volume.real (Metric.ball x r))⁻¹ * ∫ w in Metric.ball x r, u0 w) ^ 2) ≤
      (aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon (Homogenization.cubeScaleFactor Qtri) Km V0 Kc Kh * B) ^ 2 *
        volume.real (Metric.ball x r) * r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  have hQm : MeasurableSet (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) := (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr).isOpen.measurableSet
  haveI : IsFiniteMeasure (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  have hR0 : 0 < r ^ ((d : ℝ) + 2) := Real.rpow_pos_of_pos hr0 _
  have hR1 : r ^ ((d : ℝ) + 2) ≤ 1 := Real.rpow_le_one hr0.le hr1 (by positivity)
  obtain ⟨n, hn1, hn2⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_level_choice (Homogenization.cubeScaleFactor Qtri)
    (r ^ ((d : ℝ) + 2)) hr hR0 hR1
  have ht0 : 0 < (d : ℝ) - epsilon := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have htd : (d : ℝ) - 1 < (d : ℝ) - epsilon := by linarith
  have hℓpos : 0 < Homogenization.cubeScaleFactor Qtri / (3 : ℝ) ^ n := by positivity
  have hℓ2 : Homogenization.cubeScaleFactor Qtri / (3 : ℝ) ^ n ≤ 2 := by linarith
  obtain ⟨MF, hMFdef⟩ : ∃ MF : ℝ, MF = B * Km *
      (Homogenization.cubeScaleFactor Qtri / (3 : ℝ) ^ n) ^ ((d : ℝ) - epsilon) /
        (Homogenization.cubeScaleFactor Qtri / (3 : ℝ) ^ n) ^ d := ⟨_, rfl⟩
  have hMF0 : 0 ≤ MF := by rw [hMFdef]; positivity
  have hF0b : ∀ y, |aux_prop_uniform_resolvent_cutoff_oscillation_source (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) h n y| ≤ MF := by
    intro y
    rw [hMFdef]
    exact aux_prop_uniform_resolvent_cutoff_oscillation_source_bound _ hr μ h B hB hbound Km _ hKm ht0 hgrowth n hℓ2 y
  have hF0m := aux_prop_uniform_resolvent_cutoff_oscillation_source_measurable (Homogenization.cubeCenter Qtri) hr
    (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) h n
  have hF0L2 : MemLp (aux_prop_uniform_resolvent_cutoff_oscillation_source (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) h n) 2 (volume.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hF0m.aestronglyMeasurable MF
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]; exact hF0b y))
  obtain ⟨v, hv⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_comparison_exists a Kc (fun v => (hcoer v).1) _ hF0L2
  obtain ⟨vc, hvcae, hvc0, hvcHol⟩ := hHol _ hF0m MF hMF0 (fun y _ => hF0b y) v hv
  have hC : 0 ≤ Kh * MF := mul_nonneg hKh hMF0
  have hglob := aux_prop_uniform_resolvent_cutoff_oscillation_holder_global (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr).isOpen vc (Kh * MF) hC hvc0 hvcHol
  have hhint : Integrable h (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) := by
    refine Integrable.mono' (integrable_const B) hh ?_
    filter_upwards [hbound] with y hy
    simpa [Real.norm_eq_abs] using hy
  have hwint : IntegrableOn (fun y => ((u - v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) :
      SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 y) (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) volume :=
    (Lp.memLp _).integrable one_le_two
  have hpair := aux_prop_uniform_resolvent_cutoff_oscillation_pairing (Homogenization.cubeCenter Qtri) hr n (μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) h hhint
    _ hwint
  have hEw : sobolevCoefficientForm a (u - v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).val
      (u - v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).val =
      (∫ y in (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), h y * ((u - v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 y ∂μ) -
      ∫ y, h y * aux_prop_uniform_resolvent_cutoff_oscillation_E (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr
          (fun z => ((u - v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 z) n y
        ∂(μ.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) := by
    rw [aux_prop_uniform_resolvent_cutoff_oscillation_form_sub, hfin, hv, hpair]
  have hwb := aux_prop_uniform_resolvent_cutoff_oscillation_w_bound hd Qtri hr ((d : ℝ) - epsilon) htd μ hac Km V0 Kc B hKm hV0 hKc
    hB hgrowth hV a (u - v) (hcoer (u - v)).1 (hcoer (u - v)).2 h hh hbound n hEw
  have hdecomp := aux_prop_uniform_resolvent_cutoff_oscillation_decomp (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) u v vc hvcae hvc0 u0 hzero
  have hW2 := (aux_prop_uniform_resolvent_cutoff_oscillation_L2_norm_sq
    ((u - v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr)) : SobolevData (centeredCube
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1).trans_le hwb
  have hcamp := aux_prop_uniform_resolvent_cutoff_oscillation_campanato_assembly (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) hQm u0 vc _ vc.continuous (Kh * MF) hC hglob
    hdecomp (Lp.memLp _) _ hW2 x r
  refine hcamp.trans ?_
  have hvol : volume.real (Metric.ball x r) = (2 * r) ^ d := by
    rw [measureReal_def, Real.volume_pi_ball x hr0, Fintype.card_fin,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hvol, hMFdef]
  have hσ : 0 < min (Homogenization.cubeScaleFactor Qtri) (1 / 3) := lt_min hr (by norm_num)
  have hCw : 0 ≤ Kc ^ 2 * V0 * ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
        (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - epsilon))) *
        (Real.sqrt (d : ℝ) * Homogenization.cubeScaleFactor Qtri) ^ (1 / 2 : ℝ)) /
      (1 - Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) - epsilon - d + 1)))) ^ 2 := by
    have : 0 ≤ Km + V0 := by linarith
    positivity
  exact aux_prop_uniform_resolvent_cutoff_oscillation_final_algebra (d := d) epsilon r _ _ B Km Kh _ hepsilon hepsilon1 hr0 hr1 hσ hCw
    hn1 hn2


/-- Uniform mass of the cube from unit-ball growth, by a fixed finite cover of its closure. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_cover {d : ℕ} (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ∃ V1 : ℝ, 0 ≤ V1 ∧ ∀ (μ : Measure (SpatialCoordinates d)) (Km : ℝ), 0 ≤ Km →
      (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), μ (Metric.ball x 1) ≤ ENNReal.ofReal Km) →
      μ (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (V1 * Km) := by
  have hcomp : IsCompact (closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (centeredCube_isBounded _ hr).closure
  obtain ⟨T, hTsub, hTfin, hcover⟩ := finite_cover_balls_of_compact hcomp one_pos
  refine ⟨(hTfin.toFinset.card : ℝ), Nat.cast_nonneg _, ?_⟩
  intro μ Km hKm hball
  have hsub : (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ⊆ ⋃ x ∈ hTfin.toFinset, Metric.ball x 1 := by
    intro y hy
    have := hcover (subset_closure hy)
    simp only [Set.mem_iUnion] at this ⊢
    obtain ⟨x, hxT, hyx⟩ := this
    exact ⟨x, hTfin.mem_toFinset.2 hxT, hyx⟩
  calc μ (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≤ μ (⋃ x ∈ hTfin.toFinset, Metric.ball x 1) := measure_mono hsub
    _ ≤ ∑ x ∈ hTfin.toFinset, μ (Metric.ball x 1) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ hTfin.toFinset, ENNReal.ofReal Km := by
        exact Finset.sum_le_sum (fun x hx => hball x (hTsub (hTfin.mem_toFinset.1 hx)))
    _ = ENNReal.ofReal ((hTfin.toFinset.card : ℝ) * Km) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- One sample: the frozen inputs at a fixed `omega` (plus absolute continuity of the cutoff speed
measures) give one constant for every cutoff, parameter, source, centre and radius. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_omega {d : ℕ} (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (muN : ℕ → Measure (SpatialCoordinates d))
    (E : ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ)
    (RN : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (uN : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    (uN0 : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (aN : ℕ → PositiveCoefficient (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    (hE : ∀ N v w, E N v w = sobolevCoefficientForm (aN N) v.val w.val)
    (hRNmeas : ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        AEMeasurable (RN N lam f) ((muN N).restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
    (hsource : ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ x ∂((muN N).restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))), |f x - lam * RN N lam f x| ≤ 2 * ‖f‖)
    (Kmu : ℝ) (Kcoer Khol : ℕ → ℝ)
    (hconstants : BddAbove (Set.range (fun N => Kcoer N)) ∧
      BddAbove (Set.range (fun N => Khol N)))
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), Metric.ball x 1 ⊆ Region)
    (hfinite : ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
          E N (uN N lam f) w =
            ∫ x in (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), (f x - lam * RN N lam f x) * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N))
    (hzero : ∀ N : ℕ, ∀ lam : ℝ, ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x : SpatialCoordinates d,
        uN0 N lam f x = Set.indicator (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) (fun y => ((uN N lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 y)) x)
    (hgrowth : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ N, muN N (Metric.ball x r) ≤ ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))
    (hcoer : ∀ N : ℕ, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤ Kcoer N * E N v v ∧
      globalFractionalSqNorm (3 / 4) (Set.indicator (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
        ENNReal.ofReal (Kcoer N * E N v v))
    (hHolder : ∀ N : ℕ, ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
      ∀ MF : ℝ, 0 ≤ MF → (∀ x ∈ (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
      ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
          E N v w = ∫ x in (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
            |vc x - vc y| ≤ Khol N * MF * dist x y ^ (1 / 2 : ℝ)))
    (hac : ∀ N, (muN N).restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≪ volume) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x : SpatialCoordinates d, ∀ r : ℝ, 0 < r → r ≤ 1 →
            (∫ y in Metric.ball x r,
              (uN0 N lam f y -
                (volume.real (Metric.ball x r))⁻¹ *
                  ∫ w in Metric.ball x r, uN0 N lam f w) ^ 2) ≤
              (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) *
                r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  obtain ⟨Cc, hCc⟩ := hconstants.1
  obtain ⟨Ch, hCh⟩ := hconstants.2
  have hKc : ∀ N, Kcoer N ≤ max Cc 0 := fun N => (hCc ⟨N, rfl⟩).trans (le_max_left _ _)
  have hKh : ∀ N, Khol N ≤ max Ch 0 := fun N => (hCh ⟨N, rfl⟩).trans (le_max_left _ _)
  have hKc0 : 0 ≤ max Cc 0 := le_max_right _ _
  have hKh0 : 0 ≤ max Ch 0 := le_max_right _ _
  have hKm0 : 0 ≤ max Kmu 0 := le_max_right _ _
  have hε1 : epsilon < 1 := by
    have h8 : (1 : ℝ) ≤ 8 * ((d : ℝ) + 2) := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have : 1 / (8 * ((d : ℝ) + 2)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h8
    linarith
  have hgrowthN : ∀ N, ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      muN N (Metric.ball x ρ) ≤ ENNReal.ofReal (max Kmu 0 * ρ ^ ((d : ℝ) - epsilon)) := by
    intro N x hx ρ hρ hρ1
    refine (hgrowth x (hNeighborhood x hx (Metric.mem_ball_self one_pos)) ρ hρ hρ1 N).trans ?_
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hρ.le _)
  obtain ⟨V1, hV1, hcov⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_cover Qtri hr
  have hV : ∀ N, muN N (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (V1 * max Kmu 0) := by
    intro N
    apply hcov (muN N) (max Kmu 0) hKm0
    intro x hx
    have := hgrowthN N x hx 1 one_pos le_rfl
    rwa [Real.one_rpow, mul_one] at this
  refine ⟨2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon (Homogenization.cubeScaleFactor Qtri) (max Kmu 0)
    (V1 * max Kmu 0) (max Cc 0) (max Ch 0), by unfold aux_prop_uniform_resolvent_cutoff_oscillation_Kinst; positivity, ?_⟩
  intro N lam hlam f x r hr0 hr1
  have hcoerN : ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤ max Cc 0 * sobolevCoefficientForm (aN N) v.val v.val ∧
      globalFractionalSqNorm (3 / 4) (Set.indicator (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
        ENNReal.ofReal (max Cc 0 * sobolevCoefficientForm (aN N) v.val v.val) := by
    intro v
    have hE0 : 0 ≤ sobolevCoefficientForm (aN N) v.val v.val := sobolevCoefficientForm_nonneg _ _
    have hmono : Kcoer N * sobolevCoefficientForm (aN N) v.val v.val ≤
        max Cc 0 * sobolevCoefficientForm (aN N) v.val v.val :=
      mul_le_mul_of_nonneg_right (hKc N) hE0
    have h := hcoer N v
    rw [hE] at h
    exact ⟨h.1.trans hmono, h.2.trans (ENNReal.ofReal_le_ofReal hmono)⟩
  have hHolN : ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 → ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), |F0 x| ≤ MF) → ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), sobolevCoefficientForm (aN N) v.val w.val =
          ∫ x in (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
            |vc x - vc y| ≤ max Ch 0 * MF * dist x y ^ (1 / 2 : ℝ)) := by
    intro F0 hF0 MF hMF hF0b v hv
    have hv' : ∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        E N v w = ∫ x in (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x := by
      intro w; rw [hE]; exact hv w
    obtain ⟨vc, h1, h2, h3⟩ := hHolder N F0 hF0 MF hMF hF0b v hv'
    refine ⟨vc, h1, h2, fun x hx y hy => (h3 x hx y hy).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
    exact mul_le_mul_of_nonneg_right (hKh N) hMF
  have hfin : ∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), sobolevCoefficientForm (aN N) (uN N lam f).val w.val =
      ∫ x in (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), (f x - lam * RN N lam f x) * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N) := by
    intro w; rw [← hE]; exact hfinite N lam hlam f w
  have hh : AEStronglyMeasurable (fun x => f x - lam * RN N lam f x) ((muN N).restrict (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) :=
    (f.continuous.aestronglyMeasurable.sub
      ((hRNmeas N lam hlam f).const_mul lam).aestronglyMeasurable)
  have hmain := aux_prop_uniform_resolvent_cutoff_oscillation_instance hd epsilon hepsilon hε1 Qtri hr (muN N) (hac N) (max Kmu 0)
    (V1 * max Kmu 0) (max Cc 0) (max Ch 0) hKm0 (mul_nonneg hV1 hKm0) hKc0 hKh0 (hgrowthN N)
    (hV N) (aN N) hcoerN hHolN (uN N lam f) (fun x => f x - lam * RN N lam f x) hh (2 * ‖f‖)
    (by positivity) (hsource N lam hlam f) hfin (uN0 N lam f) (hzero N lam f) x r hr0 hr1
  refine hmain.trans (le_of_eq ?_)
  ring




theorem aux_prop_uniform_resolvent_cutoff_oscillation_of_ac
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (P : Measure (BilateralField d))
    (muN : ℕ → BilateralField d → Measure (SpatialCoordinates d))
    (E : ℕ → BilateralField d →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → ℝ)
    (RN : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (uN : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (uN0 : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hE : ∀ N omega v w, E N omega v w =
      sobolevCoefficientForm (aN N omega) v.val w.val)
    (hRNmeas : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        AEMeasurable (RN N omega lam f)
          ((muN N omega).restrict ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))
    (hsource : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ x ∂((muN N omega).restrict
          ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))),
          |f x - lam * RN N omega lam f x| ≤ 2 * ‖f‖)
    (Kmu : BilateralField d → ℝ)
    (Kcoer Khol : ℕ → BilateralField d → ℝ)
    (hconstants : ∀ᵐ omega ∂P,
      BddAbove (Set.range (fun N => Kcoer N omega)) ∧
      BddAbove (Set.range (fun N => Khol N omega)))
    (Region : Set (SpatialCoordinates d))
    (hRegionBounded : Bornology.IsBounded Region)
    (hNeighborhood : ∀ x ∈ closure
        ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hfinite : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
          E N omega (uN N omega lam f) w =
            ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega))
    (hzero : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ,
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x : SpatialCoordinates d,
          uN0 N omega lam f x =
            Set.indicator
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun y => ((uN N omega lam f : SobolevData (centeredCube
                (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr)).1 y)) x)
    (hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ N, muN N omega (Metric.ball x r) ≤
        ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
    (hcoer : ∀ᵐ omega ∂P, ∀ N : ℕ,
      ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E N omega v v ∧
        globalFractionalSqNorm (3 / 4)
          (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
            (fun x => (v : SobolevData (centeredCube
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E N omega v v))
    (hHolder : ∀ᵐ omega ∂P, ∀ N : ℕ,
      ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
      ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        |F0 x| ≤ MF) →
      ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
        (∀ w : killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
          E N omega v w =
            ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              F0 x * (w : SobolevData (centeredCube
                (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x - vc y| ≤ Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
    (hac : ∀ᵐ omega ∂P, ∀ N : ℕ,
      (muN N omega).restrict ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) ≪ volume) :
    ∀ᵐ omega ∂P, ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x : SpatialCoordinates d, ∀ r : ℝ, 0 < r → r ≤ 1 →
            (∫ y in Metric.ball x r,
              (uN0 N omega lam f y -
                (volume.real (Metric.ball x r))⁻¹ *
                  ∫ w in Metric.ball x r, uN0 N omega lam f w) ^ 2) ≤
              (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) *
                r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  filter_upwards [hRNmeas, hsource, hconstants, hfinite, hzero, hgrowth, hcoer, hHolder, hac]
    with omega h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact aux_prop_uniform_resolvent_cutoff_oscillation_omega hd epsilon hepsilon hepsilon' Qtri hr (fun N => muN N omega)
    (fun N => E N omega) (fun N => RN N omega) (fun N => uN N omega) (fun N => uN0 N omega)
    (fun N => aN N omega) (fun N v w => hE N omega v w) h1 h2 (Kmu omega)
    (fun N => Kcoer N omega) (fun N => Khol N omega) h3 Region hNeighborhood h4 h5 h6 h7 h8 h9



/-- Supplier for the repaired input `hac`: the actual finite-cutoff speed measures (and any
restriction of them) are absolutely continuous with respect to Lebesgue measure. -/
theorem aux_prop_uniform_resolvent_cutoff_oscillation_cutoffSpeedMeasure_restrict_ac {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (S T : Set (SpatialCoordinates d)) :
    ((cutoffSpeedMeasure M H omega N).restrict S).restrict T ≪ volume := by
  refine (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self.trans Measure.restrict_le_self)).trans ?_
  exact withDensity_absolutelyContinuous _ _



theorem prop_uniform_resolvent_cutoff_oscillation
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (P : Measure (BilateralField d))
    (muN : ℕ → BilateralField d → Measure (SpatialCoordinates d))
    (E : ℕ → BilateralField d →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → ℝ)
    (RN : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (uN : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (uN0 : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hE : ∀ N omega v w, E N omega v w =
      sobolevCoefficientForm (aN N omega) v.val w.val)
    (hRNmeas : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        AEMeasurable (RN N omega lam f)
          ((muN N omega).restrict ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))
    (hsource : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ x ∂((muN N omega).restrict
          ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))),
          |f x - lam * RN N omega lam f x| ≤ 2 * ‖f‖)
    (Kmu : BilateralField d → ℝ)
    (Kcoer Khol : ℕ → BilateralField d → ℝ)
    (hconstants : ∀ᵐ omega ∂P,
      BddAbove (Set.range (fun N => Kcoer N omega)) ∧
      BddAbove (Set.range (fun N => Khol N omega)))
    (Region : Set (SpatialCoordinates d))
    (hRegionBounded : Bornology.IsBounded Region)
    (hNeighborhood : ∀ x ∈ closure
        ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hfinite : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
          E N omega (uN N omega lam f) w =
            ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega))
    (hzero : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ,
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x : SpatialCoordinates d,
          uN0 N omega lam f x =
            Set.indicator
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun y => ((uN N omega lam f : SobolevData (centeredCube
                (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr)).1 y)) x)
    (hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ N, muN N omega (Metric.ball x r) ≤
        ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
    (hcoer : ∀ᵐ omega ∂P, ∀ N : ℕ,
      ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E N omega v v ∧
        globalFractionalSqNorm (3 / 4)
          (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
            (fun x => (v : SobolevData (centeredCube
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E N omega v v))
    (hHolder : ∀ᵐ omega ∂P, ∀ N : ℕ,
      ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
      ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        |F0 x| ≤ MF) →
      ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
        (∀ w : killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
          E N omega v w =
            ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              F0 x * (w : SobolevData (centeredCube
                (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x - vc y| ≤ Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
    (hac : ∀ᵐ omega ∂P, ∀ N : ℕ,
      (muN N omega).restrict ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) ≪ volume) :
    ∀ᵐ omega ∂P, ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x : SpatialCoordinates d, ∀ r : ℝ, 0 < r → r ≤ 1 →
            (∫ y in Metric.ball x r,
              (uN0 N omega lam f y -
                (volume.real (Metric.ball x r))⁻¹ *
                  ∫ w in Metric.ball x r, uN0 N omega lam f w) ^ 2) ≤
              (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) *
                r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) :=
  aux_prop_uniform_resolvent_cutoff_oscillation_of_ac hd epsilon hepsilon hepsilon' Qtri hr P muN E RN uN uN0 aN hE hRNmeas
    hsource Kmu Kcoer Khol hconstants Region hRegionBounded hNeighborhood hfinite hzero hgrowth
    hcoer hHolder hac

end Paper
