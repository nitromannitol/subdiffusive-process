import SubdiffusiveProcess.Paper.lem_extremes
import SubdiffusiveProcess.Paper.prop_as_response_bank_shift_invariance
import SubdiffusiveProcess.Analysis.RpowMomentBound
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Lane4.Bridge
import Mathlib.Tactic
open MeasureTheory Set Filter Topology SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The deterministic translation of the whole bilateral field by `w`, exactly the map of
`prop_as_response_bank_shift_invariance`. -/
def aux_lem_cutoffs_damped_extrema_uniform_shift (d : ℕ) (w : SpatialCoordinates d)
    (om : BilateralField d) : BilateralField d :=
  fun j => (om j).comp
    (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
      C(SpatialCoordinates d, SpatialCoordinates d))

theorem aux_lem_cutoffs_damped_extrema_uniform_shift_apply (d : ℕ) (w : SpatialCoordinates d)
    (om : BilateralField d) (j : ℤ) (x : SpatialCoordinates d) :
    aux_lem_cutoffs_damped_extrema_uniform_shift d w om j x = om j (w + x) := by
  have hx : cubeDilation w 0 1 x = w + x := by
    funext i
    simp [cubeDilation]
  simp [aux_lem_cutoffs_damped_extrema_uniform_shift, hx]

/-- The translation preserves the law of the common-scale product field. -/
theorem aux_lem_cutoffs_damped_extrema_uniform_shift_map {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (w : SpatialCoordinates d) :
    Measure.map (aux_lem_cutoffs_damped_extrema_uniform_shift d w)
        (chaosSampleLaw M).toMeasure = (chaosSampleLaw M).toMeasure :=
  prop_as_response_bank_shift_invariance d M w

theorem aux_lem_cutoffs_damped_extrema_uniform_shift_aemeasurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (w : SpatialCoordinates d) :
    AEMeasurable (aux_lem_cutoffs_damped_extrema_uniform_shift d w)
      (chaosSampleLaw M).toMeasure := by
  by_contra h
  have hmap := aux_lem_cutoffs_damped_extrema_uniform_shift_map M w
  rw [Measure.map_of_not_aemeasurable h] at hmap
  have h1 : ((chaosSampleLaw M).toMeasure) Set.univ = 1 := measure_univ
  rw [← hmap] at h1
  simp at h1

/-- Almost-sure properties are transported by the translation. -/
theorem aux_lem_cutoffs_damped_extrema_uniform_shift_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (w : SpatialCoordinates d)
    {P : BilateralField d → Prop}
    (hP : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, P om) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      P (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) := by
  refine ae_of_ae_map
    (aux_lem_cutoffs_damped_extrema_uniform_shift_aemeasurable M w) ?_
  rw [aux_lem_cutoffs_damped_extrema_uniform_shift_map]
  exact hP

theorem aux_lem_cutoffs_damped_extrema_uniform_partialSum_shift (d : ℕ)
    (w : SpatialCoordinates d) (om : BilateralField d) (L : ℕ) (x : SpatialCoordinates d) :
    infraredPartialSum (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) L x =
      infraredPartialSum om L (w + x) - infraredPartialSum om L w := by
  unfold infraredPartialSum
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, aux_lem_cutoffs_damped_extrema_uniform_shift_apply, add_zero]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- The infrared field transforms by translation and recentring, almost surely. -/
theorem aux_lem_cutoffs_damped_extrema_uniform_ir_shift {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (w : SpatialCoordinates d) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x : SpatialCoordinates d,
      H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) x = H om (w + x) - H om w := by
  have h1 := hH.2
  have h2 := aux_lem_cutoffs_damped_extrema_uniform_shift_ae M w h1
  filter_upwards [h1, h2] with om h1 h2
  intro x
  have hA : Tendsto (fun L => infraredPartialSum
      (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) L x) atTop
      (nhds (H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) x)) :=
    ((continuous_eval_const x).tendsto _).comp h2
  have hB : Tendsto (fun L => infraredPartialSum om L (w + x)) atTop (nhds (H om (w + x))) :=
    ((continuous_eval_const (w + x)).tendsto _).comp h1
  have hC : Tendsto (fun L => infraredPartialSum om L w) atTop (nhds (H om w)) :=
    ((continuous_eval_const w).tendsto _).comp h1
  have hD : Tendsto (fun L => infraredPartialSum
      (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) L x) atTop
      (nhds (H om (w + x) - H om w)) := by
    simp only [aux_lem_cutoffs_damped_extrema_uniform_partialSum_shift]
    exact hB.sub hC
  exact tendsto_nhds_unique hA hD

/-- The cutoff coefficient of the translated field is the translated coefficient times the
constant infrared recentring factor. -/
theorem aux_lem_cutoffs_damped_extrema_uniform_cutoff_shift {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : SpatialCoordinates d) (om : BilateralField d)
    (hHw : ∀ x : SpatialCoordinates d,
      H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) x = H om (w + x) - H om w)
    (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) N x =
      cutoffCoefficient M H om N (w + x) * Real.exp (-H om w) := by
  unfold cutoffCoefficient cutoffPotential
  rw [hHw x]
  simp only [aux_lem_cutoffs_damped_extrema_uniform_shift_apply]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A closed root is covered by finitely many closed unit cubes centred in the root. -/
theorem aux_lem_cutoffs_damped_extrema_uniform_unit_cover {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ t : Finset (SpatialCoordinates d),
      (∀ w ∈ t, w ∈ (closedCube z r hr : Set (SpatialCoordinates d))) ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), ∃ w ∈ t,
        x - w ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)) := by
  obtain ⟨t, hts, htfin, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall z (r / 2)) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨htfin.toFinset, ?_, ?_⟩
  · intro w hw
    exact hts (htfin.mem_toFinset.mp hw)
  · intro x hx
    have hx' := hcover (show x ∈ Metric.closedBall z (r / 2) from hx)
    rcases Set.mem_iUnion₂.mp hx' with ⟨w, hw, hxw⟩
    refine ⟨w, htfin.mem_toFinset.mpr hw, ?_⟩
    change x - w ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2)
    rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact (Metric.mem_ball.mp hxw).le


/-- One term of the shifted-cover bracketing: `A = a e^c` with `lo ≤ a ≤ hi`, `0 < lo`. -/
theorem aux_lem_cutoffs_damped_extrema_uniform_term (a lo hi c A : ℝ) (hlo : 0 < lo)
    (h1 : lo ≤ a) (h2 : a ≤ hi) (hA : A = a * Real.exp c) :
    A ≤ Real.exp |c| * hi ∧ A⁻¹ ≤ Real.exp |c| * lo⁻¹ := by
  have ha : 0 < a := hlo.trans_le h1
  have hc1 : Real.exp c ≤ Real.exp |c| := Real.exp_le_exp.2 (le_abs_self c)
  have hc2 : Real.exp (-c) ≤ Real.exp |c| := Real.exp_le_exp.2 (neg_le_abs c)
  constructor
  · rw [hA]
    have hhi : 0 ≤ hi := ha.le.trans h2
    calc a * Real.exp c ≤ hi * Real.exp |c| :=
          mul_le_mul h2 hc1 (Real.exp_pos _).le hhi
      _ = _ := by ring
  · have hinv : a⁻¹ ≤ lo⁻¹ := (inv_le_inv₀ ha hlo).mpr h1
    rw [hA, mul_inv, ← Real.exp_neg]
    calc a⁻¹ * Real.exp (-c) ≤ lo⁻¹ * Real.exp |c| :=
          mul_le_mul hinv hc2 (Real.exp_pos _).le (inv_pos.2 hlo).le
      _ = _ := by ring

/-- **Root-uniform damped extrema.** `lem_extremes` is used once, on the unit cube at the
origin with `p = 2`; the disorder threshold `delta0` depends only on `d` and `eta`. The
extremes on an arbitrary closed root are assembled from the translated unit-cube extremes
over a finite cover, with the infrared recentring factors `e^{±H(w)}` at the cover centres
absorbed by Hölder (exponents `2, 2`). Only the constant `A` and the extremes depend on the
root. -/
theorem lem_cutoffs_damped_extrema_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        ∃ A : ℝ, 0 ≤ A ∧
        ∃ mlow mhigh : ℕ → BilateralField d → ℝ,
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < mlow N om ∧
              ∀ x ∈ (closedCube z0 R hR : Set (SpatialCoordinates d)),
                mlow N om ≤ cutoffCoefficient M H om N x ∧
                  cutoffCoefficient M H om N x ≤ mhigh N om) ∧
          (∀ N : ℕ, MemLp (fun om => (3 : ℝ) ^ (-((N : ℝ) * eta)) *
              (mhigh N om + (mlow N om)⁻¹)) 1 (chaosSampleLaw M).toMeasure) ∧
          (∀ N : ℕ, eLpNorm (fun om => (3 : ℝ) ^ (-((N : ℝ) * eta)) *
              (mhigh N om + (mlow N om)⁻¹)) 1 (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (A * Real.exp (-(eta * Real.log 3 / 2)) ^ N)) := by
  obtain ⟨Cp, Cd, cd, hCp, hCd, hcd, hext⟩ :=
    aux_lem_extremes_compat d hd (0 : SpatialCoordinates d) 1 one_pos 2 (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hCDp : 0 < Cd + Cp := by linarith
  refine ⟨min (cd / 2) (min 1 (eta * Real.log 3 / (2 * (Cd + Cp)))),
    lt_min (by positivity) (lt_min one_pos (div_pos (mul_pos heta hlog3) (by positivity))), ?_⟩
  intro M H hIR hδ z0 R hR
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδcd : M.delta ≤ cd / 2 := hδ.trans (min_le_left _ _)
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδe : M.delta ≤ eta * Real.log 3 / (2 * (Cd + Cp)) :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨D, mlow0, mhigh0, -, hae0, -, hmem0, -, hnorm0⟩ := hext M H hIR hδcd
  have hrate : Cd * M.delta + Cp * M.delta ^ 2 ≤ eta * Real.log 3 / 2 := by
    have h2 : M.delta ^ 2 ≤ M.delta := by
      rw [sq]
      exact mul_le_of_le_one_right hδpos.le hδ1
    have h3 : Cp * M.delta ^ 2 ≤ Cp * M.delta := mul_le_mul_of_nonneg_left h2 hCp.le
    calc Cd * M.delta + Cp * M.delta ^ 2 ≤ Cd * M.delta + Cp * M.delta := by linarith
      _ = (Cd + Cp) * M.delta := by ring
      _ ≤ (Cd + Cp) * (eta * Real.log 3 / (2 * (Cd + Cp))) :=
          mul_le_mul_of_nonneg_left hδe hCDp.le
      _ = eta * Real.log 3 / 2 := by
          field_simp
  obtain ⟨t, htroot, htcover⟩ := aux_lem_cutoffs_damped_extrema_uniform_unit_cover z0 R hR
  have hz : z0 ∈ (closedCube z0 R hR : Set (SpatialCoordinates d)) := by
    change dist z0 z0 ≤ R / 2
    rw [dist_self]
    positivity
  have h0 : (0 : SpatialCoordinates d) ∈
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    change dist (0 : SpatialCoordinates d) 0 ≤ 1 / 2
    rw [dist_self]
    norm_num
  have hne : t.Nonempty := by
    obtain ⟨w, hw, -⟩ := htcover z0 hz
    exact ⟨w, hw⟩
  set μ := (chaosSampleLaw M).toMeasure with hμ
  -- the extremes on the shifted unit cube, and the shifted infrared law, almost surely
  have hall : ∀ᵐ om ∂μ, ∀ w ∈ t,
      (∀ N : ℕ, 0 < mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) ∧
        ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
          mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) ≤ cutoffCoefficient M H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) N x ∧
            cutoffCoefficient M H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) N x ≤ mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om)) ∧
      (∀ x : SpatialCoordinates d, H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) x = H om (w + x) - H om w) := by
    have hae1 : ∀ᵐ om ∂μ, ∀ N : ℕ, 0 < mlow0 N om ∧
        ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
          mlow0 N om ≤ cutoffCoefficient M H om N x ∧
            cutoffCoefficient M H om N x ≤ mhigh0 N om := by
      filter_upwards [hae0] with om hom N
      exact (hom N).2
    refine (Filter.eventually_all_finset t).2 ?_
    intro w _
    exact (aux_lem_cutoffs_damped_extrema_uniform_shift_ae M w hae1).and
      (aux_lem_cutoffs_damped_extrema_uniform_ir_shift M H hIR w)
  have hpos_of : ∀ om, (∀ w ∈ t,
      (∀ N : ℕ, 0 < mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) ∧
        ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
          mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) ≤ cutoffCoefficient M H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) N x ∧
            cutoffCoefficient M H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) N x ≤ mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om)) ∧
      (∀ x : SpatialCoordinates d, H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) x = H om (w + x) - H om w)) →
      ∀ N : ℕ, ∀ w ∈ t, 0 < mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) := by
    intro om hom N w hw
    have hb := ((hom w hw).1 N).2 0 h0
    exact (cutoffCoefficient_pos M H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) N 0).trans_le hb.2
  let mhigh : ℕ → BilateralField d → ℝ :=
    fun N om => ∑ w ∈ t, Real.exp |H om w| * mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om)
  let mlow : ℕ → BilateralField d → ℝ :=
    fun N om => (∑ w ∈ t, Real.exp |H om w| * (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)⁻¹
  have hsum : ∀ N om, mhigh N om + (mlow N om)⁻¹ =
      ∑ w ∈ t, Real.exp |H om w| * (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹) := by
    intro N om
    simp only [mhigh, mlow, inv_inv, ← Finset.sum_add_distrib, mul_add]
  -- (a): bracketing
  have hbracket : ∀ᵐ om ∂μ, ∀ N : ℕ, 0 < mlow N om ∧
      ∀ x ∈ (closedCube z0 R hR : Set (SpatialCoordinates d)),
        mlow N om ≤ cutoffCoefficient M H om N x ∧
          cutoffCoefficient M H om N x ≤ mhigh N om := by
    filter_upwards [hall] with om hom N
    have hpos : ∀ w ∈ t, 0 < Real.exp |H om w| * (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹ := fun w hw =>
      mul_pos (Real.exp_pos _) (inv_pos.2 ((hom w hw).1 N).1)
    have hSpos : 0 < ∑ w ∈ t, Real.exp |H om w| * (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹ :=
      Finset.sum_pos hpos hne
    refine ⟨inv_pos.2 hSpos, ?_⟩
    intro x hx
    obtain ⟨w, hwt, hxw⟩ := htcover x hx
    have hshift := aux_lem_cutoffs_damped_extrema_uniform_cutoff_shift M H w om (hom w hwt).2 N
      (x - w)
    have hwx : w + (x - w) = x := by abel
    rw [hwx] at hshift
    have hb := ((hom w hwt).1 N).2 (x - w) hxw
    have hA : cutoffCoefficient M H om N x =
        cutoffCoefficient M H (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) N (x - w) * Real.exp (H om w) := by
      rw [hshift, mul_assoc, ← Real.exp_add]
      simp
    obtain ⟨h1, h2⟩ := aux_lem_cutoffs_damped_extrema_uniform_term _ _ _ (H om w)
      _ ((hom w hwt).1 N).1 hb.1 hb.2 hA
    have hApos := cutoffCoefficient_pos M H om N x
    constructor
    · have hle : (cutoffCoefficient M H om N x)⁻¹ ≤
          ∑ w ∈ t, Real.exp |H om w| * (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹ :=
        h2.trans (Finset.single_le_sum (f := fun w => Real.exp |H om w| * (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)
          (fun w hw => (hpos w hw).le) hwt)
      exact (inv_le_comm₀ hApos hSpos).1 hle
    · have hhi := hpos_of om hom N
      exact h1.trans (Finset.single_le_sum
        (f := fun w => Real.exp |H om w| * mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))
        (fun w hw => mul_nonneg (Real.exp_pos _).le (hhi w hw).le) hwt)
  -- (b), (c): Hölder with exponents (2, 2)
  have h2e : ENNReal.ofReal 2 = 2 := by simp
  have hE2 : ∀ N : ℕ, MemLp (fun om => mhigh0 N om + (mlow0 N om)⁻¹) 2 μ := fun N => by
    have := hmem0 N
    rwa [h2e] at this
  have hEn2 : ∀ N : ℕ, eLpNorm (fun om => mhigh0 N om + (mlow0 N om)⁻¹) 2 μ ≤
      ENNReal.ofReal (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)) := fun N => by
    have := hnorm0 N
    rwa [h2e] at this
  obtain ⟨Cexp, -, hCexp⟩ := exp_H_point_eLpNorm_uniform_bound hd (d := d)
  have hexp2 : ∀ w : SpatialCoordinates d,
      MemLp (fun om => Real.exp |H om w|) 2 μ := fun w => by
    have := (hCexp M H hIR w 2 two_pos).1
    rwa [h2e] at this
  have hEshift : ∀ (N : ℕ) (w : SpatialCoordinates d),
      MemLp (fun om => mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹) 2 μ ∧
      eLpNorm (fun om => mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹) 2 μ =
        eLpNorm (fun om => mhigh0 N om + (mlow0 N om)⁻¹) 2 μ := by
    intro N w
    have hmap := aux_lem_cutoffs_damped_extrema_uniform_shift_map M w
    have hae := aux_lem_cutoffs_damped_extrema_uniform_shift_aemeasurable M w
    refine ⟨MemLp.comp_of_map (f := aux_lem_cutoffs_damped_extrema_uniform_shift d w)
      (g := fun om => mhigh0 N om + (mlow0 N om)⁻¹) ?_ hae, ?_⟩
    · rw [hmap]
      exact hE2 N
    · have h := eLpNorm_map_measure (p := 2) (f := aux_lem_cutoffs_damped_extrema_uniform_shift d w)
        (g := fun om => mhigh0 N om + (mlow0 N om)⁻¹) (by rw [hmap]; exact (hE2 N).1) hae
      rw [hmap] at h
      exact h.symm
  set S : ℝ≥0∞ := ∑ w ∈ t, eLpNorm (fun om => Real.exp |H om w|) 2 μ with hS
  have hStop : S ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun w _ => (hexp2 w).eLpNorm_lt_top).ne
  have hSs : S = ENNReal.ofReal S.toReal := (ENNReal.ofReal_toReal hStop).symm
  have hterm : ∀ (N : ℕ) (w : SpatialCoordinates d),
      MemLp (fun om => Real.exp |H om w| * (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)) 1 μ ∧
      eLpNorm (fun om => Real.exp |H om w| * (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)) 1 μ ≤
        eLpNorm (fun om => Real.exp |H om w|) 2 μ *
          eLpNorm (fun om => mhigh0 N om + (mlow0 N om)⁻¹) 2 μ := by
    intro N w
    have hf := (hEshift N w).1
    have hφ := hexp2 w
    refine ⟨MemLp.mul' (p := 2) (q := 2) (r := 1) hf hφ, ?_⟩
    have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf.1 hφ.1 (μ := μ)
    rw [(hEshift N w).2] at h
    exact h
  have hFeq : ∀ N : ℕ, (fun om => (3 : ℝ) ^ (-((N : ℝ) * eta)) *
      (mhigh N om + (mlow N om)⁻¹)) = fun om => (3 : ℝ) ^ (-((N : ℝ) * eta)) *
      ∑ w ∈ t, Real.exp |H om w| * (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹) := by
    intro N
    funext om
    rw [hsum N om]
  have hsummem : ∀ N : ℕ, MemLp (fun om => ∑ w ∈ t, Real.exp |H om w| *
      (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)) 1 μ := fun N =>
    memLp_finset_sum t fun w _ => (hterm N w).1
  refine ⟨S.toReal * Cp, mul_nonneg ENNReal.toReal_nonneg hCp.le, mlow, mhigh, hbracket,
    fun N => ?_, fun N => ?_⟩
  · rw [hFeq N]
    exact (hsummem N).const_mul _
  · rw [hFeq N]
    set c : ℝ := (3 : ℝ) ^ (-((N : ℝ) * eta)) with hc
    have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
    have hsmul := eLpNorm_const_smul c (fun om => ∑ w ∈ t, Real.exp |H om w| *
      (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)) 1 μ
    have hsumle : eLpNorm (fun om => ∑ w ∈ t, Real.exp |H om w| *
        (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)) 1 μ ≤
        S * eLpNorm (fun om => mhigh0 N om + (mlow0 N om)⁻¹) 2 μ := by
      have h1 := eLpNorm_sum_le (p := 1) (μ := μ) (s := t)
        (f := fun w om => Real.exp |H om w| * (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹))
        (fun w _ => (hterm N w).1.1) le_rfl
      have h1' : eLpNorm (fun om => ∑ w ∈ t, Real.exp |H om w| *
          (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)) 1 μ =
          eLpNorm (∑ w ∈ t, fun om => Real.exp |H om w| *
            (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)) 1 μ := by
        congr 1
        funext om
        simp [Finset.sum_apply]
      rw [h1', hS, Finset.sum_mul]
      exact h1.trans (Finset.sum_le_sum fun w _ => (hterm N w).2)
    have hkey : c * (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ))) ≤
        Cp * Real.exp (-(eta * Real.log 3 / 2)) ^ N := by
      have hexp : Real.log 3 * (-((N : ℝ) * eta)) +
          (Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ) ≤
          (N : ℝ) * (-(eta * Real.log 3 / 2)) := by
        have h := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg N)
        have e1 : Real.log 3 * (-((N : ℝ) * eta)) = -(2 * ((eta * Real.log 3 / 2) * N)) := by
          ring
        have e2 : (N : ℝ) * (-(eta * Real.log 3 / 2)) = -((eta * Real.log 3 / 2) * N) := by
          ring
        rw [e1, e2]
        linarith
      rw [hc, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_nat_mul]
      calc Real.exp (Real.log 3 * (-((N : ℝ) * eta))) *
            (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)))
          = Cp * Real.exp (Real.log 3 * (-((N : ℝ) * eta)) +
              (Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)) := by
            rw [Real.exp_add]; ring
        _ ≤ Cp * Real.exp ((N : ℝ) * (-(eta * Real.log 3 / 2))) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hCp.le
    have hs0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
    calc eLpNorm (fun om => c * ∑ w ∈ t, Real.exp |H om w| *
          (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)) 1 μ
        = ‖c‖ₑ * eLpNorm (fun om => ∑ w ∈ t, Real.exp |H om w| *
          (mhigh0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om) + (mlow0 N (aux_lem_cutoffs_damped_extrema_uniform_shift d w om))⁻¹)) 1 μ := hsmul
      _ ≤ ENNReal.ofReal c * (S * ENNReal.ofReal
            (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)))) := by
          rw [Real.enorm_of_nonneg hc0]
          exact mul_le_mul_of_nonneg_left (hsumle.trans
            (mul_le_mul_of_nonneg_left (hEn2 N) (zero_le _))) (zero_le _)
      _ = ENNReal.ofReal (S.toReal * (c * (Cp * Real.exp
            ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ))))) := by
          conv_lhs => rw [hSs]
          rw [← ENNReal.ofReal_mul hs0, ← ENNReal.ofReal_mul hc0]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (S.toReal * Cp * Real.exp (-(eta * Real.log 3 / 2)) ^ N) := by
          apply ENNReal.ofReal_le_ofReal
          calc S.toReal * (c * (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ))))
              ≤ S.toReal * (Cp * Real.exp (-(eta * Real.log 3 / 2)) ^ N) :=
                mul_le_mul_of_nonneg_left hkey hs0
            _ = _ := by ring

end Paper
