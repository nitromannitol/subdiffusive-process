import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lem_extension_cell_moment
import SubdiffusiveProcess.Paper.lem_cell_ellipticity_compare

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-! ## Ellipticity moments on a cell (paper `mfd:lem-cell-ellipticity`, L8540-8569)

Route (the paper's proof, with the stationary input taken from `lem_extension_cell_moment`):

1. *Stationary unit-cell input* (paper `sup_m ‖Λ_{s,q}(𝕔_0;A_m^0) + λ⁻¹_{s,q}(𝕔_0;A_m^0)‖_{L^{2p}} < ∞`):
   `lem_extension_cell_moment` at `k = 0`, the unit cell about the origin of the root cube
   `(0,2)`, order `β = 1/2 + 4 s0` (`s0 = min(s/2, 1/16)`), moment `4p`, uniformly in the cutoff.
2. *Scaling* (paper `A_N(z+3^{-k}y) = s_N(U) e^{G_k(z+3^{-k}y)-G_k(z)} Ã^0_{N-k}(y)`): the
   two-sided pointwise ratio bound `aux_lem_cell_ellipticity_ratio` between the cell coefficient
   and the zoomed stationary coefficient, with the envelope
   `‖H‖_K + (k physical layers) + 2 log 2 δ² k`.
3. *Monotonicity and homogeneity* of the coarse constants: `lem_cell_ellipticity_compare`.
4. *Hölder and the sub-Gaussian envelope moment*: two Hölder steps, invariance of the chaos law
   under the zoom, and the envelope moment `≤ exp(… + B(2p) δ² k)`, `B(v) = 4 log 2 + v c_d²`;
   `B(2p) ≤ (2 log 2 + c_d²)(p + p²)` for `p ≥ 1` gives the model-free rate. -/

section
open Homogenization Homogenization.Book.Ch02

theorem aux_lem_cell_ellipticity_root_center {d : ℕ} :
    cubeCenter (originCube d 0) = (0 : SpatialCoordinates d) := by
  ext i
  simp only [cubeCenter, originCube, Pi.zero_apply, Int.cast_zero, zero_mul]

theorem aux_lem_cell_ellipticity_root_normalize {d : ℕ} (x : SpatialCoordinates d) :
    aux_lem_extension_cell_moment_cubeNormalize (originCube d 0) x = x := by
  have h := aux_lem_extension_cell_moment_cubeNormalize_scale (originCube d 0) 0
    (by simp only [originCube, Nat.cast_zero, neg_zero]) x
  rw [h, aux_lem_cell_ellipticity_root_center]
  simp only [Nat.cast_zero, zpow_zero, sub_zero, one_smul]

/-- Pointwise two-sided ratio bound between the cell coefficient `A_N(w + 3^{-k} x)` and the
stationary unit-cell coefficient (same infrared field, zoomed sample `om'`, `N - k` layers). -/
theorem aux_lem_cell_ellipticity_ratio {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K K0 : Compacts (SpatialCoordinates d)) (N k : ℕ) (hk : k ≤ N)
    (w : SpatialCoordinates d)
    (hK : ∀ x ∈ openCubeSet (originCube d 0),
      (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈ (K : Set (SpatialCoordinates d)))
    (hK0 : ∀ x ∈ openCubeSet (originCube d 0), x ∈ (K0 : Set (SpatialCoordinates d)))
    (om : BilateralField d) (x : SpatialCoordinates d) (hx : x ∈ openCubeSet (originCube d 0)) :
    cutoffCoefficient M H om N (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ≤
        Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K k w om +
          aux_lem_extension_cell_moment_aboveLogEnvelope M H K0 0 0
            (aux_lem_extension_cell_moment_zoom (k : ℤ) w om)) *
          cutoffCoefficient M H (aux_lem_extension_cell_moment_zoom (k : ℤ) w om) (N - k) x ∧
      cutoffCoefficient M H (aux_lem_extension_cell_moment_zoom (k : ℤ) w om) (N - k) x ≤
        Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K k w om +
          aux_lem_extension_cell_moment_aboveLogEnvelope M H K0 0 0
            (aux_lem_extension_cell_moment_zoom (k : ℤ) w om)) *
          cutoffCoefficient M H om N (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) := by
  set om' := aux_lem_extension_cell_moment_zoom (k : ℤ) w om with hom'
  have h1 := aux_lem_extension_cell_moment_aboveLogEnvelope_bounds M H K N k 0
    (by rwa [Nat.add_zero]) (originCube d 0)
    (by simp only [Nat.cast_zero, sub_zero, descendantsAtScale_self, Finset.mem_singleton]) w (fun x hx => hK x hx) om x hx
  rw [aux_lem_cell_ellipticity_root_normalize, aux_lem_cell_ellipticity_root_center] at h1
  simp only [smul_zero, add_zero] at h1
  have h2 : |Real.log (cutoffCoefficient M H om' (N - k) x) -
      Real.log (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om' (N - k) x)| ≤
      aux_lem_extension_cell_moment_aboveLogEnvelope M H K0 0 0 om' := by
    rw [aux_lem_extension_cell_moment_cutoff_log, aux_lem_extension_cell_moment_cutoff_log]
    simp only [ContinuousMap.zero_apply]
    have hHpt : |H om' x| ≤ ‖(H om').restrict (K0 : Set (SpatialCoordinates d))‖ :=
      ContinuousMap.norm_coe_le_norm ((H om').restrict (K0 : Set (SpatialCoordinates d)))
        ⟨x, hK0 x hx⟩
    have hnn : 0 ≤ aux_lem_extension_cell_moment_physicalLogNorm M (0 - 1)
        ((3 : ℝ) ^ (((0 - 1 : ℕ)) : ℤ) • (0 : SpatialCoordinates d)) om' := norm_nonneg _
    unfold aux_lem_extension_cell_moment_aboveLogEnvelope
    have : -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k)) + H om' x +
        (∑ j ∈ Finset.range (N - k + 1), om' (-(j : ℤ)) x) -
          (((N - k : ℕ) : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
        (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k)) + 0 +
          (∑ j ∈ Finset.range (N - k + 1), om' (-(j : ℤ)) x) -
          (((N - k : ℕ) : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) = H om' x := by ring
    rw [this]
    have hD : 0 ≤ (2 * Real.log 2) * M.delta ^ 2 * ((0 : ℕ) : ℝ) := by positivity
    linarith only [hHpt, hnn, hD]
  have hpos1 := SubdiffusiveProcess.Lane4.cutoffCoefficient_pos M H om N
    (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i)
  have hpos2 := SubdiffusiveProcess.Lane4.cutoffCoefficient_pos M H om' (N - k) x
  have hpos3 := SubdiffusiveProcess.Lane4.cutoffCoefficient_pos M
    (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om' (N - k) x
  have hlog : |Real.log (cutoffCoefficient M H om N (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i)) -
      Real.log (cutoffCoefficient M H om' (N - k) x)| ≤
      aux_lem_extension_cell_moment_aboveLogEnvelope M H K k w om +
        aux_lem_extension_cell_moment_aboveLogEnvelope M H K0 0 0 om' := by
    refine (abs_sub_le _ (Real.log (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
      om' (N - k) x)) _).trans (add_le_add h1 ?_)
    rw [abs_sub_comm]
    exact h2
  exact aux_lem_extension_cell_moment_ratio_of_log hpos1 hpos2 hlog

end

section
open Homogenization Homogenization.Book.Ch02

/-- **Deterministic cell bound.**  The target ellipticities of the cell are at most a
constant times the exponential of the two envelopes times the stationary unit-cell
ellipticities `Λ_{s0,2} + λ_{s0,2}⁻¹` of the zoomed sample. -/
theorem aux_lem_cell_ellipticity_pointwise {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (N k : ℕ) (hk : k ≤ N)
    (w : SpatialCoordinates d)
    (hcell : (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)))
    (K K0 : Compacts (SpatialCoordinates d))
    (hK : ∀ x ∈ openCubeSet (originCube d 0),
      (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈ (K : Set (SpatialCoordinates d)))
    (hK0 : ∀ x ∈ openCubeSet (originCube d 0), x ∈ (K0 : Set (SpatialCoordinates d)))
    (s s0 : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hs0 : 0 < s0) (h2 : 2 * s0 ≤ s)
    (qn : ℝ≥0∞) (hq : qn = 1 ∨ qn = 2)
    (z1 : SpatialCoordinates d) (R1 : ℝ) (hR1 : 0 < R1)
    (w1 : SpatialCoordinates d) (r1 : ℝ) (hr1 : 0 < r1)
    (hsub1 : (centeredCube w1 r1 hr1 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z1 R1 hR1 : Set (SpatialCoordinates d)))
    (hid : ∀ x : SpatialCoordinates d, (fun i => w1 i + r1 * x i) = x)
    (om : BilateralField d) :
    E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ))) s qn +
        (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))
          s qn)⁻¹ ≤
      (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ *
        (Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K k w om +
            aux_lem_extension_cell_moment_aboveLogEnvelope M H K0 0 0
              (aux_lem_extension_cell_moment_zoom (k : ℤ) w om)) *
          (E.Lam z1 R1 hR1 (cutoffPositiveCoefficient M H
              (aux_lem_extension_cell_moment_zoom (k : ℤ) w om) (N - k) z1 hR1) w1 r1 s0 2 +
            (E.lam z1 R1 hR1 (cutoffPositiveCoefficient M H
              (aux_lem_extension_cell_moment_zoom (k : ℤ) w om) (N - k) z1 hR1) w1 r1 s0 2)⁻¹)) := by
  set om' := aux_lem_extension_cell_moment_zoom (k : ℤ) w om with hom'
  set c := Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K k w om +
    aux_lem_extension_cell_moment_aboveLogEnvelope M H K0 0 0 om') with hc
  have hcpos : 0 < c := Real.exp_pos _
  exact lem_cell_ellipticity_compare d E z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
    ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) hcell z1 R1 hR1
    (cutoffPositiveCoefficient M H om' (N - k) z1 hR1) w1 r1 hr1 hsub1
    (fun x => cutoffCoefficient M H om N (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i))
    (fun x => cutoffCoefficient M H om' (N - k) x) c hcpos
    (fun Q hQ => aux_lem_extension_cell_moment_chart_scalar_identity E M H om N z0 R hR w _
      (by positivity) hcell Q hQ)
    (fun Q hQ => by
      have := aux_lem_extension_cell_moment_chart_scalar_identity E M H om' (N - k) z1 R1 hR1
        w1 r1 hr1 hsub1 Q hQ
      simpa only [hid] using this)
    (fun x hx => (aux_lem_cell_ellipticity_ratio M H K K0 N k hk w hK hK0 om x hx).1)
    (fun x hx => (aux_lem_cell_ellipticity_ratio M H K K0 N k hk w hK hK0 om x hx).2)
    s s0 hs hs0 h2 qn hq

end


theorem aux_lem_cell_ellipticity_cell_le {d : ℕ} (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hw : w = 0) (hr1 : r = 1) :
    centeredCube w r hr ≤ centeredCube (0 : SpatialCoordinates d) 2 (by norm_num) := by
  subst hw hr1
  change Metric.ball (0 : SpatialCoordinates d) (1 / 2) ⊆ Metric.ball 0 (2 / 2)
  exact Metric.ball_subset_ball (by norm_num)

section
open Homogenization Homogenization.Book.Ch02

theorem aux_lem_cell_ellipticity_closedBall_zero_mem {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    x ∈ (Metric.closedBall (0 : SpatialCoordinates d) 1 : Set (SpatialCoordinates d)) := by
  have h := aux_lem_extension_cell_moment_mem_unit_root hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [(h i).1, (h i).2]

/-- **Moment bound of the cell ellipticities, given the stationary unit-cell input.** -/
theorem aux_lem_cell_ellipticity_moment {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (p : ℝ) (hp : 1 ≤ p)
    (s s0 : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hs0 : 0 < s0) (h2 : 2 * s0 ≤ s)
    (qn : ℝ≥0∞) (hq : qn = 1 ∨ qn = 2)
    (z1 : SpatialCoordinates d) (R1 : ℝ) (hR1 : 0 < R1)
    (w1 : SpatialCoordinates d) (r1 : ℝ) (hr1 : 0 < r1)
    (hsub1 : (centeredCube w1 r1 hr1 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z1 R1 hR1 : Set (SpatialCoordinates d)))
    (hid : ∀ x : SpatialCoordinates d, (fun i => w1 i + r1 * x i) = x)
    (Cq0 : ℝ) (hCq0 : 0 < Cq0)
    (hY : ∀ N' : ℕ,
      AEStronglyMeasurable (fun om =>
        E.Lam z1 R1 hR1 (cutoffPositiveCoefficient M H om N' z1 hR1) w1 r1 s0 2 +
          (E.lam z1 R1 hR1 (cutoffPositiveCoefficient M H om N' z1 hR1) w1 r1 s0 2)⁻¹)
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om =>
        E.Lam z1 R1 hR1 (cutoffPositiveCoefficient M H om N' z1 hR1) w1 r1 s0 2 +
          (E.lam z1 R1 hR1 (cutoffPositiveCoefficient M H om N' z1 hR1) w1 r1 s0 2)⁻¹)
        (ENNReal.ofReal (2 * (2 * p))) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cq0) :
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (N k : ℕ), k ≤ N → ∀ (w : SpatialCoordinates d),
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
        eLpNorm
            (fun om =>
              E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn +
                (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn)⁻¹)
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cq * Real.exp ((2 * Real.log 2 +
            (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
              (p + p ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
  obtain ⟨CK, hCKnn, hCKb⟩ := aux_lem_extension_cell_moment_aboveEnvelope_moment (d := d) hd
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  let K : Compacts (SpatialCoordinates d) := ⟨Metric.closedBall z0 R, isCompact_closedBall _ _⟩
  let K0 : Compacts (SpatialCoordinates d) := ⟨Metric.closedBall 0 1, isCompact_closedBall _ _⟩
  set C1 : ℝ := (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ with hC1
  have hC1pos : 0 < C1 := by
    have := aux_lem_cell_ellipticity_base_lt_one (s := s0) (q := 2) (by linarith only [hs0])
    exact inv_pos.2 (by linarith only [this])
  set B : ℝ → ℝ := fun v => aux_lem_extension_cell_moment_aboveRate d v with hB
  set a1 : ℝ := Real.exp (Real.log 4 / (2 * p) + 4 * (2 * p) * CK K * M.delta ^ 2 +
    B (2 * p) * M.delta ^ 2) with ha1
  set a2 : ℝ := Real.exp (Real.log 4 / (2 * (2 * p)) + 4 * (2 * (2 * p)) * CK K0 * M.delta ^ 2 +
    B (2 * (2 * p)) * M.delta ^ 2 + B (2 * (2 * p)) * M.delta ^ 2 * ((0 : ℕ) : ℝ)) with ha2
  refine ⟨C1 * a1 * a2 * Cq0, by positivity, ?_⟩
  intro N k hk w hcell
  have hsub : (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
      Set (SpatialCoordinates d)) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)) := hcell
  have hK : ∀ x ∈ openCubeSet (originCube d 0),
      (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈ (K : Set (SpatialCoordinates d)) := by
    intro x hx
    have hyroot := hsub (aux_lem_extension_cell_moment_cellAffine_mem w _ (by positivity) hx)
    change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 ≤ R
    change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 < R / 2 at hyroot
    linarith only [hyroot, hR]
  have hK0 : ∀ x ∈ openCubeSet (originCube d 0), x ∈ (K0 : Set (SpatialCoordinates d)) :=
    fun x hx => aux_lem_cell_ellipticity_closedBall_zero_mem hx
  set μ := (chaosSampleLaw M).toMeasure with hμ
  set T := aux_lem_extension_cell_moment_zoom (k : ℤ) w with hT
  have hTmp : MeasurePreserving T μ μ :=
    aux_lem_extension_cell_moment_zoom_measurePreserving M (k : ℤ) w
  let G1 : BilateralField d → ℝ := fun om =>
    Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K k w om)
  let G2 : BilateralField d → ℝ := fun om =>
    Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K0 0 0 om)
  let Y : BilateralField d → ℝ := fun om =>
    E.Lam z1 R1 hR1 (cutoffPositiveCoefficient M H om (N - k) z1 hR1) w1 r1 s0 2 +
      (E.lam z1 R1 hR1 (cutoffPositiveCoefficient M H om (N - k) z1 hR1) w1 r1 s0 2)⁻¹
  let X : BilateralField d → ℝ := fun om =>
    E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ))) s qn +
      (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))
        s qn)⁻¹
  have hG1m : AEStronglyMeasurable G1 μ :=
    (aux_lem_extension_cell_moment_aboveEnvelope_measurable M H hH.1 K k w).exp.aestronglyMeasurable
  have hG2m : AEStronglyMeasurable G2 μ :=
    (aux_lem_extension_cell_moment_aboveEnvelope_measurable M H hH.1 K0 0 0).exp.aestronglyMeasurable
  obtain ⟨hYm, hYb⟩ := hY (N - k)
  have hGYm : AEStronglyMeasurable (fun om => G2 om * Y om) μ := hG2m.mul hYm
  have hGYTm : AEStronglyMeasurable (fun om => G2 (T om) * Y (T om)) μ :=
    hGYm.comp_measurePreserving hTmp
  have hYnn : ∀ om, 0 ≤ Y om := fun om => by
    have h1 := E.Lam_pos z1 R1 hR1 (cutoffPositiveCoefficient M H om (N - k) z1 hR1) w1 r1 s0 2
    have h2 := inv_pos.2 (E.lam_pos z1 R1 hR1 (cutoffPositiveCoefficient M H om (N - k) z1 hR1)
      w1 r1 s0 2)
    exact (add_pos h1 h2).le
  have hXnn : ∀ om, 0 ≤ X om := fun om => by
    have h1 := E.Lam_pos z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
      ((3 : ℝ) ^ (-(k : ℤ))) s qn
    have h2 := inv_pos.2 (E.lam_pos z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
      ((3 : ℝ) ^ (-(k : ℤ))) s qn)
    exact (add_pos h1 h2).le
  have hpoint : ∀ om, X om ≤ C1 * (G1 om * (G2 (T om) * Y (T om))) := fun om => by
    have h := aux_lem_cell_ellipticity_pointwise E M H z0 R hR N k hk w hsub K K0 hK hK0 s s0 hs
      hs0 h2 qn hq z1 R1 hR1 w1 r1 hr1 hsub1 hid om
    calc X om ≤ _ := h
      _ = _ := by
        simp only [G1, G2, Y, T, Real.exp_add]
        ring
  have hnorm1 : eLpNorm X (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C1 *
      eLpNorm (fun om => G1 om * (G2 (T om) * Y (T om))) (ENNReal.ofReal p) μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards with om
    rw [Real.norm_of_nonneg (hXnn om), Real.norm_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hYnn _)))]
    exact hpoint om
  have hnorm2 := aux_lem_extension_cell_moment_eLpNorm_mul μ p hp0 G1
    (fun om => G2 (T om) * Y (T om)) hG1m hGYTm
  have hnorm3 : eLpNorm (fun om => G2 (T om) * Y (T om)) (ENNReal.ofReal (2 * p)) μ =
      eLpNorm (fun om => G2 om * Y om) (ENNReal.ofReal (2 * p)) μ :=
    eLpNorm_comp_measurePreserving (g := fun om => G2 om * Y om) hGYm hTmp
  have hnorm4 := aux_lem_extension_cell_moment_eLpNorm_mul μ (2 * p) (by positivity) G2 Y
    hG2m hYm
  have hG1b : eLpNorm G1 (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal (Real.exp
      (Real.log 4 / (2 * p) + 4 * (2 * p) * CK K * M.delta ^ 2 + B (2 * p) * M.delta ^ 2 +
        B (2 * p) * M.delta ^ 2 * (k : ℝ))) :=
    hCKb M H hH K k w (2 * p) (by positivity)
  have hG2b : eLpNorm G2 (ENNReal.ofReal (2 * (2 * p))) μ ≤ ENNReal.ofReal a2 :=
    hCKb M H hH K0 0 0 (2 * (2 * p)) (by positivity)
  have hcd : B (2 * p) ≤ (2 * Real.log 2 +
      (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) * (p + p ^ 2) := by
    simp only [hB, aux_lem_extension_cell_moment_aboveRate]
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : 0 ≤ Real.log 2 * ((p - 1) * (p + 2)) :=
      mul_nonneg hl.le (mul_nonneg (sub_nonneg.2 hp) (by linarith only [hp0]))
    have h2 : 0 ≤ (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 * (p * (p - 1)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg hp0.le (sub_nonneg.2 hp))
    nlinarith only [h1, h2]
  have hexp : Real.exp (Real.log 4 / (2 * p) + 4 * (2 * p) * CK K * M.delta ^ 2 +
      B (2 * p) * M.delta ^ 2 + B (2 * p) * M.delta ^ 2 * (k : ℝ)) ≤
      a1 * Real.exp ((2 * Real.log 2 +
        (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
          (p + p ^ 2) * M.delta ^ 2 * (k : ℝ)) := by
    rw [ha1, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hk0 : (0 : ℝ) ≤ M.delta ^ 2 * (k : ℝ) := by positivity
    linarith only [mul_le_mul_of_nonneg_right hcd hk0]
  calc eLpNorm X (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal C1 * eLpNorm (fun om => G1 om * (G2 (T om) * Y (T om)))
          (ENNReal.ofReal p) μ := hnorm1
    _ ≤ ENNReal.ofReal C1 * (eLpNorm G1 (ENNReal.ofReal (2 * p)) μ *
          eLpNorm (fun om => G2 (T om) * Y (T om)) (ENNReal.ofReal (2 * p)) μ) :=
        mul_le_mul' le_rfl hnorm2
    _ = ENNReal.ofReal C1 * (eLpNorm G1 (ENNReal.ofReal (2 * p)) μ *
          eLpNorm (fun om => G2 om * Y om) (ENNReal.ofReal (2 * p)) μ) := by rw [hnorm3]
    _ ≤ ENNReal.ofReal C1 * (eLpNorm G1 (ENNReal.ofReal (2 * p)) μ *
          (eLpNorm G2 (ENNReal.ofReal (2 * (2 * p))) μ *
            eLpNorm Y (ENNReal.ofReal (2 * (2 * p))) μ)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hnorm4)
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal (a1 * Real.exp ((2 * Real.log 2 +
          (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
            (p + p ^ 2) * M.delta ^ 2 * (k : ℝ))) *
          (ENNReal.ofReal a2 * ENNReal.ofReal Cq0)) := by
        refine mul_le_mul' le_rfl (mul_le_mul' ?_ (mul_le_mul' hG2b hYb))
        exact hG1b.trans (ENNReal.ofReal_le_ofReal hexp)
    _ = ENNReal.ofReal (C1 * a1 * a2 * Cq0 * Real.exp ((2 * Real.log 2 +
          (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
            (p + p ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring


end



theorem lem_cell_ellipticity :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d),
  ∃ Cd : ℝ, 0 < Cd ∧
  ∀ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
  ∀ (qn : ℝ≥0∞), (qn = 1 ∨ qn = 2) →
  ∀ (p : ℝ), 1 ≤ p →
  ∃ deltaq : ℝ, 0 < deltaq ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ deltaq →
    ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (N k : ℕ), k ≤ N →
      ∀ (w : SpatialCoordinates d),
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
        AEStronglyMeasurable
            (fun om =>
              E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn +
                (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn)⁻¹)
            (chaosSampleLaw M).toMeasure ∧
        eLpNorm
            (fun om =>
              E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn +
                (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn)⁻¹)
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal
              (Cq * Real.exp (Cd * (p + p ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
  intro d hd _ _ E
  refine ⟨2 * Real.log 2 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2,
    by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity, ?_⟩
  intro s hs qn hqn p hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set s0' : ℝ := min (s / 2) (1 / 16) with hs0'
  have hs0'pos : 0 < s0' := lt_min (by linarith only [hs.1]) (by norm_num)
  have hs0'le : 2 * s0' ≤ s := by have := min_le_left (s / 2) (1 / 16); linarith only [this]
  have hs0'le' : s0' ≤ 1 / 16 := min_le_right _ _
  set beta : ℝ := 1 / 2 + 4 * s0' with hbeta
  have hbeta_mem : beta ∈ Set.Ioo (1 / 2 : ℝ) 1 := ⟨by linarith only [hbeta, hs0'pos], by linarith only [hbeta, hs0'le']⟩
  have hs0eq : (beta - 1 / 2) / 4 = s0' := by rw [hbeta]; ring
  obtain ⟨deltaq, Cd0, hdq, hCd0, hbb⟩ := lem_extension_cell_moment d hd E beta
    ((d + 1 : ℝ) / (2 * (2 * p))) (2 * (2 * p)) hbeta_mem (by positivity) (by linarith only [hp])
    (by rw [mul_div_cancel₀ _ (by positivity)]; linarith only [])
  refine ⟨deltaq, hdq, ?_⟩
  intro M Rm H hH hδ z0 R hR
  obtain ⟨Cq0, hCq0, hbbM⟩ := hbb M Rm H hH hδ 0 2 (by norm_num)
  have hcell0 : centeredCube (fun i => ((0 : ℝ) + (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) * ((0 : ℤ) : ℝ)))
      ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) (by positivity) ≤
      centeredCube (0 : SpatialCoordinates d) 2 (by norm_num) :=
    aux_lem_cell_ellipticity_cell_le _ _ _
      (by funext i; simp only [Nat.cast_zero, neg_zero, zpow_zero, Int.cast_zero, mul_zero, add_zero, Pi.zero_apply])
      (by simp only [Nat.cast_zero, neg_zero, zpow_zero])
  have hY : ∀ N' : ℕ,
      AEStronglyMeasurable (fun om =>
        E.Lam 0 2 (by norm_num) (cutoffPositiveCoefficient M H om N' 0 (by norm_num))
          (fun i => ((0 : ℝ) + (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) * ((0 : ℤ) : ℝ)))
          ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) ((beta - 1 / 2) / 4) 2 +
          (E.lam 0 2 (by norm_num) (cutoffPositiveCoefficient M H om N' 0 (by norm_num))
            (fun i => ((0 : ℝ) + (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) * ((0 : ℤ) : ℝ)))
            ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) ((beta - 1 / 2) / 4) 2)⁻¹)
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om =>
        E.Lam 0 2 (by norm_num) (cutoffPositiveCoefficient M H om N' 0 (by norm_num))
          (fun i => ((0 : ℝ) + (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) * ((0 : ℤ) : ℝ)))
          ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) ((beta - 1 / 2) / 4) 2 +
          (E.lam 0 2 (by norm_num) (cutoffPositiveCoefficient M H om N' 0 (by norm_num))
            (fun i => ((0 : ℝ) + (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) * ((0 : ℤ) : ℝ)))
            ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) ((beta - 1 / 2) / 4) 2)⁻¹)
        (ENNReal.ofReal (2 * (2 * p))) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cq0 := by
    intro N'
    obtain ⟨h1, h2⟩ := hbbM 1 (fun _ => 0) N' 0 0 (fun _ => 0) (Nat.zero_le _) hcell0
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
  obtain ⟨Cq, hCq, hmom⟩ := aux_lem_cell_ellipticity_moment hd E M H hH z0 R hR p hp s
    ((beta - 1 / 2) / 4) hs (by rw [hs0eq]; exact hs0'pos) (by rw [hs0eq]; exact hs0'le) qn hqn
    0 2 (by norm_num) _ ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) (by positivity)
    (fun x hx => hcell0 hx) (fun x => by funext i; simp only [Nat.cast_zero, neg_zero, zpow_zero, Int.cast_zero, mul_zero, zero_add, one_mul]) Cq0 hCq0 hY
  exact ⟨Cq, hCq, fun N k hk w hcell =>
    ⟨aux_lem_cell_ellipticity_aestronglyMeasurable hd E M H hH s hs z0 R hR N w _ (by positivity)
      hcell qn hqn, hmom N k hk w hcell⟩⟩

end Paper
