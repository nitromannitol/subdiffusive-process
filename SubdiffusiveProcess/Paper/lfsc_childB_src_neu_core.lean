module

public import SubdiffusiveProcess.FiniteStopping.SourcedStageAt
public import SubdiffusiveProcess.FiniteStopping.HarmonicStepComparison
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.MeanZero
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.lem_finite_stopping_crude_cost
public import SubdiffusiveProcess.Paper.lem_finite_stopping_moments
public import SubdiffusiveProcess.Paper.lfsc_childB_src_dir_core0
public import SubdiffusiveProcess.Paper.fscc_holder_predicates

@[expose] public section

/-!
# `lfsc_childB_src_neu_core` — sourced ChildB (mean-zero Neumann), one coefficient family

Neumann half of `\label{mfd:lem-finite-source-comparison}` (proof, paragraph 3): for a mean-zero Neumann source solution the
`C^α` representative is the Hölder bundle of `fscc_*_holder_neumann` (`holNeu`, `J ≥ -j`); its oscillation bounds its sup
(mean zero), which gives the global energy `∫ F u ≤ Kf |Q| sup|u|` (no growth theorem) and the crude cell cost by the extension
estimate exactly as in the Dirichlet case.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

/-- A function continuous on the closed cube has a continuous extension to the whole space that agrees with it on the
closed cube (compose with the coordinatewise clamp). -/
theorem aux_lfsc_childB_src_neu_core_extend {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d))) :
    ∃ U' : SpatialCoordinates d → ℝ, Continuous U' ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), U' x = U x := by
  let cl : SpatialCoordinates d → SpatialCoordinates d :=
    fun x i => max (z i - r / 2) (min (z i + r / 2) (x i))
  have hcl : Continuous cl := continuous_pi fun i =>
    continuous_const.max (continuous_const.min (continuous_apply i))
  have hmem : ∀ x, cl x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    intro x
    change cl x ∈ Metric.closedBall z (r / 2)
    rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity)]
    intro i
    rw [Real.dist_eq, abs_le]
    have h1 : z i - r / 2 ≤ max (z i - r / 2) (min (z i + r / 2) (x i)) := le_max_left _ _
    have h2 : max (z i - r / 2) (min (z i + r / 2) (x i)) ≤ z i + r / 2 :=
      max_le (by linarith) (min_le_left _ _)
    show -(r / 2) ≤ cl x i - z i ∧ cl x i - z i ≤ r / 2
    constructor <;> simp only [cl] <;> linarith
  refine ⟨U ∘ cl, hU.comp_continuous hcl hmem, ?_⟩
  intro x hx
  change U (cl x) = U x
  congr 1
  funext i
  have hx' : x ∈ Metric.closedBall z (r / 2) := hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity)] at hx'
  have := hx' i
  rw [Real.dist_eq, abs_le] at this
  simp only [cl]
  rw [min_eq_right (by linarith [this.2]), max_eq_right (by linarith [this.1])]

/-- Mean zero and a uniform oscillation bound bound the sup: `|U| ≤ Ω`. -/
theorem aux_lfsc_childB_src_neu_core_sup_le {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)))
    (hmean : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), U x) = 0) {Om : ℝ}
    (hosc : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)), |U x - U y| ≤ Om) :
    ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), |U x| ≤ Om := by
  intro x hx
  have hQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr :=
    centeredCube_subset_closedCube z hr
  have hint : IntegrableOn U (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (hU.integrableOn_compact (closedCube z r hr).isCompact).mono_set hQ
  have hvol : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    centeredCube_volume_pos z hr
  have h1 : ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), (U x - U y) =
      U x * volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    have hc : IntegrableOn (fun _ : SpatialCoordinates d => U x)
        (centeredCube z r hr : Set (SpatialCoordinates d)) volume :=
      integrableOn_const (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top) enorm_ne_top
    rw [integral_sub hc hint, hmean, setIntegral_const, sub_zero, smul_eq_mul, mul_comm]
  have h2 : ‖∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), (U x - U y)‖ ≤
      Om * volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    norm_setIntegral_le_of_norm_le_const (by rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top)
      (fun y hy => by rw [Real.norm_eq_abs]; exact hosc x hx y (hQ hy))
  rw [h1, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hvol.le] at h2
  exact le_of_mul_le_mul_right h2 hvol

/-- Sup-metric Hölder bound gives the Hölder seminorm bound. -/
theorem aux_lfsc_childB_src_neu_core_holder {d : ℕ} (S : Set (SpatialCoordinates d))
    (U : SpatialCoordinates d → ℝ) {alpha L : ℝ} (halpha : 0 < alpha) (hL : 0 ≤ L)
    (h : ∀ x ∈ S, ∀ y ∈ S, |U x - U y| ≤ L * dist x y ^ alpha) :
    IsHolderOn alpha S U ∧ holderSeminorm alpha S U ≤ L := by
  have hb : ∀ v ∈ holderRatioSet alpha S U, v ≤ L := by
    rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
    have hdpos : 0 < dist x y := dist_pos.mpr hxy
    have hle : dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      rw [dist_pi_le_iff (Real.sqrt_nonneg _)]
      intro j
      rw [Real.dist_eq]
      calc |x j - y j| = Real.sqrt ((x j - y j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    have hepos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := lt_of_lt_of_le hdpos hle
    have hpow : dist x y ^ alpha ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha :=
      Real.rpow_le_rpow dist_nonneg hle halpha.le
    have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha := Real.rpow_pos_of_pos hepos _
    rw [div_le_iff₀ hpos]
    calc |U x - U y| ≤ L * dist x y ^ alpha := h x hx y hy
      _ ≤ L * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha := by gcongr
  exact ⟨⟨L, hb⟩, Real.sSup_le hb hL⟩

/-- Both clauses at one sample, explicit random constants (Neumann counterpart of `aux_lfsc_childB_src_dir_omega`). -/
theorem aux_lfsc_childB_src_neu_omega {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    {σ α β η C1 : ℝ} (hα : 0 < α) (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) (hβα : β ≤ α) (hαβ1 : α - β ≤ 1)
    (hσ : 2 - 2 * α + η ≤ σ) (hC1 : 0 < C1)
    (h1 : aux_lem_finite_stopping_crude_cost_ClauseOne Jc β C1)
    {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {Hs Ht : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (z : SpatialCoordinates d) (j : ℤ) (hr : (0 : ℝ) < (3 : ℝ) ^ j) (H1 : ℕ) (hH1 : 0 < H1)
    (N : ℕ) (hNj : 4 * j.natAbs ≤ N) (hNH : 4 * H1 ≤ N) (T S : ℕ) (hNT : N ≤ T)
    (omega : BilateralField d) (KhS : ℝ) (Ke : ℕ → ℝ)
    (hHol : aux_fscc_holder_predicates_holNeu d z ((3 : ℝ) ^ j) hr
      (cutoffPositiveCoefficient model Hs omega S z hr) α KhS)
    (hEω : aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Ht z j β η omega Ke)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf) (hFm : Measurable F)
    (hFb : ∀ x ∈ centeredCube z ((3 : ℝ) ^ j) hr, |F x| ≤ Kf)
    (hmean : (∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)), F x) = 0)
    (u : meanZeroSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (hsol : SolvesNeumann (cutoffPositiveCoefficient model Hs omega S z hr) F u) :
    let uw : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr) :=
      ⟨(u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)),
        ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩
    (∀ (w0 : Fin (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) → OddGridIndex d 1)
        (w : Fin (aux_lem_finite_stopping_crude_cost_obsB H1 N) →
          OddGridIndex d (subdivisionHalfWidth H1)),
      aux_lem_finite_stopping_crude_cost_respOn (cutoffPositiveCoefficient model Ht omega T z hr) uw
          (aux_lem_finite_stopping_crude_cost_cell2_le_root z hr
            (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
            (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
          (aux_lem_finite_stopping_crude_cost_cell2_killedPoincare z hr
            (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
            (aux_lem_finite_stopping_crude_cost_obsB H1 N) w) ≤
        (C1 * (d : ℝ) * |Ke T| * (|KhS| * (((3 : ℝ) ^ j) ^ α + 1)) ^ 2) *
          (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_crude_cost_obsB H1 N)
            (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^
              ((d : ℝ) - σ) * Kf ^ 2) ∧
    aux_lem_finite_stopping_crude_cost_energyOn (cutoffPositiveCoefficient model Hs omega S z hr)
        (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (|KhS| * (((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ j) ^ α)) * Kf ^ 2 := by
  intro uw
  obtain ⟨U, hUc, hUeq, hUh⟩ := hHol F Kf hKf hFm hFb hmean u hsol
  have hQ : (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ⊆
      closedCube z ((3 : ℝ) ^ j) hr := centeredCube_subset_closedCube z hr
  have hrα : 0 ≤ ((3 : ℝ) ^ j) ^ α := Real.rpow_nonneg hr.le _
  set Om : ℝ := |KhS| * Kf * ((3 : ℝ) ^ j) ^ α with hOm
  have hOm0 : 0 ≤ Om := by positivity
  have hdist : ∀ x ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)), dist x y ≤ (3 : ℝ) ^ j := by
    intro x hx y hy
    have hx' : dist x z ≤ (3 : ℝ) ^ j / 2 := hx
    have hy' : dist y z ≤ (3 : ℝ) ^ j / 2 := hy
    calc dist x y ≤ dist x z + dist y z := dist_triangle_right x y z
      _ ≤ _ := by linarith
  have hosc : ∀ x ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)), |U x - U y| ≤ Om := by
    intro x hx y hy
    calc |U x - U y| ≤ KhS * Kf * dist x y ^ α := hUh x hx y hy
      _ ≤ |KhS| * Kf * dist x y ^ α := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hKf
      _ ≤ |KhS| * Kf * ((3 : ℝ) ^ j) ^ α := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow dist_nonneg (hdist x hx y hy) hα.le
  have hmeanU : (∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)), U x) = 0 := by
    have hz := ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).2
    rw [← hz]
    exact (integral_congr_ae hUeq).symm
  have hsup := aux_lfsc_childB_src_neu_core_sup_le z hr U hUc hmeanU hosc
  constructor
  · obtain ⟨U', hU'c, hU'eq⟩ := aux_lfsc_childB_src_neu_core_extend z hr U hUc
    have hU'u : ((uw : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))] U' := by
      filter_upwards [hUeq, ae_restrict_mem (centeredCube z ((3 : ℝ) ^ j) hr).isOpen.measurableSet]
        with x hx hxQ
      exact hx.trans (hU'eq x (hQ hxQ)).symm
    have hL : 0 ≤ |KhS| * Kf := by positivity
    obtain ⟨hU'h, hsemi⟩ := aux_lfsc_childB_src_neu_core_holder
      (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) U' hα hL (by
        intro x hx y hy
        rw [hU'eq x hx, hU'eq y hy]
        calc |U x - U y| ≤ KhS * Kf * dist x y ^ α := hUh x hx y hy
          _ ≤ |KhS| * Kf * dist x y ^ α := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
              exact mul_le_mul_of_nonneg_right (le_abs_self _) hKf)
    have hUn' : cAlphaNorm α (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) U' ≤
        (|KhS| * (((3 : ℝ) ^ j) ^ α + 1)) * Kf := by
      unfold cAlphaNorm
      have hs1 : sSup {v : ℝ | ∃ x ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
          v = |U' x|} ≤ Om := by
        apply Real.sSup_le _ hOm0
        rintro _ ⟨x, hx, rfl⟩
        rw [hU'eq x hx]
        exact hsup x hx
      calc _ ≤ Om + |KhS| * Kf := add_le_add hs1 hsemi
        _ = _ := by rw [hOm]; ring
    intro w0 w
    obtain ⟨a, hc, hside⟩ := aux_lem_finite_stopping_crude_cost_cell2_grid hH1 hNj z w0
      (aux_lem_finite_stopping_crude_cost_obsB H1 N) w
    have hkT : H1 * (aux_lem_finite_stopping_crude_cost_obsLo H1 N +
        aux_lem_finite_stopping_crude_cost_obsB H1 N) ≤ T := by
      have hlh := aux_lem_finite_stopping_crude_cost_obsLo_le_obsHi hH1 hNH
      have hsum : aux_lem_finite_stopping_crude_cost_obsLo H1 N +
          aux_lem_finite_stopping_crude_cost_obsB H1 N =
          aux_lem_finite_stopping_crude_cost_obsHi H1 N := by
        unfold aux_lem_finite_stopping_crude_cost_obsB; omega
      have h4 := aux_lem_finite_stopping_crude_cost_four_H1_obsHi_le hH1 N
      rw [hsum]
      omega
    have hpos := descendantSide_pos (subdivisionHalfWidth H1)
      (aux_lem_finite_stopping_crude_cost_obsB H1 N)
      (descendantSide_pos 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) hr)
    have hsub : centeredCube
        (fun i => z i + (3 : ℝ) ^ (-((H1 * (aux_lem_finite_stopping_crude_cost_obsLo H1 N +
          aux_lem_finite_stopping_crude_cost_obsB H1 N) : ℕ) : ℤ)) * (a i : ℝ))
        ((3 : ℝ) ^ (-((H1 * (aux_lem_finite_stopping_crude_cost_obsLo H1 N +
          aux_lem_finite_stopping_crude_cost_obsB H1 N) : ℕ) : ℤ))) (by positivity) ≤
        centeredCube z ((3 : ℝ) ^ j) hr :=
      (le_of_eq (aux_lem_finite_stopping_crude_cost_centeredCube_congr hc hside hpos
        (by positivity)).symm).trans
        (aux_lem_finite_stopping_crude_cost_cell2_le_root z hr
          (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
          (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
    have hE := hEω T _ a hkT hsub
    rw [← hc, ← hside] at hE
    have hLam : Jc.Lam z ((3 : ℝ) ^ j) hr
        (cutoffPositiveCoefficient model Ht omega T z hr)
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) w0)
          (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j))
          (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
        (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_crude_cost_obsB H1 N)
          (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j)))
        ((β - 1 / 2) / 4) 2 ≤
        |Ke T| * (descendantSide (subdivisionHalfWidth H1)
          (aux_lem_finite_stopping_crude_cost_obsB H1 N)
          (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ (-η) := by
      refine le_trans (le_add_of_nonneg_right (inv_nonneg.2 (Jc.lam_pos _ _ _ _ _ _ _ _).le))
        (hE.trans ?_)
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hpos.le _)
    have hρ1 : descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_crude_cost_obsB H1 N)
        (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j)) ≤ 1 := by
      rw [hside]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hcost := aux_lem_finite_stopping_crude_cost_cell_cost Jc hβ hβα hαβ1 hσ (by omega) hC1 h1 hr
      hpos hρ1
      (aux_lem_finite_stopping_crude_cost_cell2_le_root z hr
        (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
        (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
      (aux_lem_finite_stopping_crude_cost_cell2_killedPoincare z hr
        (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
        (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
      (cutoffPositiveCoefficient model Ht omega T z hr) uw U' hU'c hU'u hU'h hUn' hLam
    refine hcost.trans (le_of_eq ?_)
    ring

  · have hE : aux_lem_finite_stopping_crude_cost_energyOn (cutoffPositiveCoefficient model Hs omega S z hr)
        (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) =
        ∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
          F x * ((uw : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 x) :=
      (SubdiffusiveProcess.FiniteStopping.sobolevCoefficientForm_eq_energyOn _ _).symm.trans (hsol uw)
    rw [hE]
    have hcongr : (∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
        F x * ((uw : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 x)) =
        ∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)), F x * U x := by
      apply integral_congr_ae
      filter_upwards [hUeq] with x hx
      show F x * ((u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 x) = F x * U x
      rw [hx]
    rw [hcongr]
    have hbound : ‖∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)), F x * U x‖ ≤
        (Kf * Om) * volume.real (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) := by
      apply norm_setIntegral_le_of_norm_le_const
        (by rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top)
      intro x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFb x hx) (hsup x (hQ hx)) (abs_nonneg _) hKf
    rw [centeredCube_volume_real] at hbound
    calc _ ≤ ‖∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)), F x * U x‖ :=
          le_abs_self _
      _ ≤ (Kf * Om) * ((3 : ℝ) ^ j) ^ d := hbound
      _ = _ := by rw [hOm]; ring

/-- Items (ii) and (iii) of `lfsc_childB_src_neu` for one coefficient parameter `Hp`, at one sample. -/
def aux_lfsc_childB_src_neu_data {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (σ : ℝ) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hp : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (j : ℤ) (H1 N M : ℕ) (reverse : Bool) (ε : ℝ)
    (omega : BilateralField d) : Prop :=
  let hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  let target := if reverse then M else N
  let source := if reverse then N else M
  let aT := cutoffPositiveCoefficient model Hp omega target z hr
  let aS := cutoffPositiveCoefficient model Hp omega source z hr
  let mg := subdivisionHalfWidth H1
  let t0 := SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j
  let B := SubdiffusiveProcess.FiniteStopping.obsB H1 N
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf → Measurable F →
    (∀ x ∈ centeredCube z ((3 : ℝ) ^ j) hr, |F x| ≤ Kf) →
    (∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)), F x) = 0 →
  ∀ u : meanZeroSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
    SolvesNeumann aS F u →
    let uw : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr) :=
      ⟨(u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)),
        ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩
    (∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
      SubdiffusiveProcess.FiniteStopping.respOn aT uw
          (SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 B w)
          (SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 B w) ≤
        (3 : ℝ) ^ (ε * (N : ℝ)) *
          (descendantSide mg B (descendantSide 1 t0 ((3 : ℝ) ^ j))) ^ ((d : ℝ) - σ) *
            Kf ^ 2) ∧
    SubdiffusiveProcess.FiniteStopping.energyOn aS
        (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (3 : ℝ) ^ (ε * (N : ℝ)) * Kf ^ 2

/-- **Sourced ChildB (mean-zero Neumann) at one root, one coefficient family `Hp`**: one event `Bad` before all data,
given the Hölder bundle `hKh3` for `Hp` (all cutoffs `J ≥ -j`), the clause-2 bank `hKe*` for the extension coefficient `Ht`,
and a weight bank `Wc` with `resp(A^{Hp}_T) ≤ Wc · resp(A^{Ht}_T)` (`Wc = 1` when `Hp = Ht`). -/
theorem lfsc_childB_src_neu_core {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    {σ α β η C1 : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) (hβα : β ≤ α) (hαβ1 : α - β ≤ 1)
    (hσ : 2 - 2 * α + η ≤ σ) (hC1 : 0 < C1)
    (h1 : aux_lem_finite_stopping_crude_cost_ClauseOne Jc β C1)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hp Ht : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ) (hH1 : 0 < H1)
    (Kh : ℕ → BilateralField d → ℝ) (Ch : ℝ)
    (hKh1 : ∀ J, MemLp (Kh J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hKh2 : ∀ J, eLpNorm (Kh J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Ch)
    (hKh3 : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, -j ≤ (J : ℤ) →
      aux_fscc_holder_predicates_holNeu d z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)
        (cutoffPositiveCoefficient model Hp om J z (zpow_pos (by norm_num) j)) α (Kh J om))
    (Ke : ℕ → BilateralField d → ℝ) (Ce : ℝ)
    (hKe1 : ∀ N, MemLp (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hKe2 : ∀ N, eLpNorm (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Ce)
    (hKe3 : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Ht z j β η om (fun N => Ke N om))
    (Wc : BilateralField d → ℝ) (CW : ℝ) (hWnn : ∀ om, 0 ≤ Wc om)
    (hWm : MemLp Wc (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hWb : eLpNorm Wc (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal CW)
    (hTr : ∀ (om : BilateralField d) (T : ℕ)
      (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)))
      {U : Opens (SpatialCoordinates d)}
      (hU : U ≤ centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))
      (hPU : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph U,
        ‖(v : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) v‖),
      SubdiffusiveProcess.FiniteStopping.respOn
          (cutoffPositiveCoefficient model Hp om T z (zpow_pos (by norm_num) j)) u hU hPU ≤
        Wc om * SubdiffusiveProcess.FiniteStopping.respOn
          (cutoffPositiveCoefficient model Ht om T z (zpow_pos (by norm_num) j)) u hU hPU) :
    ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
      ∀ omega ∉ Bad, aux_lfsc_childB_src_neu_data σ model Hp z j H1 N M reverse ε omega := by
  intro ε hε
  have hα : 0 < α := lt_of_lt_of_le (by linarith [hβ.1]) hβα
  set P := (chaosSampleLaw model).toMeasure with hPdef
  have hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hmem : ∀ (i : Fin 3) (J : ℕ), MemLp (![Kh, Ke, fun _ => Wc] i J) (ENNReal.ofReal 1) P := by
    intro i J
    fin_cases i
    · exact hKh1 J
    · exact hKe1 J
    · exact hWm
  have hbd : ∀ (i : Fin 3) (J : ℕ),
      eLpNorm (![Kh, Ke, fun _ => Wc] i J) (ENNReal.ofReal 1) P ≤
        ENNReal.ofReal (max (max Ch Ce) CW) := by
    intro i J
    fin_cases i
    · exact (hKh2 J).trans (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_left _ _)))
    · exact (hKe2 J).trans (ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_left _ _)))
    · exact hWb.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  obtain ⟨Ctail, hCt, hloc⟩ :=
    _root_.SubdiffusiveProcess.Paper.lem_finite_stopping_moments d model 3 1 (max (max Ch Ce) CW) le_rfl
      ![Kh, Ke, fun _ => Wc] hmem hbd
  have hε5 : 0 < ε / 5 := by positivity
  set r : ℝ := (3 : ℝ) ^ j with hrdef
  have hrα : 0 ≤ r ^ α := Real.rpow_nonneg hr.le _
  obtain ⟨N1, hN1⟩ := aux_lem_finite_stopping_crude_cost_exists_nat_const_le_rpow
    (max (C1 * d * (r ^ α + 1) ^ 2) (r ^ d * r ^ α)) _ hε5
  refine ⟨Ctail, ε / 5, max (max (4 * j.natAbs) (4 * H1)) N1, hCt, hε5, ?_⟩
  intro N M hN hNM reverse
  have hNj : 4 * j.natAbs ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNH : 4 * H1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN1 : N1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨Bad0, hBad0m, hBad0P, hBad0⟩ := hloc (ε / 5) hε5 N M
  have hGae : ∀ᵐ om ∂P, (∀ J : ℕ, -j ≤ (J : ℤ) →
      aux_fscc_holder_predicates_holNeu d z ((3 : ℝ) ^ j) hr
        (cutoffPositiveCoefficient model Hp om J z hr) α (Kh J om)) ∧
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Ht z j β η om (fun N => Ke N om) :=
    hKh3.and hKe3
  set Gc := {om | ¬ ((∀ J : ℕ, -j ≤ (J : ℤ) →
      aux_fscc_holder_predicates_holNeu d z ((3 : ℝ) ^ j) hr
        (cutoffPositiveCoefficient model Hp om J z hr) α (Kh J om)) ∧
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Ht z j β η om (fun N => Ke N om))}
    with hGc
  have hGc0 : P Gc = 0 := ae_iff.1 hGae
  refine ⟨Bad0 ∪ toMeasurable P Gc, hBad0m.union (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · calc P (Bad0 ∪ toMeasurable P Gc) ≤ P Bad0 + P (toMeasurable P Gc) := measure_union_le _ _
      _ = P Bad0 := by rw [measure_toMeasurable, hGc0, add_zero]
      _ ≤ ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-1 * (ε / 5) * (N : ℝ))) := hBad0P
      _ = ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-(ε / 5) * (N : ℝ))) := by ring_nf
  intro omega homega
  have hω0 : omega ∉ Bad0 := fun h => homega (Or.inl h)
  have hωG : (∀ J : ℕ, -j ≤ (J : ℤ) →
      aux_fscc_holder_predicates_holNeu d z ((3 : ℝ) ^ j) hr
        (cutoffPositiveCoefficient model Hp omega J z hr) α (Kh J omega)) ∧
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Ht z j β η omega (fun N => Ke N omega) := by
    by_contra h
    exact homega (Or.inr (subset_toMeasurable P Gc h))
  have hK := hBad0 omega hω0
  have hKhN : |Kh N omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 0).1
  have hKhM : |Kh M omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 0).2
  have hKeN : |Ke N omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 1).1
  have hKeM : |Ke M omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 1).2
  have hWω : |Wc omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 2).1
  have hWpos : 0 ≤ Wc omega := hWnn omega
  have hWω' : Wc omega ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (le_abs_self _).trans hWω
  have hmono : (3 : ℝ) ^ (ε / 5 * (N1 : ℝ)) ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hNN1) hε5.le)
  have hcst : C1 * d * (r ^ α + 1) ^ 2 ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) :=
    ((le_max_left _ _).trans hN1).trans hmono
  have hcst2 : r ^ d * r ^ α ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := ((le_max_right _ _).trans hN1).trans hmono
  have hT : N ≤ (if reverse then M else N) := by cases reverse <;> simp [hNM]
  have hSN : N ≤ (if reverse then N else M) := by cases reverse <;> simp [hNM]
  have hKeT : |Ke (if reverse then M else N) omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := by
    cases reverse
    · exact hKeN
    · exact hKeM
  have hKhS : |Kh (if reverse then N else M) omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := by
    cases reverse
    · exact hKhM
    · exact hKhN
  have hSj : -j ≤ ((if reverse then N else M : ℕ) : ℤ) := by
    have : 4 * j.natAbs ≤ (if reverse then N else M) := le_trans hNj hSN
    omega
  have hcst0 : 0 ≤ C1 * d * (r ^ α + 1) ^ 2 := by positivity
  have hcellc := aux_lfsc_childB_src_dir_core0_five hcst0 (abs_nonneg _) (abs_nonneg _) hWpos
    hcst hKeT hKhS hWω'
  have hrootc := aux_lfsc_childB_src_dir_core0_two hε.le (abs_nonneg _)
    (by positivity : (0 : ℝ) ≤ r ^ d * r ^ α) hKhS hcst2
  intro F Kf hKf hFm hFb hmean u hsol
  have hfin := aux_lfsc_childB_src_neu_omega hd Jc hα hβ hβα hαβ1 hσ hC1 h1
    (Hs := Hp) (Ht := Ht) z j hr H1 hH1 N hNj hNH (if reverse then M else N) (if reverse then N else M) hT
    omega (Kh (if reverse then N else M) omega) (fun N => Ke N omega) (hωG.1 _ hSj) hωG.2
    F Kf hKf hFm hFb hmean u hsol
  obtain ⟨hcell, hroot⟩ := hfin
  have hKf2 : 0 ≤ Kf ^ 2 := sq_nonneg _
  refine ⟨fun w0 w => ?_, hroot.trans ?_⟩
  · refine (hTr omega (if reverse then M else N) _ _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (hcell w0 w) hWpos).trans ?_
    have hside := Real.rpow_nonneg (descendantSide_pos (subdivisionHalfWidth H1)
      (SubdiffusiveProcess.FiniteStopping.obsB H1 N)
      (descendantSide_pos 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) hr)).le ((d : ℝ) - σ)
    calc Wc omega * ((C1 * (d : ℝ) * |Ke (if reverse then M else N) omega| *
          (|Kh (if reverse then N else M) omega| * (r ^ α + 1)) ^ 2) *
          (descendantSide (subdivisionHalfWidth H1) (SubdiffusiveProcess.FiniteStopping.obsB H1 N)
            (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))) ^
              ((d : ℝ) - σ) * Kf ^ 2)
        = ((C1 * d * (r ^ α + 1) ^ 2) * |Ke (if reverse then M else N) omega| *
            |Kh (if reverse then N else M) omega| ^ 2 * Wc omega) *
          (descendantSide (subdivisionHalfWidth H1) (SubdiffusiveProcess.FiniteStopping.obsB H1 N)
            (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))) ^
              ((d : ℝ) - σ) * Kf ^ 2 := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hKf2
        exact mul_le_mul_of_nonneg_right hcellc hside
  · apply mul_le_mul_of_nonneg_right _ hKf2
    calc (|Kh (if reverse then N else M) omega| * (r ^ d * r ^ α)) ≤ _ := hrootc

end SubdiffusiveProcess.Paper
