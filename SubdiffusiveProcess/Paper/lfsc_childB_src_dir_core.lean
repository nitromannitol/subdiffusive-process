module

public import SubdiffusiveProcess.FiniteStopping.SourcedStageAt
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.lem_finite_stopping_crude_cost
public import SubdiffusiveProcess.Paper.lem_finite_stopping_moments

@[expose] public section

/-!
# `lfsc_childB_src_dir_core` — sourced ChildB (Dirichlet, one infrared parameter)

Port of `lem_finite_stopping_crude_cost` (`childB_at_root`, `omega_final`, `root_energy`) with the source carried:
for one coefficient parameter `Hp` (the infrared field or `0`), given the literal `prop_growth` body (`GrowthBody`,
whose local clause carries `F, Kf, φ, b, u`) and the literal clause-2 grid bound `ClauseTwoAt` of `lem_extension`,
outside ONE event `Bad` (chosen before every source, datum and solution) the final-depth target cell responses and
the global source energy are bounded by `3^{εN}` times the data norm `Bd² = (Kf + ‖φ‖_{C²})²`.
Paper `\label{mfd:lem-finite-source-comparison}`, proof paragraph 3 (and Step 3 of `\label{mfd:lem-finite-stopping}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

/-- Items (ii) and (iii) of `lfsc_childB_src_dir` for one coefficient parameter `Hp`, at one sample. -/
def aux_lfsc_childB_src_dir_data {d : ℕ} [NeZero d]
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
  ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
  ∀ b u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
    ((b : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))] phi →
    SolvesDirichlet aS F b u →
    let Bd : ℝ := Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi
    (∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
      SubdiffusiveProcess.FiniteStopping.respOn aT u
          (SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 B w)
          (SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 B w) ≤
        (3 : ℝ) ^ (ε * (N : ℝ)) *
          (descendantSide mg B (descendantSide 1 t0 ((3 : ℝ) ^ j))) ^ ((d : ℝ) - σ) *
            Bd ^ 2) ∧
    SubdiffusiveProcess.FiniteStopping.energyOn aS
        (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (3 : ℝ) ^ (ε * (N : ℝ)) * Bd ^ 2

/-- Both clauses at one sample with the explicit random constants (source-carrying `omega_final`). -/
theorem aux_lfsc_childB_src_dir_omega {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    {σ α β η t C1 : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) (hβα : β ≤ α) (hαβ1 : α - β ≤ 1)
    (hσ : 2 - 2 * α + η ≤ σ) (hC1 : 0 < C1)
    (h1 : aux_lem_finite_stopping_crude_cost_ClauseOne Jc β C1)
    {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {Hs Ht : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (z : SpatialCoordinates d) (j : ℤ) (hr : (0 : ℝ) < (3 : ℝ) ^ j) (H1 : ℕ) (hH1 : 0 < H1)
    (N : ℕ) (hNj : 4 * j.natAbs ≤ N) (hNH : 4 * H1 ≤ N) (T S : ℕ) (hNT : N ≤ T)
    (omega : BilateralField d) (Kg Ke : ℕ → ℝ)
    (hGω : aux_lem_finite_stopping_crude_cost_GrowthAt model Hs z ((3 : ℝ) ^ j) hr t α omega Kg)
    (hEω : aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Ht z j β η omega Ke)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf) (hFm : Measurable F)
    (hFb : ∀ x ∈ centeredCube z ((3 : ℝ) ^ j) hr, |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi)
    (b u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (hb : ((b : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))] phi)
    (hsol : SolvesDirichlet (cutoffPositiveCoefficient model Hs omega S z hr) F b u) :
    (∀ (w0 : Fin (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) → OddGridIndex d 1)
        (w : Fin (aux_lem_finite_stopping_crude_cost_obsB H1 N) →
          OddGridIndex d (subdivisionHalfWidth H1)),
      aux_lem_finite_stopping_crude_cost_respOn (cutoffPositiveCoefficient model Ht omega T z hr) u
          (aux_lem_finite_stopping_crude_cost_cell2_le_root z hr
            (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
            (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
          (aux_lem_finite_stopping_crude_cost_cell2_killedPoincare z hr
            (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
            (aux_lem_finite_stopping_crude_cost_obsB H1 N) w) ≤
        (C1 * (d : ℝ) * |Ke T| * |Kg S| ^ 2) *
          (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_crude_cost_obsB H1 N)
            (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^
              ((d : ℝ) - σ) *
            (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2) ∧
    aux_lem_finite_stopping_crude_cost_energyOn (cutoffPositiveCoefficient model Hs omega S z hr)
        (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (((3 : ℝ) ^ d) ^ j.toNat * |Kg S|) *
        (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2 := by
  have hg0 : 0 ≤ c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi :=
    aux_lem_finite_stopping_crude_cost_c2Norm_nonneg _ _
  have hFae : AEMeasurable F (volume.restrict (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))) :=
    hFm.aemeasurable
  have hFab : ∀ᵐ x ∂(volume.restrict (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))),
      |F x| ≤ Kf :=
    ae_restrict_of_forall_mem (centeredCube z ((3 : ℝ) ^ j) hr).isOpen.measurableSet hFb
  have hG1 := hGω S F Kf hKf hFae hFab phi
    (c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) hphi le_rfl b u hb hsol
  constructor
  · obtain ⟨U, hUc, hUu, hUh, hUn⟩ := hG1.2
    have hUn' : cAlphaNorm α (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) U ≤
        |Kg S| * (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) :=
      hUn.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (add_nonneg hKf hg0))
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
      (cutoffPositiveCoefficient model Ht omega T z hr) u U hUc hUu hUh hUn' hLam
    refine hcost.trans (le_of_eq ?_)
    ring
  · have hloc := hG1.1
    have hside1 := aux_lem_finite_stopping_crude_cost_side_toNat_le_one j
    have hcov := aux_lem_finite_stopping_crude_cost_energy_cover z hr j.toNat hside1
      (cutoffPositiveCoefficient model Hs omega S z hr)
      (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
      (Kg S * (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2)
      (fun c hc => by
        have hmeas : MeasurableSet (Metric.ball c 1 ∩
            (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))) :=
          Metric.isOpen_ball.measurableSet.inter (centeredCube z ((3 : ℝ) ^ j) hr).isOpen.measurableSet
        rw [aux_lem_finite_stopping_crude_cost_energyOn_eq_local _ _ hmeas Set.inter_subset_right]
        refine (hloc c 1 hc one_pos le_rfl).trans (le_of_eq ?_)
        rw [Real.one_rpow, mul_one])
    refine hcov.trans ?_
    have h3 : 0 ≤ ((3 : ℝ) ^ d) ^ j.toNat := by positivity
    calc ((3 : ℝ) ^ d) ^ j.toNat * (Kg S *
          (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2)
        ≤ ((3 : ℝ) ^ d) ^ j.toNat * (|Kg S| *
          (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ h3
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ = _ := by ring


/-- **Sourced ChildB (Dirichlet) at one root for one coefficient parameter**: outside one event `Bad` (before all
data), (ii) and (iii). -/
theorem lfsc_childB_src_dir_core {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    {σ α β η t C1 : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) (hβα : β ≤ α) (hαβ1 : α - β ≤ 1)
    (hσ : 2 - 2 * α + η ≤ σ) (hC1 : 0 < C1)
    (h1 : aux_lem_finite_stopping_crude_cost_ClauseOne Jc β C1)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hp : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ) (hH1 : 0 < H1)
    (Kg : ℕ → BilateralField d → ℝ) (Cg : Fin 1 → ℝ)
    (hG : aux_lem_finite_stopping_crude_cost_GrowthBody model Hp z ((3 : ℝ) ^ j)
      (zpow_pos (by norm_num) j) t α 1 (fun _ => 1) Kg Cg)
    (Ke : ℕ → BilateralField d → ℝ) (Ce : ℝ)
    (hKe1 : ∀ N, MemLp (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hKe2 : ∀ N, eLpNorm (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Ce)
    (hKe3 : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Hp z j β η om (fun N => Ke N om)) :
    ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
      ∀ omega ∉ Bad, aux_lfsc_childB_src_dir_data σ model Hp z j H1 N M reverse ε omega := by
  intro ε hε
  set P := (chaosSampleLaw model).toMeasure with hPdef
  have hmem : ∀ (i : Fin 2) (J : ℕ), MemLp (![Kg, Ke] i J) (ENNReal.ofReal 1) P := by
    intro i J
    fin_cases i
    · exact hG.1 0 J
    · exact hKe1 J
  have hbd : ∀ (i : Fin 2) (J : ℕ),
      eLpNorm (![Kg, Ke] i J) (ENNReal.ofReal 1) P ≤ ENNReal.ofReal (max (Cg 0) Ce) := by
    intro i J
    fin_cases i
    · exact (hG.2.1 0 J).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · exact (hKe2 J).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  obtain ⟨Ctail, hCt, hloc⟩ :=
    _root_.SubdiffusiveProcess.Paper.lem_finite_stopping_moments d model 2 1 (max (Cg 0) Ce) le_rfl ![Kg, Ke] hmem hbd
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨N1, hN1⟩ := aux_lem_finite_stopping_crude_cost_exists_nat_const_le_rpow
    (max (C1 * d) (((3 : ℝ) ^ d) ^ j.toNat)) _ hε4
  refine ⟨Ctail, ε / 4, max (max (4 * j.natAbs) (4 * H1)) N1, hCt, hε4, ?_⟩
  intro N M hN hNM reverse
  have hNj : 4 * j.natAbs ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNH : 4 * H1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN1 : N1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨Bad0, hBad0m, hBad0P, hBad0⟩ := hloc (ε / 4) hε4 N M
  have hGae : ∀ᵐ om ∂P, aux_lem_finite_stopping_crude_cost_GrowthAt model Hp z ((3 : ℝ) ^ j)
      (zpow_pos (by norm_num) j) t α om (fun N => Kg N om) ∧
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Hp z j β η om (fun N => Ke N om) :=
    hG.2.2.2.and hKe3
  set Gc := {om | ¬ (aux_lem_finite_stopping_crude_cost_GrowthAt model Hp z ((3 : ℝ) ^ j)
      (zpow_pos (by norm_num) j) t α om (fun N => Kg N om) ∧
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Hp z j β η om (fun N => Ke N om))}
    with hGc
  have hGc0 : P Gc = 0 := ae_iff.1 hGae
  refine ⟨Bad0 ∪ toMeasurable P Gc, hBad0m.union (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · calc P (Bad0 ∪ toMeasurable P Gc) ≤ P Bad0 + P (toMeasurable P Gc) := measure_union_le _ _
      _ = P Bad0 := by rw [measure_toMeasurable, hGc0, add_zero]
      _ ≤ ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-1 * (ε / 4) * (N : ℝ))) := hBad0P
      _ = ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-(ε / 4) * (N : ℝ))) := by ring_nf
  intro omega homega
  have hω0 : omega ∉ Bad0 := fun h => homega (Or.inl h)
  have hωG : aux_lem_finite_stopping_crude_cost_GrowthAt model Hp z ((3 : ℝ) ^ j)
      (zpow_pos (by norm_num) j) t α omega (fun N => Kg N omega) ∧
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model Hp z j β η omega (fun N => Ke N omega) := by
    by_contra h
    exact homega (Or.inr (subset_toMeasurable P Gc h))
  have hK := hBad0 omega hω0
  have hKgN : |Kg N omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := (hK 0).1
  have hKgM : |Kg M omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := (hK 0).2
  have hKeN : |Ke N omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := (hK 1).1
  have hKeM : |Ke M omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := (hK 1).2
  have hmono : (3 : ℝ) ^ (ε / 4 * (N1 : ℝ)) ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hNN1) hε4.le)
  have hC1d : C1 * d ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := ((le_max_left _ _).trans hN1).trans hmono
  have h3d : ((3 : ℝ) ^ d) ^ j.toNat ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) :=
    ((le_max_right _ _).trans hN1).trans hmono
  have hE1 : (1 : ℝ) ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hT : N ≤ (if reverse then M else N) := by cases reverse <;> simp [hNM]
  have hKeT : |Ke (if reverse then M else N) omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := by
    cases reverse
    · exact hKeN
    · exact hKeM
  have hKgS : |Kg (if reverse then N else M) omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := by
    cases reverse
    · exact hKgM
    · exact hKgN
  have hC1d0 : 0 ≤ C1 * d := mul_nonneg hC1.le (Nat.cast_nonneg d)
  obtain ⟨hcellc, -⟩ := aux_lem_finite_stopping_crude_cost_four_factors hC1d0 (abs_nonneg _)
    (abs_nonneg _) hC1d hKeT hKgS zero_le_one hE1
  obtain ⟨-, hrootc⟩ := aux_lem_finite_stopping_crude_cost_four_factors
    (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ d) ^ j.toNat)
    (abs_nonneg _) zero_le_one h3d hKgS hE1 zero_le_one hE1
  intro F Kf hKf hFm hFb phi hphi b u hb hsol
  have hfin := aux_lfsc_childB_src_dir_omega (Hs := Hp) (Ht := Hp) hd Jc hβ hβα hαβ1 hσ hC1 h1 z j (zpow_pos (by norm_num) j) H1 hH1
    N hNj hNH (if reverse then M else N) (if reverse then N else M) hT omega
    (fun N => Kg N omega) (fun N => Ke N omega) hωG.1 hωG.2 F Kf hKf hFm hFb phi hphi b u hb hsol
  obtain ⟨hcell, hroot⟩ := hfin
  have hg0 : 0 ≤ c2Norm (closedCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) :
      Set (SpatialCoordinates d)) phi := aux_lem_finite_stopping_crude_cost_c2Norm_nonneg _ _
  have hBd : 0 ≤ (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) :
      Set (SpatialCoordinates d)) phi) ^ 2 := sq_nonneg _
  refine ⟨fun w0 w => (hcell w0 w).trans ?_, hroot.trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hBd
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (descendantSide_pos _ _
      (descendantSide_pos _ _ (zpow_pos (by norm_num) j))).le _)
    calc C1 * (d : ℝ) * |Ke (if reverse then M else N) omega| *
          |Kg (if reverse then N else M) omega| ^ 2
        = C1 * (d : ℝ) * |Ke (if reverse then M else N) omega| *
          |Kg (if reverse then N else M) omega| ^ 2 * (1 : ℝ) ^ 0 := by ring
      _ ≤ _ := hcellc
  · apply mul_le_mul_of_nonneg_right _ hBd
    calc ((3 : ℝ) ^ d) ^ j.toNat * |Kg (if reverse then N else M) omega|
        = ((3 : ℝ) ^ d) ^ j.toNat * |Kg (if reverse then N else M) omega| * 1 * 1 := by ring
      _ ≤ _ := hrootc

end SubdiffusiveProcess.Paper
