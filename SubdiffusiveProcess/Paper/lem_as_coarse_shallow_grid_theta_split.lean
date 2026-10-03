module

public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lem_as_coarse_deep_grid
public import Mathlib.Tactic

@[expose] public section

/-!
# Theta order for the retained shallow grid

The frozen `lem_as_coarse_shallow_grid` chooses `theta` and `delta0` before the model,
while every available response-comparison rate (`lem_finite_stopping`,
`lem_finite_source_comparison`, `prop_as_dirichlet`, `prop_as_response_bank_cauchy`,
`prop_as_response_bank`) is chosen after the model.  This file shows that no uniform
rate is needed: the paper's comparison argument (lines 4498--4511) only has to cover a
*model/sample dependent* fraction `theta' ≤ theta`; the remaining depths
`theta' N < k ≤ theta N` are covered by the crude grid bound of `lem_extension` (paper
4539--4546), whose disorder threshold depends only on the exponent `eta < rho`, and whose
random constant grows subexponentially almost surely.

* `aux_lem_as_coarse_shallow_grid_split`: deterministic two-regime split.
* `aux_lem_as_coarse_shallow_grid_crude`: the crude grid, with `delta0` chosen before any
  grid fraction or growth rate (replay of the proved `lem_as_coarse_deep_grid`).
* `aux_lem_as_coarse_shallow_grid_of_local_theta`: the frozen shallow conclusion, for any
  prescribed `0 < theta < 1`, from the retained estimate with a local fraction.
-/

open MeasureTheory Set Filter Topology SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Two-regime split.**  A bound `K 3^{ρk}` on the depths `k ≤ θ' N` and a crude bound
`K_N 3^{ηk}` (`η < ρ`, `K_N ≤ 3^{(ρ-η)θ' N}` eventually) on all depths `k₀ ≤ k ≤ N` give
the bound `max K 1 · 3^{ρk}` on the depths `k ≤ θ N`, for every `θ ≤ 1`. -/
theorem aux_lem_as_coarse_shallow_grid_split
    (F : ℕ → ℕ → ℝ) (rho eta theta theta' K : ℝ) (Kc : ℕ → ℝ) (k0 N0 : ℕ)
    (heta : eta < rho) (htheta' : 0 < theta') (htheta1 : theta ≤ 1)
    (hshallow : ∀ N : ℕ, N0 ≤ N → ∀ k : ℕ, (k : ℝ) ≤ theta' * (N : ℝ) →
      F N k ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)))
    (hcrude : ∀ N k : ℕ, k0 ≤ k → k ≤ N →
      F N k ≤ Kc N * (3 : ℝ) ^ (eta * (k : ℝ)))
    (hKc : ∀ᶠ N : ℕ in atTop, Kc N ≤ (3 : ℝ) ^ ((rho - eta) * theta' * (N : ℝ))) :
    ∃ N1 : ℕ, ∀ N : ℕ, N1 ≤ N → ∀ k : ℕ, (k : ℝ) ≤ theta * (N : ℝ) →
      F N k ≤ max K 1 * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  have hk0 : ∀ᶠ N : ℕ in atTop, (k0 : ℝ) ≤ theta' * (N : ℝ) :=
    (Tendsto.const_mul_atTop htheta' tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 ((hKc.and hk0).and (eventually_ge_atTop N0))
  refine ⟨N1, fun N hN k hk => ?_⟩
  obtain ⟨⟨hKcN, hk0N⟩, hN0⟩ := hN1 N hN
  have hpow : 0 < (3 : ℝ) ^ (rho * (k : ℝ)) := by positivity
  have hmax : K * (3 : ℝ) ^ (rho * (k : ℝ)) ≤ max K 1 * (3 : ℝ) ^ (rho * (k : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
  have hone : (3 : ℝ) ^ (rho * (k : ℝ)) ≤ max K 1 * (3 : ℝ) ^ (rho * (k : ℝ)) :=
    le_mul_of_one_le_left hpow.le (le_max_right _ _)
  by_cases hks : (k : ℝ) ≤ theta' * (N : ℝ)
  · exact (hshallow N hN0 k hks).trans hmax
  · have hlt : theta' * (N : ℝ) < (k : ℝ) := lt_of_not_ge hks
    have hk0k : k0 ≤ k := by
      have : (k0 : ℝ) < (k : ℝ) := lt_of_le_of_lt hk0N hlt
      exact_mod_cast this.le
    have hkN : k ≤ N := by
      have hN' : theta * (N : ℝ) ≤ (N : ℝ) :=
        mul_le_of_le_one_left (Nat.cast_nonneg N) htheta1
      exact_mod_cast hk.trans hN'
    have hexp : (rho - eta) * theta' * (N : ℝ) ≤ (rho - eta) * (k : ℝ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hlt.le (by linarith)
    calc F N k ≤ Kc N * (3 : ℝ) ^ (eta * (k : ℝ)) := hcrude N k hk0k hkN
      _ ≤ (3 : ℝ) ^ ((rho - eta) * theta' * (N : ℝ)) * (3 : ℝ) ^ (eta * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hKcN (by positivity)
      _ ≤ (3 : ℝ) ^ ((rho - eta) * (k : ℝ)) * (3 : ℝ) ^ (eta * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
      _ = (3 : ℝ) ^ (rho * (k : ℝ)) := by
          rw [← Real.rpow_add (by norm_num)]
          ring_nf
      _ ≤ max K 1 * (3 : ℝ) ^ (rho * (k : ℝ)) := hone

/-- **Crude grid with the threshold before every grid fraction.**  The grid clause of
`lem_extension` at exponent `eta` (and `p = 1`, `β = 3/4`) bounds the two cell-matrix maxima
of the root chart at every relative depth `k₀ ≤ k ≤ N`, in both infrared conventions, by one
random constant `K_N 3^{ηk}`; Borel--Cantelli at the countably many rates `1/(j+1)` makes
`K_N` subexponential almost surely.  Unlike `lem_as_coarse_deep_grid`, no grid fraction or
growth rate is fixed before `delta0`. -/
theorem aux_lem_as_coarse_shallow_grid_crude
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d)
    (Xc : in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (_Rm : in_responses d M)
      (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M Hir →
      M.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ Kc : ℕ → ℝ,
        (∀ xi : ℝ, 0 < xi →
          ∀ᶠ N : ℕ in atTop, Kc N ≤ (3 : ℝ) ^ (xi * (N : ℝ))) ∧
        ∃ k0 : ℕ, ∀ withIR : Bool,
          let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
            if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
          ∀ N k : ℕ, k0 ≤ k → k ≤ N →
            Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                (Homogenization.originCube d 0) (-(k : ℤ))
                (Jc.chart z r hr
                  (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
              Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                (Homogenization.originCube d 0) (-(k : ℤ))
                (Jc.chart z r hr
                  (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
              Kc N * (3 : ℝ) ^ (eta * (k : ℝ)) := by
  haveI : NeZero d := ⟨by omega⟩
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hbeta : (3 / 4 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1 := by norm_num
  have hs0 : ((3 / 4 : ℝ) - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by norm_num
  obtain ⟨delta0, hdelta0, hgridAll⟩ :=
    (lem_extension d hd Jc Xc Sf).2 eta 1 heta le_rfl (3 / 4) hbeta
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Hir hIR hdelta z r hr hj
  obtain ⟨j, hrj⟩ := hj
  set m : ℕ := Int.toNat (-j) with hm
  set n : ℕ := Int.toNat j with hn
  have hrmn : r = (3 : ℝ) ^ (n : ℤ) * (3 : ℝ) ^ (-(m : ℤ)) := by
    rw [hrj, ← zpow_add₀ h3]
    congr 1
    omega
  set μ := (chaosSampleLaw M).toMeasure with hμ
  obtain ⟨K, Cb, hLp, hBd, hae⟩ :=
    hgridAll M Rm Hir hIR (hdelta.trans (min_le_right _ _)) z r hr 1 (fun _ => z)
  let Kg : ℕ → BilateralField d → ℝ := fun N => (hLp N).aestronglyMeasurable.mk (K N)
  have hKg_meas : ∀ N, Measurable (Kg N) := fun N =>
    (hLp N).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hKg_ae : ∀ N, K N =ᵐ[μ] Kg N := fun N => (hLp N).aestronglyMeasurable.ae_eq_mk
  have hKgLp : ∀ N, MemLp (Kg N) (ENNReal.ofReal 1) μ := fun N => (hLp N).ae_eq (hKg_ae N)
  have hKgBd : ∀ N, eLpNorm (Kg N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal (max Cb 0) := by
    intro N
    rw [← eLpNorm_congr_ae (hKg_ae N)]
    exact (hBd N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- Borel--Cantelli at every rate `1/(j+1)` simultaneously
  have hBC : ∀ᵐ ω ∂μ, ∀ i : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Kg N ω ≤ (3 : ℝ) ^ ((1 / ((i : ℝ) + 1)) * (N : ℝ)) := by
    rw [ae_all_iff]
    intro i
    exact aux_lem_as_coarse_deep_grid_uniform_lp_eventually μ Kg hKg_meas 1 (max Cb 0)
      (1 / ((i : ℝ) + 1)) le_rfl (le_max_right _ _) (by positivity) hKgLp hKgBd
  have hKeq : ∀ᵐ ω ∂μ, ∀ N, K N ω = Kg N ω := ae_all_iff.2 hKg_ae
  filter_upwards [hae, hBC, hKeq] with ω hω hBCω hKeqω
  obtain ⟨h, hh⟩ : ∃ h : ℝ, ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      |Hir ω y| ≤ h := by
    obtain ⟨C, hC⟩ := (closedCube z r hr).isCompact.exists_bound_of_continuousOn
      (Hir ω).continuous.continuousOn
    exact ⟨C, fun y hy => by
      simpa [Real.norm_eq_abs] using hC y (centeredCube_subset_closedCube z hr hy)⟩
  set Ccmp : ℝ := 2 + 6 * Real.exp (2 * h) with hCcmp
  have hCcmp1 : 1 ≤ Ccmp := by
    have := Real.exp_pos (2 * h)
    linarith
  set W : ℝ := (3 : ℝ) ^ (2 * (((3 / 4 : ℝ) - 1 / 2) / 4) * (m : ℝ)) with hW
  have hW0 : 0 ≤ W := by positivity
  set C0 : ℝ := 2 * Ccmp * W with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨fun N => max 1 (C0 * Kg N ω), ?_, m + n, ?_⟩
  · -- subexponential growth at every positive rate
    intro xi hxi
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt (half_pos hxi)
    have hE2 : ∀ᶠ N : ℕ in atTop,
        Kg N ω ≤ (3 : ℝ) ^ ((1 / ((i : ℝ) + 1)) * (N : ℝ)) :=
      eventually_atTop.2 (hBCω i)
    have hE3 := aux_lem_as_coarse_ms_eventually_rpow_ge (c := xi / 2) (by linarith) C0
    filter_upwards [hE2, hE3] with N hN2 hN3
    apply max_le
    · exact Real.one_le_rpow (by norm_num) (by positivity)
    · have hmono : (3 : ℝ) ^ ((1 / ((i : ℝ) + 1)) * (N : ℝ)) ≤
          (3 : ℝ) ^ (xi / 2 * (N : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right hi.le (Nat.cast_nonneg N))
      calc C0 * Kg N ω ≤ C0 * (3 : ℝ) ^ (xi / 2 * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (hN2.trans hmono) hC00
        _ ≤ (3 : ℝ) ^ (xi / 2 * (N : ℝ)) * (3 : ℝ) ^ (xi / 2 * (N : ℝ)) :=
            mul_le_mul_of_nonneg_right hN3 (by positivity)
        _ = (3 : ℝ) ^ (xi * (N : ℝ)) := by
            rw [← Real.rpow_add (by norm_num)]
            ring_nf
  · have key : ∀ N k : ℕ, m + n ≤ k → k ≤ N →
      (∀ X Y : ℝ,
        X ≤ Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ)))) →
        Y ≤ Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ)))) →
        X + Y ≤ max 1 (C0 * Kg N ω) * (3 : ℝ) ^ (eta * (k : ℝ))) ∧
      0 ≤ W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ))) ∧
      ∀ R ∈ Homogenization.descendantsAtScale
        (Homogenization.originCube d 0) (-(k : ℤ)),
        Homogenization.Book.Ch02.coarseBMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M Hir ω N z hr) z r) ≤
          W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ))) ∧
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M Hir ω N z hr) z r) ≤
          W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ))) ∧
        Homogenization.Book.Ch02.coarseBMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr) z r) ≤
          Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ)))) ∧
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr) z r) ≤
          Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ)))) := by
      intro N k hk0 hkN
      have hgrid : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
          (centeredCube (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
              ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z r hr) →
          Jc.Lam z r hr (cutoffPositiveCoefficient M Hir ω N z hr)
              (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
              (((3 / 4 : ℝ) - 1 / 2) / 4) 2 +
            (Jc.lam z r hr (cutoffPositiveCoefficient M Hir ω N z hr)
              (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
                (((3 / 4 : ℝ) - 1 / 2) / 4) 2)⁻¹ ≤
            K N ω * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) :=
        fun k nidx hk hsub => hω N k 0 nidx hk hsub
      have hcell : ∀ R ∈ Homogenization.descendantsAtScale
          (Homogenization.originCube d 0) (-(k : ℤ)),
          0 ≤ Kg N ω ∧
          Homogenization.Book.Ch02.coarseBMatrixNorm R
              (Jc.chart z r hr (cutoffPositiveCoefficient M Hir ω N z hr) z r) ≤
            W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ))) ∧
          Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
              (Jc.chart z r hr (cutoffPositiveCoefficient M Hir ω N z hr) z r) ≤
            W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ))) ∧
          Homogenization.Book.Ch02.coarseBMatrixNorm R
              (Jc.chart z r hr (cutoffPositiveCoefficient M
                (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr) z r) ≤
            Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ)))) ∧
          Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
              (Jc.chart z r hr (cutoffPositiveCoefficient M
                (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr) z r) ≤
            Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ)))) := by
        intro R hR
        have hR' : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
            ((Homogenization.originCube d 0).scale - (k : ℤ)) := by
          simpa [Homogenization.originCube] using hR
        obtain ⟨hK0, hb, hs⟩ := aux_lem_as_coarse_deep_grid_cell hd Jc M Hir ω N z r hr m n hrmn
          _ hs0 eta (K N ω) heta.le hgrid k hk0 hkN hR'
        rw [hKeqω N] at hK0 hb hs
        obtain ⟨hcb, hcs⟩ := aux_lem_as_coarse_deep_grid_ir_compare hd Jc M Hir ω N z r hr h hh R
          (aux_lem_as_coarse_ms_desc_sub hR')
        refine ⟨hK0, hb, hs, hcb.trans (mul_le_mul_of_nonneg_left hb (by positivity)),
          hcs.trans (mul_le_mul_of_nonneg_left hs (by positivity))⟩
      obtain ⟨R0, hR0⟩ := Homogenization.descendantsAtScale_nonempty
        (Homogenization.originCube d 0) (k := -(k : ℤ)) (by simp [Homogenization.originCube])
      have hK0 : 0 ≤ Kg N ω := (hcell R0 hR0).1
      have hpk : 0 < (3 : ℝ) ^ (eta * (k : ℝ)) := by positivity
      refine ⟨fun X Y hX hY => ?_, by positivity, fun R hR => (hcell R hR).2⟩
      calc X + Y ≤ C0 * Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ)) := by
            rw [hC0]
            nlinarith
        _ ≤ max 1 (C0 * Kg N ω) * (3 : ℝ) ^ (eta * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hpk.le
    intro withIR
    cases withIR with
    | false =>
      intro Hc N k hk0 hkN
      obtain ⟨hfinal, hB0, hcell⟩ := key N k hk0 hkN
      have hB0' : 0 ≤ Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ)))) :=
        mul_nonneg (by linarith) hB0
      apply hfinal
      · exact aux_lem_as_coarse_deep_grid_finsetSup_le _ _ hB0'
          fun R hR => (hcell R hR).2.2.1
      · exact aux_lem_as_coarse_deep_grid_finsetSup_le _ _ hB0'
          fun R hR => (hcell R hR).2.2.2
    | true =>
      intro Hc N k hk0 hkN
      obtain ⟨hfinal, hB0, hcell⟩ := key N k hk0 hkN
      have hup : W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ))) ≤
          Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (eta * (k : ℝ)))) :=
        le_mul_of_one_le_left hB0 hCcmp1
      apply hfinal
      · exact (aux_lem_as_coarse_deep_grid_finsetSup_le _ _ hB0
          fun R hR => (hcell R hR).1).trans hup
      · exact (aux_lem_as_coarse_deep_grid_finsetSup_le _ _ hB0
          fun R hR => (hcell R hR).2.1).trans hup

/-- **Frozen theta order from a local retained fraction.**  Suppose the paper's retained
estimate holds with a fraction `theta'` chosen *after* the model (indeed after the root and
the sample).  Then for every prescribed `0 < theta < 1` the retained bound holds on all
depths `k ≤ theta N`, with one disorder threshold chosen before the model. -/
theorem aux_lem_as_coarse_shallow_grid_of_local_theta
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d)
    (Xc : in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (rho : ℝ) (hrho : 0 < rho)
    (hloc : ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir →
        M.delta ≤ min 1 delta1 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ theta' : ℝ, 0 < theta' ∧
          ∃ K : ℝ, 0 < K ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ k : ℕ, (k : ℝ) ≤ theta' * (N : ℝ) →
                Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
                  Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
                  K * (3 : ℝ) ^ (rho * (k : ℝ)))
    (theta : ℝ) (htheta1 : theta ≤ 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        ∀ (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir →
        M.delta ≤ min 1 delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ k : ℕ, (k : ℝ) ≤ theta * (N : ℝ) →
                Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
                  Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
                  K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  obtain ⟨delta1, hdelta1, hloc⟩ := hloc
  have heta : 0 < rho / 2 := half_pos hrho
  obtain ⟨delta2, hdelta2, hcrude⟩ :=
    aux_lem_as_coarse_shallow_grid_crude d hd Jc Xc Sf (rho / 2) heta
  refine ⟨min delta1 delta2, lt_min hdelta1 hdelta2, ?_⟩
  intro M Rm Sreg It Hir hIR hdelta z r hr hj
  have hd1 : M.delta ≤ min 1 delta1 :=
    hdelta.trans (min_le_min le_rfl (min_le_left _ _))
  have hd2 : M.delta ≤ min 1 delta2 :=
    hdelta.trans (min_le_min le_rfl (min_le_right _ _))
  filter_upwards [hloc M Rm Sreg It Hir hIR hd1 z r hr hj, hcrude M Rm Hir hIR hd2 z r hr hj]
    with ω hlocω hcrω
  obtain ⟨theta', htheta', K, hK, hsh⟩ := hlocω
  obtain ⟨Kc, hKc, k0, hcr⟩ := hcrω
  refine ⟨max K 1, lt_of_lt_of_le hK (le_max_left _ _), ?_⟩
  intro withIR
  obtain ⟨N0, hN0⟩ := hsh withIR
  have hKcθ := hKc ((rho - rho / 2) * theta') (mul_pos (by linarith) htheta')
  exact aux_lem_as_coarse_shallow_grid_split _ rho (rho / 2) theta theta' K Kc k0 N0
    (by linarith) htheta' htheta1 hN0 (hcr withIR) (by simpa [mul_assoc] using hKcθ)

/-- The frozen `lem_as_coarse_shallow_grid` conclusion (verbatim binder order, `theta`
and `delta0` before the model) from the local-fraction retained estimate. -/
theorem aux_lem_as_coarse_shallow_grid_frozen_of_local_theta
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d)
    (Xc : in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (rho : ℝ) (hrho : 0 < rho)
    (hloc : ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir →
        M.delta ≤ min 1 delta1 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ theta' : ℝ, 0 < theta' ∧
          ∃ K : ℝ, 0 < K ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ k : ℕ, (k : ℝ) ≤ theta' * (N : ℝ) →
                Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
                  Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
                  K * (3 : ℝ) ^ (rho * (k : ℝ))) :
    ∃ theta delta0 : ℝ, 0 < theta ∧ theta < 1 ∧ 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        ∀ (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir →
        M.delta ≤ min 1 delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ k : ℕ, (k : ℝ) ≤ theta * (N : ℝ) →
                Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
                  Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
                  K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  obtain ⟨delta0, hdelta0, h⟩ :=
    aux_lem_as_coarse_shallow_grid_of_local_theta d hd Jc Xc Sf rho hrho hloc (1 / 2)
      (by norm_num)
  exact ⟨1 / 2, delta0, by norm_num, by norm_num, hdelta0, h⟩




theorem lem_as_coarse_shallow_grid_theta_split
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d)
    (Xc : in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (rho : ℝ) (hrho : 0 < rho)
    (hloc : ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir →
        M.delta ≤ min 1 delta1 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ theta' : ℝ, 0 < theta' ∧
          ∃ K : ℝ, 0 < K ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ k : ℕ, (k : ℝ) ≤ theta' * (N : ℝ) →
                Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
                  Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
                  K * (3 : ℝ) ^ (rho * (k : ℝ))) :
    ∃ theta delta0 : ℝ, 0 < theta ∧ theta < 1 ∧ 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        ∀ (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir →
        M.delta ≤ min 1 delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ k : ℕ, (k : ℝ) ≤ theta * (N : ℝ) →
                Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
                  Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
                  K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  exact aux_lem_as_coarse_shallow_grid_frozen_of_local_theta d hd Jc Xc Sf rho hrho hloc

end Paper


