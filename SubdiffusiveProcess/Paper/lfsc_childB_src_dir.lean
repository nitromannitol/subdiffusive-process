import SubdiffusiveProcess.FiniteStopping.SourcedStageAt
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.prop_growth_admissible
import SubdiffusiveProcess.Paper.calib_H0_triadic_root_growth
import SubdiffusiveProcess.Paper.lem_finite_stopping_crude_cost
import SubdiffusiveProcess.Paper.lfsc_reference_grid_bound
import SubdiffusiveProcess.Paper.lfsc_childB_src_dir_core
import SubdiffusiveProcess.Paper.lfsc_childB_src_dir_core0




set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

/-- Flag-`H` growth bank (`prop_growth` for `r ≤ 1`, `prop_growth_large_root` for `r > 1`) at one exponent, as `GrowthBody`. -/
theorem aux_lfsc_childB_src_dir_growthH {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (t alpha : ℝ) (h1 : (d : ℝ) - 1 < t) (h2 : t < d) (h3 : 0 < alpha) (h4 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (j : ℤ),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin 1 → ℝ),
        aux_lem_finite_stopping_crude_cost_GrowthBody M H z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)
          t alpha 1 (fun _ => 1) K Cbound := by
  obtain ⟨δg, hδg, hGr⟩ := aux_lem_finite_stopping_crude_cost_growthBody_of_prop_growth hd Jc Pc Xc W Cp Sf
    t alpha 1 (fun _ => 1) h1 h2 h3 h4 (fun _ => le_rfl)
  obtain ⟨δL, hδL, hGL⟩ := aux_lem_finite_stopping_crude_cost_largeRootGrowth hd Jc Pc Xc Sf W Cp
    t alpha 1 (fun _ => 1) h1 h2 h3 h4 (fun _ => le_rfl)
  refine ⟨min δg δL, lt_min hδg hδL, ?_⟩
  intro model Rm Sreg It H hH hsmall z j
  by_cases hj : j ≤ 0
  · exact hGr model Rm Sreg It H hH (hsmall.trans (min_le_left _ _))
      z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) (zpow_le_one_of_nonpos₀ (by norm_num) hj)
  · exact hGL model Rm Sreg It H hH (hsmall.trans (min_le_right _ _))
      z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) (one_lt_zpow₀ (by norm_num) (by omega))

/-- Flag-`0` growth bank (`prop_growth_admissible` at truncation level `0` for `r ≤ 1`,
`calib_H0_triadic_root_growth` for `r = 3^j > 1`) at one exponent, as `GrowthBody` for the coefficient `0`. -/
theorem aux_lfsc_childB_src_dir_growth0 {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (t alpha : ℝ) (h1 : (d : ℝ) - 1 < t) (h2 : t < d) (h3 : 0 < alpha) (h4 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg), M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (j : ℤ),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin 1 → ℝ),
        aux_lem_finite_stopping_crude_cost_GrowthBody M
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)
          t alpha 1 (fun _ => 1) K Cbound := by
  obtain ⟨δa, hδa, hGa⟩ := prop_growth_admissible d hd Jc Pc Xc W Cp Sf t alpha 1 (fun _ => 1)
    h1 h2 h3 h4 (fun _ => le_rfl)
  obtain ⟨δc, hδc, hGc⟩ := calib_H0_triadic_root_growth d hd Jc Pc Xc W Cp Sf t alpha 1 (fun _ => 1)
    h1 h2 h3 h4 (fun _ => le_rfl)
  refine ⟨min δa δc, lt_min hδa hδc, ?_⟩
  intro model Rm Sreg It hsmall z j
  by_cases hj : j ≤ 0
  · have hzero : (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) =
        fun om => infraredPartialSum om 0 := by
      funext om; simp [infraredPartialSum]
    obtain ⟨K, Cb, hmem⟩ := hGa model Rm Sreg It (fun om => infraredPartialSum om 0) (Or.inr ⟨0, rfl⟩)
      (hsmall.trans (min_le_left _ _)) z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)
      (zpow_le_one_of_nonpos₀ (by norm_num) hj)
    refine ⟨K, Cb, ?_⟩
    rw [hzero]
    exact hmem
  · have hj0 : 0 < j := lt_of_not_ge hj
    obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = (j' : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hj0.le).symm⟩
    have hj'pos : 0 < j' := by exact_mod_cast hj0
    have hcast : (3 : ℝ) ^ ((j' : ℕ) : ℤ) = (3 : ℝ) ^ j' := zpow_natCast 3 j'
    have key : ∀ (r r' : ℝ) (hr : 0 < r) (hr' : 0 < r'), r = r' → ∀ (K : ℕ → BilateralField d → ℝ)
        (C : Fin 1 → ℝ), aux_lem_finite_stopping_crude_cost_GrowthBody model
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z r' hr' t alpha 1 (fun _ => 1) K C →
        aux_lem_finite_stopping_crude_cost_GrowthBody model
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z r hr t alpha 1 (fun _ => 1) K C := by
      intro r r' hr hr' h K C hG
      subst h
      exact hG
    obtain ⟨K, Cb, hmem⟩ := hGc model Rm (hsmall.trans (min_le_right _ _)) j' hj'pos z
      (by positivity)
    exact ⟨K, Cb, key _ _ _ _ hcast K Cb hmem⟩

/-- Extension supplier: clause 1 and the grid clause 2 at `(β, η) = (5/8, min σ 1 / 2)`. -/
theorem aux_lfsc_childB_src_dir_ext {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Xc : in_extension d hd Jc) (Sf : SobolevFoundationalInput d hd)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ C1 : ℝ, 0 < C1 ∧ aux_lem_finite_stopping_crude_cost_ClauseOne Jc (5 / 8) C1 ∧
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (j : ℤ),
      ∃ (Ke : ℕ → BilateralField d → ℝ) (Ce : ℝ),
        (∀ N, MemLp (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Ce) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc M H z j (5 / 8) (min σ 1 / 2) om (fun N => Ke N om) := by
  obtain ⟨hβ, -, -, -, -, -, hη⟩ := aux_lem_finite_stopping_crude_cost_exponents σ hσ
  have hext := Paper.lem_extension d hd Jc Xc Sf
  obtain ⟨C1, hC1, h1⟩ := hext.1 (5 / 8) hβ
  obtain ⟨δe, hδe, hE⟩ := hext.2 (min σ 1 / 2) 1 hη le_rfl (5 / 8) hβ
  refine ⟨C1, hC1, h1, δe, hδe, ?_⟩
  intro model Rm H hH hδ z j
  obtain ⟨Ke, Ce, hKe1, hKe2, hKe3⟩ := hE model Rm H hH hδ
    z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) 1 (fun _ => z)
  exact ⟨Ke, Ce, hKe1, hKe2, aux_lem_finite_stopping_crude_cost_clauseTwo_of Jc z j (5 / 8) (min σ 1 / 2) Ke hKe3⟩


/-- Item (i) of `lfsc_childB_src_dir` (both infrared flags) at one sample. -/
def aux_lfsc_childB_src_dir_ref {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (σ : ℝ) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (j : ℤ) (H1 N M : ℕ) (reverse : Bool) (ε : ℝ)
    (omega : BilateralField d) : Prop :=
  ∀ infrared : Bool,
    let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) :=
      if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
    let source := if reverse then N else M
    let mg := subdivisionHalfWidth H1
    let t0 := SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j
    let B := SubdiffusiveProcess.FiniteStopping.obsB H1 N
    ∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg), s ≤ B →
      (SubdiffusiveProcess.FiniteStopping.reference model Hused omega source
        (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s))
        (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
          (descendantSide 1 t0 ((3 : ℝ) ^ j)) s w))⁻¹ ≤ (3 : ℝ) ^ (ε * (N : ℝ)) *
        (descendantSide mg s (descendantSide 1 t0 ((3 : ℝ) ^ j))) ^ (-(min σ 1 / 2))

/-- The three-part event of `lfsc_childB_src_dir` at one sample: (i) for both flags, (ii)+(iii) for `H` and for `0`. -/
def aux_lfsc_childB_src_dir_all {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (σ : ℝ) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (j : ℤ) (H1 N M : ℕ) (reverse : Bool) (ε : ℝ)
    (omega : BilateralField d) : Prop :=
  aux_lfsc_childB_src_dir_ref σ model H z j H1 N M reverse ε omega ∧
    aux_lfsc_childB_src_dir_data σ model H z j H1 N M reverse ε omega ∧
    aux_lfsc_childB_src_dir_data σ model (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
      z j H1 N M reverse ε omega

/-- The assembly, with the per-sample statement folded into `aux_lfsc_childB_src_dir_all`. -/
theorem aux_lfsc_childB_src_dir_main {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
      (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ), 0 < H1 →
    haveI : NeZero d := ⟨by omega⟩
    ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
      ∀ omega ∉ Bad, aux_lfsc_childB_src_dir_all σ model H z j H1 N M reverse ε omega := by
  obtain ⟨hβ, hβα, hαβ1, hσ', hα0, hα1, hη⟩ := aux_lem_finite_stopping_crude_cost_exponents σ hσ
  obtain ⟨δi, hδi, hI⟩ := lfsc_reference_grid_bound hd hσ
  obtain ⟨C1, hC1, h1, δe, hδe, hE⟩ := aux_lfsc_childB_src_dir_ext hd Jc Xc Sf σ hσ
  obtain ⟨δH, hδH, hGH⟩ := aux_lfsc_childB_src_dir_growthH hd Jc Pc Xc Sf W Cp
    ((d : ℝ) - 1 / 2) (1 - min σ 1 / 4) (by linarith) (by linarith) hα0 hα1
  obtain ⟨δ0, hδ0, hG0⟩ := aux_lfsc_childB_src_dir_growth0 hd Jc Pc Xc Sf W Cp
    ((d : ℝ) - 1 / 2) (1 - min σ 1 / 4) (by linarith) (by linarith) hα0 hα1
  refine ⟨min δi (min δe (min δH δ0)), lt_min hδi (lt_min hδe (lt_min hδH hδ0)), ?_⟩
  intro model Rm Sreg It H hH hsmall z j H1 hH1
  haveI : NeZero d := ⟨by omega⟩
  have hs1 : model.delta ≤ δi := hsmall.trans (min_le_left _ _)
  have hs2 : model.delta ≤ δe := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : model.delta ≤ δH :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs4 : model.delta ≤ δ0 :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨KgH, CgH, hGHm⟩ := hGH model Rm Sreg It H hH hs3 z j
  obtain ⟨Kg0, Cg0, hG0m⟩ := hG0 model Rm Sreg It hs4 z j
  obtain ⟨Ke, Ce, hKe1, hKe2, hKe3⟩ := hE model Rm H hH hs2 z j
  have hcH := lfsc_childB_src_dir_core hd Jc hβ hβα hαβ1 hσ' hC1 h1 model H z j H1 hH1
    KgH CgH hGHm Ke Ce hKe1 hKe2 hKe3
  have hc0 := lfsc_childB_src_dir_core0 hd Jc hβ hβα hαβ1 hσ' hC1 h1 model H hH z j H1 hH1
    Kg0 Cg0 hG0m Ke Ce hKe1 hKe2 hKe3
  have hi := hI model Rm H hH hs1 z j H1 hH1
  have hi' : ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool, ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
        ∀ omega ∉ Bad, aux_lfsc_childB_src_dir_ref σ model H z j H1 N M reverse ε omega :=
    fun ε hε => hi ε hε
  exact aux_lfsc_childB_src_dir_core0_union (chaosSampleLaw model).toMeasure
    (fun N M reverse ε omega => aux_lfsc_childB_src_dir_ref σ model H z j H1 N M reverse ε omega)
    (fun N M reverse ε omega => aux_lfsc_childB_src_dir_data σ model H z j H1 N M reverse ε omega)
    (fun N M reverse ε omega => aux_lfsc_childB_src_dir_data σ model
      (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z j H1 N M reverse ε omega)
    hi' hcH hc0

theorem lfsc_childB_src_dir
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d model)
      (Sreg : in_6_16 d model) (It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ), 0 < H1 →
    haveI : NeZero d := ⟨by omega⟩
    ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
      ∀ omega ∉ Bad, ∀ infrared : Bool,
      let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) :=
        if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
      let hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
      let target := if reverse then M else N
      let source := if reverse then N else M
      let aT := cutoffPositiveCoefficient model Hused omega target z hr
      let aS := cutoffPositiveCoefficient model Hused omega source z hr
      let mg := subdivisionHalfWidth H1
      let t0 := SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j
      let B := SubdiffusiveProcess.FiniteStopping.obsB H1 N
      -- (i) crude lower bound of the reference scale at every stage-2 cell (data independent)
      (∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg), s ≤ B →
        (SubdiffusiveProcess.FiniteStopping.reference model Hused omega source
          (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s))
          (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
            (descendantSide 1 t0 ((3 : ℝ) ^ j)) s w))⁻¹ ≤ (3 : ℝ) ^ (ε * (N : ℝ)) *
          (descendantSide mg s (descendantSide 1 t0 ((3 : ℝ) ^ j))) ^ (-(min σ 1 / 2))) ∧
      -- (ii)+(iii) for every source, datum and Dirichlet source solution
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
        SubdiffusiveProcess.FiniteStopping.energyOn aS (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
            (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
          (3 : ℝ) ^ (ε * (N : ℝ)) * Bd ^ 2 := by
  obtain ⟨δ, hδ, h⟩ := aux_lfsc_childB_src_dir_main hd Jc Pc Xc Sf W Cp σ hσ
  refine ⟨δ, hδ, ?_⟩
  intro model Rm Sreg It H hH hsmall z j H1 hH1 ε hε
  obtain ⟨C, γ, N0, hC, hγ, hev⟩ := h model Rm Sreg It H hH hsmall z j H1 hH1 ε hε
  refine ⟨C, γ, N0, hC, hγ, ?_⟩
  intro N M hN hNM reverse
  obtain ⟨Bad, hm, hp, hq⟩ := hev N M hN hNM reverse
  refine ⟨Bad, hm, hp, fun omega hom infrared => ?_⟩
  obtain ⟨hq1, hq2, hq3⟩ := hq omega hom
  cases infrared
  · exact ⟨hq1 false, hq3⟩
  · exact ⟨hq1 true, hq2⟩

end Paper
