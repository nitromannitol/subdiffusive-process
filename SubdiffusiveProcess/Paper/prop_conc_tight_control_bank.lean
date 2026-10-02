import SubdiffusiveProcess.Paper.prop_conc_native_cell_control
import SubdiffusiveProcess.Paper.prop_conc_actual_controls_with_moment

/-! A countable tight bank whose bounded subsequences carry all actual analytic controls.
This exposes the finite-cutoff bounds before subsequence selection; it does not assert concentration. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- Coercivity and the actual harmonic mesh bounds supply all deterministic analytic controls. -/
theorem aux_prop_conc_tight_control_bank_assemble
    {d : ℕ} (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ → ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha)
    (B : ℝ) (hB : 0 ≤ B)
    (hcoer : ∀ n (v : S.space),
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v.val.1)).toReal ^ 2 ≤
      B * responseForm S (cutoffPositiveCoefficient M H om (N n) z hr) v v)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => cutoffCoefficient M H om (N n)) t alpha) :
    Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
      (fun n => cutoffPositiveCoefficient M H om (N n) z hr)) := by
  obtain ⟨D, hDc, hDd, hDs⟩ := SmoothSources.exists_countable_dense_smooth_submodule z r hr
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hdR, ht]
  refine ⟨{
    K := B + 1
    K_pos := by linarith only [hB]
    coercive := ?_
    interpolation := Interp
    sources := D
    sources_countable := hDc
    sources_dense := hDd
    sources_smooth := hDs
    mesh := ?_
    t := t
    t_lower := ht
    t_upper := htd
    cutoffs := aux_prop_conc_actual_coercivity_cutoffs_with_moment_cutoffs
      hd z hr S hS M H om N t alpha ht0 ha hcell }⟩
  · intro n v
    refine ⟨Sob.h1_fractional_finite z r hr
      ⟨v.val, killedSobolevGraph_le_weakSobolevGraph (hS ▸ v.property)⟩, (hcoer n v).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith only []) (responseForm_nonneg _ _ _)
  · exact prop_conc_mesh_approximate_control hd z r hr S hS
      (fun n => cutoffCoefficient M H om (N n))
      (fun n => cutoffCoefficient_continuous M H om (N n))
      (fun n x => cutoffCoefficient_pos M H om (N n) x)
      (fun n => cutoffPositiveCoefficient M H om (N n) z hr)
      (fun n => (cutoffPositiveCoefficient_representative M H om (N n) z hr).2.2.2)
      t alpha hcell

/-- Actual cutoff controls are supplied on every subsequence bounded by one fixed countable tight bank. -/
theorem prop_conc_tight_control_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (hS : S.space = killedSobolevGraph (centeredCube z r hr)),
      ∃ (F : Option ((J : ℕ) × OddGridIndex d (triadicHalf J)) → ℕ → BilateralField d → ℝ)
        (C : Option ((J : ℕ) × OddGridIndex d (triadicHalf J)) → ℝ≥0),
        (∀ i n, MemLp (F i n) 1 (chaosSampleLaw M).toMeasure) ∧
        (∀ i n, eLpNorm (F i n) 1 (chaosSampleLaw M).toMeasure ≤ C i) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ N : ℕ → ℕ, (∀ i, ∃ B : ℝ, ∀ n, |F i (N n) om| ≤ B) →
          Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
            (fun n => cutoffPositiveCoefficient M H om (N n) z hr)) ∧
          aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
            (fun n => cutoffCoefficient M H om (N n)) t alpha := by
  classical
  obtain ⟨deltaSmall, hdeltaSmall, hsmall⟩ := prop_growth d hd I Pin X W Cp Sob
    t alpha 1 (fun _ => 1) ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨deltaLarge, hdeltaLarge, hlarge⟩ := prop_growth_large_root d hd I Pin X W Cp Sob
    t alpha 1 (fun _ => 1) ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨deltaC, hdeltaC, hcoerc⟩ := prop_conc_coercivity_bank d hd I Pin Sob
  refine ⟨min (min deltaSmall deltaLarge) deltaC, lt_min (lt_min hdeltaSmall hdeltaLarge) hdeltaC, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS
  let Idx := (J : ℕ) × OddGridIndex d (triadicHalf J)
  let cz : Idx → SpatialCoordinates d := fun i => oddGridCenter z r (triadicHalf i.1) i.2
  let cr : Idx → ℝ := fun i => r / (2 * (triadicHalf i.1 : ℝ) + 1)
  have chr : ∀ i, 0 < cr i := fun _ => div_pos hr (by positivity)
  have hcell (i : Idx) := if h : cr i ≤ 1 then
      hsmall M Rm Sreg It H hIR (hdelta.trans ((min_le_left _ _).trans (min_le_left _ _)))
        (cz i) (cr i) (chr i) h
    else hlarge M Rm Sreg It H hIR (hdelta.trans ((min_le_left _ _).trans (min_le_right _ _)))
      (cz i) (cr i) (chr i) (lt_of_not_ge h)
  choose K0 C0 hmem hnorm _hge hgrowth using hcell
  obtain ⟨Kc, Cc, hKc0, hKcm, hKcn, hc⟩ :=
    hcoerc M Rm H hIR (hdelta.trans (min_le_right _ _)) z r hr
  let bank : Option Idx → ℕ → BilateralField d → ℝ := fun i =>
    match i with | none => Kc | some j => K0 j
  let bounds : Option Idx → ℝ≥0 := fun i =>
    match i with | none => Cc | some j => (C0 j 0).toNNReal
  refine ⟨bank, bounds, ?_, ?_, ?_⟩
  · intro i n
    cases i with
    | none => exact hKcm n
    | some j => simpa only [bank, ENNReal.ofReal_one] using hmem j 0 n
  · intro i n
    cases i with
    | none => exact hKcn n
    | some j => simpa only [bank, bounds, ENNReal.ofReal_one, ENNReal.coe_toNNReal] using hnorm j 0 n
  filter_upwards [ae_all_iff.mpr hgrowth] with om hg
  intro N hb
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hdR, ht]
  have hall : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => cutoffCoefficient M H om (N n)) t alpha := by
    intro J hside theta htheta thetaH hthetaH k
    let i : Idx := ⟨J, k⟩
    obtain ⟨B, hB⟩ := hb (some i)
    apply prop_conc_native_cell_control hd (cz i) (cr i) (chr i)
      ((lane2_cell_side_eq r J).le.trans hside)
      (fun n => cutoffCoefficient M H om (N n))
      (fun n => cutoffPositiveCoefficient M H om (N n) (cz i) (chr i))
      (fun n => (cutoffPositiveCoefficient_representative M H om (N n) (cz i) (chr i)).2.2.2)
      t alpha (max B 0) ht0 ha (le_max_right _ _) _ theta
      (htheta.of_le (WithTop.coe_le_coe.mpr le_top))
      (thetaH.restrict (oddGridCell z r hr (triadicHalf J) k).isOpen
        (oddGridCell_subset z hr (triadicHalf J) k)) hthetaH
    intro n phi hphi b u hbrep hsolve
    have hKle : K0 i (N n) om ≤ max B 0 :=
      ((le_abs_self _).trans (hB n)).trans (le_max_left _ _)
    have hCphi0 := aux_prop_growth_c2Norm_nonneg (closedCube (cz i) (cr i) (chr i) :
      Set (SpatialCoordinates d)) phi
    obtain ⟨henergy, U, hUcont, hUae, hUholder, hUnorm⟩ := hg i (N n)
      (fun _ => 0) 0 le_rfl aemeasurable_const
      (Eventually.of_forall fun _ => by norm_num) phi _ hphi le_rfl b u hbrep hsolve
    refine ⟨?_, U, hUcont, hUae, hUholder, ?_⟩
    · intro x rad hx hrad hrad1
      have he := henergy x rad hx hrad hrad1
      rw [zero_add] at he
      exact he.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKle (sq_nonneg _)) (Real.rpow_nonneg hrad.le _))
    · rw [zero_add] at hUnorm
      exact hUnorm.trans (mul_le_mul_of_nonneg_right hKle hCphi0)
  obtain ⟨B, hB⟩ := hb none
  refine ⟨aux_prop_conc_tight_control_bank_assemble hd Sob Interp M H om N z r hr S hS
    t alpha ht htd ha (max B 0) (le_max_right _ _) ?_ hall, hall⟩
  intro n v
  have hbound : Kc (N n) om ≤ max B 0 :=
    ((le_abs_self _).trans (hB n)).trans (le_max_left _ _)
  exact (hc (N n) om ⟨v.val, hS ▸ v.property⟩).trans
    (mul_le_mul_of_nonneg_right hbound (sobolevCoefficientForm_nonneg _ _))

end
end Paper
