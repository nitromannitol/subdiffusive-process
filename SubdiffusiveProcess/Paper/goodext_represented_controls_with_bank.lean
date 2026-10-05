module

public import SubdiffusiveProcess.Paper.prop_conc_actual_controls
public import SubdiffusiveProcess.Paper.prop_conc_countable_native_growth_with_bank
public import SubdiffusiveProcess.Paper.inputs_classical_countable_bounded_subsequence
public import SubdiffusiveProcess.Paper.candidate_represented_source_bank

@[expose] public section

/-! Transfers actual cutoff analytic controls to equal-law represented environments; it does not assert that fixed-environment subsequences persist as environments vary. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.ResponseMoments Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- One represented subsequence carries analytic controls, every mesh-cell bound, and any countable uniformly integrable scalar bank. -/
theorem goodext_represented_controls_with_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (_hS : S.space = killedSobolevGraph (centeredCube z r hr)) (N : ℕ → ℕ)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (_hEnv : ∀ n, Measurable (env n))
        (_hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
        (Jbank : Type) [Countable Jbank]
        (Xbank : Jbank → ℕ → Omega → ℝ) (Bbank : Jbank → ℝ≥0)
        (_hExtraMem : ∀ j n, MemLp (Xbank j n) 1 P)
        (_hExtraNorm : ∀ j n, eLpNorm (Xbank j n) 1 P ≤ Bbank j),
      ∀ᵐ om ∂P,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
          (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) z hr)) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
          (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n))) t alpha ∧
        ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ n, |Xbank j (seq n) om| ≤ B := by
  classical
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨deltaSmall, hdeltaSmall, hsmall⟩ :=
    prop_growth d hd I Pin X W Cp Sob t alpha 1 (fun _ => 1)
      ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨deltaLarge, hdeltaLarge, hlarge⟩ :=
    prop_growth_large_root d hd I Pin X W Cp Sob t alpha 1 (fun _ => 1)
      ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨deltaCoer, hdeltaCoer, hcoerAll⟩ :=
    prop_conc_coercivity_bank d hd I Pin Sob
  refine ⟨min (min deltaSmall deltaLarge) deltaCoer,
    lt_min (lt_min hdeltaSmall hdeltaLarge) hdeltaCoer, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS N Omega _ P _ env hEnv hLaw
    Jbank _ Xbank Bbank hExtraMem hExtraNorm
  let Idx := (J : ℕ) × OddGridIndex d (triadicHalf J)
  let cz : Idx → SpatialCoordinates d := fun i =>
    oddGridCenter z r (triadicHalf i.1) i.2
  let cr : Idx → ℝ := fun i => r / (2 * (triadicHalf i.1 : ℝ) + 1)
  have chr : ∀ i, 0 < cr i := fun _ => div_pos hr (by positivity)
  have hdeltaSmall' : M.delta ≤ deltaSmall :=
    hdelta.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdeltaLarge' : M.delta ≤ deltaLarge :=
    hdelta.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdeltaCoer' : M.delta ≤ deltaCoer := hdelta.trans (min_le_right _ _)
  obtain ⟨Kcoer, Ccoer, hKcoer, hKmem, hKnorm, hcoer⟩ :=
    hcoerAll M Rm H hIR hdeltaCoer' z r hr
  have hcell (i : Idx) := if hside : cr i ≤ 1 then
      hsmall M Rm Sreg It H hIR hdeltaSmall' (cz i) (cr i) (chr i) hside
    else hlarge M Rm Sreg It H hIR hdeltaLarge' (cz i) (cr i) (chr i)
      (lt_of_not_ge hside)
  choose Kcell Ccell hmemCell hnormCell _hgeCell hgrowthCell using hcell
  let basebank : Option Idx → ℕ → Omega → ℝ := fun oi n om =>
    match oi with
    | none => Kcoer (N n) (env n om)
    | some i => Kcell i (N n) (env n om)
  let basebounds : Option Idx → ℝ≥0 := fun oi =>
    match oi with
    | none => Ccoer
    | some i => (Ccell i 0).toNNReal
  have hmp (n : ℕ) : MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure :=
    ⟨hEnv n, hLaw n⟩
  have hbaseMem : ∀ oi n, MemLp (basebank oi n) 1 P := by
    intro oi n
    cases oi with
    | none =>
        change MemLp (Kcoer (N n) ∘ env n) 1 P
        exact (hKmem (N n)).comp_measurePreserving (hmp n)
    | some i =>
        simpa only [basebank, Function.comp_apply, ENNReal.ofReal_one] using!
          (hmemCell i 0 (N n)).comp_measurePreserving (hmp n)
  have hbaseNorm : ∀ oi n, eLpNorm (basebank oi n) 1 P ≤ basebounds oi := by
    intro oi n
    cases oi with
    | none =>
        change eLpNorm (Kcoer (N n) ∘ env n) 1 P ≤ Ccoer
        rw [eLpNorm_comp_measurePreserving
          (hKmem (N n)).aestronglyMeasurable (hmp n)]
        exact hKnorm (N n)
    | some i =>
        change eLpNorm (Kcell i (N n) ∘ env n) 1 P ≤ (Ccell i 0).toNNReal
        rw [eLpNorm_comp_measurePreserving
          (hmemCell i 0 (N n)).aestronglyMeasurable (hmp n)]
        simpa only [ENNReal.ofReal_one, ENNReal.coe_toNNReal] using!
          hnormCell i 0 (N n)
  let bank : (Option Idx ⊕ Jbank) → ℕ → Omega → ℝ := Sum.elim basebank Xbank
  let bounds : (Option Idx ⊕ Jbank) → ℝ≥0 := Sum.elim basebounds Bbank
  have hbankMem : ∀ i n, MemLp (bank i n) 1 P := by
    intro i n
    cases i with
    | inl oi => exact hbaseMem oi n
    | inr j => exact hExtraMem j n
  have hbankNorm : ∀ i n, eLpNorm (bank i n) 1 P ≤ bounds i := by
    intro i n
    cases i with
    | inl oi => exact hbaseNorm oi n
    | inr j => exact hExtraNorm j n
  let CellGrowth (i : Idx) (m : ℕ) (xi : BilateralField d) : Prop :=
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube (cz i) (cr i) (chr i) :
        Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂(volume.restrict (centeredCube (cz i) (cr i) (chr i) :
        Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube (cz i) (cr i) (chr i) : Set (SpatialCoordinates d))
          phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube (cz i) (cr i) (chr i))),
          ((b : SobolevData (centeredCube (cz i) (cr i) (chr i))).1 :
            SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube (cz i) (cr i) (chr i) :
                Set (SpatialCoordinates d))] phi →
          SolvesDirichlet
            (cutoffPositiveCoefficient M H xi m (cz i) (chr i)) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube (cz i) (cr i) (chr i) → 0 < rad → rad ≤ 1 →
            localGradientEnergy
              (cutoffPositiveCoefficient M H xi m (cz i) (chr i))
              (s := Metric.ball x rad ∩ (centeredCube (cz i) (cr i) (chr i) :
                Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter
                (centeredCube (cz i) (cr i) (chr i)).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube (cz i) (cr i)
                (chr i)))) ≤ Kcell i m xi * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube (cz i) (cr i) (chr i))).1 :
              SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict (centeredCube (cz i) (cr i) (chr i) :
                  Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha
              (closedCube (cz i) (cr i) (chr i) : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha
              (closedCube (cz i) (cr i) (chr i) : Set (SpatialCoordinates d)) U ≤
                Kcell i m xi * (Kf + Cphi))
  have hgrowthEnv : ∀ᵐ om ∂P, ∀ i n, CellGrowth i (N n) (env n om) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    filter_upwards [ae_of_ae_map (hEnv n).aemeasurable
      (by rw [hLaw n]; exact hgrowthCell i)] with om hm
    exact hm (N n)
  have hbank := inputs_classical_countable_bounded_subsequence P bank bounds
    hbankMem hbankNorm
  filter_upwards [hbank, hgrowthEnv] with om hbankOm hgrowthOm
  obtain ⟨seq, hseq, hbound⟩ := hbankOm
  obtain ⟨B, hB, hKcoerBound⟩ := hbound (Sum.inl none)
  have hcellBounds : ∀ i, ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      |Kcell i (N (seq n)) (env (seq n) om)| ≤ K := by
    intro i
    obtain ⟨K, hK, hKbound⟩ := hbound (Sum.inl (some i))
    exact ⟨K, hK, hKbound⟩
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hdR, ht]
  have hcellAll : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n))) t alpha := by
    intro Jmesh hside theta htheta thetaH hthetaH k
    let i : Idx := ⟨Jmesh, k⟩
    have hcr : cr i ≤ 1 := (cell_side_eq r Jmesh).le.trans hside
    obtain ⟨K, hK, hKbound⟩ := hcellBounds i
    let beta : H1Function (centeredCube (cz i) (cr i) (chr i) :
        Set (SpatialCoordinates d)) := thetaH.restrict
          (oddGridCell z r hr (triadicHalf Jmesh) k).isOpen
          (oddGridCell_subset z hr (triadicHalf Jmesh) k)
    have hbeta : beta.toFun = theta := by
      change thetaH.toFun = theta
      exact hthetaH
    let Cphi := c2Norm (closedCube (cz i) (cr i) (chr i) :
      Set (SpatialCoordinates d)) theta
    have hCphi : 0 ≤ Cphi := aux_prop_growth_c2Norm_nonneg _ _
    have hE : 0 ≤ K * Cphi ^ 2 := mul_nonneg hK (sq_nonneg _)
    refine ⟨K * Cphi ^ 2, 2 ^ t * (K * Cphi ^ 2), K * Cphi,
      hE, mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE,
      mul_nonneg hK hCphi, ?_⟩
    intro n v hharm htrace hvcont
    let a := cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) (cz i) (chr i)
    have hc := (cutoffPositiveCoefficient_representative M H (env (seq n) om)
      (N (seq n)) (cz i) (chr i)).2.2.2
    have hmin := native_harmonic_energy_eq_infimum a _ hc beta v htrace hharm
    have hP := centeredCube_killedPoincare (cz i) (chr i)
    have hsolve := solvesDirichlet_zero_of_native_minimum hP a _ hc beta v htrace hmin.le
    have hraw := hgrowthOm i (seq n)
    obtain ⟨henergy, U, hUcont, hUae, hUholder, hUnorm⟩ :=
      hraw (fun _ => 0) 0 le_rfl aemeasurable_const
        (Filter.Eventually.of_forall fun _ => by norm_num)
        theta Cphi (htheta.of_le (WithTop.coe_le_coe.mpr le_top)) le_rfl _ _
        ((sobolevDataOfH1_fst_coeFn beta).trans
          (Filter.Eventually.of_forall fun x => congrFun hbeta x)) hsolve
    have hKle : Kcell i (N (seq n)) (env (seq n) om) ≤ K :=
      (le_abs_self _).trans (hKbound n)
    have heq := eqOn_closure_of_ae_eq_restrict
      (centeredCube (cz i) (cr i) (chr i)).isOpen hvcont hUcont.continuousOn
      ((sobolevDataOfH1_fst_coeFn v).symm.trans hUae)
    rw [aux_prop_conc_form_cutoff_continuity_closure_cube] at heq
    have hholder : IsHolderOn alpha
        (closedCube (cz i) (cr i) (chr i) : Set (SpatialCoordinates d)) v.toFun :=
      (isHolderOn_congr heq).mpr hUholder
    have hnorm : cAlphaNorm alpha
        (closedCube (cz i) (cr i) (chr i) : Set (SpatialCoordinates d)) v.toFun ≤
        K * Cphi := by
      rw [cAlphaNorm_congr heq]
      have hmul : Kcell i (N (seq n)) (env (seq n) om) * (0 + Cphi) ≤ K * Cphi := by
        simpa only [zero_add] using mul_le_mul_of_nonneg_right hKle hCphi
      exact hUnorm.trans hmul
    have henergyScaled : ∀ x rad, x ∈ centeredCube (cz i) (cr i) (chr i) →
        0 < rad → rad ≤ 1 →
        localGradientEnergy a
          (s := Metric.ball x rad ∩ (centeredCube (cz i) (cr i) (chr i) :
            Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter
            (centeredCube (cz i) (cr i) (chr i)).isOpen.measurableSet)
          (sobolevGradient (sobolevDataOfH1 v)) ≤ K * Cphi ^ 2 * rad ^ t := by
      intro x rad hx hrad hrad1
      have hrawEnergy := henergy x rad hx hrad hrad1
      have hcoef : Kcell i (N (seq n)) (env (seq n) om) * Cphi ^ 2 * rad ^ t ≤
          K * Cphi ^ 2 * rad ^ t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKle (sq_nonneg Cphi))
          (Real.rpow_nonneg hrad.le _)
      calc
        _ ≤ Kcell i (N (seq n)) (env (seq n) om) * Cphi ^ 2 * rad ^ t := by
          simpa only [zero_add] using hrawEnergy
        _ ≤ K * Cphi ^ 2 * rad ^ t := hcoef
    constructor
    · apply native_energy_le_of_unit_growth (cz i) (chr i) hcr a _ hc v
      simpa only [Real.one_rpow, mul_one] using henergyScaled (cz i) 1
        (Metric.mem_ball_self (half_pos (chr i))) one_pos le_rfl
    · constructor
      · intro x hx rad hrad hrad1
        exact native_energyMeasure_growth_of_localGradient (cz i) (chr i) hcr a _ hc v
          (K * Cphi ^ 2) t hE ht0
          (fun y hy s hs hs1 => henergyScaled y s hy hs hs1) x rad hrad hrad1
      · have hset : (oddGridCell z r hr (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)) = centeredCube (cz i) (cr i) (chr i) := by
          rw [oddGridCell_coe, centeredCube]
          dsimp only [cz, cr, i]
          rfl
        have hpair := aux_lem_cutoffs_pair_bound_of_holder ha hholder hnorm
        intro x hx y hy
        apply hpair x ?_ y ?_
        · rw [← aux_prop_conc_form_cutoff_continuity_closure_cube, ← hset]
          exact hx
        · rw [← aux_prop_conc_form_cutoff_continuity_closure_cube, ← hset]
          exact hy
  have ⟨D, hDc, hDd, hDs⟩ :=
    SmoothSources.exists_countable_dense_smooth_submodule z r hr
  refine ⟨seq, hseq, ?_, hcellAll, fun j => hbound (Sum.inr j)⟩
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
    cutoffs := ?_ }⟩
  · intro n v
    refine ⟨Sob.h1_fractional_finite z r hr
      ⟨v.val, killedSobolevGraph_le_weakSobolevGraph (hS ▸ v.property)⟩, ?_⟩
    have hc0 := hcoer (N (seq n)) (env (seq n) om) ⟨v.val, hS ▸ v.property⟩
    have hle : Kcoer (N (seq n)) (env (seq n) om) ≤ B :=
      (le_abs_self _).trans (hKcoerBound n)
    have hle' : Kcoer (N (seq n)) (env (seq n) om) ≤ B + 1 := by
      linarith only [hle]
    exact hc0.trans (mul_le_mul_of_nonneg_right hle'
      (sobolevCoefficientForm_nonneg _ _))
  · exact prop_conc_mesh_approximate_control hd z r hr S hS
      (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n)))
      (fun n => cutoffCoefficient_continuous M H (env (seq n) om) (N (seq n)))
      (fun n x => cutoffCoefficient_pos M H (env (seq n) om) (N (seq n)) x)
      (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) z hr)
      (fun n => (cutoffPositiveCoefficient_representative M H (env (seq n) om)
        (N (seq n)) z hr).2.2.2)
      t alpha hcellAll
  · have ht0' : 0 ≤ t := ht0
    apply prop_conc_mesh_cutoff_family d hd z r hr S hS
      (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n)))
      (fun n => cutoffCoefficient_continuous M H (env (seq n) om) (N (seq n)))
      (fun n x => cutoffCoefficient_pos M H (env (seq n) om) (N (seq n)) x)
      (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) z hr)
      (fun n => (cutoffPositiveCoefficient_representative M H (env (seq n) om)
        (N (seq n)) z hr).2.2.2)
      t alpha ht0' ha
    exact hcellAll

end SubdiffusiveProcess.Paper
