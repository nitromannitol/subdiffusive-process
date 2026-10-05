module

public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_onestep
public import SubdiffusiveProcess.Paper.lem_as_regularity_native_allowance
public import SubdiffusiveProcess.Paper.lem_as_regularity_reference_extremes
public import SubdiffusiveProcess.Paper.lem_as_regularity_primitive_witness
public import SubdiffusiveProcess.Paper.lem_as_regularity_unit_sup
public import SubdiffusiveProcess.Paper.inputs_responses_witness
public import SubdiffusiveProcess.Paper.inputs_hES_witness

@[expose] public section

/-! A common random constant controls Dirichlet oscillation on every resolved grid window.
The microscopic windows and pointwise Holder conclusion are not asserted here. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The original prefix bank gives cutoff-uniform Dirichlet grid-window decay. -/
theorem lem_as_regularity_dirichlet_mesh
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha : ℝ) (hal : 0 < alpha) (hal1 : alpha < 1) :
    ∃ delta0 : ℝ,0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d,ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,∃ K : ℝ,0 < K ∧
    ∀ (N k : ℕ),k ≤ N → ∀ a ∈ gridIndices d 1 (k+1),
      gridPoint (k+1) a ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),0 ≤ Kf →
      AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),|F y| ≤ Kf) →
    ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),ContDiff ℝ 2 phi →
      c2Norm (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
    ∀ b u : weakSobolevGraph (unitNeumannCube d),
      ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos) F b u →
    ∀ U : SpatialCoordinates d → ℝ,Continuous U →
      ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U →
      let V := Metric.ball (gridPoint (k+1) a) ((9/2:ℝ)*(3:ℝ)^(-(k:ℤ))) ∩
        (unitNeumannCube d : Set (SpatialCoordinates d))
      normalizedL2On V (fun y => U y-averageOn V U) ≤
        K*(Kf+Cphi)*(3:ℝ)^(-(alpha*k)) := by
  have dimNZ : NeZero d := ⟨by omega⟩
  obtain ⟨eps,rate,ds,C,Cp0,heps,hrate,hds,hC,hCp0,hstep⟩ :=
    lem_as_regularity_dirichlet_onestep d hd E D (1-alpha) (by linarith only [hal1])
  obtain ⟨Cresp,dr,hCr,hdr,hresponses⟩ := inputs_responses_witness d hd 1 le_rfl
  let q : ℝ := 256*d+32
  have hq : 1 ≤ q := by dsimp only [q]; linarith only [Nat.cast_nonneg (α:=ℝ) d]
  have hsq : 8*(d:ℝ) < (1/32:ℝ)*q := by dsimp only [q]; linarith
  let A := 2*((d:ℝ)*Real.log 3+1)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hent : (d:ℝ)*Real.log 3 < A*(1/2) := by dsimp only [A]; linarith
  obtain ⟨db,hdb,hbank⟩ := lem_as_regularity_native_allowance d hd E Pc Xc Sf W Cp D inputs_hES_witness
    Step Dbase Interp Cresp hCr (1/32) eps q rate A (by norm_num) heps hq hsq hrate hA
    2 1 1 (1/2) zero_le_one (by norm_num) hent
  obtain ⟨dv,hdv,href⟩ := lem_as_regularity_reference_extremes d hd 1 zero_lt_one
  obtain ⟨du,hdu,hsup⟩ := lem_as_regularity_unit_sup d hd E Pc Xc W Cp Sf D Step Dbase Interp
  refine ⟨min ds (min dr (min db (min dv du))),lt_min hds (lt_min hdr (lt_min hdb (lt_min hdv hdu))),?_⟩
  intro M Rm Sreg It H hIR hdelta
  have hds' := hdelta.trans (min_le_left _ _)
  have hdr' := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdb' := hdelta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdv' := hdelta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hdu' := hdelta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨Rm0,hRm0,-⟩ := hresponses M hdr'
  obtain ⟨eta,Fs,Ps,Rs,Draw,Z,good,hEta,hPS⟩ :=
    lem_as_regularity_primitive_witness M (1/32) eps (by norm_num) heps
  filter_upwards [hstep M Rm0 H hIR hds' eta Fs Ps Rs Draw Z good hEta hPS,
    hbank M Rm0 Sreg It H hIR hdb' hRm0 eta hEta Fs Ps Rs Draw Z good hPS,
    href M Rm0 H hIR hdv',hsup M Rm Sreg It H hIR hdu'] with omega hs hb hv hu
  obtain ⟨B,hB,hb⟩ := hb
  obtain ⟨V,hV,hv⟩ := hv
  obtain ⟨Cs,hCs,hu⟩ := hu
  let Kdeep := C*(243*Cs+d+V*Cp0)
  let Kshallow := Cs*(3:ℝ)^(alpha*(2*B))
  have hKd : 0 < Kdeep := by dsimp only [Kdeep]; positivity
  have hKs : 0 < Kshallow := by dsimp only [Kshallow]; positivity
  refine ⟨Kdeep+Kshallow,add_pos hKd hKs,?_⟩
  intro N k hkN a ha hw F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsol U hU hrep W0
  have hCphi0 : 0 ≤ Cphi := (aux_prop_growth_holder_assembly_c2Norm_nonneg _ _).trans hCphi
  have hdata : 0 ≤ Kf+Cphi := add_nonneg hKf hCphi0
  have hsupU := hu N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsol U hU hrep
  have hsupf : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) y| ≤ Cs*(Kf+Cphi) := by
    filter_upwards [hrep,ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with y hy hym
    rw [hy]
    exact hsupU y (centeredCube_subset_closedCube _ _ hym)
  have hosc := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.normalizedL2On_sub_average_eq_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset (show W0 ⊆ (unitNeumannCube d : Set (SpatialCoordinates d)) from inter_subset_right) hrep)
  by_cases hk : 2*B ≤ (k:ℝ)
  · let p : PrefixRootIndex d := (k,a,1)
    have hp : p ∈ prefixRootCatalogue d 1 1 k := (mem_prefixRootCatalogue 1 1 k p).mpr ⟨rfl,ha,by dsimp only [p]; omega⟩
    have hlev : prefixRootLevel 1 p = 0 := by norm_num [prefixRootLevel,p]
    have hh := hb N k p hp (by rw [hlev]; exact Int.natCast_nonneg _)
    simp only [hlev,sub_zero,Int.toNat_natCast] at hh
    dsimp only [prefixRootCentre,p] at hh
    have hall : nativeScoreAllowance (fun j => Z N j ((3:ℝ)^N • gridPoint (k+1) a) omega)
        (fun j => Draw N j ((3:ℝ)^N • gridPoint (k+1) a) omega) N rate ≤ k := by
      have hn : ((nativeScoreAllowance (fun j => Z N j ((3:ℝ)^N • gridPoint (k+1) a) omega)
        (fun j => Draw N j ((3:ℝ)^N • gridPoint (k+1) a) omega) N rate):ℝ) ≤ k := by
        change (nativeScoreAllowance _ _ _ _ : ℝ) ≤ _ at hh
        linarith only [hh,hk]
      exact_mod_cast hn
    have hs0 := hs N k hkN (gridPoint (k+1) a) hw hall F Kf hKf hFm hFb phi Cphi hphi hCphi
      b u hb0 hsol (Cs*(Kf+Cphi)) (mul_nonneg hCs.le hdata) hsupf
    dsimp only at hs0
    rw [show 1-(1-alpha)=alpha by ring,hosc] at hs0
    have hr := hv N 0 (Nat.zero_le _) _ (centeredCube_subset_closedCube _ _ hw)
    simp only [Nat.cast_zero,mul_zero,Real.rpow_zero,mul_one] at hr
    have hri : (aux_in_deterministic_onestep_sref M H omega N 0 (gridPoint (k+1) a))⁻¹ ≤ V :=
      (le_add_of_nonneg_left (aux_in_deterministic_onestep_sref_pos M H omega N 0 _).le).trans hr
    have hrr := mul_le_mul_of_nonneg_right hri (mul_nonneg hCp0.le hKf)
    have hbr : 243*(Cs*(Kf+Cphi))+(d:ℝ)*Cphi+
        (aux_in_deterministic_onestep_sref M H omega N 0 (gridPoint (k+1) a))⁻¹*Cp0*Kf ≤
        (243*Cs+d+V*Cp0)*(Kf+Cphi) := by
      nlinarith only [hrr,mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) hKf,
        mul_nonneg (mul_nonneg hV.le hCp0.le) hCphi0]
    have hd := hs0.trans (mul_le_mul_of_nonneg_left hbr (mul_nonneg hC.le (by positivity)))
    calc _ ≤ Kdeep*(Kf+Cphi)*(3:ℝ)^(-(alpha*k)) := by dsimp only [Kdeep]; convert hd using 1 ; ring
         _ ≤ (Kdeep+Kshallow)*(Kf+Cphi)*(3:ℝ)^(-(alpha*k)) := by gcongr; linarith only [hKs]
  · have hWfin : volume W0 ≠ ⊤ := (lt_of_le_of_lt (measure_mono inter_subset_right)
        (show volume (unitNeumannCube d : Set (SpatialCoordinates d)) < ⊤ by
          rw [unitNeumannCube,centeredCube_volume]; exact ENNReal.ofReal_lt_top)).ne
    have hWpos : 0 < (volume W0).toReal := ENNReal.toReal_pos
      ((isOpen_ball.inter (unitNeumannCube d).isOpen).measure_pos volume ⟨gridPoint (k+1) a,
        mem_ball_self (by positivity),hw⟩).ne' hWfin
    have hf : MemLp ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) 2
        (volume.restrict W0) := (Lp.memLp _).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
    have hh := normalizedOscillation_le_of_ae_bound (isOpen_ball.inter (unitNeumannCube d).isOpen).measurableSet
      hWpos hWfin _ hf (Cs*(Kf+Cphi)) (mul_nonneg hCs.le hdata)
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right hsupf)
    rw [hosc] at hh
    have hone : 1 ≤ (3:ℝ)^(alpha*(2*B))*(3:ℝ)^(-(alpha*k)) := by
      rw [← Real.rpow_add (by norm_num)]
      apply Real.one_le_rpow (by norm_num)
      nlinarith only [hal,le_of_not_ge hk]
    have hm := mul_le_mul_of_nonneg_left hone (mul_nonneg hCs.le hdata)
    calc _ ≤ Cs*(Kf+Cphi) := hh
         _ ≤ Kshallow*(Kf+Cphi)*(3:ℝ)^(-(alpha*k)) := by dsimp only [Kshallow]; nlinarith only [hm]
         _ ≤ (Kdeep+Kshallow)*(Kf+Cphi)*(3:ℝ)^(-(alpha*k)) := by gcongr; linarith only [hKd]

end SubdiffusiveProcess.Paper
