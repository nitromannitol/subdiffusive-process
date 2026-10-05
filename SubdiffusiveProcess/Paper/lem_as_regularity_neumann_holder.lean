module

public import SubdiffusiveProcess.Paper.lem_as_regularity_neumann_energy
public import SubdiffusiveProcess.Paper.lem_as_regularity_neumann_cells
public import SubdiffusiveProcess.Paper.lem_as_regularity_campanato_cells

@[expose] public section

/-! Root coarse coercivity and all-radius energy yield cutoff-uniform Neumann Holder bounds. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Neumann Holder regularity has a common constant over every cutoff, source and solution. -/
theorem lem_as_regularity_neumann_holder (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha : ℝ) (hal : 0 < alpha) (hal1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
        ∀ (N : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
          AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x) = 0 →
        ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) f u →
          ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha
              (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U ∧
            ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha
              (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U ≤ K * Kf := by
  let alpha0 := (1 + alpha) / 2
  have haa0 : alpha < alpha0 := by dsimp only [alpha0]; linarith only [hal1]
  have ha00 : 0 < alpha0 := hal.trans haa0
  have ha01 : alpha0 < 1 := by dsimp only [alpha0]; linarith only [hal1]
  let t := (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2*alpha) + d) / 2
  obtain ⟨ht1, ht2, he⟩ := aux_cor_neumann_source_t1_exponent d alpha hal1
  change (d : ℝ) - 1 < t at ht1
  change t < (d : ℝ) at ht2
  change 0 < 2 + t - 2*alpha - d at he
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by linarith only [hd2, ht1]
  let e := min (2 + t - 2*alpha - d) 1
  have hepos : 0 < e := lt_min he zero_lt_one
  have he1 : e ≤ 1 := min_le_right _ _
  have hs : e / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by linarith only [he1]⟩
  obtain ⟨de, hde, henergy⟩ := lem_as_regularity_neumann_energy d hd E Pc Xc W Cp Sf
    D Step Dbase Interp t ht1 ht2
  obtain ⟨dc, hdc, hcoarse⟩ := lem_as_coarse d hd E Pc Xc Sf W Cp D inputs_hES_witness
    Step Dbase Interp (e / 2) (3/4) hs (by norm_num)
  obtain ⟨dm, hdm, hmic⟩ := aux_cor_neumann_source_campanato d hd E Pc Xc W D alpha0
    1 (fun _ => 1) ha00 ha01 (fun _ => le_rfl)
  obtain ⟨Cd, hCd, hcamp⟩ := lem_as_regularity_campanato_cells (d := d) alpha alpha0 hal hal1.le haa0
  refine ⟨min de (min dm (min 1 dc)), lt_min hde (lt_min hdm (lt_min zero_lt_one hdc)), ?_⟩
  intro M Rm Sreg It H hIR hdelta
  obtain ⟨Km, Cm, hKm, -, -, hm⟩ := hmic M Rm Sreg It H hIR
    (hdelta.trans ((min_le_right _ _).trans (min_le_left _ _)))
  filter_upwards [henergy M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)), hm,
    hcoarse M Rm Sreg It H hIR (hdelta.trans ((min_le_right _ _).trans (min_le_right _ _)))
      (fun _ => (1/2:ℝ)) 1 one_pos ⟨0, by norm_num⟩] with omega hen hmic hc
  obtain ⟨KE, hKE, hen⟩ := hen
  obtain ⟨Kell, hKell, hc⟩ := hc
  obtain ⟨X, hX, hcells⟩ := lem_as_regularity_neumann_cells hd E Pc alpha t ht0 he KE Kell hKE.le hKell.le
  have hCp : 0 < Cp.C alpha := Cp.C_pos alpha hal hal1
  refine ⟨(2 + Real.sqrt d) * Cp.C alpha * (Cd * (X+1)), by positivity, ?_⟩
  intro N f Kf hKf hf hfb hf0 u hu
  have hroot0 := (hc true).1 2 (Or.inr rfl) N
  simp only [ite_true] at hroot0
  have hroot : (E.lam (fun _ => (1/2:ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos)
      (fun _ => (1/2:ℝ)) 1 (e/2) 2)⁻¹ ≤ Kell :=
    (le_add_of_nonneg_left (E.Lam_pos _ _ _ _ _ _ _ _).le).trans hroot0
  have hcell := hcells M H omega N hroot u Kf (hen N f Kf hKf hf hfb hf0 u hu)
  have hcampa := hcamp X hX.le u Kf (Km N omega) hKf (hKm N omega) hcell
    (hmic N f Kf hKf hf hfb hf0 u hu)
  exact aux_cor_neumann_source_holder_of_campanato Cp hal hal1 u (by positivity) hKf hcampa

end SubdiffusiveProcess.Paper
