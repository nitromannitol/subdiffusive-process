module

public import SubdiffusiveProcess.Paper.prop_conc
public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.thm_prop_env_orig_limits
public import SubdiffusiveProcess.Paper.prop_conc_setup
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The conclusion of `aux_prop_conc_thin_core` after `C0`, `p` are fixed, as a predicate (text copied). -/
def aux_thm_prop_env_conc_core
    (d : ℕ) (hd : 2 ≤ d) (I : Paper.in_J d) (C0 p aexp : ℝ) : Prop :=
      ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ) (m M : ℝ)
        (zcell : SpatialCoordinates d) (k : ℕ) (cellIdx paddedIdx : ℕ)
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
          zcell k cellIdx paddedIdx hPk AE AF),
      let ck : ℝ := ∫ om, Matrix.trace (AF om) / Matrix.trace (AE om) ∂P
      let B : Ω → Matrix (Fin d) (Fin d) ℝ := fun om =>
        (Matrix.trace (AE om))⁻¹ • (AF om - ck • AE om)
      let Band : ℕ → MeasurableSpace Ω := fun Hband =>
        ⨆ (j : ℤ) (_h : |j + (k : ℤ)| ≤ (Hband : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun om : Ω => field om j)
      ck ∈ Icc m M ∧
      (∀ i j : Fin d, ∫ om, B om i j ∂P = 0) ∧
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |B om i j|) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * model.delta * (M - m)) ∧
      ∀ Hband : ℕ,
        eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
          |B om i j - (P[fun om' => B om' i j | Band Hband]) om|) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (Hband : ℝ)))

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The conditioning band of the environment space is the pullback of the band on the sample space. -/
theorem aux_thm_prop_env_scale_band_comap {d : ℕ} {Ω : Type*}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] (field : Ω → BilateralField d) (k Hband : ℕ) :
    aux_thm_prop_scale_band field k Hband =
      MeasurableSpace.comap field
        (aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) k Hband) := by
  unfold aux_thm_prop_scale_band
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The conditional moment bounds of the relative matrices transfer from the sample space
to any space carrying a measure-preserving `field` and a.e. equal matrices. -/
theorem aux_thm_prop_env_moments_transport {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure Ω) [IsProbabilityMeasure P] (field : Ω → BilateralField d)
    (P0 : Measure (BilateralField d)) [IsProbabilityMeasure P0]
    (hmp : MeasurePreserving field P P0)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (AE0 AF0 : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (hE : ∀ j, ∀ᵐ om ∂P, AE j om = AE0 j (field om))
    (hF : ∀ j, ∀ᵐ om ∂P, AF j om = AF0 j (field om))
    (hE0 : ∀ j i k, Measurable (fun β => AE0 j β i k))
    (hF0 : ∀ j i k, Measurable (fun β => AF0 j β i k))
    (hband : ∀ k Hband, aux_thm_prop_scale_band field k Hband =
      MeasurableSpace.comap field
        (aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) k Hband))
    (ck : ℝ → ℝ) (H1 : ℕ) (p C aexp : ℝ) (hp : 1 ≤ p)
    (h0 : aux_thm_prop_cell_matrix_moments P0 (fun β => β) z r AE0 AF0 ck H1 p C aexp) :
    aux_thm_prop_cell_matrix_moments P field z r AE AF ck H1 p C aexp := by
  intro n zc
  let F0 : BilateralField d → Matrix (Fin d) (Fin d) ℝ :=
    aux_thm_prop_cell_relative_matrix z r AE0 AF0 ck zc (aux_thm_prop_mass_side H1 n)
  let F : Ω → Matrix (Fin d) (Fin d) ℝ :=
    aux_thm_prop_cell_relative_matrix z r AE AF ck zc (aux_thm_prop_mass_side H1 n)
  have hB : ∀ᵐ om ∂P, F om = F0 (field om) := by
    filter_upwards [hE (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1,
      hF (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1] with om hEom hFom
    change aux_thm_prop_cell_relative_matrix z r AE AF ck zc (aux_thm_prop_mass_side H1 n) om
      = aux_thm_prop_cell_relative_matrix z r AE0 AF0 ck zc (aux_thm_prop_mass_side H1 n) (field om)
    by_cases hav : aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side H1 n)
    · rw [aux_thm_prop_cell_relative_matrix_eq _ _ _ _ _ _ _ hav,
          aux_thm_prop_cell_relative_matrix_eq _ _ _ _ _ _ _ hav]
      unfold aux_thm_prop_relative_matrix
      rw [hEom, hFom]
    · simp only [aux_thm_prop_cell_relative_matrix, if_neg hav]
  have hB0entry : ∀ i j : Fin d, Measurable (fun β : BilateralField d => F0 β i j) := by
    intro i j
    by_cases hav : aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side H1 n)
    · have hfun : (fun β : BilateralField d => F0 β i j) =
          (fun β : BilateralField d =>
            aux_thm_prop_relative_matrix AE0 AF0 ck r
              (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1 β i j) := by
        funext β
        change aux_thm_prop_cell_relative_matrix z r AE0 AF0 ck zc (aux_thm_prop_mass_side H1 n) β i j =
          aux_thm_prop_relative_matrix AE0 AF0 ck r
            (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1 β i j
        rw [aux_thm_prop_cell_relative_matrix_eq _ _ _ _ _ _ _ hav]
      rw [hfun]
      exact aux_thm_prop_relative_matrix_measurable AE0 AF0 ck r hE0 hF0 _ i j
    · have hfun : (fun β : BilateralField d => F0 β i j) = fun _ : BilateralField d => (0 : ℝ) := by
        funext β
        change aux_thm_prop_cell_relative_matrix z r AE0 AF0 ck zc (aux_thm_prop_mass_side H1 n) β i j = (0 : ℝ)
        simp only [aux_thm_prop_cell_relative_matrix, if_neg hav, Matrix.zero_apply]
      rw [hfun]
      exact measurable_const
  have hS0 : Measurable (fun β : BilateralField d => ∑ i : Fin d, ∑ j : Fin d, |F0 β i j|) :=
    Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => (hB0entry i j).abs))
  have hSint : Integrable (fun β : BilateralField d => ∑ i : Fin d, ∑ j : Fin d, |F0 β i j|) P0 :=
    MemLp.integrable (ENNReal.one_le_ofReal.mpr hp)
      (lt_of_le_of_lt (h0 n zc).1 ENNReal.ofReal_lt_top)
  have hSeq : (fun om : Ω => ∑ i : Fin d, ∑ j : Fin d, |F om i j|) =ᵐ[P]
      (fun om : Ω => ∑ i : Fin d, ∑ j : Fin d, |F0 (field om) i j|) := by
    filter_upwards [hB] with om hom
    rw [hom]
  constructor
  · calc eLpNorm (fun om : Ω => ∑ i : Fin d, ∑ j : Fin d, |F om i j|) (ENNReal.ofReal p) P
        = eLpNorm (fun om : Ω => ∑ i : Fin d, ∑ j : Fin d, |F0 (field om) i j|) (ENNReal.ofReal p) P :=
          eLpNorm_congr_ae hSeq
      _ = eLpNorm (fun β : BilateralField d => ∑ i : Fin d, ∑ j : Fin d, |F0 β i j|)
            (ENNReal.ofReal p) P0 :=
          eLpNorm_comp_measurePreserving hS0.aestronglyMeasurable hmp
      _ ≤ ENNReal.ofReal C := (h0 n zc).1
  · intro Hband
    have hband_eq := hband (H1 * n) Hband
    have hb : aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband =
        ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (Hband : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun β : BilateralField d => β j) := rfl
    have hm : aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband ≤
        (inferInstance : MeasurableSpace (BilateralField d)) := by
      unfold aux_thm_prop_scale_band
      exact iSup_le fun j => iSup_le fun _ => measurable_iff_comap_le.mp (measurable_pi_apply j)
    have hcond : ∀ i j : Fin d, ∀ᵐ om ∂P,
        (P[fun om => F om i j | aux_thm_prop_scale_band field (H1 * n) Hband]) om
          = (P0[fun β => F0 β i j |
              aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband])
            (field om) := by
      intro i j
      have hfij : Integrable (fun β : BilateralField d => F0 β i j) P0 := by
        refine Integrable.mono hSint (hB0entry i j).aestronglyMeasurable ?_
        filter_upwards with β
        have hnn : 0 ≤ ∑ y : Fin d, ∑ x : Fin d, |F0 β y x| :=
          Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => abs_nonneg _
        have h1 : |F0 β i j| ≤ ∑ x : Fin d, |F0 β i x| :=
          Finset.single_le_sum (f := fun x : Fin d => |F0 β i x|) (s := Finset.univ)
            (fun x _ => abs_nonneg _) (Finset.mem_univ j)
        have h2 : (∑ x : Fin d, |F0 β i x|) ≤ ∑ y : Fin d, ∑ x : Fin d, |F0 β y x| :=
          Finset.single_le_sum (f := fun y : Fin d => ∑ x : Fin d, |F0 β y x|) (s := Finset.univ)
            (fun y _ => Finset.sum_nonneg fun x _ => abs_nonneg _) (Finset.mem_univ i)
        calc ‖F0 β i j‖ = |F0 β i j| := Real.norm_eq_abs _
          _ ≤ ∑ y : Fin d, ∑ x : Fin d, |F0 β y x| := le_trans h1 h2
          _ = ‖∑ y : Fin d, ∑ x : Fin d, |F0 β y x|‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hcc := condExp_comp_measurePreserving hmp hm hfij
      have h1 : (P[fun om => F om i j | aux_thm_prop_scale_band field (H1 * n) Hband]) =ᵐ[P]
          (P[fun om => F0 (field om) i j | aux_thm_prop_scale_band field (H1 * n) Hband]) := by
        apply condExp_congr_ae
        filter_upwards [hB] with om hom
        rw [hom]
      have h2 : (P[fun om => F0 (field om) i j | aux_thm_prop_scale_band field (H1 * n) Hband]) =ᵐ[P]
          (P[fun om => F0 (field om) i j |
            (aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband).comap
              field]) := by
        rw [hband_eq]
      exact h1.trans (h2.trans hcc)
    have hcall : ∀ᵐ om ∂P, ∀ i j : Fin d,
        (P[fun om => F om i j | aux_thm_prop_scale_band field (H1 * n) Hband]) om
          = (P0[fun β => F0 β i j |
              aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband])
            (field om) := by
      rw [eventually_all]
      intro i
      rw [eventually_all]
      intro j
      exact hcond i j
    have hcm : ∀ i j : Fin d, Measurable (fun β : BilateralField d =>
        (P0[fun β => F0 β i j |
          aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband]) β) := by
      intro i j
      exact ((stronglyMeasurable_condExp (μ := P0) (m :=
        aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband)
        (f := fun β : BilateralField d => F0 β i j)).measurable).mono hm le_rfl
    have hTmeas : Measurable (fun β : BilateralField d => ∑ i : Fin d, ∑ j : Fin d,
        |F0 β i j - (P0[fun β => F0 β i j |
          aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband]) β|) :=
      Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        ((hB0entry i j).sub (hcm i j)).abs
    have hSae : (fun om : Ω => ∑ i : Fin d, ∑ j : Fin d,
        |F om i j - (P[fun om => F om i j | aux_thm_prop_scale_band field (H1 * n) Hband]) om|) =ᵐ[P]
      (fun om : Ω => ∑ i : Fin d, ∑ j : Fin d,
        |F0 (field om) i j - (P0[fun β => F0 β i j |
          aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband]) (field om)|) := by
      filter_upwards [hB, hcall] with om hom hc
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hom, hc i j]
    calc eLpNorm (fun om : Ω => ∑ i : Fin d, ∑ j : Fin d,
          |F om i j - (P[fun om => F om i j | aux_thm_prop_scale_band field (H1 * n) Hband]) om|)
          (ENNReal.ofReal p) P
        = eLpNorm (fun om : Ω => ∑ i : Fin d, ∑ j : Fin d,
          |F0 (field om) i j - (P0[fun β => F0 β i j |
            aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband])
              (field om)|) (ENNReal.ofReal p) P := eLpNorm_congr_ae hSae
      _ = eLpNorm (fun β : BilateralField d => ∑ i : Fin d, ∑ j : Fin d,
          |F0 β i j - (P0[fun β => F0 β i j |
            aux_thm_prop_scale_band (Ω := BilateralField d) (fun β => β) (H1 * n) Hband]) β|)
          (ENNReal.ofReal p) P0 := eLpNorm_comp_measurePreserving hTmeas.aestronglyMeasurable hmp
      _ ≤ ENNReal.ofReal (C * 3 ^ (-aexp * (Hband : ℝ))) := (h0 n zc).2 Hband

end Part2

section Part3
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Lane3
open scoped Topology ENNReal NNReal InnerProductSpace BigOperators

/-- The deterministic expected trace ratio at a mass radius, read off any mass cell of that radius. -/
def aux_thm_prop_env_ck {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d))
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (AE AF : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ) (H1 : ℕ) (rho : ℝ) : ℝ := by
  classical
  exact if h : ∃ j, (∃ n, r j = aux_thm_prop_mass_side H1 n) ∧ r j = rho then
    ∫ β, Matrix.trace (AF h.choose β) / Matrix.trace (AE h.choose β) ∂P else 0

/-- **Concentration of the limiting cell matrices on the original space.** -/
theorem thm_prop_env_concentration
    (d : ℕ) (hd : 2 ≤ d) [NeZero d] (I : Paper.in_J d) (C0 : ℝ) (p aexp : ℝ) (H1 : ℕ)
    (hcore : aux_thm_prop_env_conc_core d hd I C0 p aexp) :
    ∃ delta0 Cp' : ℝ, 0 < delta0 ∧ 0 < Cp' ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization model H)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GE0 GF0 : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE0 NF0 : ℕ → ℕ)
        (hJ0 : in_joint_extracted_candidates d model H (BilateralField d)
          (chaosSampleLaw model).toMeasure (fun β => β) z r hr Sspace
          (fun i N β => volumeResponseOperator (Sspace i)
            (Lane4.cutoffPositiveCoefficient model H β N (z i) (hr i))) GE0 GF0 NE0 NF0)
        (AE0 AF0 : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hsymE : ∀ j β, (AE0 j β).transpose = AE0 j β)
        (hsymF : ∀ j β, (AF0 j β).transpose = AF0 j β)
        (hAE : ∀ j, (∃ n, r j = aux_thm_prop_mass_side H1 n) →
          ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
            aux_thm_prop_affine_converges model H β (z j) (r j) (hr j) NE0
              (aux_thm_prop_env_hPcube (z j) (r j) (hr j)) (AE0 j β))
        (hAF : ∀ j, (∃ n, r j = aux_thm_prop_mass_side H1 n) →
          ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
            aux_thm_prop_affine_converges model H β (z j) (r j) (hr j) NF0
              (aux_thm_prop_env_hPcube (z j) (r j) (hr j)) (AF0 j β))
        (m M : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
        (horder0 : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
          limitFormDomain (GE0 i β) = limitFormDomain (GF0 i β) ∧
          ∀ u ∈ limitFormDomain (GE0 i β),
            m * (limitFormEnergy (GE0 i β) u).toReal ≤ (limitFormEnergy (GF0 i β) u).toReal ∧
            (limitFormEnergy (GF0 i β) u).toReal ≤ M * (limitFormEnergy (GE0 i β) u).toReal),
        aux_thm_prop_cell_matrix_moments (chaosSampleLaw model).toMeasure (fun β => β) z r AE0 AF0
          (aux_thm_prop_env_ck (chaosSampleLaw model).toMeasure z r AE0 AF0 H1) H1 p
          (Cp' * model.delta * (M - m)) aexp := by
  obtain ⟨delta0, Cp', hd0, hCp', hh⟩ := hcore
  refine ⟨delta0, Cp', hd0, hCp', ?_⟩
  intro _ _ model hδ Rm Sreg It H hH z r hr Sspace GE0 GF0 NE0 NF0 hJ0 AE0 AF0 hsymE hsymF hAE hAF
    m M hm hmM hM horder0
  haveI : IsProbabilityMeasure (chaosSampleLaw model).toMeasure := inferInstance
  have hck : ∀ j, (∃ n, r j = aux_thm_prop_mass_side H1 n) →
      aux_thm_prop_env_ck (chaosSampleLaw model).toMeasure z r AE0 AF0 H1 (r j) =
        ∫ β, Matrix.trace (AF0 j β) / Matrix.trace (AE0 j β) ∂(chaosSampleLaw model).toMeasure := by
    intro j hj
    have hex : ∃ i, (∃ n, r i = aux_thm_prop_mass_side H1 n) ∧ r i = r j := ⟨j, hj, rfl⟩
    unfold aux_thm_prop_env_ck
    rw [dif_pos hex]
    have hc := hex.choose_spec
    exact (aux_thm_prop_expected_trace_ratio_equal_radii model H hH
      (chaosSampleLaw model).toMeasure (fun β => β) measurable_id Measure.map_id
      (z hex.choose) (z j) (hr hex.choose) (hr j) hc.2.symm
      (aux_thm_prop_env_hPcube (z hex.choose) (r hex.choose) (hr hex.choose))
      (aux_thm_prop_env_hPcube (z j) (r j) (hr j)) NE0 NF0
      (AE0 hex.choose) (AF0 hex.choose) (AE0 j) (AF0 j)
      (hAE hex.choose hc.1) (hAF hex.choose hc.1) (hAE j hj) (hAF j hj)).symm
  apply aux_thm_prop_cell_moments_mask
  intro n zc havail
  obtain ⟨hzC, hrC, hzP, hrP⟩ := aux_thm_prop_cell_index_spec z r zc
    (aux_thm_prop_mass_side H1 n) havail
  set jC := (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1 with hjC
  set jP := (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).2 with hjP
  have hmass : ∃ n', r jC = aux_thm_prop_mass_side H1 n' := ⟨n, hrC⟩
  have hs_rpow : aux_thm_prop_mass_side H1 n = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)) :=
    aux_thm_prop_mass_side_rpow H1 n
  have hrk : r jC = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)) := hrC.trans hs_rpow
  have hPk := aux_thm_prop_env_hPcube (z jC) ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)))
    (Real.rpow_pos_of_pos zero_lt_three _)
  have hAEjC : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ pvec : Fin d → ℝ,
      Tendsto (fun j => aux_prop_conc_setup_resp model H (z jC) (H1 * n) hPk (NE0 j) β pvec)
        atTop (𝓝 (pvec ⬝ᵥ (AE0 jC β).mulVec pvec)) := by
    filter_upwards [hAE jC hmass] with β hβ pvec
    exact (hβ pvec).congr (fun j => (aux_thm_prop_env_setup_resp_eq model H (z jC) (H1 * n)
      (r jC) (hr jC) hrk (aux_thm_prop_env_hPcube (z jC) (r jC) (hr jC)) hPk (NE0 j) β pvec).symm)
  have hAFjC : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ pvec : Fin d → ℝ,
      Tendsto (fun j => aux_prop_conc_setup_resp model H (z jC) (H1 * n) hPk (NF0 j) β pvec)
        atTop (𝓝 (pvec ⬝ᵥ (AF0 jC β).mulVec pvec)) := by
    filter_upwards [hAF jC hmass] with β hβ pvec
    exact (hβ pvec).congr (fun j => (aux_thm_prop_env_setup_resp_eq model H (z jC) (H1 * n)
      (r jC) (hr jC) hrk (aux_thm_prop_env_hPcube (z jC) (r jC) (hr jC)) hPk (NF0 j) β pvec).symm)
  have hcell := hh model hδ Rm Sreg It H (BilateralField d) (chaosSampleLaw model).toMeasure
    (fun β => β) z r hr Sspace
    (fun i N β => volumeResponseOperator (Sspace i)
      (Lane4.cutoffPositiveCoefficient model H β N (z i) (hr i))) GE0 GF0 NE0 NF0 m M (z jC)
    (H1 * n) jC jP hPk (AE0 jC) (AF0 jC)
    ⟨hJ0, ⟨hm, hmM, hM⟩, horder0, ⟨rfl, hrk⟩,
      ⟨hzP.trans hzC.symm, hrP.trans (by rw [hs_rpow])⟩, hsymE jC, hsymF jC, hAEjC, hAFjC⟩
  have hck' := hck jC hmass
  have hB : ∀ β, aux_thm_prop_relative_matrix AE0 AF0
      (aux_thm_prop_env_ck (chaosSampleLaw model).toMeasure z r AE0 AF0 H1) r jC β =
      (Matrix.trace (AE0 jC β))⁻¹ • (AF0 jC β - (∫ β', Matrix.trace (AF0 jC β') /
        Matrix.trace (AE0 jC β') ∂(chaosSampleLaw model).toMeasure) • AE0 jC β) := by
    intro β
    unfold aux_thm_prop_relative_matrix
    rw [hck']
  show eLpNorm _ _ _ ≤ _ ∧ _
  simp only [hB]
  exact ⟨hcell.2.2.1, hcell.2.2.2⟩

end Part3

section Part4
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Lane3
open scoped Topology ENNReal NNReal InnerProductSpace BigOperators

/-- The moment bounds only involve the matrices of mass cells. -/
theorem aux_thm_prop_env_moments_mask_congr {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (AE AF AE' AF' : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ)
    (H1 : ℕ) (p C aexp : ℝ)
    (hE : ∀ j, (∃ n, r j = aux_thm_prop_mass_side H1 n) → AE' j = AE j)
    (hF : ∀ j, (∃ n, r j = aux_thm_prop_mass_side H1 n) → AF' j = AF j)
    (h : aux_thm_prop_cell_matrix_moments P field z r AE AF ck H1 p C aexp) :
    aux_thm_prop_cell_matrix_moments P field z r AE' AF' ck H1 p C aexp := by
  intro n zc
  have h' := h n zc
  by_cases hav : aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side H1 n)
  · have hs := aux_thm_prop_cell_index_spec z r zc (aux_thm_prop_mass_side H1 n) hav
    have hmass : ∃ n', r (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1 =
        aux_thm_prop_mass_side H1 n' := ⟨n, hs.2.1⟩
    have hrel : aux_thm_prop_cell_relative_matrix z r AE' AF' ck zc (aux_thm_prop_mass_side H1 n) =
        aux_thm_prop_cell_relative_matrix z r AE AF ck zc (aux_thm_prop_mass_side H1 n) := by
      funext om
      rw [aux_thm_prop_cell_relative_matrix_eq z r AE' AF' ck zc _ hav,
        aux_thm_prop_cell_relative_matrix_eq z r AE AF ck zc _ hav]
      unfold aux_thm_prop_relative_matrix
      rw [hE _ hmass, hF _ hmass]
    simp only [hrel]
    exact h'
  · have hrel : aux_thm_prop_cell_relative_matrix z r AE' AF' ck zc (aux_thm_prop_mass_side H1 n) =
        aux_thm_prop_cell_relative_matrix z r AE AF ck zc (aux_thm_prop_mass_side H1 n) := by
      funext om
      classical
      simp only [aux_thm_prop_cell_relative_matrix, if_neg hav]
    simp only [hrel]
    exact h'

/-- **The concentration bounds transfer from the original space to the represented space.** -/
theorem aux_thm_prop_env_hconc_of_orig {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure Ω) [IsProbabilityMeasure P] (field : Ω → BilateralField d)
    (P0 : Measure (BilateralField d)) [IsProbabilityMeasure P0]
    (hmp : MeasurePreserving field P P0)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (H1 : ℕ)
    (AEh AFh : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (AE0 AF0 : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (hEid : ∀ j, (∃ n, r j = aux_thm_prop_mass_side H1 n) →
      ∀ᵐ om ∂P, AEh j om = AE0 j (field om))
    (hFid : ∀ j, (∃ n, r j = aux_thm_prop_mass_side H1 n) →
      ∀ᵐ om ∂P, AFh j om = AF0 j (field om))
    (hE0 : ∀ j i k, Measurable (fun β => AE0 j β i k))
    (hF0 : ∀ j i k, Measurable (fun β => AF0 j β i k))
    (ck : ℝ → ℝ) (p C aexp : ℝ) (hp : 1 ≤ p)
    (h0 : aux_thm_prop_cell_matrix_moments P0 (fun β => β) z r AE0 AF0 ck H1 p C aexp) :
    aux_thm_prop_cell_matrix_moments P field z r AEh AFh ck H1 p C aexp := by
  classical
  let mass : ℕ → Prop := fun j => ∃ n, r j = aux_thm_prop_mass_side H1 n
  let AEm : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ := fun j om => if mass j then AEh j om else 0
  let AFm : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ := fun j om => if mass j then AFh j om else 0
  let AE0m : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun j β =>
    if mass j then AE0 j β else 0
  let AF0m : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun j β =>
    if mass j then AF0 j β else 0
  have h0m : aux_thm_prop_cell_matrix_moments P0 (fun β => β) z r AE0m AF0m ck H1 p C aexp :=
    aux_thm_prop_env_moments_mask_congr P0 (fun β => β) z r AE0 AF0 AE0m AF0m ck H1 p C aexp
      (fun j hj => by funext β; simp only [AE0m, mass, if_pos hj])
      (fun j hj => by funext β; simp only [AF0m, mass, if_pos hj]) h0
  have hmom := aux_thm_prop_env_moments_transport P field P0 hmp z r AEm AFm AE0m AF0m
    (fun j => by
      by_cases hj : mass j
      · filter_upwards [hEid j hj] with om h
        simp only [AEm, AE0m, mass, if_pos hj, h]
      · exact Filter.Eventually.of_forall fun om => by simp only [AEm, AE0m, mass, if_neg hj])
    (fun j => by
      by_cases hj : mass j
      · filter_upwards [hFid j hj] with om h
        simp only [AFm, AF0m, mass, if_pos hj, h]
      · exact Filter.Eventually.of_forall fun om => by simp only [AFm, AF0m, mass, if_neg hj])
    (fun j i k => by
      by_cases hj : mass j
      · simp only [AE0m, mass, if_pos hj]; exact hE0 j i k
      · simp only [AE0m, mass, if_neg hj]; exact measurable_const)
    (fun j i k => by
      by_cases hj : mass j
      · simp only [AF0m, mass, if_pos hj]; exact hF0 j i k
      · simp only [AF0m, mass, if_neg hj]; exact measurable_const)
    (fun k Hband => aux_thm_prop_env_scale_band_comap field k Hband) ck H1 p C aexp hp h0m
  exact aux_thm_prop_env_moments_mask_congr P field z r AEm AFm AEh AFh ck H1 p C aexp
    (fun j hj => by funext om; simp only [AEm, mass, if_pos hj])
    (fun j hj => by funext om; simp only [AFm, mass, if_pos hj]) hmom

end Part4

section Part5


/-- A moment exponent large enough for the density count. -/
theorem aux_thm_prop_env_pconst (H1 d : ℕ) (aexp : ℝ) (haexp : 0 < aexp) :
    ∃ p : ℝ, 2 ≤ p ∧
      2 * (2 * Real.log 2 + 1 + (48 / (1 / 32 : ℝ)) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3 := by
  set A : ℝ := 2 * (2 * Real.log 2 + 1 + (48 / (1 / 32 : ℝ)) *
          (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) with hA
  refine ⟨max 2 (A / (aexp * Real.log 3)), le_max_left _ _, ?_⟩
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
  have hpos : 0 < aexp * Real.log 3 := mul_pos haexp hlog3
  have hle : A / (aexp * Real.log 3) ≤ max 2 (A / (aexp * Real.log 3)) := le_max_right _ _
  have h := mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
  rw [div_mul_cancel₀ A (ne_of_gt hpos)] at h
  calc A ≤ max 2 (A / (aexp * Real.log 3)) * (aexp * Real.log 3) := h
    _ = max 2 (A / (aexp * Real.log 3)) * aexp * Real.log 3 := by ring

end Part5

end Paper
end
