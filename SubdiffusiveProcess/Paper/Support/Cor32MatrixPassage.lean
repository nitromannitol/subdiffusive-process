module

public import SubdiffusiveProcess.Paper.Support.Cor32ModelDefinitions
public import SubdiffusiveProcess.Paper.candidate_good_estimates_matrix_passage
public import SubdiffusiveProcess.ResponseMoments.TraceCoercivity

@[expose] public section





open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_cor_32_reference_pos {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (eRef : ℕ → ℝ)
    (he : ∀ k, 0 < eRef k) (k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) :
    0 < aux_cor_32_reference H eRef k z omega :=
  mul_pos (he k) (Real.exp_pos _)

lemma aux_cor_32_reference_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (eRef : ℕ → ℝ) (k : ℕ) (z : SpatialCoordinates d) :
    Measurable (aux_cor_32_reference H eRef k z) := by
  apply Measurable.const_mul
  apply Measurable.exp
  exact ((continuous_eval_const z).measurable.comp hH).add
    (Finset.measurable_sum _ fun j _ =>
      (continuous_eval_const z).measurable.comp (measurable_pi_apply (-(j : ℤ))))

/-- Actual normalized finite-cutoff chart convergence derives the guard on the original law. -/
lemma aux_cor_32_chart_guard
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (s sigma : ℝ) (hsigma : sigma ∈ Ioc (0 : ℝ) 1) (gH cbuf : ℕ)
    (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal) (phi : ℕ → ℕ)
    (k : ℕ) (z : SpatialCoordinates d)
    (ZLim DLim : ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AELim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ)
    (hArr : aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Z Draw phi
      k z ZLim DLim loLim hiLim AELim errLim ratioLim)
    (eRef : ℕ → ℝ) (he : ∀ k, 0 < eRef k)
    (k0 : ℕ) (lambdaLim cell epshom cdet : ℝ) (hcell : 0 < cell) :
    let c0 := ((d : ℝ) / cell ^ 2)⁻¹
    let U : Fin 3 × (Fin d → Fin 3) := (0, fun _ => 1)
    let A := fun omega => aux_cor_32_reference H eRef k z omega • AELim U omega
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      omega ∈ gcat_good k0 lambdaLim cell epshom cdet ZLim DLim loLim hiLim errLim ratioLim →
        0 < Matrix.trace (A omega) ∧
          ∀ x : Fin d → ℝ, c0 * Matrix.trace (A omega) * (x ⬝ᵥ x) ≤
            x ⬝ᵥ (A omega).mulVec x := by
  intro c0 U A
  obtain ⟨_, _, hlo, hhi, hA, _, _⟩ := hArr
  have hChart := aux_candidate_good_estimates_matrix_passage_chart_limit_ae
    (chaosSampleLaw M).toMeasure I sigma hsigma
    (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
    (fun n omega => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n)
      (gcat_rootCentre gH k z U) (zpow_pos (by norm_num) _))
    (fun n omega => gcat_sN M H (phi n) (gcat_rootLevel gH k U)
      (gcat_rootCentre gH k z U) omega)
    _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (loLim U) (hiLim U) (AELim U) (hlo U) (hhi U) (hA U)
  filter_upwards [hChart] with omega hc hg
  have hbounds := hg.2.1 U
  have hpos := hcell.trans_le hbounds.1
  obtain ⟨_, htr, hquad⟩ := hc hpos
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hC : (0 : ℝ) < (d : ℝ) / cell ^ 2 := div_pos hd (sq_pos_of_pos hcell)
  have hdim : (d : ℝ) ≤ ((d : ℝ) / cell ^ 2) * cell ^ 2 := by
    rw [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hcell))]
  have hcoerce := aux_candidate_good_estimates_matrix_passage_good_matrix_bounds
    cell ((d : ℝ) / cell ^ 2) (loLim U omega) (hiLim U omega) (AELim U omega)
    hcell hC hdim hbounds.1 hbounds.2 htr hquad
  exact _root_.SubdiffusiveProcess.ResponseMoments.trace_coercivity_smul (AELim U omega)
    (aux_cor_32_reference H eRef k z omega) c0
    (aux_cor_32_reference_pos H eRef he k z omega)
    (_root_.SubdiffusiveProcess.ResponseMoments.trace_pos_of_quadratic_lower _ _ hpos hquad) hcoerce

end SubdiffusiveProcess.Paper
