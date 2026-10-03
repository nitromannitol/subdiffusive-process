module

public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerCoefficient

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization.Book MeasureTheory

open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The general packaging -/

/-- **Every positive continuous scalar field is uniformly elliptic on a public
bounded domain.**  This is `exists_aCutoffCoeffOnData` with the cutoff replaced
by an arbitrary field: the proof uses only continuity and positivity. -/
theorem exists_scalarCoeffOnData_of_continuous_pos {a : Vec d → ℝ}
    (ha : Continuous a) (hpos : ∀ x, 0 < a x) (U : Ch02.Domain d) :
    Nonempty (ScalarCoeffOnData U a) := by
  have hU_compact : IsCompact (closure (U : Set (Vec d))) :=
    U.isDomain.isBoundedDomain.isBounded.isCompact_closure
  have hU_nonempty : (closure (U : Set (Vec d))).Nonempty := U.nonempty.closure
  obtain ⟨x_min, hx_min, h_min⟩ :=
    hU_compact.exists_isMinOn hU_nonempty ha.continuousOn
  obtain ⟨x_max, hx_max, h_max⟩ :=
    hU_compact.exists_isMaxOn hU_nonempty ha.continuousOn
  refine ⟨{
    lam := a x_min
    Lam := a x_max
    lam_pos := hpos x_min
    lam_le_Lam := h_min hx_max
    aeStronglyMeasurable := ?_
    aeBounds := ?_
  }⟩
  · intro i j
    have h_cont_matrix : Continuous (fun x : Vec d =>
        Homogenization.scalarMatrix (d := d) (a x)) :=
      ha.smul continuous_const
    have h_cont_entry : Continuous (fun x : Vec d =>
        Homogenization.scalarMatrix (d := d) (a x) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp h_cont_matrix)
    have h_mem : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Vec d)),
        x ∈ (U : Set (Vec d)) :=
      MeasureTheory.ae_restrict_mem U.measurableSet
    refine h_cont_entry.aestronglyMeasurable.congr ?_
    filter_upwards [h_mem] with x hx
    simp only [scalarCoeffField,
      Homogenization.restrictCoeffField_apply_of_mem hx]
  · have h_mem : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Vec d)),
        x ∈ (U : Set (Vec d)) :=
      MeasureTheory.ae_restrict_mem U.measurableSet
    filter_upwards [h_mem] with x hx
    exact ⟨h_min (subset_closure hx), h_max (subset_closure hx)⟩

/-- The chosen uniform-ellipticity certificate of a positive continuous scalar
field on a public bounded domain. -/
noncomputable def scalarCoeffOnDataOfContinuousPos {a : Vec d → ℝ}
    (ha : Continuous a) (hpos : ∀ x, 0 < a x) (U : Ch02.Domain d) :
    ScalarCoeffOnData U a :=
  Classical.choice (exists_scalarCoeffOnData_of_continuous_pos ha hpos U)

/-! ## The two source fields -/

/-- `B_k = exp (g_k - tau^2)` is continuous, sample by sample. -/
theorem continuous_shellFactor (M : GMCModel d) (k : ℕ)
    (omega : PotentialSample d) : Continuous (shellFactor M k omega) :=
  Real.continuous_exp.comp
    (((omega k).contDiff_one.continuous).sub continuous_const)

/-- Every layer product is continuous, sample by sample. -/
theorem continuous_layerCoefficient (M : GMCModel d) (S : Finset ℕ)
    (omega : PotentialSample d) : Continuous (layerCoefficient M S omega) :=
  continuous_finset_prod _ fun k _ => continuous_shellFactor M k omega

/-- The sparse coefficient `A_N^{(R)}` is continuous, sample by sample. -/
theorem continuous_sparseLayerCoefficient (M : GMCModel d) (R N : ℕ)
    (omega : PotentialSample d) :
    Continuous (sparseLayerCoefficient M R N omega) :=
  continuous_finset_prod _ fun j _ => continuous_shellFactor M (j * R) omega

/-- The sparse coefficient `A_N^{(R)}` is positive. -/
theorem sparseLayerCoefficient_pos (M : GMCModel d) (R N : ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    0 < sparseLayerCoefficient M R N omega x :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

/-- **The sparse coefficient as a public elliptic coefficient.**  This is the
packaging Step 4 needs in order to apply `aMatrix` to `A_N^{(R)}`. -/
noncomputable def sparseLayerCoeffOnData (M : GMCModel d) (R N : ℕ)
    (omega : PotentialSample d) (U : Ch02.Domain d) :
    ScalarCoeffOnData U (sparseLayerCoefficient M R N omega) :=
  scalarCoeffOnDataOfContinuousPos (continuous_sparseLayerCoefficient M R N omega)
    (sparseLayerCoefficient_pos M R N omega) U

/-- The shell factor `B_k` as a public elliptic coefficient. -/
noncomputable def shellFactorCoeffOnData (M : GMCModel d) (k : ℕ)
    (omega : PotentialSample d) (U : Ch02.Domain d) :
    ScalarCoeffOnData U (shellFactor M k omega) :=
  scalarCoeffOnDataOfContinuousPos (continuous_shellFactor M k omega)
    (fun _ => Real.exp_pos _) U



noncomputable def randomSparseMatrix (M : GMCModel d) (R N : ℕ)
    (U : Ch02.Domain d) (omega : PotentialSample d) : Mat d :=
  aMatrix U (sparseLayerCoeffOnData M R N omega U).toCoeffOn

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
