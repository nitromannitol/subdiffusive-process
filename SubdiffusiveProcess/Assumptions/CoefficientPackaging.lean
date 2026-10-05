module

public import SubdiffusiveProcess.Assumptions.Cutoff
public import Homogenization.Ambient.ScalarMatrix
public import Homogenization.Book.Ch02.Theorems

@[expose] public section

/-!
# Scalar coefficient packaging

This module packages the positive continuous cutoff as a uniformly elliptic
scalar coefficient on each bounded domain used by the deterministic theory.
-/



namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization.Book

noncomputable section

abbrev Vec (d : ℕ) := Homogenization.Vec d

/-- A scalar representative viewed as a matrix coefficient field. -/
def scalarCoeffField {d : ℕ} (a : Vec d → ℝ) : Homogenization.CoeffField d :=
  fun x => Homogenization.scalarMatrix (a x)

/-- The data needed to package one scalar coefficient on a public domain. -/
structure ScalarCoeffOnData {d : ℕ} (U : Ch02.Domain d) (a : Vec d → ℝ) where
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  aeStronglyMeasurable :
    ∀ i j : Fin d,
      AEStronglyMeasurable
        (fun x : Vec d =>
          Homogenization.restrictCoeffField (U : Set (Vec d))
            (scalarCoeffField a) x i j)
        (Homogenization.volumeMeasureOn (U : Set (Vec d)))
  aeBounds :
    ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Vec d)),
      lam ≤ a x ∧ a x ≤ Lam

/-- The public coefficient object associated with scalar data. -/
noncomputable def ScalarCoeffOnData.toCoeffOn {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (h : ScalarCoeffOnData U a) : Ch02.CoeffOn U where
  toCoeffField := scalarCoeffField a
  lam := h.lam
  Lam := h.Lam
  lam_pos := h.lam_pos
  lam_le_Lam := h.lam_le_Lam
  aeStronglyMeasurable := h.aeStronglyMeasurable
  aeElliptic := h.aeBounds.mono fun x hx => by
    have hax : 0 < a x := lt_of_lt_of_le h.lam_pos hx.1
    exact (Homogenization.isEllipticMatrix_scalarMatrix hax).mono
      h.lam_pos hx.1 hx.2

/-- Compactness and positivity give a cutoff uniform ellipticity package on
every bounded domain. -/
theorem exists_aCutoffCoeffOnData {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) :
    Nonempty (ScalarCoeffOnData U (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)) := by
  let a := _root_.SubdiffusiveProcess.Model.aCutoff M L ω
  have ha_cont : Continuous a :=
    _root_.SubdiffusiveProcess.Model.continuous_aCutoff M L ω
  have hU_compact : IsCompact (closure (U : Set (Vec d))) :=
    U.isDomain.isBoundedDomain.isBounded.isCompact_closure
  have hU_nonempty : (closure (U : Set (Vec d))).Nonempty :=
    U.nonempty.closure
  obtain ⟨x_min, hx_min, h_min⟩ :=
    hU_compact.exists_isMinOn hU_nonempty ha_cont.continuousOn
  obtain ⟨x_max, hx_max, h_max⟩ :=
    hU_compact.exists_isMaxOn hU_nonempty ha_cont.continuousOn
  refine ⟨{
    lam := a x_min
    Lam := a x_max
    lam_pos := ?_
    lam_le_Lam := h_min hx_max
    aeStronglyMeasurable := ?_
    aeBounds := ?_
  }⟩
  · exact _root_.SubdiffusiveProcess.Model.aCutoff_pos M L ω x_min
  · intro i j
    have h_cont_matrix : Continuous (fun x : Vec d =>
        Homogenization.scalarMatrix (d := d) (a x)) :=
      ha_cont.smul continuous_const
    have h_cont_entry : Continuous (fun x : Vec d =>
        Homogenization.scalarMatrix (d := d) (a x) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp h_cont_matrix)
    have h_meas_entry : AEStronglyMeasurable
        (fun x : Vec d => Homogenization.scalarMatrix (d := d) (a x) i j)
        (Homogenization.volumeMeasureOn (U : Set (Vec d))) :=
      h_cont_entry.aestronglyMeasurable
    have h_mem : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Vec d)),
        x ∈ (U : Set (Vec d)) :=
      MeasureTheory.ae_restrict_mem U.measurableSet
    refine h_meas_entry.congr ?_
    filter_upwards [h_mem] with x hx
    simp only [scalarCoeffField,
      Homogenization.restrictCoeffField_apply_of_mem hx]
    rfl
  · have h_mem : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Vec d)),
        x ∈ (U : Set (Vec d)) :=
      MeasureTheory.ae_restrict_mem U.measurableSet
    filter_upwards [h_mem] with x hx
    exact ⟨h_min (subset_closure hx), h_max (subset_closure hx)⟩

/-- A finite-cutoff coefficient on an arbitrary public bounded domain. -/
noncomputable def aCutoffCoeffOnData {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) :
    ScalarCoeffOnData U (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) :=
  Classical.choice (exists_aCutoffCoeffOnData M L ω U)

end

end SubdiffusiveProcess.CoarseGrainingVocab
