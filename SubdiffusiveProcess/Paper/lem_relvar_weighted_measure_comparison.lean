module

public import SubdiffusiveProcess.Paper.lem_borel_weights
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Comparison of the represented weighted measures under the displayed
coefficient and normalization hypotheses. -/
theorem lem_relvar_weighted_measure_comparison
    (d : ℕ) (_hd : 2 ≤ d)
    (Q : Opens (SpatialCoordinates d))
    (E F Eg Fg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F)
    (GammaEg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg)
    (GammaFg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Fg)
    (hdomEF : E.domain = F.domain)
    (hdomEg : Eg.domain = E.domain)
    (hdomFg : Fg.domain = E.domain)
    (m M : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (horder : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
      MeasurableSet A →
        m * (GammaE.measure u A).toReal ≤ (GammaF.measure u A).toReal ∧
          (GammaF.measure u A).toReal ≤ M * (GammaE.measure u A).toReal)
    (g : SpatialCoordinates d → ℝ) (G : ℝ)
    (_hbound : ∀ x, |g x| ≤ G)
    (hweightE : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
      MeasurableSet A →
        GammaEg.measure u A =
          ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u))
    (hweightF : ∀ u ∈ F.domain, ∀ A : Set (SpatialCoordinates d),
      MeasurableSet A →
        GammaFg.measure u A =
          ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u)) :
    ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      m * (GammaEg.measure u A).toReal ≤ (GammaFg.measure u A).toReal ∧
        (GammaFg.measure u A).toReal ≤ M * (GammaEg.measure u A).toReal := by
  intro u hu A hA
  have huF : u ∈ F.domain := by
    rw [← hdomEF]
    exact hu
  have huEg : u ∈ Eg.domain := by
    rw [hdomEg]
    exact hu
  have huFg : u ∈ Fg.domain := by
    rw [hdomFg]
    exact hu
  have hEtop : GammaE.measure u A ≠ ⊤ := by
    apply ne_top_of_lt
    exact (measure_mono (subset_univ A)).trans_lt (GammaE.measure_univ_lt_top u hu)
  have hFtop : GammaF.measure u A ≠ ⊤ := by
    apply ne_top_of_lt
    exact (measure_mono (subset_univ A)).trans_lt (GammaF.measure_univ_lt_top u huF)
  have hEgTop : GammaEg.measure u A ≠ ⊤ := by
    apply ne_top_of_lt
    exact (measure_mono (subset_univ A)).trans_lt (GammaEg.measure_univ_lt_top u huEg)
  have hFgTop : GammaFg.measure u A ≠ ⊤ := by
    apply ne_top_of_lt
    exact (measure_mono (subset_univ A)).trans_lt (GammaFg.measure_univ_lt_top u huFg)
  have hbase_lower :
      ENNReal.ofReal m • GammaE.measure u ≤ GammaF.measure u := by
    rw [Measure.le_iff]
    intro B hB
    have hEBtop : GammaE.measure u B ≠ ⊤ := by
      apply ne_top_of_lt
      exact (measure_mono (subset_univ B)).trans_lt (GammaE.measure_univ_lt_top u hu)
    have hFBtop : GammaF.measure u B ≠ ⊤ := by
      apply ne_top_of_lt
      exact (measure_mono (subset_univ B)).trans_lt (GammaF.measure_univ_lt_top u huF)
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEBtop) hFBtop).mp
    simpa [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hm] using (horder u hu B hB).1
  have hM : 0 ≤ M := hm.trans hmM
  have hbase_upper :
      GammaF.measure u ≤ ENNReal.ofReal M • GammaE.measure u := by
    rw [Measure.le_iff]
    intro B hB
    have hEBtop : GammaE.measure u B ≠ ⊤ := by
      apply ne_top_of_lt
      exact (measure_mono (subset_univ B)).trans_lt (GammaE.measure_univ_lt_top u hu)
    have hFBtop : GammaF.measure u B ≠ ⊤ := by
      apply ne_top_of_lt
      exact (measure_mono (subset_univ B)).trans_lt (GammaF.measure_univ_lt_top u huF)
    apply (ENNReal.toReal_le_toReal hFBtop
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEBtop)).mp
    simpa [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hM] using (horder u hu B hB).2
  have hlin_lower :
      ENNReal.ofReal m *
          (∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u)) ≤
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u) := by
    have h := lintegral_mono'
      (f := fun x : SpatialCoordinates d => ENNReal.ofReal (Real.exp (g x)))
      (g := fun x : SpatialCoordinates d => ENNReal.ofReal (Real.exp (g x)))
      (Measure.restrict_mono_measure hbase_lower A)
      (fun _ => le_rfl)
    rw [Measure.restrict_smul, lintegral_smul_measure] at h
    exact h
  have hlin_upper :
      ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u) ≤
        ENNReal.ofReal M *
          (∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u)) := by
    have h := lintegral_mono'
      (f := fun x : SpatialCoordinates d => ENNReal.ofReal (Real.exp (g x)))
      (g := fun x : SpatialCoordinates d => ENNReal.ofReal (Real.exp (g x)))
      (Measure.restrict_mono_measure hbase_upper A)
      (fun _ => le_rfl)
    rw [Measure.restrict_smul, lintegral_smul_measure] at h
    exact h
  have hweightedE := hweightE u hu A hA
  have hweightedF := hweightF u huF A hA
  have hIntEtop :
      (∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u)) ≠ ⊤ := by
    rw [← hweightedE]
    exact hEgTop
  have hIntFtop :
      (∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u)) ≠ ⊤ := by
    rw [← hweightedF]
    exact hFgTop
  constructor
  · rw [hweightedE, hweightedF]
    have hreal := ENNReal.toReal_mono hIntFtop hlin_lower
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm] using hreal
  · rw [hweightedE, hweightedF]
    have hRtop := ENNReal.mul_ne_top (a := ENNReal.ofReal M)
      (b := ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u))
      ENNReal.ofReal_ne_top hIntEtop
    have hreal := ENNReal.toReal_mono hRtop hlin_upper
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using hreal

end
end SubdiffusiveProcess.Paper
