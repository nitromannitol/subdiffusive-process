module

public import SubdiffusiveProcess.Paper.prop_conc_mesh_cell_energy
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Geometry.TriadicApproximation

@[expose] public section

/-! Harmonic mesh approximations with bounded energy along further subsequences.
They approximate each smooth compactly supported function on an arbitrary cube.
The construction does not assert bounded energy on the original cutoff sequence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Actual harmonic meshes uniformly approximate smooth data with bounded energy on a further subsequence. -/
theorem prop_conc_mesh_native_subsequence
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ phi : SpatialCoordinates d → ℝ,
        ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ eps : ℝ, 0 < eps →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ w : ℕ → H10Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ B : ℝ, ∀ n : ℕ,
        energy (cutoffCoefficient M H om (N (seq n)))
          (centeredCube z r hr : Set (SpatialCoordinates d)) (w n).toH1Function ≤ B ∧
        ContinuousOn (w n).toH1Function.toFun
          (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
          |(w n).toH1Function.toFun x - phi x| < eps := by
  classical
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_mesh_cell_energy d hd I Pin X W Cp Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr N
  filter_upwards [hs M Rm Sreg It H hIR hdelta z r hr N] with om hom
  intro phi hphi hcompact hsupp eps heps
  obtain ⟨Cmesh, _, hmesh⟩ := mesh_interpolator (d := d) hd
  let G : ℝ := sSup ((fun y => ‖fderiv ℝ phi y‖) ''
    closure (centeredCube z r hr : Set (SpatialCoordinates d)))
  obtain ⟨J, hside, herror⟩ := exists_triadic_side_error_lt r (Cmesh * G) eps heps
  obtain ⟨seq, hmono, hbound⟩ := hom J hside
  obtain ⟨B, hB⟩ := hbound phi hphi hcompact
  let beta : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z r hr).isOpen (hphi.of_le (by norm_num)) hcompact
  have hex : ∀ n : ℕ, ∃ w : H10Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      energy (cutoffCoefficient M H om (N (seq n)))
        (centeredCube z r hr : Set (SpatialCoordinates d)) w.toH1Function ≤ B ∧
      ContinuousOn w.toH1Function.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |w.toH1Function.toFun x - phi x| < eps := by
    intro n
    obtain ⟨lam, Lam, hlam, habound⟩ := cutoffCoefficient_closedCube_bounds
      M H om (N (seq n)) z hr
    obtain ⟨w, hwcont, _, hwsum, hwerr⟩ := hmesh z r hr J
      (cutoffCoefficient M H om (N (seq n))) lam Lam hlam
      (cutoffCoefficient_continuous M H om (N (seq n)))
      (fun x hx => habound x (centeredCube_subset_closedCube z hr hx)) beta hphi hcompact hsupp
    refine ⟨w, hwsum.trans_le (hB n), hwcont, ?_⟩
    intro x hx
    refine (hwerr x hx).trans_lt ?_
    change Cmesh * (r / (3 : ℝ) ^ J) * G < eps
    nlinarith only [herror]
  choose w hw using hex
  exact ⟨seq, hmono, w, B, hw⟩

end
end SubdiffusiveProcess.Paper
