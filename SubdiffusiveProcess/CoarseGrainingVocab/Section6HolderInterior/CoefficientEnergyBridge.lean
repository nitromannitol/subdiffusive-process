module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ScalarEnergyIdentity
public import SubdiffusiveProcess.Providers.Section2.CoarseGrainedPoincare

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}



theorem sqrt_integral_scalarEnergy_eq_vectorNormalizedL2On
    (Q : TriadicCube d) (a : Vec d → ℝ) (ha : ∀ x, 0 ≤ a x)
    (v : Vec d → Vec d) :
    Real.sqrt (∫ x, vecDot (v x) (matVecMul (scalarCoeffField a x) (v x))
        ∂ normalizedCubeMeasure Q) =
      vectorNormalizedL2On (openCubeSet Q) (fun x ↦ Real.sqrt (a x) • v x) := by
  have hpt : (fun x ↦ vecDot (v x) (matVecMul (scalarCoeffField a x) (v x))) =
      fun x ↦ Homogenization.euclideanNorm (Real.sqrt (a x) • v x) ^ 2 := by
    funext x
    exact vecDot_matVecMul_scalarCoeffField_eq_sq a ha v x
  rw [hpt]
  unfold vectorNormalizedL2On normalizedL2On
  rw [volumeAverage_openCubeSet_eq_cubeAverage,
    cubeAverage_eq_integral_normalizedCubeMeasure]

/-- The zero vector field is solenoidal on any window. -/
theorem isSolenoidalOn_zero (W : Set (Vec d)) :
    IsSolenoidalOn W (fun _ ↦ (0 : Vec d)) := by
  intro φ
  have : (fun x ↦ vecDot (0 : Vec d) (φ.toH1Function.grad x)) = fun _ ↦ (0 : ℝ) := by
    funext x
    simp [vecDot]
  simp [this]

/-- The zero vector field is `L²` on any window. -/
theorem memVectorL2_zero (W : Set (Vec d)) :
    MemVectorL2 W (fun _ ↦ (0 : Vec d)) := by
  simp

/-- **The coarse-grained Poincaré estimate in row 2's vocabulary.**

For an arbitrary `H¹` function on an arbitrary triadic cube, the scale
normalized negative Besov norm of the gradient is bounded by the weighted
gradient energy of the cutoff coefficient, at the discount and lower-ellipticity
factors.  No PDE hypothesis on `u` is used: the solenoidal slot of
`coarsePoincareRaw` is filled with the zero field. -/
theorem scaleNormalizedNegativeBesov_grad_le_weightedEnergy [NeZero d]
    (Q : TriadicCube d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (s : ℝ) (hs : 0 < s) (q : Ch02.MultiscaleExponent) (hq : q.IsAdmissible)
    (u : H1Function (openCubeSet Q)) :
    Ch03.scaleNormalizedNegativeBesovVectorNorm Q s q u.grad ≤
      Ch03.poincareDiscountFactor s q *
        Ch03.poincareLowerEllipticityFactor Q (aCutoffFamily M L omega) s q *
          vectorNormalizedL2On (openCubeSet Q)
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) := by
  have hsym : ∀ R : TriadicCube d,
      Ch02.CoeffOn.IsSymmetric ((aCutoffFamily M L omega).coeffOn R) := by
    intro R
    filter_upwards with x
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp only [aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField, Matrix.smul_apply]
    by_cases hij : i = j
    · subst j
      rfl
    · simp [hij, Ne.symm hij]
  have hraw := (SubdiffusiveProcess.Providers.Section2.coarsePoincareRaw Q
    (aCutoffFamily M L omega) hsym s hs q hq u (fun _ ↦ (0 : Vec d))
    (memVectorL2_zero _) (isSolenoidalOn_zero _)).1
  have hrep : ((aCutoffFamily M L omega).coeffOn Q).toCoeffField =
      scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) := rfl
  rw [hrep] at hraw
  rwa [sqrt_integral_scalarEnergy_eq_vectorNormalizedL2On Q _
    (fun x ↦ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le) u.grad] at hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
