module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.RoughDirichletDatum
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.EnergySplit
public import Homogenization.PDE.EnergyIdentities

@[expose] public section

/-!
# Dirichlet minimality for symmetric rough coefficients

The boundary split in the manuscript uses the Dirichlet principle separately
for its affine and fractional datum pieces.  This module records the exact
rough-coefficient version.  The symmetry hypothesis is explicit; it is
automatic for the scalar cutoff families used by SubdiffusiveProcess.

Argument: this is the coefficient-weighted analogue of
`Section6BoundaryL2.integral_vecDot_grad_self_le_of_isUnitWeaklyHarmonicOn`.
The proof uses the same zero-trace witness, with weighted Cauchy--Schwarz in
place of the Euclidean square expansion.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem vecDot_sub_right_local (a b c : Vec d) :
    vecDot a (b - c) = vecDot a b - vecDot a c := by
  classical
  show (∑ i : Fin d, a i * (b i - c i)) =
    (∑ i : Fin d, a i * b i) - ∑ i : Fin d, a i * c i
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem integrableOn_publicFlux_pairing
    (Q : TriadicCube d) (a : CoeffFamily d)
    (u v : H1Function (openCubeSet Q)) :
    IntegrableOn
      (fun x => vecDot
        (matVecMul (publicCoeffField Q a x) (u.grad x)) (v.grad x))
      (openCubeSet Q) :=
  integrableOn_vecDot_of_memVectorL2
    (memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_openCubeSet Q a) u.grad_memVectorL2)
    v.grad_memVectorL2

/-- A zero-force solution with symmetric coefficient minimizes coefficient
energy among functions with the same boundary datum.  The pointwise gradient
identity is the one returned by
`exists_dirichletForcedCubeSolution_boundaryData_withGradient`. -/
theorem localizedCoeffEnergyValue_le_boundaryData_of_zeroForce
    [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d)
    (h : H1Function (openCubeSet Q))
    (v : DirichletForcedCubeSolution Q a (fun _ => 0))
    (rho : H10Function (openCubeSet Q))
    (hgrad : ∀ x, rho.toH1Function.grad x = v.toH1.grad x - h.grad x)
    (hsymm : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      Matrix.IsSymm (publicCoeffField Q a x)) :
    localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v.toH1 ≤
      localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) h := by
  let A : CoeffField d := publicCoeffField Q a
  let Ev : Vec d → ℝ := coefficientEnergyDensity A v.toH1.grad
  let Eh : Vec d → ℝ := coefficientEnergyDensity A h.grad
  let Cross : Vec d → ℝ :=
    fun x => vecDot (matVecMul (A x) (v.toH1.grad x)) (h.grad x)
  have hEv : IntegrableOn Ev (openCubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_openCubeSet Q a)
      v.toH1.grad_memVectorL2
  have hEh : IntegrableOn Eh (openCubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_openCubeSet Q a) h.grad_memVectorL2
  have hCross : IntegrableOn Cross (openCubeSet Q) :=
    integrableOn_publicFlux_pairing Q a v.toH1 h
  have hweakNative := v.weakSolution rho
  have hweak :
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (A x) (v.toH1.grad x))
            (rho.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot ((fun _ : Vec d => (0 : Vec d)) x)
            (rho.toH1Function.grad x) ∂volume := by
    calc
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (A x) (v.toH1.grad x))
            (rho.toH1Function.grad x) ∂volume =
          ∫ x in openCubeSet Q,
            vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
              (v.toH1.grad x)) (rho.toH1Function.grad x) ∂volume := by
        simpa only [A, Ch02.cubeDomain_coe] using!
          (integral_flux_eq_publicCoeffField Q a v.toH1 rho).symm
      _ = ∫ x in openCubeSet Q,
          vecDot ((fun _ : Vec d => (0 : Vec d)) x)
            (rho.toH1Function.grad x) ∂volume := by
        simpa only [Ch02.cubeDomain_coe] using hweakNative
  have hzero :
      ∫ x in openCubeSet Q,
          vecDot ((fun _ : Vec d => (0 : Vec d)) x)
            (rho.toH1Function.grad x) ∂volume = 0 := by
    simp [vecDot]
  rw [hzero] at hweak
  have hsplit :
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (A x) (v.toH1.grad x))
            (rho.toH1Function.grad x) ∂volume =
        (∫ x in openCubeSet Q, Ev x ∂volume) -
          ∫ x in openCubeSet Q, Cross x ∂volume := by
    have hfun :
        (fun x => vecDot (matVecMul (A x) (v.toH1.grad x))
          (rho.toH1Function.grad x)) =
        fun x => Ev x - Cross x := by
      funext x
      rw [hgrad x]
      simp only [Ev, Cross, coefficientEnergyDensity_eq_unsymmetrized]
      rw [vecDot_sub_right_local]
      congr 1
      exact vecDot_comm _ _
    rw [hfun, integral_sub hEv hCross]
  have henergyEq :
      ∫ x in openCubeSet Q, Ev x ∂volume =
        ∫ x in openCubeSet Q, Cross x ∂volume := by
    linarith only [hweak, hsplit]
  have hpoint : Cross ≤ᵐ[volume.restrict (openCubeSet Q)]
      fun x => Ev x / 2 + Eh x / 2 := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q), hsymm] with x hx hsymmetric
    have hA := (publicCoeffField_isEllipticFieldOn_openCubeSet Q a).2 x hx
    have habs :=
      abs_vecDot_matVecMul_symmPart_le_half_add_half_of_isEllipticMatrix
        hA (v.toH1.grad x) (h.grad x)
    have hcrossSymm :
        Cross x = vecDot (v.toH1.grad x)
          (matVecMul (symmPart (A x)) (h.grad x)) := by
      have hs : symmPart (A x) = A x := by
        ext i j
        have hij : (A x) j i = (A x) i j :=
          (Matrix.IsSymm.ext_iff.mp hsymmetric) i j
        simp only [symmPart]
        rw [hij]
        ring
      rw [hs]
      calc
        Cross x = vecDot (h.grad x) (matVecMul (A x) (v.toH1.grad x)) := by
          exact vecDot_comm _ _
        _ = vecDot (v.toH1.grad x) (matVecMul (A x) (h.grad x)) :=
          (vecDot_matVecMul_comm_of_isSymm hsymmetric
            (v.toH1.grad x) (h.grad x)).symm
    rw [hcrossSymm]
    exact (le_abs_self _).trans habs
  have hhalf : IntegrableOn (fun x => Ev x / 2 + Eh x / 2)
      (openCubeSet Q) := (hEv.div_const 2).add (hEh.div_const 2)
  have hmono := integral_mono_ae hCross hhalf hpoint
  have hsplitHalf :
      ∫ x in openCubeSet Q, (Ev x / 2 + Eh x / 2) ∂volume =
        (∫ x in openCubeSet Q, Ev x ∂volume) / 2 +
          (∫ x in openCubeSet Q, Eh x ∂volume) / 2 := by
    rw [integral_add (hEv.div_const 2) (hEh.div_const 2),
      integral_div, integral_div]
  rw [hsplitHalf, ← henergyEq] at hmono
  have hint : ∫ x in openCubeSet Q, Ev x ∂volume ≤
      ∫ x in openCubeSet Q, Eh x ∂volume := by
    linarith only [hmono]
  rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) v.toH1,
    localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) h]
  unfold volumeAverage
  have hvol : 0 ≤ (volume (openCubeSet Q)).toReal⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  exact mul_le_mul_of_nonneg_left hint hvol

/-- Existence form of the rough Dirichlet principle.  Symmetry may be checked
on the public `CoeffOn` representative; it is transported to the everywhere
elliptic representative internally. -/
theorem exists_zeroForceDirichletLift_energy_le
    [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (h : H1Function (openCubeSet Q))
    (hsymm : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      Matrix.IsSymm ((a.coeffOn Q).toCoeffField x)) :
    ∃ v : DirichletForcedCubeSolution Q a (fun _ => 0),
      v.boundaryData = h ∧
        localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v.toH1 ≤
          localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) h := by
  have hzero : MemVectorL2 (openCubeSet Q) (fun _ : Vec d => (0 : Vec d)) :=
    MemLp.zero
  obtain ⟨v, hv, rho, _hvalue, hgrad⟩ :=
    exists_dirichletForcedCubeSolution_boundaryData_withGradient Q a h hzero
  have hpublicSymm : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      Matrix.IsSymm (publicCoeffField Q a x) := by
    filter_upwards [publicCoeffField_ae_eq_openCubeSet Q a, hsymm] with x hfield hx
    rw [hfield]
    exact hx
  exact ⟨v, hv,
    localizedCoeffEnergyValue_le_boundaryData_of_zeroForce
      Q a h v rho hgrad hpublicSymm⟩

/-- Scalar cutoff families satisfy the symmetry premise of the rough
Dirichlet principle pointwise (hence also almost everywhere). -/
theorem aCutoffFamily_coeffOn_isSymm
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (x : Vec d) :
    Matrix.IsSymm (((aCutoffFamily M L omega).coeffOn Q).toCoeffField x) := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField, Matrix.smul_apply]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [hij, Ne.symm hij]

/-- The zero-force rough extension of arbitrary boundary data at the GMC
cutoff coefficient has no more energy than the datum itself. -/
theorem exists_aCutoffZeroForceDirichletLift_energy_le
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (h : H1Function (openCubeSet Q)) :
    ∃ v : DirichletForcedCubeSolution Q (aCutoffFamily M L omega) (fun _ => 0),
      v.boundaryData = h ∧
        localizedCoeffEnergyValue (openCubeSet Q)
            ((aCutoffFamily M L omega).coeffOn Q) v.toH1 ≤
          localizedCoeffEnergyValue (openCubeSet Q)
            ((aCutoffFamily M L omega).coeffOn Q) h := by
  apply exists_zeroForceDirichletLift_energy_le Q (aCutoffFamily M L omega) h
  filter_upwards with x
  exact aCutoffFamily_coeffOn_isSymm M L omega Q x

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
