module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepVariationalPatching
public import Homogenization.PDE.EnergyIdentities
public import Homogenization.CoarseGraining.MagicIdentities.Basics

@[expose] public section

/-!
# Cell energy identities for the one-step patch

This module formalizes the deterministic algebra in Step 2 of the one-step
upper proof.  It provides the three-term
quadratic expansion of a patched field and, from the weak equation for the
oscillatory cell corrector, the exact identity

```text
int (F + grad phi) . a (F + grad phi)
  = int F . a (F + grad phi).
```

The latter is the manuscript's minimizing identity.  It is
stated for a general symmetric uniformly elliptic coefficient field, so the
GMC scalar cutoff is an immediate specialization.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Pointwise three-term expansion of a symmetric quadratic energy. -/
theorem oneStep_half_cellEnergy_add {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) (S T : Vec d) :
    (1 / 2 : ℝ) * vecDot (S + T) (matVecMul A (S + T)) =
      (1 / 2 : ℝ) * vecDot S (matVecMul A S) +
        vecDot S (matVecMul A T) +
        (1 / 2 : ℝ) * vecDot T (matVecMul A T) :=
  magic_half_vecDot_add_of_isSymm hA S T

/-- Adding the zero-trace corrector to its forcing produces a weakly
coefficient-solenoidal cell field.  This simultaneously covers the principal
field `p_z + grad chi_z` and the oscillatory field `F_z + grad phi_z`. -/
theorem oneStep_correctedField_weakDivergenceFree {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    {F : Vec d → Vec d} {phi : H10Function U}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hF : MemVectorL2 U F)
    (hphi : IsZeroTraceDirichletRhsWeakSolution a U phi
      (fun x => -matVecMul (a x) (F x))) :
    ∀ psi : H10Function U,
      ∫ x in U,
          vecDot (matVecMul (a x) (F x + phi.toH1Function.grad x))
            (psi.toH1Function.grad x) ∂volume = 0 := by
  intro psi
  let G : Vec d → Vec d := fun x => phi.toH1Function.grad x
  let D : Vec d → Vec d := fun x => psi.toH1Function.grad x
  have hG : MemVectorL2 U G := phi.toH1Function.grad_memVectorL2
  have hD : MemVectorL2 U D := psi.toH1Function.grad_memVectorL2
  have haF : MemVectorL2 U (fun x => matVecMul (a x) (F x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hF
  have haG : MemVectorL2 U (fun x => matVecMul (a x) (G x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hG
  have hAFD : IntegrableOn (fun x => vecDot (matVecMul (a x) (F x)) (D x)) U :=
    integrableOn_vecDot_of_memVectorL2 haF hD
  have hAGD : IntegrableOn (fun x => vecDot (matVecMul (a x) (G x)) (D x)) U :=
    integrableOn_vecDot_of_memVectorL2 haG hD
  have hweak := hphi psi
  have hcancel :
      ∫ x in U, vecDot (matVecMul (a x) (G x)) (D x) ∂volume =
        -∫ x in U, vecDot (matVecMul (a x) (F x)) (D x) ∂volume := by
    calc
      ∫ x in U, vecDot (matVecMul (a x) (G x)) (D x) ∂volume =
          ∫ x in U, vecDot (-matVecMul (a x) (F x)) (D x) ∂volume := by
        simpa only [G, D] using hweak
      _ = -∫ x in U, vecDot (matVecMul (a x) (F x)) (D x) ∂volume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        simp only [vecDot_neg_left]
  have hsplit : (fun x =>
      vecDot (matVecMul (a x) (F x + G x)) (D x)) =
      fun x => vecDot (matVecMul (a x) (F x)) (D x) +
        vecDot (matVecMul (a x) (G x)) (D x) := by
    funext x
    simp only [matVecMul_add, vecDot_add_left]
  change (∫ x in U,
    vecDot (matVecMul (a x) (F x + G x)) (D x) ∂volume) = 0
  rw [hsplit, integral_add hAFD hAGD, hcancel]
  ring

/-- The weak equation makes the corrected oscillatory field coefficient-
orthogonal to every zero-trace gradient. -/
theorem oneStep_correctedField_orthogonal_grad {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    {F : Vec d → Vec d} {phi : H10Function U}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hF : MemVectorL2 U F)
    (hphi : IsZeroTraceDirichletRhsWeakSolution a U phi
      (fun x => -matVecMul (a x) (F x))) :
    ∫ x in U,
        vecDot
          (matVecMul (a x) (F x + phi.toH1Function.grad x))
          (phi.toH1Function.grad x) ∂volume = 0 := by
  let G : Vec d → Vec d := fun x => phi.toH1Function.grad x
  have hG : MemVectorL2 U G := phi.toH1Function.grad_memVectorL2
  have haF : MemVectorL2 U (fun x => matVecMul (a x) (F x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hF
  have haG : MemVectorL2 U (fun x => matVecMul (a x) (G x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hG
  have hAFG : IntegrableOn (fun x => vecDot (matVecMul (a x) (F x)) (G x)) U :=
    integrableOn_vecDot_of_memVectorL2 haF hG
  have hAGG : IntegrableOn (fun x => vecDot (matVecMul (a x) (G x)) (G x)) U :=
    integrableOn_vecDot_of_memVectorL2 haG hG
  have hweak := hphi phi
  have hneg :
      ∫ x in U, vecDot (-matVecMul (a x) (F x)) (G x) ∂volume =
        -∫ x in U, vecDot (matVecMul (a x) (F x)) (G x) ∂volume := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    simp only [vecDot_neg_left]
  have hcancel :
      ∫ x in U, vecDot (matVecMul (a x) (G x)) (G x) ∂volume =
        -∫ x in U, vecDot (matVecMul (a x) (F x)) (G x) ∂volume := by
    exact hweak.trans hneg
  have hsplit : (fun x =>
      vecDot (matVecMul (a x) (F x + G x)) (G x)) =
      fun x => vecDot (matVecMul (a x) (F x)) (G x) +
        vecDot (matVecMul (a x) (G x)) (G x) := by
    funext x
    simp only [matVecMul_add, vecDot_add_left]
  change (∫ x in U, vecDot (matVecMul (a x) (F x + G x)) (G x) ∂volume) = 0
  rw [hsplit, integral_add hAFG hAGG, hcancel]
  ring

/-- The exact oscillatory-cell minimizing identity. -/
theorem oneStep_oscillatoryCell_energy_identity {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    {F : Vec d → Vec d} {phi : H10Function U}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hF : MemVectorL2 U F)
    (hphi : IsZeroTraceDirichletRhsWeakSolution a U phi
      (fun x => -matVecMul (a x) (F x))) :
    ∫ x in U,
        vecDot (F x + phi.toH1Function.grad x)
          (matVecMul (a x) (F x + phi.toH1Function.grad x)) ∂volume =
      ∫ x in U,
        vecDot (F x)
          (matVecMul (a x) (F x + phi.toH1Function.grad x)) ∂volume := by
  let G : Vec d → Vec d := fun x => phi.toH1Function.grad x
  let T : Vec d → Vec d := fun x => F x + G x
  have hG : MemVectorL2 U G := phi.toH1Function.grad_memVectorL2
  have hT : MemVectorL2 U T := hF.add hG
  have haT : MemVectorL2 U (fun x => matVecMul (a x) (T x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hT
  have hFT : IntegrableOn (fun x => vecDot (F x) (matVecMul (a x) (T x))) U :=
    integrableOn_vecDot_of_memVectorL2 hF haT
  have hGT : IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (T x))) U :=
    integrableOn_vecDot_of_memVectorL2 hG haT
  have horth := oneStep_correctedField_orthogonal_grad hEll hF hphi
  have horth' : ∫ x in U,
      vecDot (G x) (matVecMul (a x) (T x)) ∂volume = 0 := by
    calc
      ∫ x in U, vecDot (G x) (matVecMul (a x) (T x)) ∂volume =
          ∫ x in U, vecDot (matVecMul (a x) (T x)) (G x) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        exact vecDot_comm _ _
      _ = 0 := by simpa only [T, G] using horth
  have hsplit : (fun x => vecDot (T x) (matVecMul (a x) (T x))) =
      fun x => vecDot (F x) (matVecMul (a x) (T x)) +
        vecDot (G x) (matVecMul (a x) (T x)) := by
    funext x
    simp only [T, vecDot_add_left]
  change (∫ x in U, vecDot (T x) (matVecMul (a x) (T x)) ∂volume) = _
  rw [hsplit, integral_add hFT hGT, horth', add_zero]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
