module

public import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ForcedReplacement
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector
public import Homogenization.Book.Ch03.Theorems.EnergyRHS.Theory

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem integral_vecDot_sub_left_split {U : Set (Vec d)}
    {F G H : Vec d → Vec d} (hF : MemVectorL2 U F) (hG : MemVectorL2 U G)
    (hH : ∀ x, H x = F x - G x) (φ : H10Function U) :
    ∫ x in U, vecDot (H x) (φ.toH1Function.grad x) ∂volume =
      (∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume) -
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂volume := by
  have hFint : IntegrableOn
      (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hGint : IntegrableOn
      (fun x => vecDot (G x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2
  have hfun : (fun x => vecDot (H x) (φ.toH1Function.grad x)) =
      fun x => vecDot (F x) (φ.toH1Function.grad x) -
        vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [hH x, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  rw [hfun, integral_sub hFint hGint]

/-- The tested flux is unchanged when the public coefficient field is replaced
by its everywhere-elliptic representative. -/
theorem integral_flux_eq_publicCoeffField (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (φ : H10Function (Ch02.cubeDomain Q : Set (Vec d))) :
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (φ.toH1Function.grad x) ∂volume =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul (publicCoeffField Q a x) (u.grad x))
          (φ.toH1Function.grad x) ∂volume := by
  refine integral_congr_ae ?_
  filter_upwards [publicCoeffField_ae_eq Q a] with x hx
  rw [hx]

/-- The force of the zero-trace corrector solved by `v - h`. -/
def roughDirichletCorrectorForce (Q : TriadicCube d) (a : CoeffFamily d)
    (h : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Vec d → Vec d :=
  fun x => g x - matVecMul (publicCoeffField Q a x) (h.grad x)

theorem memVectorL2_roughDirichletCorrectorForce (Q : TriadicCube d)
    (a : CoeffFamily d) (h : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    MemVectorL2 (openCubeSet Q) (roughDirichletCorrectorForce Q a h g) :=
  hg.sub (memVectorL2_matVecMul_of_isEllipticFieldOn
    (publicCoeffField_isEllipticFieldOn_openCubeSet Q a) h.grad_memVectorL2)

variable [NeZero d]

/-- Existence of the zero-trace corrector at the rough coefficient field. -/
theorem exists_zeroTraceDirichletCorrector_rough (Q : TriadicCube d)
    (a : CoeffFamily d) (h : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    ∃ rho : H10Function (openCubeSet Q),
      IsZeroTraceDirichletRhsWeakSolution (publicCoeffField Q a) (openCubeSet Q)
        rho (roughDirichletCorrectorForce Q a h g) :=
  exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
    (a := publicCoeffField Q a) (U := openCubeSet Q)
    (g := roughDirichletCorrectorForce Q a h g)
    (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
    (memVectorL2_roughDirichletCorrectorForce Q a h hg)
    (hasPotentialZeroTraceClosureRealization_openCubeSet Q)
    (Ch02.openCubeSet_nonempty Q)
    (publicCoeffField_isEllipticFieldOn_openCubeSet Q a)

/-- A forced solution at the rough field whose boundary datum is exactly `h`.
The returned zero-trace witness carries pointwise value and gradient identities,
which are stronger than the a.e. field stored in
`DirichletForcedCubeSolution`. -/
theorem exists_dirichletForcedCubeSolution_boundaryData_withGradient
    (Q : TriadicCube d)
    (a : CoeffFamily d) (h : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    ∃ v : DirichletForcedCubeSolution Q a g, v.boundaryData = h ∧
      ∃ rho : H10Function (openCubeSet Q),
        (∀ y, rho.toH1Function.toFun y = v.toH1.toFun y - h.toFun y) ∧
          ∀ y, rho.toH1Function.grad y = v.toH1.grad y - h.grad y := by
  obtain ⟨rho, hrho⟩ := exists_zeroTraceDirichletCorrector_rough Q a h hg
  have hflux : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul (publicCoeffField Q a x) (h.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_openCubeSet Q a) h.grad_memVectorL2
  have hrhoflux : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul (publicCoeffField Q a x) (rho.toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_openCubeSet Q a)
      rho.toH1Function.grad_memVectorL2
  have hweak : IsForcedEquation Q a (h + rho.toH1Function) g := by
    intro φ
    have hsplit := Section6SchauderDatum.integral_vecDot_add_left_split
      (U := openCubeSet Q) hflux hrhoflux
      (H := fun x => matVecMul (publicCoeffField Q a x)
        ((h + rho.toH1Function).grad x))
      (fun x => by
        show matVecMul (publicCoeffField Q a x) ((h + rho.toH1Function).grad x) = _
        rw [H1Function.add_grad, matVecMul_add]) φ
    have hforce := integral_vecDot_sub_left_split
      (U := openCubeSet Q) hg hflux
      (H := roughDirichletCorrectorForce Q a h g) (fun x => rfl) φ
    rw [integral_flux_eq_publicCoeffField Q a (h + rho.toH1Function) φ]
    simp only [Ch02.cubeDomain_coe]
    rw [hsplit, hrho φ, hforce]
    ring
  have hexact : ∀ x, rho.toH1Function.toFun x =
      (h + rho.toH1Function).toFun x - h.toFun x := by
    intro x
    rw [H1Function.add_toFun]
    ring
  have hexactGrad : ∀ x, rho.toH1Function.grad x =
      (h + rho.toH1Function).grad x - h.grad x := by
    intro x
    rw [H1Function.add_grad]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  exact ⟨⟨h + rho.toH1Function, h, hweak,
    ⟨rho, Filter.Eventually.of_forall hexact⟩⟩, rfl, rho, hexact, hexactGrad⟩

/-- Value-only compatibility wrapper for the original rough Dirichlet lift
interface. -/
theorem exists_dirichletForcedCubeSolution_boundaryData (Q : TriadicCube d)
    (a : CoeffFamily d) (h : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    ∃ v : DirichletForcedCubeSolution Q a g, v.boundaryData = h ∧
      ∃ rho : H10Function (openCubeSet Q),
        ∀ y, rho.toH1Function.toFun y = v.toH1.toFun y - h.toFun y := by
  obtain ⟨v, hv, rho, hvalue, _hgrad⟩ :=
    exists_dirichletForcedCubeSolution_boundaryData_withGradient Q a h hg
  exact ⟨v, hv, rho, hvalue⟩

omit [NeZero d] in
/-- Exact zero-trace witnesses for two solutions with the same datum give an
`H¹₀` witness for their difference. -/
theorem memH10_sub_of_exact_zeroTrace {Q : TriadicCube d}
    {u v h : H1Function (openCubeSet Q)}
    {rhou rhov : H10Function (openCubeSet Q)}
    (hu : ∀ y, rhou.toH1Function.toFun y = u.toFun y - h.toFun y)
    (hv : ∀ y, rhov.toH1Function.toFun y = v.toFun y - h.toFun y) :
    MemH10 (openCubeSet Q) (fun y => u.toFun y - v.toFun y) := by
  have hsub := memH10_sub (U := openCubeSet Q)
    (u := fun y => u.toFun y - h.toFun y)
    (v := fun y => v.toFun y - h.toFun y)
    ⟨rhou, funext hu⟩ ⟨rhov, funext hv⟩
  have hfun : (fun y => (u.toFun y - h.toFun y) - (v.toFun y - h.toFun y)) =
      fun y => u.toFun y - v.toFun y := by
    funext y
    ring
  rwa [hfun] at hsub

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
