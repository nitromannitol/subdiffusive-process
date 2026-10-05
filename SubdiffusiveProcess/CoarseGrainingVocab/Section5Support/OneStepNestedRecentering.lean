module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannDirichletReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceParentMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepAxisCubeHarmonicExistence

@[expose] public section

/-!
# Nested recentring of the one-step correctors

This module supplies the weak-equation transport used at every level of the
concentric-cube argument.
The large-cube solution is restricted to an interior triadic cube and the
canonical translated solution with the same shell datum is subtracted.  The
remainder is harmonic on that cube.

Arbitrary-gap harmonic estimates are available, so this module exposes the single recentering operation;
downstream code may compose it along any nested cube family.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private theorem vecDot_sub_left_oneStep {d : ℕ} (a b c : Vec d) :
    vecDot (a - b) c = vecDot a c - vecDot b c := by
  unfold vecDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Pi.sub_apply]
  ring

/-- Change only the propositionally equal domain carried by a zero-trace
Sobolev function. -/
def castH10Domain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) : H10Function V :=
  hUV ▸ u

/-- Change only the propositionally equal domain carried by a mean-zero
Sobolev function. -/
def castMeanZeroDomain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) : H1MeanZeroFunction V :=
  hUV ▸ u

def castH1Domain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) : H1Function V :=
  hUV ▸ u

@[simp] theorem norm_gradToHilbertVectorL2_castH10Domain
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V) (u : H10Function U) :
    ‖(castH10Domain hUV u).toH1Function.gradToHilbertVectorL2‖ =
      ‖u.toH1Function.gradToHilbertVectorL2‖ := by
  subst V
  rfl

@[simp] theorem norm_gradToHilbertVectorL2_castMeanZeroDomain
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H1MeanZeroFunction U) :
    ‖(castMeanZeroDomain hUV u).gradToHilbertVectorL2‖ =
      ‖u.gradToHilbertVectorL2‖ := by
  subst V
  rfl

@[simp] private theorem castH1Domain_sub {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u v : H1Function U) :
    castH1Domain hUV (u - v) = castH1Domain hUV u - castH1Domain hUV v := by
  subst V
  rfl

@[simp] private theorem norm_gradToHilbertVectorL2_castH1Domain
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V) (u : H1Function U) :
    ‖(castH1Domain hUV u).gradToHilbertVectorL2‖ =
      ‖u.gradToHilbertVectorL2‖ := by
  subst V
  rfl

private theorem grad_castH1Domain
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V) (u : H1Function U) :
    (castH1Domain hUV u).grad = u.grad := by
  subst V
  rfl

private theorem WeakPoissonEquationOn.castDomain_oneStep
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    {u : H1Function U} {f : Vec d → ℝ}
    (hu : WeakPoissonEquationOn U u f) :
    WeakPoissonEquationOn V (castH1Domain hUV u) f := by
  subst V
  exact hu

private theorem IsZeroTraceDirichletRhsWeakSolution.castDomain
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    {u : H10Function U} {g : Vec d → Vec d}
    (hu : IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d) U u g) :
    IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d) V
      (castH10Domain hUV u) g := by
  subst V
  exact hu

private theorem IsMeanZeroNeumannRhsWeakSolution.castDomain
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    {u : H1MeanZeroFunction U} {g : Vec d → Vec d}
    (hu : IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d) U u g) :
    IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d) V
      (castMeanZeroDomain hUV u) g := by
  subst V
  exact hu

/-- Square integrability passes from a domain to a measurable restriction.
This is the local copy of the first transport atom in Superdiffusion's
`OscillationNestedTransport`. -/
private theorem memVectorL2_mono_set {d : ℕ} {U V : Set (Vec d)}
    (hVU : V ⊆ U) {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 V f :=
  hf.mono_measure (Measure.restrict_mono hVU le_rfl)

/-- Move a vector-divergence weak equation to an open subdomain.  The proof is
the potential/solenoidal restriction supplied by CoarseGraining. -/
theorem weakVectorEquation_restrict {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [IsFiniteMeasure (volumeMeasureOn V)] {A G : Vec d → Vec d}
    (hA : MemVectorL2 U A) (hG : MemVectorL2 U G)
    (hw : ∀ psi : H10Function U,
      ∫ x in U, vecDot (A x) (psi.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (G x) (psi.toH1Function.grad x) ∂volume) :
    ∀ psi : H10Function V,
      ∫ x in V, vecDot (A x) (psi.toH1Function.grad x) ∂volume =
        ∫ x in V, vecDot (G x) (psi.toH1Function.grad x) ∂volume := by
  have hAV : MemVectorL2 V A := memVectorL2_mono_set hVU hA
  have hGV : MemVectorL2 V G := memVectorL2_mono_set hVU hG
  have hDV : MemVectorL2 V (fun x ↦ A x - G x) := hAV.sub hGV
  have hsolU : IsSolenoidalOn U (fun x ↦ A x - G x) := by
    intro phi
    have hOne : IntegrableOn
        (fun x ↦ vecDot (A x) (phi.toH1Function.grad x)) U volume :=
      integrableOn_vecDot_of_memVectorL2 hA phi.toH1Function.grad_memVectorL2
    have hTwo : IntegrableOn
        (fun x ↦ vecDot (G x) (phi.toH1Function.grad x)) U volume :=
      integrableOn_vecDot_of_memVectorL2 hG phi.toH1Function.grad_memVectorL2
    simp_rw [vecDot_sub_left_oneStep]
    rw [integral_sub hOne hTwo, hw phi, sub_self]
  have hsolV : IsSolenoidalOn V (fun x ↦ A x - G x) :=
    hsolU.restrict_of_isOpen_of_memVectorL2 hU hV hVU hDV
  intro psi
  have hOne : IntegrableOn
      (fun x ↦ vecDot (A x) (psi.toH1Function.grad x)) V volume :=
    integrableOn_vecDot_of_memVectorL2 hAV psi.toH1Function.grad_memVectorL2
  have hTwo : IntegrableOn
      (fun x ↦ vecDot (G x) (psi.toH1Function.grad x)) V volume :=
    integrableOn_vecDot_of_memVectorL2 hGV psi.toH1Function.grad_memVectorL2
  have hzero := hsolV psi
  simp_rw [vecDot_sub_left_oneStep] at hzero
  rw [integral_sub hOne hTwo, sub_eq_zero] at hzero
  exact hzero

/-- A homogeneous equation against every zero-trace Sobolev test is a weak
Poisson equation with zero scalar right-hand side. -/
theorem weakPoissonEquationOn_zero_of_h10 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (u : H1Function U)
    (hu : ∀ psi : H10Function U,
      ∫ x in U, vecDot (u.grad x) (psi.toH1Function.grad x) ∂volume = 0) :
    WeakPoissonEquationOn U u (fun _ ↦ 0) := by
  intro phi hphi hphiSupport hphiSub
  let phiZero : H10Function U :=
    H10Function.ofContDiff hU (hphi.of_le (by simp)) hphiSupport hphiSub
  simpa only [phiZero, H10Function.ofContDiff, H1Function.ofContDiff,
    zero_mul, integral_zero] using! hu phiZero

/-- Subtract two `H¹` fields which have the same vector-divergence equation
against zero-trace tests. -/
theorem weakPoissonEquationOn_sub_of_same_h10_equation
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (u v : H1Function U) (G : Vec d → Vec d)
    (hu : ∀ psi : H10Function U,
      ∫ x in U, vecDot (u.grad x) (psi.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (G x) (psi.toH1Function.grad x) ∂volume)
    (hv : ∀ psi : H10Function U,
      ∫ x in U, vecDot (v.grad x) (psi.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (G x) (psi.toH1Function.grad x) ∂volume) :
    WeakPoissonEquationOn U (u - v) (fun _ ↦ 0) := by
  apply weakPoissonEquationOn_zero_of_h10 hU
  intro psi
  have huInt : IntegrableOn
      (fun x ↦ vecDot (u.grad x) (psi.toH1Function.grad x)) U volume :=
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2
      psi.toH1Function.grad_memVectorL2
  have hvInt : IntegrableOn
      (fun x ↦ vecDot (v.grad x) (psi.toH1Function.grad x)) U volume :=
    integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2
      psi.toH1Function.grad_memVectorL2
  rw [show (∫ x in U, vecDot ((u - v).grad x) (psi.toH1Function.grad x) ∂volume) =
      (∫ x in U, vecDot (u.grad x) (psi.toH1Function.grad x) ∂volume) -
        ∫ x in U, vecDot (v.grad x) (psi.toH1Function.grad x) ∂volume by
    rw [← integral_sub huInt hvInt]
    apply integral_congr_ae
    filter_upwards with x
    rw [H1Function.sub_grad, vecDot_sub_left_oneStep]]
  rw [hu psi, hv psi, sub_self]

/-- The canonical translated zero-Dirichlet solution, viewed on the literal
triadic cube rather than on its definitionally equal translated origin cube. -/
def oneStepTriadicDirichletSolution {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    H10Function (openCubeSet Q) :=
  castH10Domain
    (openCubeSet_eq_translateSet_originCube_of_triadicCube Q).symm
    (oneStepTranslatedDirichletSolution M n h p (triadicCubeShift Q)
      Q.scale omega hh)

/-- Neumann counterpart of `oneStepTriadicDirichletSolution`. -/
def oneStepTriadicNeumannSolution {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    H1MeanZeroFunction (openCubeSet Q) :=
  castMeanZeroDomain
    (openCubeSet_eq_translateSet_originCube_of_triadicCube Q).symm
    (oneStepTranslatedNeumannSolution M n h p (triadicCubeShift Q)
      Q.scale omega hh)

/-- The triadic Dirichlet representative solves the literal shell problem on
its cube. -/
theorem oneStepTriadicDirichletSolution_isWeakSolution {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
      (openCubeSet Q) (oneStepTriadicDirichletSolution M n h p Q omega hh)
      (fun x ↦ -oneStepMultiplierAt M n h x omega • p) := by
  exact IsZeroTraceDirichletRhsWeakSolution.castDomain
    (openCubeSet_eq_translateSet_originCube_of_triadicCube Q).symm
    (oneStepTranslatedDirichletSolution_isWeakSolution M n h p
      (triadicCubeShift Q) Q.scale omega hh)

/-- The triadic Neumann representative solves the same literal shell problem. -/
theorem oneStepTriadicNeumannSolution_isWeakSolution {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet Q) (oneStepTriadicNeumannSolution M n h p Q omega hh)
      (fun x ↦ -oneStepMultiplierAt M n h x omega • p) := by
  exact IsMeanZeroNeumannRhsWeakSolution.castDomain
    (openCubeSet_eq_translateSet_originCube_of_triadicCube Q).symm
    (oneStepTranslatedNeumannSolution_isWeakSolution M n h p
      (triadicCubeShift Q) Q.scale omega hh)

/-- The scalar weak divergence of the shell carrier is independent of the
ambient cube used to realize its Sobolev coordinates. -/
theorem oneStepShellForcingH1_divergence_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (Q R : TriadicCube d)
    (hh : 0 < h) :
    (oneStepShellForcingH1 M n h omega p Q hh).divergence =
      (oneStepShellForcingH1 M n h omega p R hh).divergence := by
  funext x
  rfl

/-- Convert the source-facing zero-trace vector equation into the scalar weak
Poisson equation used by the interior harmonic theory. -/
theorem weakPoissonEquationOn_oneStepShellDirichlet {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (u : H10Function (openCubeSet Q))
    (hu : IsZeroTraceDirichletRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u
      (fun x ↦ -(oneStepShellForcingH1 M n h omega p Q hh).toField x)) :
    WeakPoissonEquationOn (openCubeSet Q) u.toH1Function
      (oneStepShellForcingH1 M n h omega p Q hh).divergence := by
  apply weakPoissonEquationOn_of_cubeDirichletDivergenceProblem Q
    (oneStepShellForcingH1 M n h omega p Q hh) u
  intro phi
  have hweak := hu phi
  simpa only [CubeDirichletDivergenceProblem, matVecMul_identityCoeffField,
    integral_neg, vecDot_neg_left] using hweak

/-- The restriction of a large zero-Dirichlet solution to an interior cube,
minus the translated canonical solution on that cube, is harmonic.  This is
the operation composed at each level of the nested-recentring chain. -/
theorem oneStepDirichlet_restrict_sub_local_harmonic {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (K : ℤ) (Q : TriadicCube d)
    (hQK : openCubeSet Q ⊆ openCubeSet (originCube d K)) (hh : 0 < h) :
    WeakPoissonEquationOn (openCubeSet Q)
      ((oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.restrict
          (isOpen_openCubeSet Q) hQK -
        (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function)
      (fun _ ↦ 0) := by
  let Gbig := oneStepShellForcingH1 M n h omega p (originCube d K) hh
  have hbig : WeakPoissonEquationOn (openCubeSet (originCube d K))
      (oneStepOriginDirichletSolution M n h p K omega hh).toH1Function
      Gbig.divergence := by
    apply weakPoissonEquationOn_oneStepShellDirichlet M n h omega p
      (originCube d K) hh
    simpa only [Gbig, oneStepShellForcingW14_toField_apply,
      oneStepShellForcing_paired_toField, neg_smul] using
      oneStepOriginDirichletSolution_isWeakSolution M n h p K omega hh
  have hbigQ := hbig.restrict (isOpen_openCubeSet Q) hQK
  have hlocal : WeakPoissonEquationOn (openCubeSet Q)
      (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
      (oneStepShellForcingH1 M n h omega p Q hh).divergence := by
    apply weakPoissonEquationOn_oneStepShellDirichlet M n h omega p Q hh
    simpa only [oneStepShellForcingW14_toField_apply,
      oneStepShellForcing_paired_toField, neg_smul] using
      oneStepTriadicDirichletSolution_isWeakSolution M n h p Q omega hh
  rw [oneStepShellForcingH1_divergence_eq M n h omega p
    (originCube d K) Q hh] at hbigQ
  exact WeakPoissonEquationOn.sub_same_rhs (isOpen_openCubeSet Q) hbigQ hlocal

/-- Neumann large-cube counterpart.  Interior compactly supported tests make
the natural boundary condition irrelevant; after restriction, subtracting the
translated local Neumann solution again leaves a harmonic function. -/
theorem oneStepNeumann_restrict_sub_local_harmonic {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (K : ℤ) (Q : TriadicCube d)
    (hQK : openCubeSet Q ⊆ openCubeSet (originCube d K)) (hh : 0 < h) :
    WeakPoissonEquationOn (openCubeSet Q)
      ((oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.restrict
          (isOpen_openCubeSet Q) hQK -
        (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function)
      (fun _ ↦ 0) := by
  let Gbig := oneStepShellForcingH1 M n h omega p (originCube d K) hh
  have hbig : WeakPoissonEquationOn (openCubeSet (originCube d K))
      (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function
      Gbig.divergence := by
    apply weakPoissonEquationOn_oneStepShellNeumann M n h omega p
      (originCube d K) hh
    simpa only [Gbig, oneStepShellForcingW14_toField_apply,
      oneStepShellForcing_paired_toField, neg_smul] using
      oneStepOriginNeumannSolution_isWeakSolution M n h p K omega hh
  have hbigQ := hbig.restrict (isOpen_openCubeSet Q) hQK
  have hlocal : WeakPoissonEquationOn (openCubeSet Q)
      (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function
      (oneStepShellForcingH1 M n h omega p Q hh).divergence := by
    apply weakPoissonEquationOn_oneStepShellNeumann M n h omega p Q hh
    simpa only [oneStepShellForcingW14_toField_apply,
      oneStepShellForcing_paired_toField, neg_smul] using
      oneStepTriadicNeumannSolution_isWeakSolution M n h p Q omega hh
  rw [oneStepShellForcingH1_divergence_eq M n h omega p
    (originCube d K) Q hh] at hbigQ
  exact WeakPoissonEquationOn.sub_same_rhs (isOpen_openCubeSet Q) hbigQ hlocal

/-! ## Arbitrary-centered parent cubes -/

/-- Lower corner of the axis-cube realization of the centered cube
`z + Q_m`. -/
def oneStepCenteredAxisCorner {d : ℕ} (z : Vec d) (m : ℤ) : Vec d :=
  fun i ↦ z i - cubeScaleFactor (originCube d m) / 2

/-- Exact conversion from the centered translated-cube convention to the
corner-and-side convention of the arbitrary-axis harmonic API. -/
theorem translateSet_openCubeSet_originCube_eq_axisCube
    {d : ℕ} (z : Vec d) (m : ℤ) :
    translateSet z (openCubeSet (originCube d m)) =
      axisCube (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)) := by
  rw [← Homogenization.Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube,
    ← Homogenization.Book.Ch03.openCubeAtScale_eq_translateSet]
  rw [Homogenization.Book.Ch03.openCubeAtScale_eq_pi_Ioo]
  ext x
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioo, axisCube,
    oneStepCenteredAxisCorner, cubeScaleFactor, originCube]
  have heq : Real.rpow (3 : ℝ) (m : ℝ) = (3 : ℝ) ^ m :=
    Real.rpow_intCast 3 m
  simp only [heq]
  constructor
  · intro hx i
    have hi := hx i
    constructor <;> linarith
  · intro hx i
    have hi := hx i
    constructor <;> linarith

/-- Recenter a large Dirichlet solution on an arbitrary concentric parent
cube `z + Q_m`.  This is the literal geometry used for the source cells: no
alignment of the parent with the scale-`m` triadic grid is required. -/
theorem oneStepDirichlet_restrict_sub_translated_harmonic
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    WeakPoissonEquationOn
      (translateSet z (openCubeSet (originCube d m)))
      ((oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.restrict
          (by
            rw [← Homogenization.Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube,
              ← Homogenization.Book.Ch03.openCubeAtScale_eq_translateSet]
            exact Homogenization.Book.Ch03.isOpen_openCubeAtScale z m)
          hsub -
        (oneStepTranslatedDirichletSolution M n h p z m omega hh).toH1Function)
      (fun _ ↦ 0) := by
  let U := openCubeSet (originCube d K)
  let V := translateSet z (openCubeSet (originCube d m))
  let G : Vec d → Vec d := fun x ↦ -oneStepMultiplierAt M n h x omega • p
  have hVopen : IsOpen V := by
    dsimp only [V]
    rw [← Homogenization.Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube,
      ← Homogenization.Book.Ch03.openCubeAtScale_eq_translateSet]
    exact Homogenization.Book.Ch03.isOpen_openCubeAtScale z m
  let : IsFiniteMeasure (volumeMeasureOn V) :=
    isFiniteMeasure_restrict.mpr
      (ne_of_lt (lt_of_le_of_lt (measure_mono hsub)
        (volume_openCubeSet_lt_top (originCube d K))))
  have hG : MemVectorL2 U G := by
    let shell := oneStepShellForcingH1 M n h omega p (originCube d K) hh
    have hshell : MemVectorL2 U (fun x ↦ -shell.toField x) := by
      simpa only [U] using! shell.memVectorL2_toField_openCubeSet.neg
    simpa only [G, shell, oneStepShellForcing_paired_toField,
      oneStepShellForcingW14_toField_apply, neg_smul] using hshell
  have hlarge : ∀ psi : H10Function U,
      ∫ x in U,
          vecDot
            ((oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.grad x)
            (psi.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (G x) (psi.toH1Function.grad x) ∂volume := by
    simpa only [U, G, IsZeroTraceDirichletRhsWeakSolution,
      matVecMul_identityCoeffField] using
      oneStepOriginDirichletSolution_isWeakSolution M n h p K omega hh
  have hlargeV := weakVectorEquation_restrict
    (isOpen_openCubeSet (originCube d K)) hVopen hsub
    (oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.grad_memVectorL2
    hG hlarge
  have hlocal : ∀ psi : H10Function V,
      ∫ x in V,
          vecDot
            ((oneStepTranslatedDirichletSolution M n h p z m omega hh).toH1Function.grad x)
            (psi.toH1Function.grad x) ∂volume =
        ∫ x in V, vecDot (G x) (psi.toH1Function.grad x) ∂volume := by
    simpa only [V, G, IsZeroTraceDirichletRhsWeakSolution,
      matVecMul_identityCoeffField] using
      oneStepTranslatedDirichletSolution_isWeakSolution M n h p z m omega hh
  exact weakPoissonEquationOn_sub_of_same_h10_equation hVopen
    ((oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.restrict
      hVopen hsub)
    (oneStepTranslatedDirichletSolution M n h p z m omega hh).toH1Function
    G hlargeV hlocal

/-- Neumann counterpart of
`oneStepDirichlet_restrict_sub_translated_harmonic`.  The mean-zero global
equation is tested with the mean-zero projection of each zero-trace test;
their gradients agree exactly. -/
theorem oneStepNeumann_restrict_sub_translated_harmonic
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    WeakPoissonEquationOn
      (translateSet z (openCubeSet (originCube d m)))
      ((oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.restrict
          (by
            rw [← Homogenization.Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube,
              ← Homogenization.Book.Ch03.openCubeAtScale_eq_translateSet]
            exact Homogenization.Book.Ch03.isOpen_openCubeAtScale z m)
          hsub -
        (oneStepTranslatedNeumannSolution M n h p z m omega hh).toH1Function)
      (fun _ ↦ 0) := by
  let U := openCubeSet (originCube d K)
  let V := translateSet z (openCubeSet (originCube d m))
  let G : Vec d → Vec d := fun x ↦ -oneStepMultiplierAt M n h x omega • p
  have hVopen : IsOpen V := by
    dsimp only [V]
    rw [← Homogenization.Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube,
      ← Homogenization.Book.Ch03.openCubeAtScale_eq_translateSet]
    exact Homogenization.Book.Ch03.isOpen_openCubeAtScale z m
  let : IsFiniteMeasure (volumeMeasureOn V) :=
    isFiniteMeasure_restrict.mpr
      (ne_of_lt (lt_of_le_of_lt (measure_mono hsub)
        (volume_openCubeSet_lt_top (originCube d K))))
  have hG : MemVectorL2 U G := by
    let shell := oneStepShellForcingH1 M n h omega p (originCube d K) hh
    have hshell : MemVectorL2 U (fun x ↦ -shell.toField x) := by
      simpa only [U] using! shell.memVectorL2_toField_openCubeSet.neg
    simpa only [G, shell, oneStepShellForcing_paired_toField,
      oneStepShellForcingW14_toField_apply, neg_smul] using hshell
  have hlarge : ∀ psi : H10Function U,
      ∫ x in U,
          vecDot
            ((oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.grad x)
            (psi.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (G x) (psi.toH1Function.grad x) ∂volume := by
    intro psi
    have hweak := oneStepOriginNeumannSolution_isWeakSolution
      M n h p K omega hh psi.toH1Function.toMeanZero
    simpa only [U, G, H1Function.toMeanZero_grad,
      matVecMul_identityCoeffField] using hweak
  have hlargeV := weakVectorEquation_restrict
    (isOpen_openCubeSet (originCube d K)) hVopen hsub
    (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.grad_memVectorL2
    hG hlarge
  have hlocal : ∀ psi : H10Function V,
      ∫ x in V,
          vecDot
            ((oneStepTranslatedNeumannSolution M n h p z m omega hh).toH1Function.grad x)
            (psi.toH1Function.grad x) ∂volume =
        ∫ x in V, vecDot (G x) (psi.toH1Function.grad x) ∂volume := by
    intro psi
    have hweak := oneStepTranslatedNeumannSolution_isWeakSolution
      M n h p z m omega hh psi.toH1Function.toMeanZero
    simpa only [V, G, H1Function.toMeanZero_grad,
      matVecMul_identityCoeffField] using hweak
  exact weakPoissonEquationOn_sub_of_same_h10_equation hVopen
    ((oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.restrict
      hVopen hsub)
    (oneStepTranslatedNeumannSolution M n h p z m omega hh).toH1Function
    G hlargeV hlocal

/-- The restriction of the large-cube Dirichlet solution, cast onto the
literal axis-cube carrier of a translated parent. -/
def oneStepDirichletAxisLargeRestriction
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    H1Function (axisCube (oneStepCenteredAxisCorner z m)
      (cubeScaleFactor (originCube d m))) :=
  castH1Domain (translateSet_openCubeSet_originCube_eq_axisCube z m)
    ((oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.restrict
        (by
          rw [← Homogenization.Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube,
            ← Homogenization.Book.Ch03.openCubeAtScale_eq_translateSet]
          exact Homogenization.Book.Ch03.isOpen_openCubeAtScale z m)
        hsub)

/-- The domain cast and Sobolev restriction used by the Dirichlet axis
carrier do not alter the global gradient representative. -/
theorem oneStepDirichletAxisLargeRestriction_grad
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    (oneStepDirichletAxisLargeRestriction
      M n h omega p z K m hsub hh).grad =
      (oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.grad := by
  unfold oneStepDirichletAxisLargeRestriction
  rw [grad_castH1Domain]
  rfl

/-- The stationary translated Dirichlet solution on the same axis cube. -/
def oneStepDirichletAxisLocalSolution
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    H1Function (axisCube (oneStepCenteredAxisCorner z m)
      (cubeScaleFactor (originCube d m))) :=
  castH1Domain (translateSet_openCubeSet_originCube_eq_axisCube z m)
    (oneStepTranslatedDirichletSolution M n h p z m omega hh).toH1Function

/-- The domain cast in the axis-local Dirichlet carrier does not change its
gradient field. -/
theorem oneStepDirichletAxisLocalSolution_grad
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    (oneStepDirichletAxisLocalSolution M n h omega p z m hh).grad =
      (oneStepTranslatedDirichletSolution M n h p z m omega hh).toH1Function.grad := by
  unfold oneStepDirichletAxisLocalSolution
  exact grad_castH1Domain _ _

/-- The recentered Dirichlet remainder in the exact arbitrary-axis carrier
consumed by the interior harmonic estimates. -/
def oneStepDirichletAxisRemainder
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    H1Function (axisCube (oneStepCenteredAxisCorner z m)
      (cubeScaleFactor (originCube d m))) :=
  oneStepDirichletAxisLargeRestriction M n h omega p z K m hsub hh -
    oneStepDirichletAxisLocalSolution M n h omega p z m hh

theorem oneStepDirichletAxisRemainder_harmonic
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    WeakPoissonEquationOn
      (axisCube (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)))
      (oneStepDirichletAxisRemainder M n h omega p z K m hsub hh)
      (fun _ ↦ 0) := by
  simpa only [oneStepDirichletAxisRemainder,
    oneStepDirichletAxisLargeRestriction, oneStepDirichletAxisLocalSolution,
    castH1Domain_sub] using WeakPoissonEquationOn.castDomain_oneStep
    (translateSet_openCubeSet_originCube_eq_axisCube z m)
    (oneStepDirichlet_restrict_sub_translated_harmonic
      M n h omega p z K m hsub hh)

/-- The restriction of the large-cube Neumann solution on a translated
parent, in the same axis-cube carrier as its stationary local comparison. -/
def oneStepNeumannAxisLargeRestriction
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    H1Function (axisCube (oneStepCenteredAxisCorner z m)
      (cubeScaleFactor (originCube d m))) :=
  castH1Domain (translateSet_openCubeSet_originCube_eq_axisCube z m)
    ((oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.restrict
        (by
          rw [← Homogenization.Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube,
            ← Homogenization.Book.Ch03.openCubeAtScale_eq_translateSet]
          exact Homogenization.Book.Ch03.isOpen_openCubeAtScale z m)
        hsub)

/-- Neumann counterpart of the unchanged-gradient readout. -/
theorem oneStepNeumannAxisLargeRestriction_grad
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    (oneStepNeumannAxisLargeRestriction
      M n h omega p z K m hsub hh).grad =
      (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.grad := by
  unfold oneStepNeumannAxisLargeRestriction
  rw [grad_castH1Domain]
  rfl

/-- The stationary translated Neumann solution on the same parent. -/
def oneStepNeumannAxisLocalSolution
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    H1Function (axisCube (oneStepCenteredAxisCorner z m)
      (cubeScaleFactor (originCube d m))) :=
  castH1Domain (translateSet_openCubeSet_originCube_eq_axisCube z m)
    (oneStepTranslatedNeumannSolution M n h p z m omega hh).toH1Function

/-- The domain cast in the axis-local Neumann carrier does not change its
gradient field. -/
theorem oneStepNeumannAxisLocalSolution_grad
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    (oneStepNeumannAxisLocalSolution M n h omega p z m hh).grad =
      (oneStepTranslatedNeumannSolution M n h p z m omega hh).toH1Function.grad := by
  unfold oneStepNeumannAxisLocalSolution
  exact grad_castH1Domain _ _

/-- Neumann arbitrary-axis remainder. -/
def oneStepNeumannAxisRemainder
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    H1Function (axisCube (oneStepCenteredAxisCorner z m)
      (cubeScaleFactor (originCube d m))) :=
  oneStepNeumannAxisLargeRestriction M n h omega p z K m hsub hh -
    oneStepNeumannAxisLocalSolution M n h omega p z m hh

theorem oneStepNeumannAxisRemainder_harmonic
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    WeakPoissonEquationOn
      (axisCube (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)))
      (oneStepNeumannAxisRemainder M n h omega p z K m hsub hh)
      (fun _ ↦ 0) := by
  simpa only [oneStepNeumannAxisRemainder,
    oneStepNeumannAxisLargeRestriction, oneStepNeumannAxisLocalSolution,
    castH1Domain_sub] using WeakPoissonEquationOn.castDomain_oneStep
    (translateSet_openCubeSet_originCube_eq_axisCube z m)
    (oneStepNeumann_restrict_sub_translated_harmonic
      M n h omega p z K m hsub hh)

/-! ## Parent-gradient bookkeeping for the harmonic remainder -/

/-- Exact normalized Hilbert-gradient norm on a positive axis cube. -/
theorem toReal_eLpNorm_hilbertify_grad_two_axisCube
    {d : ℕ} (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u : H1Function (axisCube z L)) :
    (eLpNorm (hilbertifyVecField u.grad) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal =
      ((L ^ d)⁻¹) ^ (1 / 2 : ℝ) * ‖u.gradToHilbertVectorL2‖ := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((L ^ d)⁻¹)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.2
    (inv_pos.mpr (pow_pos hL d))
  rw [CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
    z L hL]
  change (eLpNorm (hilbertifyVecField u.grad) 2
    (c • volume.restrict (axisCube z L))).toReal = _
  rw [eLpNorm_smul_measure_of_ne_zero hc,
    CubeCalderonZygmund.eLpNorm_hilbertify_grad_two_eq_ofReal_norm_gradToHilbertVectorL2]
  norm_num only [ENNReal.toReal_ofNat]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  have hpow : 0 ≤ L ^ d := (pow_pos hL d).le
  simp only [c]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hpow)]
  rw [ENNReal.toReal_ofReal (norm_nonneg _)]
  congr 2
  norm_num

/-- The normalized axis-cube norm of the local translated Dirichlet
solution is exactly the stationary observable used by the moment layer. -/
theorem axisNorm_oneStepDirichletAxisLocalSolution_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    (eLpNorm (hilbertifyVecField
        (oneStepDirichletAxisLocalSolution M n h omega p z m hh).grad) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)))).toReal =
      oneStepTranslatedDirichletNormalizedGradient
        M n h p z m omega hh := by
  rw [toReal_eLpNorm_hilbertify_grad_two_axisCube
    (oneStepCenteredAxisCorner z m)
    (by simpa [cubeScaleFactor] using!
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) m))]
  unfold oneStepDirichletAxisLocalSolution
    oneStepTranslatedDirichletNormalizedGradient
  rw [norm_gradToHilbertVectorL2_castH1Domain,
    cubeVolume_eq_scaleFactor_pow]

/-- Neumann counterpart of the preceding exact readout. -/
theorem axisNorm_oneStepNeumannAxisLocalSolution_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    (eLpNorm (hilbertifyVecField
        (oneStepNeumannAxisLocalSolution M n h omega p z m hh).grad) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)))).toReal =
      oneStepTranslatedNeumannNormalizedGradient
        M n h p z m omega hh := by
  rw [toReal_eLpNorm_hilbertify_grad_two_axisCube
    (oneStepCenteredAxisCorner z m)
    (by simpa [cubeScaleFactor] using!
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) m))]
  unfold oneStepNeumannAxisLocalSolution
    oneStepTranslatedNeumannNormalizedGradient
  rw [norm_gradToHilbertVectorL2_castH1Domain,
    cubeVolume_eq_scaleFactor_pow]
  rfl



theorem axisGradientCoordinateSum_le_dimension_mul
    {d : ℕ} (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u : H1Function (axisCube z L)) :
    (∑ k : Fin d,
        (eLpNorm (fun x ↦ u.grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal) ≤
      (d : ℝ) *
        (eLpNorm (hilbertifyVecField u.grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal := by
  have hvec : MemLp (hilbertifyVecField u.grad) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) :=
    CubeCalderonZygmund.memHilbertVectorL2_axisCubeNormalizedMeasure z hL
      (memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2)
  have hcoord : ∀ k : Fin d,
      (eLpNorm (fun x ↦ u.grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal ≤
        (eLpNorm (hilbertifyVecField u.grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal := by
    intro k
    apply ENNReal.toReal_mono hvec.eLpNorm_ne_top
    exact coordinate_eLpNorm_le_euclidean
      (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)
      FiniteLpExponent.two u.grad k
  calc
    (∑ k : Fin d,
        (eLpNorm (fun x ↦ u.grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal) ≤
        ∑ _k : Fin d,
          (eLpNorm (hilbertifyVecField u.grad) 2
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal :=
      Finset.sum_le_sum fun k _ ↦ hcoord k
    _ = (d : ℝ) *
        (eLpNorm (hilbertifyVecField u.grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal := by
      simp [nsmul_eq_mul]



theorem axisGradientCoordinateSum_sub_le_dimension_mul_add
    {d : ℕ} (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u v : H1Function (axisCube z L)) :
    (∑ k : Fin d,
        (eLpNorm (fun x ↦ (u - v).grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal) ≤
      (d : ℝ) *
        ((eLpNorm (hilbertifyVecField u.grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal +
        (eLpNorm (hilbertifyVecField v.grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal) := by
  have hu : MemLp (hilbertifyVecField u.grad) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) :=
    CubeCalderonZygmund.memHilbertVectorL2_axisCubeNormalizedMeasure z hL
      (memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2)
  have hv : MemLp (hilbertifyVecField v.grad) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) :=
    CubeCalderonZygmund.memHilbertVectorL2_axisCubeNormalizedMeasure z hL
      (memHilbertVectorL2_hilbertifyVecField v.grad_memVectorL2)
  have hsub :
      (eLpNorm (hilbertifyVecField (u - v).grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal ≤
        (eLpNorm (hilbertifyVecField u.grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal +
        (eLpNorm (hilbertifyVecField v.grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal := by
    have hraw := CubeCalderonZygmund.axisCubeNormalized_eLpNorm_two_sub_le
      z (L := L) (F := hilbertifyVecField u.grad) (G := hilbertifyVecField v.grad)
    have htop :
        eLpNorm (hilbertifyVecField u.grad) 2
              (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) +
            eLpNorm (hilbertifyVecField v.grad) 2
              (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨hu.eLpNorm_ne_top, hv.eLpNorm_ne_top⟩
    rw [← ENNReal.toReal_add hu.eLpNorm_ne_top hv.eLpNorm_ne_top]
    apply ENNReal.toReal_mono htop
    simpa only [H1Function.sub_grad, hilbertifyVecField, Pi.sub_apply, map_sub] using! hraw
  calc
    (∑ k : Fin d,
        (eLpNorm (fun x ↦ (u - v).grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal) ≤
        (d : ℝ) *
          (eLpNorm (hilbertifyVecField (u - v).grad) 2
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal :=
      axisGradientCoordinateSum_le_dimension_mul z hL (u - v)
    _ ≤ (d : ℝ) *
        ((eLpNorm (hilbertifyVecField u.grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal +
        (eLpNorm (hilbertifyVecField v.grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal) :=
      mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg d)



theorem oneStepDirichletAxisRemainder_coordinateSum_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    (∑ k : Fin d,
        (eLpNorm (fun x ↦
            (oneStepDirichletAxisRemainder
              M n h omega p z K m hsub hh).grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal) ≤
      (d : ℝ) *
        ((eLpNorm (hilbertifyVecField
            (oneStepDirichletAxisLargeRestriction
              M n h omega p z K m hsub hh).grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal +
        (eLpNorm (hilbertifyVecField
            (oneStepDirichletAxisLocalSolution
              M n h omega p z m hh).grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal) := by
  simpa only [oneStepDirichletAxisRemainder] using
    axisGradientCoordinateSum_sub_le_dimension_mul_add
      (oneStepCenteredAxisCorner z m)
      (by simpa [cubeScaleFactor] using!
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) m))
      (oneStepDirichletAxisLargeRestriction M n h omega p z K m hsub hh)
      (oneStepDirichletAxisLocalSolution M n h omega p z m hh)



theorem oneStepNeumannAxisRemainder_coordinateSum_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    (∑ k : Fin d,
        (eLpNorm (fun x ↦
            (oneStepNeumannAxisRemainder
              M n h omega p z K m hsub hh).grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal) ≤
      (d : ℝ) *
        ((eLpNorm (hilbertifyVecField
            (oneStepNeumannAxisLargeRestriction
              M n h omega p z K m hsub hh).grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal +
        (eLpNorm (hilbertifyVecField
            (oneStepNeumannAxisLocalSolution
              M n h omega p z m hh).grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal) := by
  simpa only [oneStepNeumannAxisRemainder] using
    axisGradientCoordinateSum_sub_le_dimension_mul_add
      (oneStepCenteredAxisCorner z m)
      (by simpa [cubeScaleFactor] using!
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) m))
      (oneStepNeumannAxisLargeRestriction M n h omega p z K m hsub hh)
      (oneStepNeumannAxisLocalSolution M n h omega p z m hh)

/-- Dirichlet remainder bound with the stationary local term rewritten in
the exact measurable moment observable. -/
theorem oneStepDirichletAxisRemainder_coordinateSum_le_large_add_translated
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    (∑ k : Fin d,
        (eLpNorm (fun x ↦
            (oneStepDirichletAxisRemainder
              M n h omega p z K m hsub hh).grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal) ≤
      (d : ℝ) *
        ((eLpNorm (hilbertifyVecField
            (oneStepDirichletAxisLargeRestriction
              M n h omega p z K m hsub hh).grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal +
          oneStepTranslatedDirichletNormalizedGradient
            M n h p z m omega hh) := by
  rw [← axisNorm_oneStepDirichletAxisLocalSolution_eq
    M n h omega p z m hh]
  exact oneStepDirichletAxisRemainder_coordinateSum_le
    M n h omega p z K m hsub hh

/-- Neumann remainder bound with the stationary local term rewritten in the
same measurable setting. -/
theorem oneStepNeumannAxisRemainder_coordinateSum_le_large_add_translated
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    (∑ k : Fin d,
        (eLpNorm (fun x ↦
            (oneStepNeumannAxisRemainder
              M n h omega p z K m hsub hh).grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal) ≤
      (d : ℝ) *
        ((eLpNorm (hilbertifyVecField
            (oneStepNeumannAxisLargeRestriction
              M n h omega p z K m hsub hh).grad) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))).toReal +
          oneStepTranslatedNeumannNormalizedGradient
            M n h p z m omega hh) := by
  rw [← axisNorm_oneStepNeumannAxisLocalSolution_eq
    M n h omega p z m hh]
  exact oneStepNeumannAxisRemainder_coordinateSum_le
    M n h omega p z K m hsub hh

/-- Interior `B_z` package for the actual large-cube Dirichlet solution after
recentering on an arbitrary parent.  Its right side is precisely the
normalized parent gradient of the harmonic remainder; the stationary local
part is exposed separately by `oneStepTranslatedDirichletSolution`. -/
theorem exists_oneStepDirichlet_recentered_cellB_bound
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
        (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
          openCubeSet (originCube d K)) (hh : 0 < h)
        (R : TriadicCube d)
        (hRhalf : openCubeSet R ⊆
          axisCubeInnerHalf (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))
        (_hRinner : openCubeSet R ⊆
          axisCube
            (CubeCalderonZygmund.axisCubeConcentricDepthCorner
              (oneStepCenteredAxisCorner z m)
              (cubeScaleFactor (originCube d m)) (depth + 1))
            (CubeCalderonZygmund.axisCubeConcentricDepthSide
              (cubeScaleFactor (originCube d m)) (depth + 1))),
        ∃ uS : H1Function
            (axisCubeInnerHalf (oneStepCenteredAxisCorner z m)
              (cubeScaleFactor (originCube d m))),
          uS.toFun =
              (oneStepDirichletAxisRemainder M n h omega p z K m hsub hh).toFun ∧
          uS.grad =
              (oneStepDirichletAxisRemainder M n h omega p z K m hsub hh).grad ∧
          ∃ H : HasWeakHessianOn
              (axisCubeInnerHalf (oneStepCenteredAxisCorner z m)
                (cubeScaleFactor (originCube d m))) uS,
            oneStepCellB R
                (H.restrict (isOpen_openCubeSet R) hRhalf) ≤
              cubeScaleFactor R * (d : ℝ) ^ 2 *
                ((triadicAxisNormalizedMeasureRatio R
                  (CubeCalderonZygmund.axisCubeConcentricDepthSide
                    (cubeScaleFactor (originCube d m)) (depth + 1))) ^
                  (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal *
                (C * (cubeScaleFactor (originCube d m))⁻¹ *
                  ∑ k : Fin d,
                    (eLpNorm (fun x ↦
                        (oneStepDirichletAxisRemainder
                          M n h omega p z K m hsub hh).grad x k) 2
                      (CubeCalderonZygmund.axisCubeNormalizedMeasure
                        (oneStepCenteredAxisCorner z m)
                        (cubeScaleFactor (originCube d m)))).toReal) := by
  obtain ⟨depth, C, hC, haxis⟩ :=
    exists_axisCube_harmonic_cellB_bound d hd
  refine ⟨depth, C, hC, ?_⟩
  intro M n h omega p z K m hsub hh R hRhalf hRinner
  have hside : 0 < cubeScaleFactor (originCube d m) := by
    simpa [cubeScaleFactor] using!
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) m)
  exact haxis (oneStepCenteredAxisCorner z m)
    (cubeScaleFactor (originCube d m)) hside
    (oneStepDirichletAxisRemainder M n h omega p z K m hsub hh)
    (oneStepDirichletAxisRemainder_harmonic M n h omega p z K m hsub hh)
    R hRhalf hRinner

/-- Neumann counterpart of the recentered arbitrary-axis `B_z` package. -/
theorem exists_oneStepNeumann_recentered_cellB_bound
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d) (K m : ℤ)
        (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
          openCubeSet (originCube d K)) (hh : 0 < h)
        (R : TriadicCube d)
        (hRhalf : openCubeSet R ⊆
          axisCubeInnerHalf (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))
        (_hRinner : openCubeSet R ⊆
          axisCube
            (CubeCalderonZygmund.axisCubeConcentricDepthCorner
              (oneStepCenteredAxisCorner z m)
              (cubeScaleFactor (originCube d m)) (depth + 1))
            (CubeCalderonZygmund.axisCubeConcentricDepthSide
              (cubeScaleFactor (originCube d m)) (depth + 1))),
        ∃ uS : H1Function
            (axisCubeInnerHalf (oneStepCenteredAxisCorner z m)
              (cubeScaleFactor (originCube d m))),
          uS.toFun =
              (oneStepNeumannAxisRemainder M n h omega p z K m hsub hh).toFun ∧
          uS.grad =
              (oneStepNeumannAxisRemainder M n h omega p z K m hsub hh).grad ∧
          ∃ H : HasWeakHessianOn
              (axisCubeInnerHalf (oneStepCenteredAxisCorner z m)
                (cubeScaleFactor (originCube d m))) uS,
            oneStepCellB R
                (H.restrict (isOpen_openCubeSet R) hRhalf) ≤
              cubeScaleFactor R * (d : ℝ) ^ 2 *
                ((triadicAxisNormalizedMeasureRatio R
                  (CubeCalderonZygmund.axisCubeConcentricDepthSide
                    (cubeScaleFactor (originCube d m)) (depth + 1))) ^
                  (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal *
                (C * (cubeScaleFactor (originCube d m))⁻¹ *
                  ∑ k : Fin d,
                    (eLpNorm (fun x ↦
                        (oneStepNeumannAxisRemainder
                          M n h omega p z K m hsub hh).grad x k) 2
                      (CubeCalderonZygmund.axisCubeNormalizedMeasure
                        (oneStepCenteredAxisCorner z m)
                        (cubeScaleFactor (originCube d m)))).toReal) := by
  obtain ⟨depth, C, hC, haxis⟩ :=
    exists_axisCube_harmonic_cellB_bound d hd
  refine ⟨depth, C, hC, ?_⟩
  intro M n h omega p z K m hsub hh R hRhalf hRinner
  have hside : 0 < cubeScaleFactor (originCube d m) := by
    simpa [cubeScaleFactor] using!
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) m)
  exact haxis (oneStepCenteredAxisCorner z m)
    (cubeScaleFactor (originCube d m)) hside
    (oneStepNeumannAxisRemainder M n h omega p z K m hsub hh)
    (oneStepNeumannAxisRemainder_harmonic M n h omega p z K m hsub hh)
    R hRhalf hRinner

/-- Simultaneous Dirichlet recentering on every member of a finite nested
family.  The nesting relation itself is deliberately kept in the geometry
producer: analytically, each level is obtained by the same restriction and
stationary translated-solution subtraction. -/
theorem oneStepDirichlet_nested_recentring
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h N : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (K : ℤ)
    (center : Fin N → Vec d) (scale : Fin N → ℤ)
    (hsub : ∀ j, translateSet (center j)
      (openCubeSet (originCube d (scale j))) ⊆
        openCubeSet (originCube d K)) (hh : 0 < h) :
    ∀ j, WeakPoissonEquationOn
      (translateSet (center j) (openCubeSet (originCube d (scale j))))
      ((oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.restrict
          (by
            rw [← Homogenization.Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube,
              ← Homogenization.Book.Ch03.openCubeAtScale_eq_translateSet]
            exact Homogenization.Book.Ch03.isOpen_openCubeAtScale
              (center j) (scale j))
          (hsub j) -
        (oneStepTranslatedDirichletSolution M n h p
          (center j) (scale j) omega hh).toH1Function)
      (fun _ ↦ 0) := by
  intro j
  exact oneStepDirichlet_restrict_sub_translated_harmonic
    M n h omega p (center j) K (scale j) (hsub j) hh

/-- Simultaneous Neumann recentering on the same arbitrary finite nested
family. -/
theorem oneStepNeumann_nested_recentring
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h N : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (K : ℤ)
    (center : Fin N → Vec d) (scale : Fin N → ℤ)
    (hsub : ∀ j, translateSet (center j)
      (openCubeSet (originCube d (scale j))) ⊆
        openCubeSet (originCube d K)) (hh : 0 < h) :
    ∀ j, WeakPoissonEquationOn
      (translateSet (center j) (openCubeSet (originCube d (scale j))))
      ((oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.restrict
          (by
            rw [← Homogenization.Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube,
              ← Homogenization.Book.Ch03.openCubeAtScale_eq_translateSet]
            exact Homogenization.Book.Ch03.isOpen_openCubeAtScale
              (center j) (scale j))
          (hsub j) -
        (oneStepTranslatedNeumannSolution M n h p
          (center j) (scale j) omega hh).toH1Function)
      (fun _ ↦ 0) := by
  intro j
  exact oneStepNeumann_restrict_sub_translated_harmonic
    M n h omega p (center j) K (scale j) (hsub j) hh

/-! ## Stationary fourth moments at every recentering level -/

/-- The translated Dirichlet parent selected by any nesting level has the
same uniform fourth moment as the canonical origin parent. -/
theorem integral_oneStepTranslatedDirichletNormalizedGradientFourth_le_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫ omega, oneStepTranslatedDirichletNormalizedGradientFourth
        M n h p z m omega hh ∂M.P.toMeasure ≤
      oneStepSourceParentGradientConst ^ (4 : ℕ) := by
  rw [integral_oneStepTranslatedDirichletNormalizedGradientFourth_eq_origin]
  exact integral_oneStepOriginDirichletNormalizedGradientFourth_le_uniform
    M n h p m hh hp hscale

/-- Neumann counterpart of the preceding stationary parent-moment endpoint. -/
theorem integral_oneStepTranslatedNeumannNormalizedGradientFourth_le_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫ omega, oneStepTranslatedNeumannNormalizedGradientFourth
        M n h p z m omega hh ∂M.P.toMeasure ≤
      oneStepSourceParentGradientConst ^ (4 : ℕ) := by
  rw [integral_oneStepTranslatedNeumannNormalizedGradientFourth_eq_origin]
  exact integral_oneStepOriginNeumannNormalizedGradientFourth_le_uniform
    M n h p m hh hp hscale

/-- A finite family of Dirichlet parents, including the whole nested family,
obeys the same normalized fourth-moment budget. -/
theorem normalized_finset_integral_oneStepTranslatedDirichletNormalizedGradientFourth_le_uniform
    {d : ℕ} [NeZero d] {iota : Type*} [DecidableEq iota]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (center : iota → Vec d) (s : Finset iota) (hs : s.Nonempty)
    (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, oneStepTranslatedDirichletNormalizedGradientFourth
          M n h p (center i) m omega hh ∂M.P.toMeasure ≤
      oneStepSourceParentGradientConst ^ (4 : ℕ) := by
  rw [normalized_finset_integral_oneStepTranslatedDirichletNormalizedGradientFourth_eq
    M n h p center s hs m hh]
  exact integral_oneStepOriginDirichletNormalizedGradientFourth_le_uniform
    M n h p m hh hp hscale

/-- Neumann finite-family version of the uniform nested-parent budget. -/
theorem normalized_finset_integral_oneStepTranslatedNeumannNormalizedGradientFourth_le_uniform
    {d : ℕ} [NeZero d] {iota : Type*} [DecidableEq iota]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (center : iota → Vec d) (s : Finset iota) (hs : s.Nonempty)
    (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, oneStepTranslatedNeumannNormalizedGradientFourth
          M n h p (center i) m omega hh ∂M.P.toMeasure ≤
      oneStepSourceParentGradientConst ^ (4 : ℕ) := by
  rw [normalized_finset_integral_oneStepTranslatedNeumannNormalizedGradientFourth_eq
    M n h p center s hs m hh]
  exact integral_oneStepOriginNeumannNormalizedGradientFourth_le_uniform
    M n h p m hh hp hscale

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
