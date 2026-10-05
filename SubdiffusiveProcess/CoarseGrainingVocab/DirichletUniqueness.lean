module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import Homogenization.Ambient.ScalarMatrix
public import Homogenization.Sobolev.PotentialSolenoidalL2Realization

@[expose] public section

/-!
# Existence and a.e. uniqueness for the section 6 weak Dirichlet problems

The section 6 surface states three weak Dirichlet problems whose first
clauses are always the same two facts: a solution exists, and any two solutions
agree almost everywhere together with their weak gradients.  This module proves
those two facts once, in the reusable shapes

* `IsScalarDirichletSolutionOn` (scalar forcing, matrix coefficient field), and
* `IsWeaklyHarmonicOn` together with `HasZeroTraceDifferenceOn` (the harmonic
  approximation shape),

so that the section 6 providers can discharge the corresponding clauses by
direct application.

The analytic content is entirely reused from the `Homogenization` library:
energy testing against the difference of two solutions
(`Homogenization.IsZeroTraceDirichletRhsWeakSolution.energy_le_rhs_pairing_of_isEllipticFieldOn`),
the zero-trace Poincare inequality
(`Homogenization.H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain`),
and the variational existence theorem for divergence-form forcing
(`Homogenization.exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization`).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book.Ch02

noncomputable section

/-! ### Geometry of the section 6 windows -/

/-- A translate of the centered paper cube is a bounded open convex domain. -/
theorem isOpenBoundedConvexDomain_translatedCube {d : ℕ} (m : ℤ) (z : Vec d) :
    IsOpenBoundedConvexDomain (translatedCube d m z) := by
  have hset : translatedCube d m z = translateSet z (cube d m) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by ext i; simp [add_comm]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by ext i; simp [add_comm]⟩
  rw [hset]
  exact (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).translateSet z

/-- A translate of the centered paper cube is nonempty. -/
theorem translatedCube_nonempty {d : ℕ} (m : ℤ) (z : Vec d) :
    (translatedCube d m z).Nonempty := by
  obtain ⟨y, hy⟩ := openCubeSet_nonempty (originCube d m)
  exact ⟨z + y, ⟨y, hy, rfl⟩⟩

/-! ### Positive scalar coefficients -/

/-- A positive constant scalar coefficient is uniformly elliptic on every
measurable window. -/
theorem isEllipticFieldOn_scalarCoeffField_const {d : ℕ} {W : Set (Vec d)}
    {sigma : ℝ} (hW : MeasurableSet W) (hsigma : 0 < sigma) :
    IsEllipticFieldOn sigma sigma W (scalarCoeffField fun _ => sigma) := by
  classical
  refine ⟨?_, ?_⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    have hpiece :
        Measurable
          (W.piecewise
            (fun _ : Vec d => Homogenization.scalarMatrix (d := d) sigma i j)
            (fun _ => 0)) :=
      measurable_const.piecewise hW measurable_const
    simpa [Set.piecewise, scalarCoeffField] using! hpiece
  · intro x _
    simpa [scalarCoeffField] using
      (Homogenization.isEllipticMatrix_scalarMatrix (d := d) hsigma)

/-- The constant coefficient `1` of the statements is the scalar
coefficient field of the constant scalar `1`. -/
theorem scalarCoeffField_one {d : ℕ} :
    (scalarCoeffField fun _ : Vec d => (1 : ℝ)) = fun _ : Vec d => (1 : Mat d) := by
  funext x
  simp [scalarCoeffField, Homogenization.scalarMatrix]

/-! ### The zero-trace difference of two solutions -/

/-- Two functions with the same zero-trace datum differ by an `H¹₀` function. -/
private theorem exists_h10_sub_of_hasZeroTraceDifferenceOn {d : ℕ}
    {W : Set (Vec d)} {u u' hD : H1Function W}
    (hu : HasZeroTraceDifferenceOn W u hD)
    (hu' : HasZeroTraceDifferenceOn W u' hD) :
    ∃ w : H10Function W,
      (∀ x, w.toH1Function.toFun x = u.toFun x - u'.toFun x) ∧
        ∀ x, w.toH1Function.grad x = u.grad x - u'.grad x := by
  obtain ⟨w₁, hw₁f, hw₁g⟩ := hu
  obtain ⟨w₂, hw₂f, hw₂g⟩ := hu'
  refine ⟨w₁ - w₂, fun x => ?_, fun x => ?_⟩
  · have hsub : (w₁ - w₂).toH1Function.toFun x =
        w₁.toH1Function.toFun x - w₂.toH1Function.toFun x := by
      change (w₁.toH1Function - w₂.toH1Function).toFun x =
        w₁.toH1Function.toFun x - w₂.toH1Function.toFun x
      rw [H1Function.sub_toFun]
    rw [hsub, hw₁f x, hw₂f x]
    ring
  · have hsub : (w₁ - w₂).toH1Function.grad x =
        w₁.toH1Function.grad x - w₂.toH1Function.grad x := by
      change (w₁.toH1Function - w₂.toH1Function).grad x =
        w₁.toH1Function.grad x - w₂.toH1Function.grad x
      rw [H1Function.sub_grad]
    rw [hsub, hw₁g x, hw₂g x]
    abel

/-! ### Energy testing and Poincare -/

/-- Energy testing: an `H¹₀` function whose coefficient flux is weakly
orthogonal to every `H¹₀` gradient has an almost everywhere vanishing
gradient.  Only the lower ellipticity bound is used. -/
private theorem h10_grad_ae_zero_of_forall_integral_eq_zero {d : ℕ}
    {W : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hne : W.Nonempty) (hEll : IsEllipticFieldOn lam Lam W a)
    {w : H10Function W}
    (hw : ∀ φ : H10Function W,
      ∫ x in W, vecDot (matVecMul (a x) (w.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂volume = 0) :
    w.toH1Function.grad =ᵐ[volume.restrict W] 0 := by
  have hw0 : IsZeroTraceDirichletRhsWeakSolution a W w (fun _ => (0 : Vec d)) := by
    intro φ
    rw [hw φ]
    simp [vecDot]
  obtain ⟨x₀, hx₀⟩ := hne
  have hlam : 0 < lam := (hEll.2 x₀ hx₀).1
  have henergy :
      lam * ∫ y in W, vecNormSq (w.toH1Function.grad y) ∂volume ≤ 0 := by
    have h :=
      IsZeroTraceDirichletRhsWeakSolution.energy_le_rhs_pairing_of_isEllipticFieldOn
        (u := w) (g := fun _ => (0 : Vec d)) hw0 hEll
    simpa [vecDot] using h
  have hsqInt :
      IntegrableOn (fun y => vecNormSq (w.toH1Function.grad y)) W :=
    integrableOn_vecNormSq_zeroTraceGrad w
  have hsqNonneg :
      0 ≤ ∫ y in W, vecNormSq (w.toH1Function.grad y) ∂volume :=
    integral_nonneg fun _ => vecNormSq_nonneg _
  have hsqZero :
      ∫ y in W, vecNormSq (w.toH1Function.grad y) ∂volume = 0 := by
    nlinarith
  have hsqAe :
      (fun y => vecNormSq (w.toH1Function.grad y)) =ᵐ[volume.restrict W] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
      hsqInt.integrable).1 hsqZero
  filter_upwards [hsqAe] with y hy
  exact vecNormSq_eq_zero hy

/-- Zero-trace Poincare: an `H¹₀` function with an almost everywhere vanishing
gradient vanishes almost everywhere. -/
private theorem h10_toFun_ae_zero_of_grad_ae_zero {d : ℕ} [NeZero d]
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W) (w : H10Function W)
    (hgrad : w.toH1Function.grad =ᵐ[volume.restrict W] 0) :
    w.toH1Function.toFun =ᵐ[volume.restrict W] 0 := by
  have hgradL2 : w.toH1Function.gradToVectorL2 = 0 := by
    apply MeasureTheory.Lp.ext
    filter_upwards
        [H1Function.coeFn_gradToVectorL2 w.toH1Function,
          MeasureTheory.Lp.coeFn_zero (E := Vec d) (p := (2 : ENNReal))
            (μ := volumeMeasureOn W),
          hgrad] with y h1 h2 h3
    rw [h1, h2, h3]
  have hval : w.toH1Function.toScalarL2 = 0 :=
    H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
      (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hW) w hgradL2
  filter_upwards
      [H1Function.coeFn_toScalarL2 w.toH1Function,
        MeasureTheory.Lp.coeFn_zero (E := ℝ) (p := (2 : ENNReal))
          (μ := volumeMeasureOn W)] with y h1 h2
  rw [← h1, hval, h2]

/-! ### The uniqueness core -/

/-- **A.e. uniqueness core.**  Two `H¹` functions with the same zero-trace
datum whose coefficient fluxes pair identically against every `H¹₀` gradient
agree almost everywhere, together with their weak gradients.

This is the shape shared by all three section 6 uniqueness clauses: the
difference is a weakly `a`-harmonic `H¹₀` function, energy testing with the
difference itself kills its gradient, and the zero-trace Poincare inequality
then kills the difference itself. -/
theorem ae_eq_of_hasZeroTraceDifferenceOn_of_forall_flux_pairing_eq {d : ℕ}
    [NeZero d] {W : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hW : IsOpenBoundedConvexDomain W) (hne : W.Nonempty)
    (hEll : IsEllipticFieldOn lam Lam W a)
    {u u' hD : H1Function W}
    (hu : HasZeroTraceDifferenceOn W u hD)
    (hu' : HasZeroTraceDifferenceOn W u' hD)
    (hpair : ∀ φ : H10Function W,
      ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) ∂volume =
        ∫ x in W, vecDot (matVecMul (a x) (u'.grad x))
          (φ.toH1Function.grad x) ∂volume) :
    u.toFun =ᵐ[volume.restrict W] u'.toFun ∧
      u.grad =ᵐ[volume.restrict W] u'.grad := by
  obtain ⟨w, hwf, hwg⟩ := exists_h10_sub_of_hasZeroTraceDifferenceOn hu hu'
  have huFlux : MemVectorL2 W (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hu'Flux : MemVectorL2 W (fun x => matVecMul (a x) (u'.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u'.grad_memVectorL2
  have hzero : ∀ φ : H10Function W,
      ∫ x in W, vecDot (matVecMul (a x) (w.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂volume = 0 := by
    intro φ
    have huInt :
        IntegrableOn
          (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)) W :=
      integrableOn_vecDot_of_memVectorL2 huFlux φ.toH1Function.grad_memVectorL2
    have hu'Int :
        IntegrableOn
          (fun x => vecDot (matVecMul (a x) (u'.grad x)) (φ.toH1Function.grad x)) W :=
      integrableOn_vecDot_of_memVectorL2 hu'Flux φ.toH1Function.grad_memVectorL2
    have hfun :
        (fun x => vecDot (matVecMul (a x) (w.toH1Function.grad x))
            (φ.toH1Function.grad x)) =
          fun x =>
            vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) -
              vecDot (matVecMul (a x) (u'.grad x)) (φ.toH1Function.grad x) := by
      funext x
      rw [hwg x]
      simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
        vecDot_neg_left]
    rw [hfun, integral_sub huInt hu'Int, hpair φ, sub_self]
  have hgrad : w.toH1Function.grad =ᵐ[volume.restrict W] 0 :=
    h10_grad_ae_zero_of_forall_integral_eq_zero hne hEll hzero
  have hfun : w.toH1Function.toFun =ᵐ[volume.restrict W] 0 :=
    h10_toFun_ae_zero_of_grad_ae_zero hW w hgrad
  constructor
  · filter_upwards [hfun] with x hx
    have := hwf x
    rw [hx] at this
    exact (sub_eq_zero.1 this.symm)
  · filter_upwards [hgrad] with x hx
    have := hwg x
    rw [hx] at this
    exact (sub_eq_zero.1 this.symm)

/-! ### Uniqueness for the two Dirichlet-theorem shapes -/

/-- **A.e. uniqueness for the scalar-forcing weak Dirichlet problem.**  This is
the clause `uLM =ᵐ uLM' ∧ ∇uLM =ᵐ ∇uLM'` of the two section 6 Dirichlet
theorems. -/
theorem ae_eq_of_isScalarDirichletSolutionOn {d : ℕ} [NeZero d]
    {a : CoeffField d} {lam Lam : ℝ} {Q : TriadicCube d}
    {u u' hD : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hu : IsScalarDirichletSolutionOn a Q u hD f)
    (hu' : IsScalarDirichletSolutionOn a Q u' hD f) :
    u.toFun =ᵐ[volume.restrict (openCubeSet Q)] u'.toFun ∧
      u.grad =ᵐ[volume.restrict (openCubeSet Q)] u'.grad :=
  ae_eq_of_hasZeroTraceDifferenceOn_of_forall_flux_pairing_eq
    (isOpenBoundedConvexDomain_openCubeSet Q) (openCubeSet_nonempty Q) hEll
    hu.1 hu'.1 fun φ => by rw [hu.2 φ, hu'.2 φ]

/-- **A.e. uniqueness for the constant coefficient `1`.**  This is the clause
`uHom =ᵐ uHom' ∧ ∇uHom =ᵐ ∇uHom'` of the two section 6 Dirichlet theorems. -/
theorem ae_eq_of_isScalarDirichletSolutionOn_one {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {u u' hD : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (hu : IsScalarDirichletSolutionOn (fun _ => (1 : Mat d)) Q u hD f)
    (hu' : IsScalarDirichletSolutionOn (fun _ => (1 : Mat d)) Q u' hD f) :
    u.toFun =ᵐ[volume.restrict (openCubeSet Q)] u'.toFun ∧
      u.grad =ᵐ[volume.restrict (openCubeSet Q)] u'.grad := by
  have hEll :
      IsEllipticFieldOn (1 : ℝ) (1 : ℝ) (openCubeSet Q)
        (fun _ => (1 : Mat d)) := by
    have h :=
      isEllipticFieldOn_scalarCoeffField_const (W := openCubeSet Q) (sigma := 1)
        (isOpenBoundedConvexDomain_openCubeSet Q).isOpen.measurableSet one_pos
    rwa [scalarCoeffField_one] at h
  exact ae_eq_of_isScalarDirichletSolutionOn hEll hu hu'

/-! ### The harmonic approximation shape -/

/-- Weak harmonicity for a scalar coefficient is the flux pairing of the
associated matrix coefficient field. -/
private theorem vecDot_matVecMul_scalarCoeffField {d : ℕ} (sigma : Vec d → ℝ)
    (x : Vec d) (v y : Vec d) :
    vecDot (matVecMul (scalarCoeffField sigma x) v) y =
      vecDot (sigma x • v) y := by
  simp [scalarCoeffField, Homogenization.matVecMul_scalarMatrix]

/-- **A.e. uniqueness for the harmonic approximation shape.**  Two weakly
`sigma`-harmonic functions with the same zero-trace datum agree almost
everywhere together with their weak gradients. -/
theorem ae_eq_of_isWeaklyHarmonicOn_of_hasZeroTraceDifferenceOn {d : ℕ}
    [NeZero d] {W : Set (Vec d)} {sigma : Vec d → ℝ} {lam Lam : ℝ}
    (hW : IsOpenBoundedConvexDomain W) (hne : W.Nonempty)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField sigma))
    {v v' uD : H1Function W}
    (hv : IsWeaklyHarmonicOn sigma W v)
    (hvD : HasZeroTraceDifferenceOn W v uD)
    (hv' : IsWeaklyHarmonicOn sigma W v')
    (hv'D : HasZeroTraceDifferenceOn W v' uD) :
    v.toFun =ᵐ[volume.restrict W] v'.toFun ∧
      v.grad =ᵐ[volume.restrict W] v'.grad := by
  refine ae_eq_of_hasZeroTraceDifferenceOn_of_forall_flux_pairing_eq hW hne hEll
    hvD hv'D fun φ => ?_
  have hleft :
      ∫ x in W, vecDot (matVecMul (scalarCoeffField sigma x) (v.grad x))
          (φ.toH1Function.grad x) ∂volume = 0 := by
    simpa only [vecDot_matVecMul_scalarCoeffField] using hv φ
  have hright :
      ∫ x in W, vecDot (matVecMul (scalarCoeffField sigma x) (v'.grad x))
          (φ.toH1Function.grad x) ∂volume = 0 := by
    simpa only [vecDot_matVecMul_scalarCoeffField] using hv' φ
  rw [hleft, hright]

/-- **A.e. uniqueness for the constant coefficient `1` harmonic approximation
shape.**  This is the second clause of the section 6 harmonic approximation
theorem. -/
theorem ae_eq_of_isWeaklyHarmonicOn_one_of_hasZeroTraceDifferenceOn {d : ℕ}
    [NeZero d] {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    (hne : W.Nonempty) {v v' uD : H1Function W}
    (hv : IsWeaklyHarmonicOn (fun _ => 1) W v)
    (hvD : HasZeroTraceDifferenceOn W v uD)
    (hv' : IsWeaklyHarmonicOn (fun _ => 1) W v')
    (hv'D : HasZeroTraceDifferenceOn W v' uD) :
    v.toFun =ᵐ[volume.restrict W] v'.toFun ∧
      v.grad =ᵐ[volume.restrict W] v'.grad :=
  ae_eq_of_isWeaklyHarmonicOn_of_hasZeroTraceDifferenceOn hW hne
    (isEllipticFieldOn_scalarCoeffField_const hW.isOpen.measurableSet one_pos)
    hv hvD hv' hv'D

/-! ### Existence for the harmonic approximation shape -/

/-- **Existence for the harmonic approximation shape.**  For a uniformly
elliptic positive scalar coefficient and an arbitrary `H¹` datum there is a
weakly `sigma`-harmonic function with that datum's trace.

The witness is `uD` corrected by the zero-trace solution of the
divergence-form problem with forcing `-sigma ∇uD`, produced by the library's
variational existence theorem. -/
theorem exists_isWeaklyHarmonicOn_and_hasZeroTraceDifferenceOn {d : ℕ}
    [NeZero d] {W : Set (Vec d)} {sigma : Vec d → ℝ} {lam Lam : ℝ}
    (hW : IsOpenBoundedConvexDomain W) (hne : W.Nonempty)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField sigma))
    (uD : H1Function W) :
    ∃ v : H1Function W,
      IsWeaklyHarmonicOn sigma W v ∧ HasZeroTraceDifferenceOn W v uD := by
  have : IsFiniteMeasure (volumeMeasureOn W) := hW.isFiniteMeasure_restrict_volume
  have hFlux : MemVectorL2 W (fun x => matVecMul (scalarCoeffField sigma x) (uD.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll uD.grad_memVectorL2
  have hg : MemVectorL2 W (fun x => -matVecMul (scalarCoeffField sigma x) (uD.grad x)) :=
    hFlux.neg
  have hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization W :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hW
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := scalarCoeffField sigma) (U := W)
      (g := fun x => -matVecMul (scalarCoeffField sigma x) (uD.grad x))
      (lam := lam) (Lam := Lam) hg hRealize hne hEll
  refine ⟨uD + w.toH1Function, ?_, ⟨w, fun _ => rfl, fun _ => rfl⟩⟩
  intro φ
  have hwφ := hw φ
  have hdatum :
      IntegrableOn
        (fun x => vecDot (matVecMul (scalarCoeffField sigma x) (uD.grad x))
          (φ.toH1Function.grad x)) W :=
    integrableOn_vecDot_of_memVectorL2 hFlux φ.toH1Function.grad_memVectorL2
  have hcorrFlux :
      MemVectorL2 W
        (fun x => matVecMul (scalarCoeffField sigma x) (w.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1Function.grad_memVectorL2
  have hcorr :
      IntegrableOn
        (fun x => vecDot (matVecMul (scalarCoeffField sigma x) (w.toH1Function.grad x))
          (φ.toH1Function.grad x)) W :=
    integrableOn_vecDot_of_memVectorL2 hcorrFlux φ.toH1Function.grad_memVectorL2
  have hsplit :
      (fun x => vecDot (sigma x • (uD + w.toH1Function).grad x)
          (φ.toH1Function.grad x)) =
        fun x =>
          vecDot (matVecMul (scalarCoeffField sigma x) (uD.grad x))
              (φ.toH1Function.grad x) +
            vecDot (matVecMul (scalarCoeffField sigma x) (w.toH1Function.grad x))
              (φ.toH1Function.grad x) := by
    funext x
    rw [vecDot_matVecMul_scalarCoeffField, vecDot_matVecMul_scalarCoeffField]
    simp [H1Function.add_grad, smul_add, vecDot_add_left]
  rw [hsplit, integral_add hdatum hcorr, hwφ]
  have hneg :
      ∫ x in W, vecDot (-matVecMul (scalarCoeffField sigma x) (uD.grad x))
          (φ.toH1Function.grad x) ∂volume =
        -∫ x in W, vecDot (matVecMul (scalarCoeffField sigma x) (uD.grad x))
          (φ.toH1Function.grad x) ∂volume := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [vecDot_neg_left])
  rw [hneg, add_neg_cancel]

/-- **Existence for the constant coefficient `1` harmonic approximation
shape.**  This is the first clause of the section 6 harmonic approximation
theorem. -/
theorem exists_isWeaklyHarmonicOn_one_and_hasZeroTraceDifferenceOn {d : ℕ}
    [NeZero d] {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    (hne : W.Nonempty)
    (uD : H1Function W) :
    ∃ v : H1Function W,
      IsWeaklyHarmonicOn (fun _ => 1) W v ∧ HasZeroTraceDifferenceOn W v uD :=
  exists_isWeaklyHarmonicOn_and_hasZeroTraceDifferenceOn hW hne
    (isEllipticFieldOn_scalarCoeffField_const hW.isOpen.measurableSet one_pos) uD

/-! ### The section 6 harmonic approximation window -/

/-- Existence on a translated paper cube, in the exact shape of the first
clause of the section 6 harmonic approximation theorem. -/
theorem exists_isWeaklyHarmonicOn_one_translatedCube {d : ℕ} [NeZero d] (m : ℤ)
    (z : Vec d) (uD : H1Function (translatedCube d m z)) :
    ∃ v : H1Function (translatedCube d m z),
      IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d m z) v ∧
        HasZeroTraceDifferenceOn (translatedCube d m z) v uD :=
  exists_isWeaklyHarmonicOn_one_and_hasZeroTraceDifferenceOn
    (isOpenBoundedConvexDomain_translatedCube m z) (translatedCube_nonempty m z) uD

/-- A.e. uniqueness on a translated paper cube, in the exact shape of the
second clause of the section 6 harmonic approximation theorem. -/
theorem ae_eq_of_isWeaklyHarmonicOn_one_translatedCube {d : ℕ} [NeZero d]
    (m : ℤ) (z : Vec d) {v v' uD : H1Function (translatedCube d m z)}
    (hv : IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d m z) v)
    (hvD : HasZeroTraceDifferenceOn (translatedCube d m z) v uD)
    (hv' : IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d m z) v')
    (hv'D : HasZeroTraceDifferenceOn (translatedCube d m z) v' uD) :
    v.toFun =ᵐ[volume.restrict (translatedCube d m z)] v'.toFun ∧
      v.grad =ᵐ[volume.restrict (translatedCube d m z)] v'.grad :=
  ae_eq_of_isWeaklyHarmonicOn_one_of_hasZeroTraceDifferenceOn
    (isOpenBoundedConvexDomain_translatedCube m z) (translatedCube_nonempty m z)
    hv hvD hv' hv'D

end

end SubdiffusiveProcess.CoarseGrainingVocab
