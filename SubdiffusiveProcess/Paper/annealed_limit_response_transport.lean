module

public import SubdiffusiveProcess.Paper.stationary_family
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.CoarseGrainingVocab.AhomStarCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.RestrictedCoefficientSigma
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixVariational
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.AnnealedDualMeanDefect
public import Homogenization.Book.Ch02.Matrices
public import Mathlib.Tactic
public import Homogenization.Book.Ch02.Dilation
public import Homogenization.Book.Ch04.Theorems.CoarseObservables
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixVariational
public import Homogenization.Book.Ch04.Theorems.DilationResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CutoffDirichletExistence
public import Homogenization.Internal.Ch02.MatrixExtraction
public import Homogenization.Internal.Ch02.Adapters
public import Homogenization.CoarseGraining.Symmetric.Response
public import Homogenization.Geometry.ConvexDomain
public import SubdiffusiveProcess.Geometry.UpstreamCube
public import SubdiffusiveProcess.Lane4.Bridge

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

noncomputable def aux_annealed_limit_response_transport_scalarRegCoeffField
    {d : ℕ} (f : C(SpatialCoordinates d, ℝ)) : RegCoeffField d where
  toFun x := scalarMatrix (f x)
  entry_measurable := by
    intro i j
    have hf : Continuous (fun x : SpatialCoordinates d =>
        scalarMatrix (f x) i j) := by
      exact (continuous_apply j).comp ((continuous_apply i).comp
        (f.continuous.smul (continuous_const : Continuous (fun _ : SpatialCoordinates d =>
          (1 : Mat d)))))
    exact hf.measurable
  entry_locInt := by
    intro i j
    have hf : Continuous (fun x : SpatialCoordinates d =>
        scalarMatrix (f x) i j) := by
      exact (continuous_apply j).comp ((continuous_apply i).comp
        (f.continuous.smul (continuous_const : Continuous (fun _ : SpatialCoordinates d =>
          (1 : Mat d)))))
    exact hf.locallyIntegrable

@[simp] theorem aux_annealed_limit_response_transport_scalarRegCoeffField_apply
    {d : ℕ} (f : C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) :
    aux_annealed_limit_response_transport_scalarRegCoeffField f x =
      scalarMatrix (f x) := rfl

theorem aux_annealed_limit_response_transport_measurable_scalarRegCoeffField
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    Measurable (aux_annealed_limit_response_transport_scalarRegCoeffField
      (d := d)) := by
  refine measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    have hy : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f y) :=
      (continuous_eval_const y).measurable
    simpa [aux_annealed_limit_response_transport_scalarRegCoeffField,
      scalarMatrix] using! hy.mul measurable_const
  · intro i j φ hφ
    let F : C(SpatialCoordinates d, ℝ) × SpatialCoordinates d → ℝ := fun z =>
      scalarMatrix (z.1 z.2) i j * φ z.2
    have heval : Measurable (fun z : C(SpatialCoordinates d, ℝ) ×
        SpatialCoordinates d => z.1 z.2) :=
      ContinuousEval.continuous_eval.measurable
    have hmat' : Measurable (fun z : C(SpatialCoordinates d, ℝ) ×
        SpatialCoordinates d => (z.1 z.2) • (1 : Mat d)) := by
      exact heval.smul
        (measurable_const : Measurable (fun _ : C(SpatialCoordinates d, ℝ) ×
          SpatialCoordinates d => (1 : Mat d)))
    have hmat : Measurable (fun z : C(SpatialCoordinates d, ℝ) ×
        SpatialCoordinates d => scalarMatrix (d := d) (z.1 z.2)) := by
      simpa only [scalarMatrix] using! hmat'
    have hF : Measurable F := by
      exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        hmat)).mul
        (hφ.measurable.comp measurable_snd)
    have hInt : StronglyMeasurable (fun f : C(SpatialCoordinates d, ℝ) =>
        ∫ x, F (f, x) ∂volume) :=
      hF.stronglyMeasurable.integral_prod_right'
    simpa [F, entryTestR,
      aux_annealed_limit_response_transport_scalarRegCoeffField] using! hInt.measurable

theorem aux_annealed_limit_response_transport_scalarRegCoeffField_elliptic
    {d : ℕ} (f : C(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 < f x) :
    Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (aux_annealed_limit_response_transport_scalarRegCoeffField f) := by
  classical
  intro Q
  let W : Set (SpatialCoordinates d) := openCubeSet Q
  have hgeom := isOpenBoundedConvexDomain_openCubeSet Q
  have hcompact : IsCompact (closure W) :=
    hgeom.isBoundedDomain.isBounded.isCompact_closure
  have hne : (closure W).Nonempty := by
    refine ⟨fun i => (Q.index i : ℝ) * cubeScaleFactor Q, ?_⟩
    have hs : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using!
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    exact subset_closure (by
      intro i
      constructor <;> linarith)
  obtain ⟨xmin, hxmin, hmin⟩ :=
    hcompact.exists_isMinOn hne f.continuous.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    hcompact.exists_isMaxOn hne f.continuous.continuousOn
  have hminpos : 0 < f xmin := hf xmin
  have hminmax : f xmin ≤ f xmax := hmin hxmax
  have hmeas : Measurable (fun x : SpatialCoordinates d =>
      if x ∈ W then f x else 0) := by
    simpa [Set.piecewise] using!
      Measurable.piecewise hgeom.isOpen.measurableSet
        f.continuous.measurable measurable_const
  have hEll : IsEllipticFieldOn (f xmin) (f xmax) W
      (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField f) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds
      hminpos hmeas (fun x hx => hmin (subset_closure hx))
        (fun x hx => hmax (subset_closure hx))
  refine ⟨f xmin, f xmax, hminpos, hminmax, ?_⟩
  change IsAEEllipticFieldOn (f xmin) (f xmax) W
    (aux_annealed_limit_response_transport_scalarRegCoeffField f).toFun
  apply IsAEEllipticFieldOn.of_isEllipticFieldOn
  simpa [W, aux_annealed_limit_response_transport_scalarRegCoeffField,
    SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField] using! hEll

theorem aux_annealed_limit_response_transport_scalar_isEllipticOn
    {d : ℕ} (Q : TriadicCube d) (f : C(SpatialCoordinates d, ℝ))
    (hf : ∀ x, 0 < f x) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (openCubeSet Q)
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField f) := by
  classical
  let W : Set (SpatialCoordinates d) := openCubeSet Q
  have hgeom := isOpenBoundedConvexDomain_openCubeSet Q
  have hcompact : IsCompact (closure W) :=
    hgeom.isBoundedDomain.isBounded.isCompact_closure
  have hne : (closure W).Nonempty := by
    refine ⟨fun i => (Q.index i : ℝ) * cubeScaleFactor Q, ?_⟩
    have hs : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using!
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    exact subset_closure (by
      intro i
      constructor <;> linarith)
  obtain ⟨xmin, hxmin, hmin⟩ :=
    hcompact.exists_isMinOn hne f.continuous.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    hcompact.exists_isMaxOn hne f.continuous.continuousOn
  have hminpos : 0 < f xmin := hf xmin
  have hminmax : f xmin ≤ f xmax := hmin hxmax
  have hmeas : Measurable (fun x : SpatialCoordinates d =>
      if x ∈ W then f x else 0) := by
    simpa [Set.piecewise] using!
      Measurable.piecewise hgeom.isOpen.measurableSet
        f.continuous.measurable measurable_const
  have hEll : IsEllipticFieldOn (f xmin) (f xmax) W
      (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField f) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds
      hminpos hmeas (fun x hx => hmin (subset_closure hx))
        (fun x hx => hmax (subset_closure hx))
  exact ⟨f xmin, f xmax, hminpos, hminmax, by simpa [W] using! hEll⟩

theorem aux_annealed_limit_response_transport_sigma_entry_response
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (f : C(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 < f x)
    (a : Homogenization.Book.Ch02.CoeffOn
      (Homogenization.Book.Ch02.cubeDomain Q))
    (ha : ∀ x, a.toCoeffField x = scalarMatrix (f x))
    (i j : Fin d) :
    Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain Q) a i j =
      if i = j then
        2 * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q (Pi.single i 1) 0
            (aux_annealed_limit_response_transport_scalarRegCoeffField f)
      else
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q (Pi.single i 1 + Pi.single j 1) 0
              (aux_annealed_limit_response_transport_scalarRegCoeffField f) -
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q (Pi.single i 1) 0
              (aux_annealed_limit_response_transport_scalarRegCoeffField f) -
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q (Pi.single j 1) 0
              (aux_annealed_limit_response_transport_scalarRegCoeffField f) := by
  let r := aux_annealed_limit_response_transport_scalarRegCoeffField f
  have hr : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField r :=
    aux_annealed_limit_response_transport_scalarRegCoeffField_elliptic f hf
  let ac := Homogenization.Book.Ch04.coeffOnOfAEEllipticOn r Q (hr Q)
  have hae : CoeffOn.AEEq a ac := by
    change a.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] ac.toCoeffField
    filter_upwards [] with x
    rw [ha x]
    rfl
  have hconv := isOpenBoundedConvexDomain_openCubeSet Q
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hconv.isFiniteMeasure_restrict_volume
  obtain ⟨lam, Lam, hlam, hLam, hEll⟩ :=
    aux_annealed_limit_response_transport_scalar_isEllipticOn Q f hf
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨R, sigma0, hcompat, hA, hSInv, hS, hK, hSigma, hCanon⟩ :=
    Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      hconv hEll hvol
  have hk : Homogenization.kappaCoarse (openCubeSet Q) r.toFun = 0 := by
    apply kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    · exact fun x => scalarMatrix_isSymm _
    · exact hA
  have hk' : Homogenization.Book.Ch02.kappaCoarse
      (Homogenization.Book.Ch02.cubeDomain Q) ac = 0 := by
    rw [Homogenization.Internal.Ch02.book_kappaCoarse_eq_kappaCoarse]
    simpa [ac] using! hk
  have hkappa' : Homogenization.Book.Ch02.sigmaStarInvKappaCoarse
      (Homogenization.Book.Ch02.cubeDomain Q) ac = 0 := by
    rw [Homogenization.Internal.Ch02.book_sigmaStarInvKappaCoarse_eq_sigmaStarInvKappaCoarse]
    apply sigmaStarInvKappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    · exact fun x => scalarMatrix_isSymm _
    · exact hA
  have hresp (p : SpatialCoordinates d) :
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p 0 r =
        Homogenization.Book.Ch02.responseJ
          (Homogenization.Book.Ch02.cubeDomain Q) ac p 0 := by
    change ResponseJ (cubeSet Q) p 0 r.toFun =
      ResponseJ (openCubeSet Q) p 0 ac.toCoeffField
    rw [responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p 0 r.toFun]
    rfl
  have hcanonical (p : SpatialCoordinates d) :
      Homogenization.Book.Ch02.canonicalSigmaCorrectedResponse
          (Homogenization.Book.Ch02.cubeDomain Q) ac p =
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p 0 r := by
    unfold Homogenization.Book.Ch02.canonicalSigmaCorrectedResponse
    rw [hresp p]
    simp [Homogenization.Book.Ch02.kappaCoarse, hk', hkappa', matVecMul,
      vecDot]
  rw [Homogenization.Book.Ch02.sigmaCoarse_eq_ofAEEq hae]
  by_cases hij : i = j
  · subst j
    simp [r, Homogenization.Book.Ch02.sigmaCoarse,
      Homogenization.Book.Ch02.sigmaEntry, hcanonical]
  · simp [Homogenization.Book.Ch02.sigmaCoarse,
      Homogenization.Book.Ch02.sigmaEntry, hij, hcanonical, r]

theorem aux_annealed_limit_response_transport_star_entry_response
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (f : C(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 < f x)
    (a : Homogenization.Book.Ch02.CoeffOn
      (Homogenization.Book.Ch02.cubeDomain Q))
    (ha : ∀ x, a.toCoeffField x = scalarMatrix (f x))
    (i j : Fin d) :
    Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain Q) a i j =
      if i = j then
        2 * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q 0 (Pi.single i 1)
            (aux_annealed_limit_response_transport_scalarRegCoeffField f)
      else
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q 0 (Pi.single i 1 + Pi.single j 1)
              (aux_annealed_limit_response_transport_scalarRegCoeffField f) -
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q 0 (Pi.single i 1)
              (aux_annealed_limit_response_transport_scalarRegCoeffField f) -
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q 0 (Pi.single j 1)
              (aux_annealed_limit_response_transport_scalarRegCoeffField f) := by
  let r := aux_annealed_limit_response_transport_scalarRegCoeffField f
  have hr : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField r :=
    aux_annealed_limit_response_transport_scalarRegCoeffField_elliptic f hf
  let ac := Homogenization.Book.Ch04.coeffOnOfAEEllipticOn r Q (hr Q)
  have hae : CoeffOn.AEEq a ac := by
    change a.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] ac.toCoeffField
    filter_upwards [] with x
    rw [ha x]
    rfl
  have hresp (q : SpatialCoordinates d) :
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q 0 q r =
        Homogenization.Book.Ch02.responseJ
          (Homogenization.Book.Ch02.cubeDomain Q) ac 0 q := by
    change ResponseJ (cubeSet Q) 0 q r.toFun =
      ResponseJ (openCubeSet Q) 0 q ac.toCoeffField
    rw [responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q 0 q r.toFun]
    rfl
  have hresp' (q : SpatialCoordinates d) :
      Homogenization.Book.Ch02.responseJ
          (Homogenization.Book.Ch02.cubeDomain Q) ac 0 q =
        ResponseJ (cubeSet Q) 0 q r.toFun := (hresp q).symm
  rw [Homogenization.Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hae]
  by_cases hij : i = j
  · subst j
    simp [r, Homogenization.Book.Ch02.sigmaStarInvCoarse,
      Homogenization.Book.Ch02.sigmaStarInvEntry, hresp']
  · simp [r, Homogenization.Book.Ch02.sigmaStarInvCoarse,
      Homogenization.Book.Ch02.sigmaStarInvEntry, hij, hresp']

theorem aux_annealed_limit_response_transport_response_p_zero_smul
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    (lam : ℝ) (hlam : 0 < lam) (p : Vec d) :
    Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q p 0 (lam • a) =
      lam * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q p 0 a := by
  change ResponseJ (cubeSet Q) p 0 (lam • a.toFun) =
    lam * ResponseJ (cubeSet Q) p 0 a.toFun
  have hcoef : ResponseJ (cubeSet Q) p 0 (lam • a.toFun) =
      ResponseJ (cubeSet Q) (Real.sqrt lam • p) 0 a.toFun := by
    simpa using! responseJ_homogeneous_coeffField (cubeSet Q) p 0 a.toFun hlam
  rw [hcoef]
  have hsqrt : Real.sqrt lam ≠ 0 := Real.sqrt_ne_zero'.mpr hlam
  have hhom := responseJ_homogeneous (cubeSet Q) p 0 a.toFun hsqrt
  rw [show ResponseJ (cubeSet Q) (Real.sqrt lam • p) 0 a.toFun =
      (Real.sqrt lam) ^ 2 * ResponseJ (cubeSet Q) p 0 a.toFun by
        simpa using! hhom]
  rw [Real.sq_sqrt (le_of_lt hlam)]

theorem aux_annealed_limit_response_transport_response_zero_q_smul
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    (lam : ℝ) (hlam : 0 < lam) (q : Vec d) :
    Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q 0 q (lam • a) =
      lam⁻¹ * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q 0 q a := by
  change ResponseJ (cubeSet Q) 0 q (lam • a.toFun) =
    lam⁻¹ * ResponseJ (cubeSet Q) 0 q a.toFun
  have hcoef : ResponseJ (cubeSet Q) 0 q (lam • a.toFun) =
      ResponseJ (cubeSet Q) 0 ((Real.sqrt lam)⁻¹ • q) a.toFun := by
    simpa using! responseJ_homogeneous_coeffField (cubeSet Q) 0 q a.toFun hlam
  rw [hcoef]
  have hsqrt : Real.sqrt lam ≠ 0 := Real.sqrt_ne_zero'.mpr hlam
  have hhom := responseJ_homogeneous (cubeSet Q) 0 q a.toFun (inv_ne_zero hsqrt)
  rw [show ResponseJ (cubeSet Q) 0 ((Real.sqrt lam)⁻¹ • q) a.toFun =
      ((Real.sqrt lam)⁻¹) ^ 2 * ResponseJ (cubeSet Q) 0 q a.toFun by
        simpa using! hhom]
  rw [inv_pow, Real.sq_sqrt (le_of_lt hlam)]

theorem aux_annealed_limit_response_transport_source_p_zero_quadratic
    {d : ℕ} [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (p : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q p 0 (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega) =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix model L
            (Homogenization.Book.Ch02.cubeDomain Q) omega) p) := by
  let U := Homogenization.Book.Ch02.cubeDomain Q
  let data := SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData model L omega U
  have hmu := SubdiffusiveProcess.CoarseGrainingVocab.cutoffMu_primal_eq_randomAMatrix_quadratic
    model L U p omega
  calc
    Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q p 0 (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega) =
        Mu (cubeSet Q) (-p, 0)
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega).toFun -
          vecDot p 0 := by
      simpa [U, data, SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField,
        SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
        SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField] using!
        (Homogenization.Book.Ch02.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot
          Q data.toCoeffOn p 0)
    _ = Mu (U : Set (Vec d)) (-p, 0) data.toCoeffOn.toCoeffField - vecDot p 0 := by
      have hset : (U : Set (Vec d)) = openCubeSet Q := by
        simp [U]
      have hfun :
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega).toFun =
            data.toCoeffOn.toCoeffField := by
        funext x
        rfl
      rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube Q (-p, 0)
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega).toFun,
        hset, hfun]
    _ = (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix model L U omega) p) := by
      rw [vecDot_zero_right, sub_zero]
      simpa [data, SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
        SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField] using! hmu

theorem aux_annealed_limit_response_transport_source_zero_q_quadratic
    {d : ℕ} [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (q : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q 0 q (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega) =
      (1 / 2 : ℝ) * vecDot q
        (matVecMul
          ((SubdiffusiveProcess.CoarseGrainingVocab.randomAStarMatrix model L
            (Homogenization.Book.Ch02.cubeDomain Q) omega)⁻¹) q) := by
  let U := Homogenization.Book.Ch02.cubeDomain Q
  let data := SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData model L omega U
  have hmu := SubdiffusiveProcess.CoarseGrainingVocab.cutoffMu_dual_eq_randomAStarInv_quadratic
    model L U q omega
  calc
    Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q 0 q (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega) =
        Mu (cubeSet Q) (0, q)
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega).toFun := by
      have hfun :
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega).toFun =
            data.toCoeffOn.toCoeffField := by
        funext x
        rfl
      calc
        Homogenization.ResponseJ (cubeSet Q) 0 q
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega).toFun =
            Homogenization.ResponseJ (cubeSet Q) 0 q
              data.toCoeffOn.toCoeffField := by rw [hfun]
        _ = Mu (cubeSet Q) (-0, q) data.toCoeffOn.toCoeffField - vecDot 0 q :=
          Homogenization.Book.Ch02.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot
            Q data.toCoeffOn 0 q
        _ = Mu (cubeSet Q) (0, q) data.toCoeffOn.toCoeffField := by simp [vecDot]
    _ = Mu (U : Set (Vec d)) (0, q) data.toCoeffOn.toCoeffField := by
      have hset : (U : Set (Vec d)) = openCubeSet Q := by
        simp [U]
      rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube Q (0, q)
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model L omega).toFun,
        hset]
      rfl
    _ = (1 / 2 : ℝ) * vecDot q
        (matVecMul
          ((SubdiffusiveProcess.CoarseGrainingVocab.randomAStarMatrix model L U omega)⁻¹) q) := hmu

theorem aux_annealed_limit_response_transport_integrable_rescaled_primal
    {d : ℕ} [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (Q : Homogenization.TriadicCube d) (p : Homogenization.Vec d) :
    Integrable
      (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q p 0 (Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)))
      model.P.toMeasure := by
  let Qd := Homogenization.Book.Ch02.dilateCube (N : ℤ) Q
  have hquad := SubdiffusiveProcess.CoarseGrainingVocab.integrable_randomAMatrix_quadratic
    model N (Homogenization.Book.Ch02.cubeDomain Qd) p
  apply hquad.congr
  exact Filter.Eventually.of_forall (fun omega => by
    have ha := SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField_aeLocallyUniformlyEllipticField
      model N omega
    calc
      (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix model N
              (Homogenization.Book.Ch02.cubeDomain Qd) omega) p) =
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Qd p 0 (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega) :=
        (aux_annealed_limit_response_transport_source_p_zero_quadratic
          model N Qd p omega).symm
      _ = Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p 0 (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)) := by
        symm
        simpa [Qd] using!
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_rescaleCoeffField_of_aelocallyUniformlyElliptic
            ha N Q p 0)

theorem aux_annealed_limit_response_transport_integrable_rescaled_dual
    {d : ℕ} [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (Q : Homogenization.TriadicCube d) (q : Homogenization.Vec d) :
    Integrable
      (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q 0 q (Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)))
      model.P.toMeasure := by
  let Qd := Homogenization.Book.Ch02.dilateCube (N : ℤ) Q
  have hmat := SubdiffusiveProcess.CoarseGrainingVocab.integrable_randomAStarMatrix_inv
    model N (Homogenization.Book.Ch02.cubeDomain Qd)
  have hquad : Integrable (fun omega => (1 / 2 : ℝ) * Homogenization.vecDot q
      (Homogenization.matVecMul
        ((SubdiffusiveProcess.CoarseGrainingVocab.randomAStarMatrix model N
          (Homogenization.Book.Ch02.cubeDomain Qd) omega)⁻¹) q))
      model.P.toMeasure := by
    apply Integrable.const_mul
    simp only [Homogenization.vecDot, Homogenization.matVecMul]
    apply integrable_finset_sum Finset.univ
    intro i _hi
    apply Integrable.const_mul
    apply integrable_finset_sum Finset.univ
    intro j _hj
    exact (((hmat.eval i).eval j).mul_const (q j))
  apply hquad.congr
  exact Filter.Eventually.of_forall (fun omega => by
    have ha := SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField_aeLocallyUniformlyEllipticField
      model N omega
    calc
      (1 / 2 : ℝ) * Homogenization.vecDot q
          (Homogenization.matVecMul
            ((SubdiffusiveProcess.CoarseGrainingVocab.randomAStarMatrix model N
              (Homogenization.Book.Ch02.cubeDomain Qd) omega)⁻¹) q) =
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Qd 0 q (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega) :=
        (aux_annealed_limit_response_transport_source_zero_q_quadratic
          model N Qd q omega).symm
      _ = Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q 0 q (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)) := by
        symm
        simpa [Qd] using!
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_rescaleCoeffField_of_aelocallyUniformlyElliptic
            ha N Q 0 q)

theorem aux_annealed_limit_response_transport_positive_field_law
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    ProbabilityTheory.IdentDistrib
      (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        (⟨fun x => Real.exp (∑ i : Fin (N + 1),
            ((omega (i : ℕ)).1.1) x -
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P), by continuity⟩ :
          C(SpatialCoordinates d, ℝ)))
      (fun omega : BilateralField d =>
        (⟨fun x => Real.exp (∑ i : Fin (N + 1),
            (omega (i : ℤ)) x -
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P), by continuity⟩ :
          C(SpatialCoordinates d, ℝ)))
      model.P.toMeasure (chaosSampleLaw model).toMeasure := by
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
    chaosRootFieldLaw model
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let X : (i : Fin (N + 1)) →
      SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → C(SpatialCoordinates d, ℝ) :=
    fun i omega => forget (omega (i : ℕ))
  let Y : (i : Fin (N + 1)) → BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun i omega => omega (i : ℤ)
  have hXY : ∀ i : Fin (N + 1),
      ProbabilityTheory.IdentDistrib (X i) (Y i)
        model.P.toMeasure (chaosSampleLaw model).toMeasure := by
    intro i
    have hforget : Measurable forget := forget.continuous.measurable
    have hcoord := SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate
      (d := d) (i : ℕ)
    have hsource : Measurable (X i) := hforget.comp hcoord
    have htarget : Measurable (Y i) := measurable_pi_apply (i : ℤ)
    have hmarg := SubdiffusiveProcess.gmc_marginal_field_law_eq_scaledLayerLaw
      model (i : ℕ)
    have hmarg' : Measure.map (X i) model.P.toMeasure = laws (i : ℤ) := by
      change Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        forget (omega (i : ℕ))) model.P.toMeasure = _
      rw [show Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          forget (omega (i : ℕ))) model.P.toMeasure =
          Measure.map forget
            (Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
              omega (i : ℕ)) model.P.toMeasure) by
        exact (Measure.map_map hforget hcoord).symm]
      have hmargMeasure := congrArg ProbabilityMeasure.toMeasure hmarg
      simpa [SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw, ν, laws,
        chaosRootFieldLaw] using! hmargMeasure
    have htarget' : Measure.map (Y i) (chaosSampleLaw model).toMeasure =
        laws (i : ℤ) := by
      change Measure.map (fun omega : BilateralField d => omega (i : ℤ))
        (Measure.infinitePi laws) = laws (i : ℤ)
      exact Measure.infinitePi_map_eval laws (i : ℤ)
    exact ⟨hsource.aemeasurable, htarget.aemeasurable,
      hmarg'.trans htarget'.symm⟩
  have hbaseP : ProbabilityTheory.iIndepFun
      (fun j : ℕ => fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        forget (omega j)) model.P.toMeasure := by
    exact model.shellPrefix.independent.comp
      (fun _ : ℕ => forget) (fun _ => forget.continuous.measurable)
  have hinj : Function.Injective (fun i : Fin (N + 1) => (i : ℕ)) := by
    intro i j hij
    exact Fin.ext hij
  have hXind : ProbabilityTheory.iIndepFun X model.P.toMeasure := by
    simpa only [X] using! hbaseP.precomp hinj
  have hbaseY : ProbabilityTheory.iIndepFun
      (fun j : ℤ => fun omega : BilateralField d => omega j)
      (Measure.infinitePi laws) :=
    ProbabilityTheory.iIndepFun_infinitePi
      (P := laws) (X := fun _ : ℤ => fun x : C(SpatialCoordinates d, ℝ) => x)
      (fun _ => measurable_id)
  have hinjZ : Function.Injective (fun i : Fin (N + 1) => (i : ℤ)) := by
    intro i j hij
    exact Fin.ext (Int.ofNat_inj.mp hij)
  have hYind : ProbabilityTheory.iIndepFun Y (Measure.infinitePi laws) := by
    simpa only [Y] using! hbaseY.precomp hinjZ
  have hfamily := ProbabilityTheory.IdentDistrib.pi hXY hXind hYind
  let sumCM : ((i : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) →
      C(SpatialCoordinates d, ℝ) := fun q =>
    ⟨fun x => Real.exp (∑ i : Fin (N + 1), q i x -
      SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P), by continuity⟩
  have hsum : Continuous (fun q : (i : Fin (N + 1)) →
      C(SpatialCoordinates d, ℝ) =>
      ∑ i : Fin (N + 1), q i) := by
    apply continuous_finset_sum
    intro i hi
    exact continuous_apply i
  let expCM : C(ℝ, ℝ) := ⟨Real.exp, Real.continuous_exp⟩
  let tauCM : C(SpatialCoordinates d, ℝ) :=
    ⟨fun _ => SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P, continuous_const⟩
  have hexp : Continuous (fun q : (i : Fin (N + 1)) →
      C(SpatialCoordinates d, ℝ) =>
      expCM.comp ((∑ i : Fin (N + 1), q i) - tauCM)) := by
    apply (ContinuousMap.continuous_postcomp expCM).comp
    exact hsum.sub continuous_const
  have hsum_meas : Measurable sumCM := by
    apply Continuous.measurable
    convert hexp using 1 <;> ext q x <;> simp [sumCM, expCM, tauCM]
  have hpost := hfamily.comp hsum_meas
  have hleft : (fun omega => sumCM (fun i => X i omega)) =
      (fun omega =>
        (⟨fun x => Real.exp (∑ i : Fin (N + 1),
            ((omega (i : ℕ)).1.1) x -
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P), by continuity⟩ :
          C(SpatialCoordinates d, ℝ))) := by
    funext omega
    rfl
  have hright : (fun omega => sumCM (fun i => Y i omega)) =
      (fun omega : BilateralField d =>
        (⟨fun x => Real.exp (∑ i : Fin (N + 1),
            (omega (i : ℤ)) x -
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P), by continuity⟩ :
          C(SpatialCoordinates d, ℝ))) := by
    funext omega
    rfl
  refine { aemeasurable_fst := ?_, aemeasurable_snd := ?_, map_eq := ?_ }
  · exact hpost.aemeasurable_fst.congr (Filter.Eventually.of_forall
      (fun omega => congrArg sumCM rfl))
  · exact hpost.aemeasurable_snd.congr (Filter.Eventually.of_forall
      (fun omega => congrArg sumCM rfl))
  · rw [← hleft, ← hright]
    exact hpost.map_eq

theorem aux_annealed_limit_response_transport_normalized_field_law
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    ProbabilityTheory.IdentDistrib
      (fun omega : BilateralField d =>
        (⟨fun x =>
          (Real.exp (((N : ℝ) + 1) *
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            Real.exp (∑ j ∈ Finset.range (N + 1),
              omega (-(j : ℤ)) x), by continuity⟩ :
          C(SpatialCoordinates d, ℝ)))
      (fun omega : BilateralField d =>
        (⟨fun x =>
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            Real.exp (∑ j ∈ Finset.range (N + 1),
              (omega (j : ℤ) ((3 : ℝ) ^ N • x) -
                SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)), by
          apply continuous_const.mul
          apply Real.continuous_exp.comp
          apply continuous_finset_sum
          intro j hj
          apply Continuous.sub
          · exact (omega (j : ℤ)).continuous.comp
              ((continuous_const : Continuous (fun _ : SpatialCoordinates d => (3 : ℝ) ^ N)).smul continuous_id)
          · exact continuous_const⟩ :
          C(SpatialCoordinates d, ℝ)))
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
    chaosRootFieldLaw model
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let dilate : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ
      (⟨fun y : SpatialCoordinates d => (3 : ℝ) ^ N • y,
        ((continuous_const : Continuous (fun _ : SpatialCoordinates d => (3 : ℝ) ^ N)).smul continuous_id)⟩ :
        C(SpatialCoordinates d, SpatialCoordinates d))
  let X : (i : Fin (N + 1)) → BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun i omega => omega (-(i : ℤ))
  let Y : (i : Fin (N + 1)) → BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun i omega => dilate (omega ((N : ℤ) - (i : ℤ)))
  have hXY : ∀ i : Fin (N + 1),
      ProbabilityTheory.IdentDistrib (X i) (Y i)
        (Measure.infinitePi laws) (Measure.infinitePi laws) := by
    intro i
    simpa only [X, Y, dilate, ν, chaosRootFieldLaw] using!
      (Paper.aux_stationary_family_relabelled_coordinate d N ν i)
  have hbase : ProbabilityTheory.iIndepFun
      (fun j : ℤ => fun omega : BilateralField d => omega j)
      (Measure.infinitePi laws) :=
    ProbabilityTheory.iIndepFun_infinitePi
      (P := laws) (X := fun _ : ℤ => fun x : C(SpatialCoordinates d, ℝ) => x)
      (fun _ => measurable_id)
  have hneg : Function.Injective (fun i : Fin (N + 1) => -(i : ℤ)) := by
    intro i j hij
    apply Fin.ext
    exact Int.ofNat_inj.mp (Int.neg_inj.mp hij)
  have hshift : Function.Injective (fun i : Fin (N + 1) =>
      (N : ℤ) - (i : ℤ)) := by
    intro i j hij
    apply Fin.ext
    have : (i : ℤ) = (j : ℤ) := by linarith
    exact Int.ofNat_inj.mp this
  have hXind : ProbabilityTheory.iIndepFun X (Measure.infinitePi laws) := by
    simpa only [X] using! hbase.precomp hneg
  have hYbase : ProbabilityTheory.iIndepFun
      (fun i : Fin (N + 1) => fun omega : BilateralField d =>
        omega ((N : ℤ) - (i : ℤ))) (Measure.infinitePi laws) := by
    simpa only using! hbase.precomp hshift
  have hYind : ProbabilityTheory.iIndepFun Y (Measure.infinitePi laws) := by
    have hcomp := hYbase.comp
      (fun _ : Fin (N + 1) => dilate)
      (fun _ => dilate.continuous.measurable)
    simpa only [Y, Function.comp_apply] using! hcomp
  have hfamily := ProbabilityTheory.IdentDistrib.pi hXY hXind hYind
  let c0 : ℝ :=
    (Real.exp (((N : ℝ) + 1) *
      SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹
  let tauCM : C(SpatialCoordinates d, ℝ) :=
    ⟨fun _ => SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P, continuous_const⟩
  let sumCM : ((i : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) →
      C(SpatialCoordinates d, ℝ) := fun q =>
    ⟨fun x => c0 * Real.exp (∑ i : Fin (N + 1), q i x), by continuity⟩
  have hsum : Continuous (fun q : (i : Fin (N + 1)) →
      C(SpatialCoordinates d, ℝ) => ∑ i : Fin (N + 1), q i) := by
    apply continuous_finset_sum
    intro i hi
    exact continuous_apply i
  let expCM : C(ℝ, ℝ) := ⟨Real.exp, Real.continuous_exp⟩
  have hsum_meas : Measurable sumCM := by
    apply Continuous.measurable
    have hinner : Continuous (fun q : (i : Fin (N + 1)) →
        C(SpatialCoordinates d, ℝ) =>
        expCM.comp (∑ i : Fin (N + 1), q i)) :=
      (ContinuousMap.continuous_postcomp expCM).comp hsum
    have heq : sumCM = (fun q => c0 • (expCM.comp (∑ i : Fin (N + 1), q i))) := by
      funext q
      ext x
      simp [sumCM, expCM, c0]
    rw [heq]
    exact (continuous_const (y := c0)).smul hinner
  have hpost := hfamily.comp hsum_meas
  have hsum_reindex (omega : BilateralField d) (x : SpatialCoordinates d) :
      (∑ i : Fin (N + 1), omega ((N : ℤ) - (i : ℤ))
          ((3 : ℝ) ^ N • x)) =
        ∑ j ∈ Finset.range (N + 1), omega (j : ℤ) ((3 : ℝ) ^ N • x) := by
    have hfin :
        (∑ i : Fin (N + 1), omega ((N : ℤ) - (i : ℤ))
            ((3 : ℝ) ^ N • x)) =
          ∑ j ∈ Finset.range (N + 1),
            omega ((N : ℤ) - (j : ℤ)) ((3 : ℝ) ^ N • x) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      rw [dif_pos (Finset.mem_range.mp hj)]
    rw [hfin, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    have hjlt : j < N + 1 := Finset.mem_range.mp hj
    have hjN : j ≤ N := by omega
    have hj' : N + 1 - 1 - j = N - j := by omega
    rw [hj', Int.ofNat_sub hjN]
    congr 2
    ring
  have hleft : (fun omega => sumCM (fun i => X i omega)) =
      (fun omega =>
        (⟨fun x => c0 * Real.exp (∑ j ∈ Finset.range (N + 1),
            omega (-(j : ℤ)) x), by continuity⟩ :
          C(SpatialCoordinates d, ℝ))) := by
    funext omega
    ext x
    change c0 * Real.exp (∑ i : Fin (N + 1), omega (-(i : ℤ)) x) =
      c0 * Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)
    congr 1
    congr 1
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    rw [dif_pos (Finset.mem_range.mp hj)]
  have hright : (fun omega => sumCM (fun i => Y i omega)) =
      (fun omega : BilateralField d =>
        (⟨fun x =>
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            Real.exp (∑ j ∈ Finset.range (N + 1),
              (omega (j : ℤ) ((3 : ℝ) ^ N • x) -
                SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)), by
          apply continuous_const.mul
          apply Real.continuous_exp.comp
          apply continuous_finset_sum
          intro j hj
          apply Continuous.sub
          · exact (omega (j : ℤ)).continuous.comp
              ((continuous_const : Continuous (fun _ : SpatialCoordinates d => (3 : ℝ) ^ N)).smul continuous_id)
          · exact continuous_const⟩ :
          C(SpatialCoordinates d, ℝ))) := by
    funext omega
    ext x
    change c0 * Real.exp (∑ i : Fin (N + 1),
        omega ((N : ℤ) - (i : ℤ)) ((3 : ℝ) ^ N • x)) =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1),
          (omega (j : ℤ) ((3 : ℝ) ^ N • x) -
            SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))
    rw [hsum_reindex]
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [Real.exp_sub]
    have ha : SubdiffusiveProcess.CoarseGrainingVocab.ahom model N ≠ 0 :=
      ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)
    have he : Real.exp (((N : ℝ) + 1) *
        SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    simp [c0, ha, he, Real.exp_neg, mul_assoc, mul_left_comm, mul_comm]
    rw [div_eq_mul_inv]
    ring
  refine { aemeasurable_fst := ?_, aemeasurable_snd := ?_, map_eq := ?_ }
  · rw [← hleft]
    exact hpost.aemeasurable_fst
  · rw [← hright]
    exact hpost.aemeasurable_snd
  · rw [← hleft, ← hright]
    exact hpost.map_eq

theorem aux_annealed_limit_response_transport_exp_sub (n : ℕ) (z τ : ℝ) :
    Real.exp (-(n : ℝ) * τ) * Real.exp (z - τ) =
      Real.exp (z - ((n : ℝ) + 1) * τ) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem aux_annealed_limit_response_transport_exp_range
    (n : ℕ) (f : ℕ → ℝ) (τ : ℝ) :
    Real.exp (-(n : ℝ) * τ) *
        Real.exp (∑ i ∈ Finset.range (n + 1), f i - τ) =
      Real.exp (∑ i ∈ Finset.range (n + 1), (f i - τ)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [← Real.exp_add]
  congr 1
  ring

theorem aux_annealed_limit_response_transport_source_matrix
    {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : SpatialCoordinates d) (c r τ : ℝ)
    (hcr : c * r = Real.exp (-(N : ℝ) * τ))
    (hτ : τ = SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) :
    c • scalarMatrix (d := d)
        (r * Real.exp (∑ i : Fin (N + 1),
          ((omega (i : ℕ)).1.1) x - τ)) =
      scalarMatrix (d := d) (SubdiffusiveProcess.Frozen.Assumptions.aCutoff
        model N omega x) := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.aCutoff_eq_exp_sub]
  rw [← hτ]
  have hsum :
      (∑ i : Fin (N + 1), ((omega (i : ℕ)).1.1) x) =
        ∑ i ∈ Finset.range (N + 1), ((omega i).1.1) x := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
  rw [hsum]
  have hscalar :
      c * (r * Real.exp (∑ i ∈ Finset.range (N + 1),
          ((omega i).1.1) x - τ)) =
        Real.exp (∑ i ∈ Finset.range (N + 1), ((omega i).1.1) x -
          ((N : ℝ) + 1) * τ) := by
    rw [← mul_assoc, hcr]
    have hsumτ :
        (∑ i ∈ Finset.range (N + 1), (((omega i).1.1) x - τ)) =
          ∑ i ∈ Finset.range (N + 1), ((omega i).1.1) x -
            ((N : ℝ) + 1) * τ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const]
      simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [← hsumτ]
    exact aux_annealed_limit_response_transport_exp_range N
      (fun i => ((omega i).1.1) x) τ
  ext i j
  simp only [Matrix.smul_apply, scalarMatrix, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    simpa using! hscalar
  · simp only [hij, if_false]
    ring

theorem aux_annealed_limit_response_transport_source_primal
    {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (Q Q' : Homogenization.TriadicCube d)
    (hresp_rescale : ∀ (p q : Homogenization.Vec d)
      (a : RegCoeffField d),
      Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a →
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p q
            (Homogenization.rescaleReg N a) =
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q' p q a)
    (p : Homogenization.Vec d) :
      (∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p 0
          (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
          ∂model.P.toMeasure) =
        (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
              (Homogenization.Book.Ch02.cubeDomain Q')) p) := by
  have heq :
      (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p 0
          (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))) =
      (fun omega =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q' p 0
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)) := by
    funext omega
    exact hresp_rescale p 0 _
      (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField_aeLocallyUniformlyEllipticField
        model N omega)
  rw [heq]
  calc
    (∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q' p 0
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)
        ∂model.P.toMeasure) =
        ∫ omega, (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix model N
              (Homogenization.Book.Ch02.cubeDomain Q') omega) p)
          ∂model.P.toMeasure := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun omega => by
        simpa only using!
          (aux_annealed_limit_response_transport_source_p_zero_quadratic
            model N Q' p omega))
    _ = (1 / 2 : ℝ) * Homogenization.vecDot p
        (Homogenization.matVecMul
          (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
            (Homogenization.Book.Ch02.cubeDomain Q')) p) := by
      exact SubdiffusiveProcess.CoarseGrainingVocab.integral_randomAMatrix_quadratic
        model N (Homogenization.Book.Ch02.cubeDomain Q') p

theorem aux_annealed_limit_response_transport_source_dual
    {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (Q Q' : Homogenization.TriadicCube d)
    (hresp_rescale : ∀ (p q : Homogenization.Vec d)
      (a : RegCoeffField d),
      Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a →
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p q
            (Homogenization.rescaleReg N a) =
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q' p q a)
    (q : Homogenization.Vec d) :
      (∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
          (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
          ∂model.P.toMeasure) =
        (1 / 2 : ℝ) * Homogenization.vecDot q
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain Q')) q) := by
  have heq :
      (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
          (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))) =
      (fun omega =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q' 0 q
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)) := by
    funext omega
    exact hresp_rescale 0 q _
      (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField_aeLocallyUniformlyEllipticField
        model N omega)
  rw [heq]
  calc
    (∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q' 0 q
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)
        ∂model.P.toMeasure) =
        ∫ omega, (1 / 2 : ℝ) * Homogenization.vecDot q
          (Homogenization.matVecMul
            ((SubdiffusiveProcess.CoarseGrainingVocab.randomAStarMatrix model N
              (Homogenization.Book.Ch02.cubeDomain Q') omega)⁻¹) q)
          ∂model.P.toMeasure := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun omega => by
        simpa only using!
          (aux_annealed_limit_response_transport_source_zero_q_quadratic
            model N Q' q omega))
    _ = (1 / 2 : ℝ) * Homogenization.vecDot q
        (Homogenization.matVecMul
          (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
            (Homogenization.Book.Ch02.cubeDomain Q')) q) := by
      exact SubdiffusiveProcess.CoarseGrainingVocab.integral_randomAStarMatrix_inv_quadratic
        model N (Homogenization.Book.Ch02.cubeDomain Q') q

theorem aux_annealed_limit_response_transport_annealed_responses
    {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (Q Q' : Homogenization.TriadicCube d)
    (fA : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c s : ℝ) (hc : 0 < c) (hcs : c⁻¹ = s)
    (hscaledID : ∀ (p q : Homogenization.Vec d),
      ProbabilityTheory.IdentDistrib
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q (c •
            aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)))
        (chaosSampleLaw model).toMeasure model.P.toMeasure)
    (hsourceP : ∀ (p : Homogenization.Vec d),
      (∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p 0
          (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
          ∂model.P.toMeasure) =
        (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
              (Homogenization.Book.Ch02.cubeDomain Q')) p))
    (hsourceQ : ∀ (q : Homogenization.Vec d),
      (∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
          (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
          ∂model.P.toMeasure) =
        (1 / 2 : ℝ) * Homogenization.vecDot q
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain Q')) q)) :
    (∀ (p : Homogenization.Vec d),
      (∫ omega,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p 0
          (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
          ∂(chaosSampleLaw model).toMeasure) =
        s * ((1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
              (Homogenization.Book.Ch02.cubeDomain Q')) p))) ∧
    (∀ (q : Homogenization.Vec d),
      (∫ omega,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
          (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
          ∂(chaosSampleLaw model).toMeasure) =
        c * ((1 / 2 : ℝ) * Homogenization.vecDot q
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain Q')) q))) := by
  constructor
  · intro p
    have hscaleResp :
        (fun omega =>
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p 0
            (c • aux_annealed_limit_response_transport_scalarRegCoeffField
              (fA omega))) =
        (fun omega => c *
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p 0
            (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))) := by
      funext omega
      exact aux_annealed_limit_response_transport_response_p_zero_smul Q _ c hc p
    have hEq := (hscaledID p 0).integral_eq
    rw [hscaleResp, MeasureTheory.integral_const_mul] at hEq
    rw [hsourceP p] at hEq
    calc
      (∫ omega,
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p 0
            (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
          ∂(chaosSampleLaw model).toMeasure) =
          c⁻¹ * (∫ omega,
            c * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p 0
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
            ∂(chaosSampleLaw model).toMeasure) := by
        rw [MeasureTheory.integral_const_mul]
        field_simp
      _ = c⁻¹ * ((1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
              (Homogenization.Book.Ch02.cubeDomain Q')) p)) := by
        rw [MeasureTheory.integral_const_mul, hEq]
      _ = s * ((1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
              (Homogenization.Book.Ch02.cubeDomain Q')) p)) := by
        rw [hcs]
  · intro q
    have hscaleResp :
        (fun omega =>
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
            (c • aux_annealed_limit_response_transport_scalarRegCoeffField
              (fA omega))) =
        (fun omega => c⁻¹ *
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
            (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))) := by
      funext omega
      exact aux_annealed_limit_response_transport_response_zero_q_smul Q _ c hc q
    have hEq := (hscaledID 0 q).integral_eq
    rw [hscaleResp, MeasureTheory.integral_const_mul] at hEq
    rw [hsourceQ q] at hEq
    calc
      (∫ omega,
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
            (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
          ∂(chaosSampleLaw model).toMeasure) =
          c * (∫ omega,
            c⁻¹ * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
            ∂(chaosSampleLaw model).toMeasure) := by
        rw [MeasureTheory.integral_const_mul]
        field_simp
      _ = c * ((1 / 2 : ℝ) * Homogenization.vecDot q
          (Homogenization.matVecMul
            (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain Q')) q)) := by
        rw [MeasureTheory.integral_const_mul, hEq]



theorem aux_annealed_limit_response_transport_assemble
    {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ)
    (U : Homogenization.Book.Ch02.Domain d)
    (a0 : BilateralField d → Homogenization.Book.Ch02.CoeffOn U)
    (Q Q' : Homogenization.TriadicCube d)
    (fA : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c s : ℝ)
    (hsval : s = (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹)
    (hcval : c = SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)
    (hQ' : Q' = Homogenization.originCube d ((N + k : ℕ) : ℤ))
    (hIntP : ∀ (p : Homogenization.Vec d),
      Integrable
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p 0
          (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
        (chaosSampleLaw model).toMeasure)
    (hIntQ : ∀ (q : Homogenization.Vec d),
      Integrable
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q 0 q
          (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
        (chaosSampleLaw model).toMeasure)
    (hrespP : ∀ (p : Homogenization.Vec d),
      (∫ omega,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p 0
          (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
          ∂(chaosSampleLaw model).toMeasure) =
        s *
          ((1 / 2 : ℝ) * Homogenization.vecDot p
            (Homogenization.matVecMul
              (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
                (Homogenization.Book.Ch02.cubeDomain Q')) p)))
    (hrespQ : ∀ (q : Homogenization.Vec d),
      (∫ omega,
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
          (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
          ∂(chaosSampleLaw model).toMeasure) =
        c *
          ((1 / 2 : ℝ) * Homogenization.vecDot q
            (Homogenization.matVecMul
              (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
                (Homogenization.Book.Ch02.cubeDomain Q')) q)))
    (hsigP : ∀ (omega : BilateralField d) (i j : Fin d),
      Homogenization.Book.Ch02.sigmaCoarse U (a0 omega) i j =
        if i = j then
          2 * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q (Pi.single i 1) 0
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
        else
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q (Pi.single i 1 + Pi.single j 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q (Pi.single i 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q (Pi.single j 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
    (hsigQ : ∀ (omega : BilateralField d) (i j : Fin d),
      Homogenization.Book.Ch02.sigmaStarInvCoarse U (a0 omega) i j =
        if i = j then
          2 * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q 0 (Pi.single i 1)
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
        else
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q 0 (Pi.single i 1 + Pi.single j 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q 0 (Pi.single i 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q 0 (Pi.single j 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))) :
    (∀ i j : Fin d,
      (Integrable (fun omega =>
        Homogenization.Book.Ch02.sigmaCoarse U (a0 omega) i j)
        (chaosSampleLaw model).toMeasure ∧
       Integrable (fun omega =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse U (a0 omega) i j)
        (chaosSampleLaw model).toMeasure)) ∧
    (∀ i j : Fin d,
      (∫ omega, Homogenization.Book.Ch02.sigmaCoarse U (a0 omega) i j
        ∂(chaosSampleLaw model).toMeasure) =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          SubdiffusiveProcess.CoarseGrainingVocab.abar model N
            (Homogenization.Book.Ch02.cubeDomain Q') i j) ∧
    (∀ i j : Fin d,
      (∫ omega, Homogenization.Book.Ch02.sigmaStarInvCoarse U (a0 omega) i j
        ∂(chaosSampleLaw model).toMeasure) =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
          SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
            (Homogenization.Book.Ch02.cubeDomain Q') i j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    constructor
    · by_cases hij : i = j
      · subst j
        have hh := (hIntP (Pi.single i 1)).const_mul (2 : ℝ)
        apply hh.congr
        exact Filter.Eventually.of_forall (fun omega => by
          simpa using! (hsigP omega i i).symm)
      · have hh := ((hIntP (Pi.single i 1 + Pi.single j 1)).sub
          (hIntP (Pi.single i 1))).sub (hIntP (Pi.single j 1))
        apply hh.congr
        exact Filter.Eventually.of_forall (fun omega => by
          simpa [hij] using! (hsigP omega i j).symm)
    · by_cases hij : i = j
      · subst j
        have hh := (hIntQ (Pi.single i 1)).const_mul (2 : ℝ)
        apply hh.congr
        exact Filter.Eventually.of_forall (fun omega => by
          simpa using! (hsigQ omega i i).symm)
      · have hh := ((hIntQ (Pi.single i 1 + Pi.single j 1)).sub
          (hIntQ (Pi.single i 1))).sub (hIntQ (Pi.single j 1))
        apply hh.congr
        exact Filter.Eventually.of_forall (fun omega => by
          simpa [hij] using! (hsigQ omega i j).symm)
  · intro i j
    by_cases hij : i = j
    · subst j
      have hentry := hrespP (Pi.single i 1)
      have hbar := SubdiffusiveProcess.CoarseGrainingVocab.abar_eq_abarScalarReadout_smul_one
        model N (N + k)
      calc
        (∫ omega,
            Homogenization.Book.Ch02.sigmaCoarse U (a0 omega) i i
              ∂(chaosSampleLaw model).toMeasure) =
            2 * (∫ omega,
              Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                (Pi.single i 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
              ∂(chaosSampleLaw model).toMeasure) := by
          rw [← MeasureTheory.integral_const_mul]
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun omega => by
              simpa using! (hsigP omega i i)))
        _ = 2 * (s * ((1 / 2 : ℝ) *
              Homogenization.vecDot (Pi.single i 1)
                (Homogenization.matVecMul
                  (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
                    (Homogenization.Book.Ch02.cubeDomain Q'))
                  (Pi.single i 1)))) := by rw [hrespP]
        _ = (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            SubdiffusiveProcess.CoarseGrainingVocab.abar model N
              (Homogenization.Book.Ch02.cubeDomain Q') i i := by
          rw [hQ']
          rw [hbar]
          rw [vecDot_single_left, matVecMul_single]
          rw [hsval]
          simp [Matrix.smul_apply, Matrix.one_apply]
          ring
    · have hsum := hrespP (Pi.single i 1 + Pi.single j 1)
      have hi := hrespP (Pi.single i 1)
      have hj := hrespP (Pi.single j 1)
      have hbar := SubdiffusiveProcess.CoarseGrainingVocab.abar_eq_abarScalarReadout_smul_one
        model N (N + k)
      calc
        (∫ omega,
            Homogenization.Book.Ch02.sigmaCoarse U (a0 omega) i j
              ∂(chaosSampleLaw model).toMeasure) =
            (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
              (Pi.single i 1 + Pi.single j 1) 0
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
              ∂(chaosSampleLaw model).toMeasure) -
            (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
              (Pi.single i 1) 0
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
              ∂(chaosSampleLaw model).toMeasure) -
            (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
              (Pi.single j 1) 0
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
              ∂(chaosSampleLaw model).toMeasure) := by
          have hsub := (hIntP (Pi.single i 1 + Pi.single j 1)).sub
            (hIntP (Pi.single i 1))
          have hrewrite :
              (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                (Pi.single i 1 + Pi.single j 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                ∂(chaosSampleLaw model).toMeasure) -
              (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                (Pi.single i 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                ∂(chaosSampleLaw model).toMeasure) -
              (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                (Pi.single j 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                ∂(chaosSampleLaw model).toMeasure) =
              (∫ omega,
                (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                  (Pi.single i 1 + Pi.single j 1) 0
                  (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
                Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                  (Pi.single i 1) 0
                  (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))) -
                Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                  (Pi.single j 1) 0
                  (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                ∂(chaosSampleLaw model).toMeasure) := by
            calc
              _ = (∫ omega,
                  (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                    (Pi.single i 1 + Pi.single j 1) 0
                    (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
                  Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                    (Pi.single i 1) 0
                    (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
                  ∂(chaosSampleLaw model).toMeasure) -
                (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
                  (Pi.single j 1) 0
                  (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                  ∂(chaosSampleLaw model).toMeasure) := by
                    rw [MeasureTheory.integral_sub (hIntP (Pi.single i 1 + Pi.single j 1))
                      (hIntP (Pi.single i 1))]
              _ = _ := by
                simpa only [Pi.sub_apply] using!
                  (MeasureTheory.integral_sub hsub (hIntP (Pi.single j 1))).symm
          rw [hrewrite]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall (fun omega => by
            simpa [hij] using! (hsigP omega i j))
        _ = s * ((1 / 2 : ℝ) * Homogenization.vecDot
              (Pi.single i 1 + Pi.single j 1)
              (Homogenization.matVecMul
                (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
                  (Homogenization.Book.Ch02.cubeDomain Q'))
                (Pi.single i 1 + Pi.single j 1))) -
            s * ((1 / 2 : ℝ) * Homogenization.vecDot (Pi.single i 1)
              (Homogenization.matVecMul
                (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
                  (Homogenization.Book.Ch02.cubeDomain Q')) (Pi.single i 1))) -
            s * ((1 / 2 : ℝ) * Homogenization.vecDot (Pi.single j 1)
              (Homogenization.matVecMul
                (SubdiffusiveProcess.CoarseGrainingVocab.abar model N
                  (Homogenization.Book.Ch02.cubeDomain Q')) (Pi.single j 1))) := by
          rw [hrespP, hrespP, hrespP]
        _ = (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            SubdiffusiveProcess.CoarseGrainingVocab.abar model N
              (Homogenization.Book.Ch02.cubeDomain Q') i j := by
          rw [hQ', hbar, hsval]
          rw [basis_sum_pairing, vecDot_single_left, matVecMul_single,
            vecDot_single_left, matVecMul_single]
          simp [Matrix.smul_apply, Matrix.one_apply, hij, Ne.symm hij]
          field_simp
          ring
  · intro i j
    by_cases hij : i = j
    · subst j
      have hentry := hrespQ (Pi.single i 1)
      calc
        (∫ omega,
            Homogenization.Book.Ch02.sigmaStarInvCoarse U (a0 omega) i i
              ∂(chaosSampleLaw model).toMeasure) =
            2 * (∫ omega,
              Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                (Pi.single i 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
              ∂(chaosSampleLaw model).toMeasure) := by
          rw [← MeasureTheory.integral_const_mul]
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun omega => by
              simpa using! (hsigQ omega i i)))
        _ = 2 * (c * ((1 / 2 : ℝ) *
              Homogenization.vecDot (Pi.single i 1)
                (Homogenization.matVecMul
                  (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
                    (Homogenization.Book.Ch02.cubeDomain Q'))
                  (Pi.single i 1)))) := by rw [hrespQ]
        _ = SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
            SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain Q') i i := by
          rw [vecDot_single_left, matVecMul_single]
          rw [hcval]
          simp
          ring
    · have hsum := hrespQ (Pi.single i 1 + Pi.single j 1)
      have hi := hrespQ (Pi.single i 1)
      have hj := hrespQ (Pi.single j 1)
      calc
        (∫ omega,
            Homogenization.Book.Ch02.sigmaStarInvCoarse U (a0 omega) i j
              ∂(chaosSampleLaw model).toMeasure) =
            (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
              (Pi.single i 1 + Pi.single j 1)
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
              ∂(chaosSampleLaw model).toMeasure) -
            (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
              (Pi.single i 1)
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
              ∂(chaosSampleLaw model).toMeasure) -
            (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
              (Pi.single j 1)
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
              ∂(chaosSampleLaw model).toMeasure) := by
          have hsub := (hIntQ (Pi.single i 1 + Pi.single j 1)).sub
            (hIntQ (Pi.single i 1))
          have hrewrite :
              (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                (Pi.single i 1 + Pi.single j 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                ∂(chaosSampleLaw model).toMeasure) -
              (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                (Pi.single i 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                ∂(chaosSampleLaw model).toMeasure) -
              (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                (Pi.single j 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                ∂(chaosSampleLaw model).toMeasure) =
              (∫ omega,
                (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                  (Pi.single i 1 + Pi.single j 1)
                  (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
                Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                  (Pi.single i 1)
                  (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))) -
                Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                  (Pi.single j 1)
                  (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                ∂(chaosSampleLaw model).toMeasure) := by
            calc
              _ = (∫ omega,
                  (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                    (Pi.single i 1 + Pi.single j 1)
                    (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
                  Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                    (Pi.single i 1)
                    (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
                  ∂(chaosSampleLaw model).toMeasure) -
                (∫ omega, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0
                  (Pi.single j 1)
                  (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
                  ∂(chaosSampleLaw model).toMeasure) := by
                    rw [MeasureTheory.integral_sub (hIntQ (Pi.single i 1 + Pi.single j 1))
                      (hIntQ (Pi.single i 1))]
              _ = _ := by
                simpa only [Pi.sub_apply] using!
                  (MeasureTheory.integral_sub hsub (hIntQ (Pi.single j 1))).symm
          rw [hrewrite]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall (fun omega => by
            simpa [hij] using! (hsigQ omega i j))
        _ = c * ((1 / 2 : ℝ) * Homogenization.vecDot
              (Pi.single i 1 + Pi.single j 1)
              (Homogenization.matVecMul
                (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
                  (Homogenization.Book.Ch02.cubeDomain Q'))
                (Pi.single i 1 + Pi.single j 1))) -
            c * ((1 / 2 : ℝ) * Homogenization.vecDot (Pi.single i 1)
              (Homogenization.matVecMul
                (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
                  (Homogenization.Book.Ch02.cubeDomain Q')) (Pi.single i 1))) -
            c * ((1 / 2 : ℝ) * Homogenization.vecDot (Pi.single j 1)
              (Homogenization.matVecMul
                (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
                  (Homogenization.Book.Ch02.cubeDomain Q')) (Pi.single j 1))) := by
          rw [hrespQ, hrespQ, hrespQ]
        _ = SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
            SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain Q') i j := by
          have hzeroij :=
            SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.abarStarInv_originCube_offdiag_eq_zero
              model N (N + k) i j hij
          have hzeroji :=
            SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.abarStarInv_originCube_offdiag_eq_zero
              model N (N + k) j i (Ne.symm hij)
          have hz0ij : SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain Q') i j = 0 := by
            simpa [hQ'] using! hzeroij
          have hz0ji : SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain Q') j i = 0 := by
            simpa [hQ'] using! hzeroji
          rw [basis_sum_pairing]
          simp only [vecDot_single_left, matVecMul_single]
          rw [hcval]
          simp [hz0ij, hz0ji]
          field_simp
          ring
theorem aux_annealed_limit_response_transport_sigma_entries
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Homogenization.TriadicCube d)
    (a0 : BilateralField d → Homogenization.Book.Ch02.CoeffOn
      (Homogenization.Book.Ch02.cubeDomain Q))
    (fA : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hposf : ∀ (omega : BilateralField d) (x : SpatialCoordinates d),
      0 < fA omega x)
    (ha0f : ∀ (omega : BilateralField d) (x : SpatialCoordinates d),
      (a0 omega).toCoeffField x = scalarMatrix (fA omega x)) :
    (∀ (omega : BilateralField d) (i j : Fin d),
      Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain Q) (a0 omega) i j =
        if i = j then
          2 * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q (Pi.single i 1) 0
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
        else
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q (Pi.single i 1 + Pi.single j 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q (Pi.single i 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q (Pi.single j 1) 0
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))) ∧
    (∀ (omega : BilateralField d) (i j : Fin d),
      Homogenization.Book.Ch02.sigmaStarInvCoarse
          (Homogenization.Book.Ch02.cubeDomain Q) (a0 omega) i j =
        if i = j then
          2 * Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q 0 (Pi.single i 1)
              (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
        else
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q 0 (Pi.single i 1 + Pi.single j 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q 0 (Pi.single i 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              Q 0 (Pi.single j 1)
                (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))) := by
  constructor
  · intro omega i j
    simpa only using!
      (aux_annealed_limit_response_transport_sigma_entry_response Q (fA omega)
        (hposf omega) (a0 omega) (fun x => ha0f omega x) i j)
  · intro omega i j
    simpa only using!
      (aux_annealed_limit_response_transport_star_entry_response Q (fA omega)
        (hposf omega) (a0 omega) (fun x => ha0f omega x) i j)

theorem aux_annealed_limit_response_transport_scaled_response
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ)
    (Q Q' : Homogenization.TriadicCube d)
    (fA : BilateralField d → C(SpatialCoordinates d, ℝ))
    (s r c : ℝ)
    (hnormR0 : ProbabilityTheory.IdentDistrib fA
      (fun omega =>
        ⟨fun x => s * Real.exp (∑ j ∈ Finset.range (N + 1),
          (omega (j : ℤ) ((3 : ℝ) ^ N • x) -
            SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)), by continuity⟩)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure)
    (hrdef : r = s * Real.exp (-(N : ℝ) *
      SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))
    (hcr0 : c * r = Real.exp (-(N : ℝ) *
      SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))
    (hQ : Q = Homogenization.originCube d (k : ℤ))
    (hQ' : Q' = Homogenization.originCube d ((N + k : ℕ) : ℤ)) :
    ∀ (p q : Homogenization.Vec d),
      ProbabilityTheory.IdentDistrib
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q (c •
            aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)))
        (chaosSampleLaw model).toMeasure model.P.toMeasure := by
  have hpos := aux_annealed_limit_response_transport_positive_field_law
    (model := model) N
  let g0 : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → C(SpatialCoordinates d, ℝ) :=
    fun omega =>
      ⟨fun x => Real.exp (∑ i : Fin (N + 1),
          ((omega (i : ℕ)).1.1) x -
            SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P), by continuity⟩
  let h0 : BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun omega =>
      ⟨fun x => Real.exp (∑ i : Fin (N + 1),
          (omega (i : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P), by continuity⟩
  let dilate : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => (3 : ℝ) ^ N • x,
      ((continuous_const : Continuous (fun _ : SpatialCoordinates d => (3 : ℝ) ^ N)).smul continuous_id)⟩
  let compD : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ dilate
  let T : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) :=
    fun f => r • compD f
  have hTmeas : Measurable T := by
    simpa only [T, Pi.smul_apply] using! ((continuous_const (y := r)).smul compD.continuous).measurable
  have hpos' : ProbabilityTheory.IdentDistrib g0 h0
      model.P.toMeasure (chaosSampleLaw model).toMeasure := by
    simpa [g0, h0] using! hpos
  have htrans : ProbabilityTheory.IdentDistrib (T ∘ g0) (T ∘ h0)
      model.P.toMeasure (chaosSampleLaw model).toMeasure :=
    hpos'.comp hTmeas
  let R : BilateralField d → C(SpatialCoordinates d, ℝ) := fun omega =>
    ⟨fun x =>
      s * Real.exp (∑ j ∈ Finset.range (N + 1),
        (omega (j : ℤ) ((3 : ℝ) ^ N • x) -
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)), by
      apply continuous_const.mul
      apply Real.continuous_exp.comp
      apply continuous_finset_sum
      intro j hj
      apply Continuous.sub
      · exact (omega (j : ℤ)).continuous.comp
          ((continuous_const : Continuous (fun _ : SpatialCoordinates d => (3 : ℝ) ^ N)).smul continuous_id)
      · exact continuous_const⟩
  have hnormR : ProbabilityTheory.IdentDistrib fA R
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
    simpa [R] using! hnormR0
  have hTR : T ∘ h0 = R := by
    funext omega
    ext x
    change r * Real.exp (∑ i : Fin (N + 1),
        (omega (i : ℤ)) ((3 : ℝ) ^ N • x) -
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) = _
    dsimp [R]
    have hsum :
        (∑ i : Fin (N + 1),
          (omega (i : ℤ)) ((3 : ℝ) ^ N • x)) =
          ∑ i ∈ Finset.range (N + 1),
            (omega (i : ℤ)) ((3 : ℝ) ^ N • x) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [dif_pos (Finset.mem_range.mp hi)]
    rw [hsum]
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [hrdef]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hnorm' : ProbabilityTheory.IdentDistrib fA
      (T ∘ h0) (chaosSampleLaw model).toMeasure
      (chaosSampleLaw model).toMeasure := by
    rw [hTR]
    exact hnormR
  have hcoef : ProbabilityTheory.IdentDistrib
      (fun omega =>
        aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
      (fun omega =>
        aux_annealed_limit_response_transport_scalarRegCoeffField
          (T (g0 omega)))
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
    have hsrc : ProbabilityTheory.IdentDistrib
        (fun omega =>
          aux_annealed_limit_response_transport_scalarRegCoeffField
            (T (g0 omega)))
        (fun omega =>
          aux_annealed_limit_response_transport_scalarRegCoeffField
            (T (h0 omega)))
        model.P.toMeasure (chaosSampleLaw model).toMeasure :=
      htrans.comp
        aux_annealed_limit_response_transport_measurable_scalarRegCoeffField
    have hleft := hnorm'.comp
      aux_annealed_limit_response_transport_measurable_scalarRegCoeffField
    exact hleft.trans hsrc.symm
  let Abar : BilateralField d → RegCoeffField d := fun omega =>
    c • aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)
  have hsource (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
      c • aux_annealed_limit_response_transport_scalarRegCoeffField
          (T (g0 omega)) = Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega) := by
    apply RegCoeffField.ext
    intro x
    rw [RegCoeffField.smul_toFun]
    dsimp
    change c • scalarMatrix ((T (g0 omega)) x) = _
    rw [show (T (g0 omega)) x =
        r * Real.exp
          (∑ i : Fin (N + 1),
            ((omega (i : ℕ)).1.1) ((3 : ℝ) ^ N • x) -
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) by
      rfl]
    have hcr : c * r = Real.exp (-(N : ℝ) *
        SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) := hcr0
    change c • scalarMatrix
        (r * Real.exp (∑ i : Fin (N + 1),
          ((omega (i : ℕ)).1.1) ((3 : ℝ) ^ N • x) -
            SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) =
      scalarMatrix (SubdiffusiveProcess.Frozen.Assumptions.aCutoff model N omega
        ((3 : ℝ) ^ N • x))
    exact aux_annealed_limit_response_transport_source_matrix model N omega
      ((3 : ℝ) ^ N • x) c r (SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) hcr rfl
  have hscale : Measurable (fun z : RegCoeffField d => c • z) := by
    apply Homogenization.measurable_of_entryTestR_transport
    · intro y i j
      simpa [RegCoeffField.smul_toFun] using!
        (Homogenization.measurable_apply_entry y i j).const_smul c
    · intro i j φ hφ
      exact ⟨c, i, j, φ, hφ,
        fun z => Homogenization.entryTestR_smul i j c z⟩
  have hbar : ProbabilityTheory.IdentDistrib Abar
      (fun omega => Homogenization.rescaleReg N
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
    have hraw := hcoef.comp hscale
    have hleft :
        (fun omega => c •
          aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)) = Abar := by
      rfl
    have hright :
        (fun omega => c •
          aux_annealed_limit_response_transport_scalarRegCoeffField
            (T (g0 omega))) =
          (fun omega => Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)) := by
      funext omega
      exact hsource omega
    rw [← hleft, ← hright]
    exact hraw
  let e : RegCoeffField d ≃ᵐ RegCoeffField d :=
    { toEquiv :=
        { toFun := Homogenization.rescaleReg N
          invFun := Homogenization.dilateReg (N : ℤ)
          left_inv := by
            intro a
            apply RegCoeffField.ext
            intro x
            simp only [Homogenization.dilateReg_apply,
              Homogenization.rescaleReg_apply, smul_smul]
            rw [zpow_natCast,
              mul_inv_cancel₀ (by positivity : ((3 : ℝ) ^ N) ≠ 0), one_smul]
          right_inv := by
            intro a
            apply RegCoeffField.ext
            intro x
            simp only [Homogenization.dilateReg_apply,
              Homogenization.rescaleReg_apply, smul_smul]
            rw [zpow_natCast,
              inv_mul_cancel₀ (by positivity : ((3 : ℝ) ^ N) ≠ 0), one_smul] }
      measurable_toFun := Homogenization.measurable_rescaleReg N
      measurable_invFun := Homogenization.measurable_dilateReg (N : ℤ) }
  have he : MeasurableEmbedding (Homogenization.rescaleReg (d := d) N) :=
    e.measurableEmbedding
  let P : Homogenization.Book.Ch04.RestrictionCoeffLaw d :=
    SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw model N
  have hP : Homogenization.Book.Ch04.RestrictionLawCarrier P := by
    dsimp [P]
    exact SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_lawCarrier model N
  have hPmap : P = Measure.map
      (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N)
      model.P.toMeasure := by
    dsimp [P]
    exact SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_eq_map model N
  have hresp_rescale (p q : Homogenization.Vec d)
      (a : RegCoeffField d)
      (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q (Homogenization.rescaleReg N a) =
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q' p q a := by
    simpa [hQ, hQ'] using!
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
        ha N k p q
  have hcompAE (p q : Homogenization.Vec d) :
      AEMeasurable
        (fun a => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q a) (Measure.map (Homogenization.rescaleReg N) P) := by
    have hcongr :
        (fun a => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q (Homogenization.rescaleReg N a)) =ᵐ[P]
        (fun a => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q' p q a) := by
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      exact hresp_rescale p q a ha
    have hh := hP.aemeasurable_restrictionResponseJObservableCubeSet Q' p q
    have hh' := hh.congr hcongr.symm
    apply (he.aemeasurable_map_iff).mpr
    simpa [Function.comp_def] using! hh'
  have hBmap : Measure.map
      (fun omega => Homogenization.rescaleReg N
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
      model.P.toMeasure =
      Measure.map (Homogenization.rescaleReg N) P := by
    rw [hPmap]
    rw [Measure.map_map]
    · rfl
    · exact Homogenization.measurable_rescaleReg N
    · exact SubdiffusiveProcess.CoarseGrainingVocab.measurable_aCutoffRegCoeffField model N
  have hAbarAE (p q : Homogenization.Vec d) :
      AEMeasurable
        (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p q)
        (Measure.map Abar (chaosSampleLaw model).toMeasure) := by
    rw [hbar.map_eq, hBmap]
    exact hcompAE p q
  have hscaledID (p q : Homogenization.Vec d) :
      ProbabilityTheory.IdentDistrib
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q (c •
            aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)))
        (chaosSampleLaw model).toMeasure model.P.toMeasure := by
    have hh := hbar.comp_of_aemeasurable (hAbarAE p q)
    change ProbabilityTheory.IdentDistrib
      (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q p q (Abar omega))
      (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        Q p q (Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)))
      (chaosSampleLaw model).toMeasure model.P.toMeasure
    exact hh
  exact hscaledID
theorem aux_annealed_limit_response_transport_full (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ (U : ℕ → Homogenization.Book.Ch02.Domain d)
      (hU : ∀ k, (U k : Set (Homogenization.Vec d)) =
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)))
      (a0 : (N k : ℕ) → BilateralField d → Homogenization.Book.Ch02.CoeffOn (U k))
      (ha0 : ∀ N k omega x, (a0 N k omega).toCoeffField x =
        ((Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
          (1 : Homogenization.Mat d)),
    ∀ (N k : ℕ),
      (∀ i j : Fin d,
        Integrable (fun omega =>
          Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) i j)
          (chaosSampleLaw model).toMeasure ∧
        Integrable (fun omega =>
          Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) i j)
          (chaosSampleLaw model).toMeasure) ∧
      (∀ i j : Fin d,
        (∫ omega,
          Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) i j
            ∂(chaosSampleLaw model).toMeasure) =
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            SubdiffusiveProcess.CoarseGrainingVocab.abar model N
              (Homogenization.Book.Ch02.cubeDomain
                (Homogenization.originCube d ((N + k : ℕ) : ℤ))) i j) ∧
      (∀ i j : Fin d,
        (∫ omega,
          Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) i j
            ∂(chaosSampleLaw model).toMeasure) =
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
            SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain
                (Homogenization.originCube d ((N + k : ℕ) : ℤ))) i j) := by
  intro U hU
  letI : NeZero d := ⟨by omega⟩
  have hdomain (k : ℕ) : U k =
      Homogenization.Book.Ch02.cubeDomain
        (Homogenization.originCube d (k : ℤ)) := by
    let Qk : Homogenization.TriadicCube d :=
      Homogenization.originCube d (k : ℤ)
    have hcar : (U k : Set (Homogenization.Vec d)) =
        (Homogenization.Book.Ch02.cubeDomain Qk : Set (Homogenization.Vec d)) := by
      rw [hU k]
      have hr : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := by positivity
      simpa [Qk, zpow_natCast] using!
        (SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube
          (d := d) (k : ℤ) hr)
    cases hUk : U k with
    | mk carrier hdom hne =>
        have hcar' : carrier =
            (Homogenization.Book.Ch02.cubeDomain Qk : Set (Homogenization.Vec d)) := by
          simpa [hUk] using! hcar
        subst carrier
        rfl
  have hUeq : U = (fun k : ℕ =>
      Homogenization.Book.Ch02.cubeDomain
        (Homogenization.originCube d (k : ℤ))) := by
    funext k
    exact hdomain k
  cases hUeq
  intro a0 ha0 N k
  let Uk : Homogenization.Book.Ch02.Domain d :=
    Homogenization.Book.Ch02.cubeDomain
      (Homogenization.originCube d (k : ℤ))
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (k : ℤ)
  let Q' : Homogenization.TriadicCube d :=
    Homogenization.originCube d ((N + k : ℕ) : ℤ)
  let fA : BilateralField d → C(SpatialCoordinates d, ℝ) := fun omega =>
    ⟨fun x =>
      (Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x), by continuity⟩
  have ha0f (omega : BilateralField d) (x : SpatialCoordinates d) :
      (a0 N k omega).toCoeffField x =
        scalarMatrix (fA omega x) := by
    rw [ha0]
    simp [fA, scalarMatrix]
  let s : ℝ := (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹
  have hs : 0 < s := by
    dsimp [s]
    exact inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)
  let r : ℝ := s * Real.exp (-(N : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let c : ℝ := s⁻¹
  have hc : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr hs
  have hnorm := aux_annealed_limit_response_transport_normalized_field_law
    (model := model) N
  have hnormR0 : ProbabilityTheory.IdentDistrib fA
      (fun omega =>
        ⟨fun x => s * Real.exp (∑ j ∈ Finset.range (N + 1),
          (omega (j : ℤ) ((3 : ℝ) ^ N • x) -
            SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)), by continuity⟩)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
    simpa [fA, s] using! hnorm
  have hscaledID := aux_annealed_limit_response_transport_scaled_response
    model N k Q Q' fA s r c hnormR0 (by dsimp [r])
      (by dsimp [c, r]; field_simp) (by rfl) (by rfl)
  have hresp_rescale (p q : Homogenization.Vec d)
      (a : RegCoeffField d)
      (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p q (Homogenization.rescaleReg N a) =
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q' p q a := by
    simpa [Q, Q'] using!
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
        ha N k p q
  have hIntP (p : Homogenization.Vec d) :
      Integrable
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q p 0 (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
        (chaosSampleLaw model).toMeasure := by
    have hBint : Integrable
        (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q p 0 (Homogenization.rescaleReg N
              (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)))
        model.P.toMeasure :=
      aux_annealed_limit_response_transport_integrable_rescaled_primal model N Q p
    have hscaled := (hscaledID p 0).integrable_iff.mpr hBint
    have hscaled' : Integrable
        (fun omega => c *
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q p 0 (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
        (chaosSampleLaw model).toMeasure := by
      apply hscaled.congr
      exact Filter.Eventually.of_forall (fun omega => by
        exact aux_annealed_limit_response_transport_response_p_zero_smul Q _ c hc p)
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ne_of_gt hc)) _).mp hscaled'
  have hsourceP (p : Homogenization.Vec d) :=
    aux_annealed_limit_response_transport_source_primal model N Q Q'
      hresp_rescale p
  have hsourceQ (q : Homogenization.Vec d) :=
    aux_annealed_limit_response_transport_source_dual model N Q Q'
      hresp_rescale q
  have hcs : c⁻¹ = s := by
    dsimp [c]
    exact inv_inv s
  have hresp := aux_annealed_limit_response_transport_annealed_responses
    model N Q Q' fA c s hc hcs hscaledID hsourceP hsourceQ
  have hrespP := hresp.1
  have hrespQ := hresp.2
  have hIntQ (q : Homogenization.Vec d) :
      Integrable
        (fun omega => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          Q 0 q
          (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
        (chaosSampleLaw model).toMeasure := by
    have hBint : Integrable
        (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
            Q 0 q (Homogenization.rescaleReg N
              (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)))
        model.P.toMeasure :=
      aux_annealed_limit_response_transport_integrable_rescaled_dual model N Q q
    have hscaled := (hscaledID 0 q).integrable_iff.mpr hBint
    have hscaled' : Integrable
        (fun omega => c⁻¹ *
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q 0 q
            (aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega)))
        (chaosSampleLaw model).toMeasure := by
      apply hscaled.congr
      exact Filter.Eventually.of_forall (fun omega => by
        exact aux_annealed_limit_response_transport_response_zero_q_smul Q _ c hc q)
    exact (integrable_const_mul_iff
      (isUnit_iff_ne_zero.mpr (ne_of_gt (inv_pos.mpr hc))) _).mp hscaled'

  have hposf (omega : BilateralField d) : ∀ x, 0 < fA omega x := by
    intro x
    have ha : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom model N :=
      SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N
    dsimp [fA]
    positivity
  have hsig := aux_annealed_limit_response_transport_sigma_entries Q (a0 N k) fA
    hposf (fun omega x => ha0f omega x)
  have hsigP := hsig.1
  have hsigQ := hsig.2

  simpa [Uk] using!
    (aux_annealed_limit_response_transport_assemble model N k Uk (a0 N k)
      Q Q' fA c s (by dsimp [s])
      (by dsimp [c, s]; exact inv_inv _) (by rfl)
      hIntP hIntQ hrespP hrespQ hsigP hsigQ)

theorem annealed_limit_response_transport (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ (U : ℕ → Homogenization.Book.Ch02.Domain d)
      (hU : ∀ k, (U k : Set (Homogenization.Vec d)) =
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)))
      (a0 : (N k : ℕ) → BilateralField d → Homogenization.Book.Ch02.CoeffOn (U k))
      (ha0 : ∀ N k omega x, (a0 N k omega).toCoeffField x =
        ((Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
          (1 : Homogenization.Mat d)),
    ∀ (N k : ℕ),
      (∀ i j : Fin d,
        Integrable (fun omega =>
          Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) i j)
          (chaosSampleLaw model).toMeasure ∧
        Integrable (fun omega =>
          Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) i j)
          (chaosSampleLaw model).toMeasure) ∧
      (∀ i j : Fin d,
        (∫ omega,
          Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) i j
            ∂(chaosSampleLaw model).toMeasure) =
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            SubdiffusiveProcess.CoarseGrainingVocab.abar model N
              (Homogenization.Book.Ch02.cubeDomain
                (Homogenization.originCube d ((N + k : ℕ) : ℤ))) i j) ∧
      (∀ i j : Fin d,
        (∫ omega,
          Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) i j
            ∂(chaosSampleLaw model).toMeasure) =
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
            SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
              (Homogenization.Book.Ch02.cubeDomain
                (Homogenization.originCube d ((N + k : ℕ) : ℤ))) i j) := by
  exact aux_annealed_limit_response_transport_full d hd model

end
end Paper
