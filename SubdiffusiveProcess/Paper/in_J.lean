module

public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Homogenization.Book.Ch02.Theorems.MatrixExtraction
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.CoarseGraining.Subadditivity
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import Homogenization.Book.Ch02.Setup
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationError
public import Homogenization.Book.Ch02.MultiscaleEllipticity

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/- A direct variational proof of the paper's finite measurable-partition
subadditivity, including null-overlap and zero-volume cells. -/
section AuxInJPartition
open Homogenization
open MeasureTheory

theorem aux_in_J_weak_partial_restrict {d : ℕ} {U V : Set (Vec d)}
    (hVU : V ⊆ U) {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) : HasWeakPartialDerivOn V i u gi := by
  intro φ hφ_smooth hφ_compact hφ_supp
  have hφ_suppU : tsupport φ ⊆ U := hφ_supp.trans hVU
  have key := h φ hφ_smooth hφ_compact hφ_suppU
  have h1 : ∀ x, x ∉ V → u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_supp hx')
    have hφ_eq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp
  have h2 : ∀ x, x ∉ V → gi x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hφ_supp hx'))]
  have h3 : ∀ x, x ∉ U → u x * (fderiv ℝ φ x) (basisVec i) = 0 :=
    fun x hx => h1 x (fun hx' => hx (hVU hx'))
  have h4 : ∀ x, x ∉ U → gi x * φ x = 0 :=
    fun x hx => h2 x (fun hx' => hx (hVU hx'))
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h1,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h2,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h3,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h4,
    key]

def aux_in_J_h1_restrict {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVU : V ⊆ U) : H1Function V :=
  { toFun := u.toFun
    grad := u.grad
    memL2 := memL2On_mono hVU u.memL2
    gradMemL2 := gradMemL2On_mono hVU u.gradMemL2
    hasWeakGradient := fun i => aux_in_J_weak_partial_restrict hVU (u.hasWeakGradient i) }

theorem aux_in_J_solenoidal_restrict_measurable {d : ℕ} {U V : Set (Vec d)}
    {g : Vec d → Vec d} (hg : IsSolenoidalOn U g)
    (hU : IsOpen U) (hV : MeasurableSet V) (hVU : V ⊆ U) :
    IsSolenoidalOn V g := by
  intro φ
  let ψ : H10Function U := φ.extendByZeroToOpenSuperset hV hU hVU
  have hψ : ∫ x in U, vecDot (g x) (ψ.toH1Function.grad x)
      ∂MeasureTheory.volume = 0 := hg ψ
  have hEq :
      ∫ x in U, vecDot (g x) (ψ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in V, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
    let F : Vec d → ℝ := fun x => vecDot (g x) (φ.toH1Function.grad x)
    calc
      ∫ x in U, vecDot (g x) (ψ.toH1Function.grad x) ∂MeasureTheory.volume =
          ∫ x in U, V.indicator F x ∂MeasureTheory.volume := by
        apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
        intro x hxU
        by_cases hxV : x ∈ V
        · simp [ψ, F, H10Function.zeroExtensionGrad, hxV]
        · simp [ψ, F, H10Function.zeroExtensionGrad, hxV, vecDot]
      _ = ∫ x in V, F x ∂MeasureTheory.volume := by
        rw [MeasureTheory.setIntegral_indicator hV, Set.inter_eq_self_of_subset_right hVU]
      _ = ∫ x in V, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := rfl
  exact hEq.symm.trans hψ

def aux_in_J_harmonic_restrict_measurable {d : ℕ} {U V : Set (Vec d)}
    {a : CoeffField d} (u : AHarmonicFunction a U)
    (hU : IsOpen U) (hV : MeasurableSet V) (hVU : V ⊆ U) :
    AHarmonicFunction a V :=
  { toH1 := aux_in_J_h1_restrict u.toH1 hVU
    isHarmonic :=
      ⟨(aux_in_J_h1_restrict u.toH1 hVU).isPotentialOn,
        aux_in_J_solenoidal_restrict_measurable u.isHarmonic.2 hU hV hVU⟩ }

theorem aux_in_J_integral_finite_partition {d n : ℕ} {U : Set (Vec d)}
    (V : Fin n → Set (Vec d)) (hV : ∀ i, MeasurableSet (V i))
    (hsub : ∀ i, V i ⊆ U)
    (hdisj : ∀ i j, i ≠ j → volume (V i ∩ V j) = 0)
    (hcov : volume (U \ ⋃ i, V i) = 0)
    {f : Vec d → ℝ} (hf : MeasureTheory.IntegrableOn f U) :
    ∫ x in U, f x ∂volume = ∑ i, ∫ x in V i, f x ∂volume := by
  classical
  let W : Set (Vec d) := ⋃ i, V i
  have hWsub : W ⊆ U := Set.iUnion_subset fun i => hsub i
  have hWmeas : MeasurableSet W := MeasurableSet.iUnion hV
  have hdiff := setIntegral_sdiff hWmeas hf hWsub
  have hzero : ∫ x in U \ W, f x ∂volume = 0 :=
    MeasureTheory.setIntegral_measure_zero f hcov
  have hUW : ∫ x in U, f x ∂volume = ∫ x in W, f x ∂volume := by
    rw [hzero] at hdiff
    exact sub_eq_zero.mp hdiff.symm
  have hpair : Pairwise (fun i j => MeasureTheory.AEDisjoint volume (V i) (V j)) :=
    fun i j hij => hdisj i j hij
  rw [hUW]
  simpa only [W, tsum_fintype] using
    (MeasureTheory.integral_iUnion_ae (fun i => (hV i).nullMeasurableSet)
      hpair (hf.mono_set hWsub))

theorem aux_in_J_cell_integral_le {d : ℕ} {U V : Set (Vec d)}
    {a : CoeffField d} {lam Lam : ℝ} (hU : IsOpen U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVfinite : volume V ≠ ⊤)
    (hEll : IsEllipticFieldOn lam Lam V a)
    (p q : Vec d) (u : AHarmonicFunction a U) :
    ∫ x in V, scalarResponseIntegrand U a p q u x ∂volume ≤
      volume.real V * ResponseJ V p q a := by
  let v : AHarmonicFunction a V := aux_in_J_harmonic_restrict_measurable u hU hV hVU
  have hfun : scalarResponseIntegrand U a p q u = scalarResponseIntegrand V a p q v := by
    funext x
    simp only [scalarResponseIntegrand, v, aux_in_J_harmonic_restrict_measurable, aux_in_J_h1_restrict]
  rw [hfun]
  by_cases hVzero : volume V = 0
  · simp [MeasureTheory.setIntegral_measure_zero _ hVzero, MeasureTheory.Measure.real,
      hVzero]
  · have : IsFiniteMeasure (volumeMeasureOn V) := by
      exact ⟨by simpa [volumeMeasureOn] using (lt_top_iff_ne_top.mpr hVfinite)⟩
    have hVreal : (volume V).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hVzero, hVfinite⟩
    have hmem : volumeAverage V (scalarResponseIntegrand V a p q v) ∈
        responseJValueSet V p q a := responseJValueSet_mem V p q a v
    have hle : volumeAverage V (scalarResponseIntegrand V a p q v) ≤
        ResponseJ V p q a :=
      le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn hEll hVreal p q hmem
    have hpos : 0 ≤ volume.real V := ENNReal.toReal_nonneg
    unfold volumeAverage at hle
    rw [MeasureTheory.Measure.real] at hpos ⊢
    calc
      ∫ x in V, scalarResponseIntegrand V a p q v x ∂volume =
          (volume V).toReal * ((volume V).toReal⁻¹ *
            ∫ x in V, scalarResponseIntegrand V a p q v x ∂volume) := by
        field_simp
      _ ≤ (volume V).toReal * ResponseJ V p q a :=
        mul_le_mul_of_nonneg_left hle hpos

theorem aux_in_J_responseJ_subadditive_measurable {d n : ℕ} {U : Set (Vec d)}
    (hUopen : IsOpen U) (hUfinite : volume U ≠ ⊤)
    (V : Fin n → Set (Vec d)) (hV : ∀ i, MeasurableSet (V i))
    (hsub : ∀ i, V i ⊆ U)
    (hdisj : ∀ i j, i ≠ j → volume (V i ∩ V j) = 0)
    (hcov : volume (U \ ⋃ i, V i) = 0)
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d) :
    ResponseJ U p q a ≤
      ∑ i : Fin n, (volume.real (V i) / volume.real U) * ResponseJ (V i) p q a := by
  classical
  let : IsFiniteMeasure (volumeMeasureOn U) := by
    exact ⟨by simpa [volumeMeasureOn] using (lt_top_iff_ne_top.mpr hUfinite)⟩
  change sSup (responseJValueSet U p q a) ≤ _
  refine csSup_le (responseJValueSet_nonempty U p q a) ?_
  rintro m ⟨u, rfl⟩
  let f : Vec d → ℝ := scalarResponseIntegrand U a p q u
  have hf : IntegrableOn f U :=
    scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u
  have hsum : ∫ x in U, f x ∂volume ≤
      ∑ i : Fin n, volume.real (V i) * ResponseJ (V i) p q a := by
    rw [aux_in_J_integral_finite_partition V hV hsub hdisj hcov hf]
    apply Finset.sum_le_sum
    intro i hi
    have hViFinite : volume (V i) ≠ ⊤ :=
      ne_top_of_le_ne_top hUfinite (measure_mono (hsub i))
    exact aux_in_J_cell_integral_le hUopen (hV i) (hsub i) hViFinite
      (IsEllipticFieldOn.mono hEll (hV i) (hsub i)) p q u
  have hnonneg : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  change volumeAverage U f ≤ _
  unfold volumeAverage
  calc
    (volume.real U)⁻¹ * ∫ x in U, f x ∂volume ≤
        (volume.real U)⁻¹ * ∑ i : Fin n, volume.real (V i) * ResponseJ (V i) p q a :=
      mul_le_mul_of_nonneg_left hsum hnonneg
    _ = ∑ i : Fin n, (volume.real (V i) / volume.real U) *
          ResponseJ (V i) p q a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem aux_in_J_responseJ_subadditive {d : ℕ}
    (U : Book.Ch02.Domain d) (a : CoeffField d) (lam Lam : ℝ)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a)
    (n : ℕ) (V : Fin n → Set (Vec d))
    (hV : ∀ i, MeasurableSet (V i))
    (hsub : ∀ i, V i ⊆ (U : Set (Vec d)))
    (hdisj : ∀ i j, i ≠ j → volume (V i ∩ V j) = 0)
    (hcov : volume ((U : Set (Vec d)) \ ⋃ i, V i) = 0)
    (p q : Vec d) :
    ResponseJ (U : Set (Vec d)) p q a ≤
      ∑ i : Fin n, (volume.real (V i) / volume.real (U : Set (Vec d))) *
        ResponseJ (V i) p q a := by
  have hUfinite : volume (U : Set (Vec d)) ≠ ⊤ := by
    exact isFiniteMeasure_restrict.mp
      (show IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d))) from inferInstance)
  exact aux_in_J_responseJ_subadditive_measurable U.isOpen hUfinite V hV hsub
    hdisj hcov hEll p q

end AuxInJPartition



structure in_J (d : ℕ) where
  /-- `λ_{s,q}(w + Q_{r'} ; a)` of Definition `d.mathcal.E`, for the sub-cube of
  centre `w` and side `r'` of the cube of side `r` carrying the coefficient `a`. -/
  lam : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    PositiveCoefficient (centeredCube z r hr) →
      SpatialCoordinates d → ℝ → ℝ → ℝ≥0∞ → ℝ
  /-- `Λ_{s,q}(w + Q_{r'} ; a)`. -/
  Lam : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    PositiveCoefficient (centeredCube z r hr) →
      SpatialCoordinates d → ℝ → ℝ → ℝ≥0∞ → ℝ
  /-- `E_{s,∞,q}(w + Q_{r'} ; a, a₀)` of Definition `d.mathcal.E`. -/
  err : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    PositiveCoefficient (centeredCube z r hr) →
      SpatialCoordinates d → ℝ → ℝ → ℝ → ℝ≥0∞ → ℝ
  /-- Actual rescaled coefficient: for an inner cube of centre `w` and side `r'` inside
  the root cube of centre `z` and side `r`, `chart z r hr a w r'` is the coefficient in
  the rescaled chart `x ↦ w + r' * x` of the inner cube, packaged as a compatible
  upstream triadic family.  Values outside the unit root are immaterial. -/
  chart : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    PositiveCoefficient (centeredCube z r hr) →
      SpatialCoordinates d → ℝ →
        Homogenization.Book.Ch02.TriadicCoeffFamily d
  /-- The chart is the actual scalar coefficient, not an unrelated datum: on every
  triadic sub-cube `Q` of the unit root, the chart's coefficient field is (a.e., for
  Lebesgue measure restricted to `Q`) the scalar matrix of the rescaled coefficient
  `x ↦ a(w + r' x)`. -/
  chart_eq : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ Q : Homogenization.TriadicCube d,
        Homogenization.openCubeSet Q ⊆
          Homogenization.openCubeSet (Homogenization.originCube d 0) →
        ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
          ((chart z r hr a w r').coeffOn Q).toCoeffField x =
            Homogenization.scalarMatrix (a.val (fun i => w i + r' * x i))
  /-- `λ_{s,q}` of Definition `d.mathcal.E` is exactly the frozen discounted sum
  `lambdaSq` of the rescaled chart family on the unit root. -/
  lam_eq : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ q : ℝ≥0∞, 1 ≤ q →
      lam z r hr a w r' s q =
        Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) s
          (if q = ⊤ then Homogenization.Book.Ch02.MultiscaleExponent.infinity
            else Homogenization.Book.Ch02.MultiscaleExponent.finite q.toReal)
          (chart z r hr a w r')
  /-- `Λ_{s,q}` of Definition `d.mathcal.E` is exactly the frozen discounted sum
  `LambdaSq` of the rescaled chart family on the unit root. -/
  Lam_eq : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ q : ℝ≥0∞, 1 ≤ q →
      Lam z r hr a w r' s q =
        Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) s
          (if q = ⊤ then Homogenization.Book.Ch02.MultiscaleExponent.infinity
            else Homogenization.Book.Ch02.MultiscaleExponent.finite q.toReal)
          (chart z r hr a w r')
  /-- The homogenization error of Definition `d.mathcal.E` is a finite extended
  nonnegative real, computed with `p = ∞`, `n = m = 0` on the normalized chart. -/
  err_finite : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ q : ℝ≥0∞, 1 ≤ q →
      ∀ a0 : ℝ, 0 < a0 →
      let e : ℝ≥0∞ :=
        if q = ⊤ then
          SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (chart z r hr a w r') a0
        else
          SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity q.toReal
            (chart z r hr a w r') a0
      e < ⊤
  /-- `E_{s,∞,q}` of Definition `d.mathcal.E` is exactly the real part of the frozen
  homogenization error of the rescaled chart, with `p = ∞`, `n = m = 0`. -/
  err_eq : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ q : ℝ≥0∞, 1 ≤ q →
      ∀ a0 : ℝ, 0 < a0 →
      err z r hr a w r' a0 s q =
        (if q = ⊤ then
            SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity
              (Homogenization.originCube d 0) 0 s
              Homogenization.Book.Ch02.MultiscaleExponent.infinity
              (chart z r hr a w r') a0
          else
            SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
              (Homogenization.originCube d 0) 0 s
              Homogenization.Book.Ch02.MultiscaleExponent.infinity q.toReal
              (chart z r hr a w r') a0).toReal
  lam_pos : ∀ z r hr a w r' s q, 0 < lam z r hr a w r' s q
  Lam_pos : ∀ z r hr a w r' s q, 0 < Lam z r hr a w r' s q
  err_nonneg : ∀ z r hr a w r' a₀ s q, 0 ≤ err z r hr a w r' a₀ s q
  /-- `e.ellipticities.monotone.ordered`: `λ` is nondecreasing in the order. -/
  lam_mono : ∀ z r hr a w r' q (s s' : ℝ), s ≤ s' →
    lam z r hr a w r' s q ≤ lam z r hr a w r' s' q
  /-- (i) `e.J.general`: `J(U,p,q;a)` is the supremum of the response values over
  `a`-harmonic `v ∈ H¹(U)`.  Upstream `responseJ` is that supremum by definition; this
  field records that it is a genuine least upper bound. -/
  responseJ_isLUB : ∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.Book.Ch02.CoeffOn U) (p q : Homogenization.Vec d),
      IsLUB (Homogenization.Book.Ch02.responseValueSet U a p q)
        (Homogenization.Book.Ch02.responseJ U a p q)
  /-- (ii) The coarse-grained matrices `a(U)`, `a_*(U)` exist on every domain: this is
  the matrix-extraction statement behind `e.variational.a`. -/
  matrices : ∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.Book.Ch02.CoeffOn U),
      Homogenization.Book.Ch02.ResponseMatrixExists U a
  /-- (iii) `e.variational.a`, the split
  `J(U,p,q;a) = ½ p·a(U)p + ½ q·a_*^{-1}(U)q − p·q`.  At a symmetric coefficient the
  upstream cross matrix `kappa` vanishes, so the general upstream formula collapses to
  the paper's. -/
  responseJ_split : ∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.Book.Ch02.CoeffOn U),
      Homogenization.Book.Ch02.CoeffOn.IsSymmetric a →
      ∀ p q : Homogenization.Vec d,
      Homogenization.Book.Ch02.responseJ U a p q =
        (1 / 2 : ℝ) * Homogenization.vecDot p
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) p) +
          (1 / 2 : ℝ) * Homogenization.vecDot q
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) q) -
          Homogenization.vecDot p q
  /-- (iv) `e.ord.bounds.truncated`:
  `(⨍_U a^{-1})^{-1} ≤ a_*(U) ≤ a(U) ≤ ⨍_U a`, the first inequality in the equivalent
  inverted form `a_*^{-1}(U) ≤ ⨍_U a^{-1}`.  Written by testing the quadratic forms, as
  upstream states them. -/
  ord_bounds : ∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.Book.Ch02.CoeffOn U),
      Homogenization.Book.Ch02.CoeffOn.IsSymmetric a →
      ∀ p : Homogenization.Vec d,
      Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) p) ≤
        Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.averagedSymmPartInv U a) p) ∧
      Homogenization.vecDot p
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarCoarse U a) p) ≤
        Homogenization.vecDot p
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) p) ∧
      Homogenization.vecDot p
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) p) ≤
        Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.averageMat U a.toCoeffField) p)
  /-- (v) `aux_in_J_responseJ_subadditive` / `e.subadditivity.J`, at the paper's strength: for
  **every** finite measurable partition `{U_i}` of the bounded Lipschitz domain `U` up to
  a null set, `J(U,p,q;a) ≤ Σ_i (|U_i|/|U|) J(U_i,p,q;a)`.

  Stated for an arbitrary finite family, not for the equi-depth triadic one.  The paper
  uses it  for the partition into the *retained* cubes, which is a proper
  subfamily of the level-`j` descendants and therefore not an equi-depth descendant
  family; an equi-depth-only field would not cover that use.

  The full measurable-partition statement is proved in this file as
  `aux_in_J_responseJ_subadditive`: restrict each harmonic competitor to a
  measurable piece using zero extension of `H¹₀` tests, split its integral
  across the a.e.-disjoint partition, then compare each cell value with its
  variational supremum. The older proposed triadic-refinement argument did
  not justify arbitrary measurable pieces. -/
  responseJ_subadditive : ∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.CoeffField d) (lam Lam : ℝ),
      Homogenization.IsEllipticFieldOn lam Lam (U : Set (Homogenization.Vec d)) a →
      ∀ (n : ℕ) (V : Fin n → Set (Homogenization.Vec d)),
        (∀ i, MeasurableSet (V i)) →
        (∀ i, V i ⊆ (U : Set (Homogenization.Vec d))) →
        (∀ i j, i ≠ j → volume (V i ∩ V j) = 0) →
        volume ((U : Set (Homogenization.Vec d)) \ ⋃ i, V i) = 0 →
      ∀ p q : Homogenization.Vec d,
      Homogenization.ResponseJ (U : Set (Homogenization.Vec d)) p q a ≤
        ∑ i : Fin n,
          (volume.real (V i) / volume.real (U : Set (Homogenization.Vec d))) *
            Homogenization.ResponseJ (V i) p q a
  /-- (vi) Scalar homogeneity :
  `J(U, a₀^{-1/2}e, a₀^{1/2}e; a) = J(U, e, e; a/a₀)` for a scalar `a₀ > 0`, obtained by
  substituting `v = a₀^{-1/2} w`.  The rescaled coefficient is a second `CoeffOn` tied to
  the first pointwise, since upstream `CoeffOn` carries its own ellipticity bounds and is
  not closed under scalar multiplication. -/
  responseJ_scalar_hom : ∀ (U : Homogenization.Book.Ch02.Domain d)
      (a b : Homogenization.Book.Ch02.CoeffOn U) (a0 : ℝ), 0 < a0 →
      (∀ x : Homogenization.Vec d, b.toCoeffField x = a0⁻¹ • a.toCoeffField x) →
      ∀ e : Homogenization.Vec d,
      Homogenization.Book.Ch02.responseJ U a
          ((Real.sqrt a0)⁻¹ • e) (Real.sqrt a0 • e) =
        Homogenization.Book.Ch02.responseJ U b e e
  /-- (vii) `e.coarse.grained.matrix.deviation.by.J` :
  `|a₀^{-1}a(U) − 1|² + |a₀a_*^{-1}(U) − 1|² ≤ C·J·(1+J)` with
  `J = max_{|e|=1} J(U, a₀^{-1/2}e, a₀^{1/2}e; a)`.  Tested on unit vectors: the paper
  applies it only at unit slopes and `Mat d` carries no norm upstream. -/
  deviation_by_J : ∃ C : ℝ, 0 < C ∧
      ∀ (U : Homogenization.Book.Ch02.Domain d)
        (a : Homogenization.Book.Ch02.CoeffOn U),
        Homogenization.Book.Ch02.CoeffOn.IsSymmetric a →
      ∀ a0 : ℝ, 0 < a0 →
      ∀ Jmax : ℝ,
        IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
            Homogenization.vecNormSq e = 1 ∧
            t = Homogenization.Book.Ch02.responseJ U a
              ((Real.sqrt a0)⁻¹ • e) (Real.sqrt a0 • e)} Jmax →
      ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
        (a0⁻¹ * Homogenization.vecDot e
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaCoarse U a) e) - 1) ^ 2 +
          (a0 * Homogenization.vecDot e
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) e) - 1) ^ 2 ≤
        C * Jmax * (1 + Jmax)
  /-- (viii) Definition `d.mathcal.E`, scale covariance of the coarse ellipticities.
  `λ_{s,q}` is defined by a scale-indexed sum over the sub-cubes of its root, relative to
  that root, so it is unchanged by translating and dilating the cube together with the
  coefficient: `λ_{s,q}(z + r𝕔_0 ; a) = λ_{s,q}(z' + 𝕔_0 ; a∘T)` where `T` is the affine map
  carrying the unit cube about `z'` onto the cube of side `r` about `z`.

  This is what the paper uses at  ("translation and dilation give the statement on
  each fixed cube") and it is part of the definition this remark's item (viii) references,
  which is why it belongs here rather than in a consumer.  The rescaled coefficient is a
  second `PositiveCoefficient` tied pointwise almost everywhere to the first, the same
  device `responseJ_scalar_hom` uses, since `PositiveCoefficient` on two different cubes
  cannot be compared directly. -/
  lam_dilation : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (z' : SpatialCoordinates d) (h1 : (0 : ℝ) < 1)
      (b : PositiveCoefficient (centeredCube z' 1 h1)),
      (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        b.val x = a.val (fun i => z i + r * (x i - z' i))) →
      ∀ (s : ℝ) (q : ℝ≥0∞),
        lam z r hr a z r s q = lam z' 1 h1 b z' 1 s q
  /-- (viii) The same covariance for `Λ_{s,q}`, which the boundary-extension branch needs. -/
  Lam_dilation : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (z' : SpatialCoordinates d) (h1 : (0 : ℝ) < 1)
      (b : PositiveCoefficient (centeredCube z' 1 h1)),
      (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        b.val x = a.val (fun i => z i + r * (x i - z' i))) →
      ∀ (s : ℝ) (q : ℝ≥0∞),
        Lam z r hr a z r s q = Lam z' 1 h1 b z' 1 s q
  /-- the coarse matrix ordering, `e.bound.Lambdas.by.Es`, for `s ∈ (0,1]`, `q ∈ {1,2}` and a
  positive scalar reference `a₀`: the two-sided comparison of the coarse
  ellipticities with the homogenization error.  At `q = 2` the upper bound is the
  printed `1 + 2E² + 2E`; at `q = 1` it is `(1 + √2 E)²`, the corrected constant of
  deviation  (the printed `q = 1`
  constant is false; GMC proves `√(a₀⁻¹Λ_{s,1}), √(a₀λ_{s,1}⁻¹) ≤ 1 + √2 E`). -/
  bound_ellipticities_by_error : ∀ z r hr a w r' (a₀ : ℝ), 0 < a₀ →
    ∀ (s : ℝ), s ∈ Set.Ioc (0:ℝ) 1 → ∀ q : ℝ≥0∞, q = 1 ∨ q = 2 →
      (1 / 2) * err z r hr a w r' a₀ s q ^ 2 ≤
          max (a₀⁻¹ * Lam z r hr a w r' s q) (a₀ * (lam z r hr a w r' s q)⁻¹) ∧
        max (a₀⁻¹ * Lam z r hr a w r' s q) (a₀ * (lam z r hr a w r' s q)⁻¹) ≤
          (if q = 1 then (1 + Real.sqrt 2 * err z r hr a w r' a₀ s q) ^ 2
            else 1 + 2 * err z r hr a w r' a₀ s q ^ 2 + 2 * err z r hr a w r' a₀ s q)

end SubdiffusiveProcess.Paper
