import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
import Mathlib.Probability.IdentDistribIndep
import SubdiffusiveProcess.Paper.stationary_family
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedStoppingAmbient
import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.LogHomogenizedBound
import SubdiffusiveProcess.Paper.finite_cutoff_log_abs_majorant
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
import Homogenization.Geometry.CubeColoring
import Homogenization.Book.Ch04.TriadicCubeTranslation
import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Geometry
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.OneCubeEllipticityComparison
import Homogenization.Book.Ch02.Theorems.Dilation
import Homogenization.CoarseGraining.Translation
import Homogenization.Geometry.TriadicCubeTranslation
import Homogenization.Internal.Ch02.Adapters
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.NormalizerSwap
import SubdiffusiveProcess.Paper.in_moments_response_moment
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.CoarseGrainingVocab.Core
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.coefficient_physical_identity
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.lem_extremes
import Homogenization.Book.Ch04.Theorems.WidetildeTheta
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CutoffDirichletExistence
import SubdiffusiveProcess.Lane4.Bridge
import Homogenization.Book.Ch05.Theorems.Section57.UniformEllipticityBridge
import SubdiffusiveProcess.Main.InfraredAdmissible


open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper




/-- The exponent `2` of the target coarse ellipticities, read in `in_J`'s convention. -/
theorem aux_lem_extension_cell_moment_exponent_two :
    (if (2 : ℝ≥0∞) = ⊤ then Homogenization.Book.Ch02.MultiscaleExponent.infinity
      else Homogenization.Book.Ch02.MultiscaleExponent.finite (2 : ℝ≥0∞).toReal) =
      Homogenization.Book.Ch02.MultiscaleExponent.finite 2 := by
  simp

/-- The order `s = (β - 1/2)/4` lies in `(0, 1]`. -/
theorem aux_lem_extension_cell_moment_order {beta : ℝ}
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor <;> linarith [hbeta.1, hbeta.2]

/-- `in_J`'s `Λ_{s,2}` is the discounted sum of the descendant `|b|` maxima of the chart. -/
theorem aux_lem_extension_cell_moment_Lam_eq_tsum {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    E.Lam z r hr a w r' s 2 =
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n *
        Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
          (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)) (E.chart z r hr a w r') := by
  rw [E.Lam_eq z r hr a w r' hr' hsub s hs 2 (by norm_num),
    aux_lem_extension_cell_moment_exponent_two]
  simp only [Homogenization.Book.Ch02.LambdaSq, Homogenization.Book.Ch02.LambdaSqFinite]
  norm_num

/-- `in_J`'s `λ_{s,2}⁻¹` is the discounted sum of the descendant `|σ_*⁻¹|` maxima of the chart. -/
theorem aux_lem_extension_cell_moment_lam_inv_eq_tsum {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    (E.lam z r hr a w r' s 2)⁻¹ =
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)) (E.chart z r hr a w r') := by
  rw [E.lam_eq z r hr a w r' hr' hsub s hs 2 (by norm_num),
    aux_lem_extension_cell_moment_exponent_two]
  simp only [Homogenization.Book.Ch02.lambdaSq, Homogenization.Book.Ch02.lambdaSqFinite]
  norm_num
  rw [Real.rpow_neg_one, inv_inv]

/-- The discounted weights `c_{s,2} 3^{-2sn}` are nonnegative. -/
theorem aux_lem_extension_cell_moment_weight_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 n := by
  unfold Homogenization.Book.Ch02.geometricWeight Homogenization.Book.Ch02.geometricDiscount
  refine mul_nonneg ?_ (Real.rpow_nonneg (by norm_num) _)
  have h : Real.rpow (3 : ℝ) (-s * 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  linarith

/-- A finite supremum of nonnegative reals is nonnegative. -/
theorem aux_lem_extension_cell_moment_finsetSupReal_nonneg {α : Type*} (S : Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ Homogenization.Book.Ch02.finsetSupReal S f :=
  Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact hf x)

/-- Every member value is below the finite supremum. -/
theorem aux_lem_extension_cell_moment_le_finsetSupReal {α : Type*} (S : Finset α)
    (f : α → ℝ) {x : α} (hx : x ∈ S) :
    f x ≤ Homogenization.Book.Ch02.finsetSupReal S f :=
  le_csSup (((S : Set α).toFinite).image f).bddAbove ⟨x, hx, rfl⟩

/-- A nonnegative real series whose `tsum` is nonzero is summable, so it dominates each
term.  (A non-summable real series has `tsum = 0`.) -/
theorem aux_lem_extension_cell_moment_term_le_tsum {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∑' n, f n ≠ 0) (n : ℕ) : f n ≤ ∑' m, f m := by
  have hs : Summable f := by
    by_contra hns
    exact h (tsum_eq_zero_of_not_summable hns)
  exact hs.le_tsum n (fun m _ => hf m)

/-- Deterministic lower bound: `Λ_{s,2}` of a sub-cube dominates the discounted `|b|` of any
chart descendant at any depth.  Summability is forced by `in_J.Lam_pos`. -/
theorem aux_lem_extension_cell_moment_Lam_ge_term {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (n : ℕ) {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ))) :
    Homogenization.Book.Ch02.geometricWeight s 2 n *
        Homogenization.Book.Ch02.coarseBMatrixNorm R (E.chart z r hr a w r') ≤
      E.Lam z r hr a w r' s 2 := by
  have heq := aux_lem_extension_cell_moment_Lam_eq_tsum E z r hr a w r' hr' hsub s hs
  have hnn : ∀ m : ℕ, 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 m *
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
        (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (m : ℤ)) (E.chart z r hr a w r') :=
    fun m => mul_nonneg (aux_lem_extension_cell_moment_weight_nonneg hs.1.le m)
      (aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _)
  have hne : (∑' m : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 m *
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
        (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (m : ℤ)) (E.chart z r hr a w r')) ≠ 0 := by
    rw [← heq]; exact (E.Lam_pos _ _ _ _ _ _ _ _).ne'
  rw [heq]
  refine le_trans ?_ (aux_lem_extension_cell_moment_term_le_tsum hnn hne n)
  exact mul_le_mul_of_nonneg_left
    (aux_lem_extension_cell_moment_le_finsetSupReal _
      (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R (E.chart z r hr a w r')) hR)
    (aux_lem_extension_cell_moment_weight_nonneg hs.1.le n)

/-- Deterministic lower bound: `λ_{s,2}⁻¹` of a sub-cube dominates the discounted
`|σ_*⁻¹|` of any chart descendant at any depth.  Summability is forced by `in_J.lam_pos`. -/
theorem aux_lem_extension_cell_moment_lam_inv_ge_term {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (n : ℕ) {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ))) :
    Homogenization.Book.Ch02.geometricWeight s 2 n *
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (E.chart z r hr a w r') ≤
      (E.lam z r hr a w r' s 2)⁻¹ := by
  have heq := aux_lem_extension_cell_moment_lam_inv_eq_tsum E z r hr a w r' hr' hsub s hs
  have hnn : ∀ m : ℕ, 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 m *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (m : ℤ)) (E.chart z r hr a w r') :=
    fun m => mul_nonneg (aux_lem_extension_cell_moment_weight_nonneg hs.1.le m)
      (aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _)
  have hne : (∑' m : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 m *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (m : ℤ)) (E.chart z r hr a w r')) ≠ 0 := by
    rw [← heq]; exact (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)).ne'
  rw [heq]
  refine le_trans ?_ (aux_lem_extension_cell_moment_term_le_tsum hnn hne n)
  exact mul_le_mul_of_nonneg_left
    (aux_lem_extension_cell_moment_le_finsetSupReal _
      (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
        (E.chart z r hr a w r')) hR)
    (aux_lem_extension_cell_moment_weight_nonneg hs.1.le n)

/-! ### Measurability of the target observable

The chart of `in_J` is pinned only almost everywhere, so measurability is transported to a
canonical regular coefficient field: the continuous rescaled cutoff field
`x ↦ A_N(w + r' x)`, whose pushforward law is a Chapter 4 law carrier. -/

/-- The cutoff coefficient `A_N` as a continuous function on all of space. -/
def aux_lem_extension_cell_moment_cutoffCM {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ) :
    C(SpatialCoordinates d, ℝ) :=
  ⟨cutoffCoefficient M H om N, cutoffCoefficient_continuous M H om N⟩

/-- The affine chart `x ↦ w + r' x` of a cell. -/
def aux_lem_extension_cell_moment_affine {d : ℕ} (w : SpatialCoordinates d) (r' : ℝ) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun x i => w i + r' * x i, by fun_prop⟩

/-- The rescaled cutoff coefficient `x ↦ A_N(w + r' x)` in the chart of a cell. -/
def aux_lem_extension_cell_moment_chartCM {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) (r' : ℝ) : C(SpatialCoordinates d, ℝ) :=
  (aux_lem_extension_cell_moment_cutoffCM M H om N).comp
    (aux_lem_extension_cell_moment_affine w r')

theorem aux_lem_extension_cell_moment_chartCM_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) (r' : ℝ) (x : SpatialCoordinates d) :
    aux_lem_extension_cell_moment_chartCM M H om N w r' x =
      cutoffCoefficient M H om N (fun i => w i + r' * x i) := rfl

/-- The cutoff coefficient is a measurable continuous-function-valued random variable,
given a measurable infrared field. -/
theorem aux_lem_extension_cell_moment_measurable_cutoffCM {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ) :
    Measurable (fun om => aux_lem_extension_cell_moment_cutoffCM M H om N) := by
  let c : ℝ := (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹
  let K : ℝ := (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  let Φ : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) := fun g =>
    c • (ContinuousMap.comp ⟨Real.exp, Real.continuous_exp⟩
      (g - ContinuousMap.const _ K))
  have hΦ : Continuous Φ :=
    ((ContinuousMap.continuous_postcomp _).comp
      (continuous_id.sub continuous_const)).const_smul c
  have hpot : Measurable (fun om : BilateralField d =>
      H om + ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j))) :=
    hH.add (Finset.measurable_sum _ fun j _ => measurable_pi_apply _)
  have heq : (fun om => aux_lem_extension_cell_moment_cutoffCM M H om N) =
      fun om => Φ (H om + ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j))) := by
    funext om
    ext x
    simp [aux_lem_extension_cell_moment_cutoffCM, Φ, c, K, cutoffCoefficient,
      cutoffPotential]
  rw [heq]
  exact hΦ.measurable.comp hpot

/-- The rescaled cutoff coefficient is a measurable random variable. -/
theorem aux_lem_extension_cell_moment_measurable_chartCM {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (w : SpatialCoordinates d) (r' : ℝ) :
    Measurable (fun om => aux_lem_extension_cell_moment_chartCM M H om N w r') :=
  (ContinuousMap.continuous_precomp (aux_lem_extension_cell_moment_affine w r')).measurable.comp
    (aux_lem_extension_cell_moment_measurable_cutoffCM M H hH N)

/-- A continuous scalar field as a regular Chapter 4 coefficient field. -/
def aux_lem_extension_cell_moment_scalarReg {d : ℕ} (f : C(SpatialCoordinates d, ℝ)) :
    Homogenization.RegCoeffField d where
  toFun x := Homogenization.scalarMatrix (f x)
  entry_measurable := by
    intro i j
    have hf : Continuous (fun x : SpatialCoordinates d =>
        Homogenization.scalarMatrix (f x) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp
        (f.continuous.smul (continuous_const : Continuous (fun _ : SpatialCoordinates d =>
          (1 : Homogenization.Mat d)))))
    exact hf.measurable
  entry_locInt := by
    intro i j
    have hf : Continuous (fun x : SpatialCoordinates d =>
        Homogenization.scalarMatrix (f x) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp
        (f.continuous.smul (continuous_const : Continuous (fun _ : SpatialCoordinates d =>
          (1 : Homogenization.Mat d)))))
    exact hf.locallyIntegrable

theorem aux_lem_extension_cell_moment_measurable_scalarReg {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    Measurable (aux_lem_extension_cell_moment_scalarReg (d := d)) := by
  refine Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    have hy : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f y) :=
      (continuous_eval_const y).measurable
    simpa [aux_lem_extension_cell_moment_scalarReg, Homogenization.scalarMatrix] using
      hy.mul measurable_const
  · intro i j φ hφ
    let F : C(SpatialCoordinates d, ℝ) × SpatialCoordinates d → ℝ := fun z =>
      Homogenization.scalarMatrix (z.1 z.2) i j * φ z.2
    have heval : Measurable (fun z : C(SpatialCoordinates d, ℝ) ×
        SpatialCoordinates d => z.1 z.2) :=
      ContinuousEval.continuous_eval.measurable
    have hmat' : Measurable (fun z : C(SpatialCoordinates d, ℝ) ×
        SpatialCoordinates d => (z.1 z.2) • (1 : Homogenization.Mat d)) :=
      heval.smul (measurable_const : Measurable (fun _ : C(SpatialCoordinates d, ℝ) ×
          SpatialCoordinates d => (1 : Homogenization.Mat d)))
    have hmat : Measurable (fun z : C(SpatialCoordinates d, ℝ) ×
        SpatialCoordinates d => Homogenization.scalarMatrix (d := d) (z.1 z.2)) := by
      simpa only [Homogenization.scalarMatrix] using hmat'
    have hF : Measurable F :=
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmat)).mul
        (hφ.measurable.comp measurable_snd)
    have hInt : StronglyMeasurable (fun f : C(SpatialCoordinates d, ℝ) =>
        ∫ x, F (f, x) ∂volume) :=
      hF.stronglyMeasurable.integral_prod_right'
    simpa [F, Homogenization.entryTestR, aux_lem_extension_cell_moment_scalarReg] using
      hInt.measurable

theorem aux_lem_extension_cell_moment_scalarReg_elliptic {d : ℕ}
    (f : C(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 < f x) :
    Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (aux_lem_extension_cell_moment_scalarReg f) := by
  classical
  intro Q
  let W : Set (SpatialCoordinates d) := Homogenization.openCubeSet Q
  have hgeom := Homogenization.isOpenBoundedConvexDomain_openCubeSet Q
  have hcompact : IsCompact (closure W) :=
    hgeom.isBoundedDomain.isBounded.isCompact_closure
  have hne : (closure W).Nonempty := by
    refine ⟨fun i => (Q.index i : ℝ) * Homogenization.cubeScaleFactor Q, ?_⟩
    have hs : 0 < Homogenization.cubeScaleFactor Q := by
      simpa [Homogenization.cubeScaleFactor] using
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
    simpa [Set.piecewise] using
      Measurable.piecewise hgeom.isOpen.measurableSet
        f.continuous.measurable measurable_const
  have hEll : Homogenization.IsEllipticFieldOn (f xmin) (f xmax) W
      (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField f) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds
      hminpos hmeas (fun x hx => hmin (subset_closure hx))
        (fun x hx => hmax (subset_closure hx))
  refine ⟨f xmin, f xmax, hminpos, hminmax, ?_⟩
  change Homogenization.IsAEEllipticFieldOn (f xmin) (f xmax) W
    (aux_lem_extension_cell_moment_scalarReg f).toFun
  apply Homogenization.IsAEEllipticFieldOn.of_isEllipticFieldOn
  simpa [W, aux_lem_extension_cell_moment_scalarReg,
    SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField] using hEll

/-- The Chapter 4 local-ellipticity event is measurable in the carrier. -/
theorem aux_lem_extension_cell_moment_measurableSet_elliptic (d : ℕ) :
    MeasurableSet {a : Homogenization.RegCoeffField d |
      Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a} := by
  classical
  have hEq : {a : Homogenization.RegCoeffField d |
      Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a} =
      ⋂ Q : Homogenization.TriadicCube d, ⋃ k : ℕ,
        {a : Homogenization.RegCoeffField d |
          Homogenization.AEEQuantitativeEllipticSlice
            (Homogenization.cubeSet Q) k a.toFun} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro ha Q
      exact ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro ha Q
      obtain ⟨k, hk⟩ := ha Q
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      have h1le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hle : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 :=
        le_trans ((inv_le_one₀ (by positivity)).2 h1le) h1le
      refine ⟨((k : ℝ) + 1)⁻¹, (k : ℝ) + 1, hkpos, hle, ?_⟩
      have hslice : Homogenization.IsAEEllipticFieldOn ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)
          (Homogenization.cubeSet Q) a.toFun := hk
      exact hslice.mono (Homogenization.measurableSet_openCubeSet Q)
        (Homogenization.openCubeSet_subset_cubeSet Q)
  rw [hEq]
  refine MeasurableSet.iInter fun Q => MeasurableSet.iUnion fun k => ?_
  exact Homogenization.LocalSigmaR_le (Homogenization.cubeSet Q) _
    (Homogenization.Book.Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k)

/-- The canonical regular field of the rescaled cutoff coefficient. -/
def aux_lem_extension_cell_moment_regField {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (w : SpatialCoordinates d) (r' : ℝ) (om : BilateralField d) :
    Homogenization.RegCoeffField d :=
  aux_lem_extension_cell_moment_scalarReg (aux_lem_extension_cell_moment_chartCM M H om N w r')

theorem aux_lem_extension_cell_moment_regField_elliptic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (w : SpatialCoordinates d) (r' : ℝ) (om : BilateralField d) :
    Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (aux_lem_extension_cell_moment_regField M H N w r' om) :=
  aux_lem_extension_cell_moment_scalarReg_elliptic _ fun _ =>
    cutoffCoefficient_pos M H om N _

theorem aux_lem_extension_cell_moment_measurable_regField {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (w : SpatialCoordinates d) (r' : ℝ) :
    Measurable (aux_lem_extension_cell_moment_regField M H N w r') :=
  aux_lem_extension_cell_moment_measurable_scalarReg.comp
    (aux_lem_extension_cell_moment_measurable_chartCM M H hH N w r')

/-- The pushforward of the chaos law under the rescaled cutoff field is a Chapter 4 law
carrier. -/
theorem aux_lem_extension_cell_moment_lawCarrier {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (w : SpatialCoordinates d) (r' : ℝ) :
    Homogenization.Book.Ch04.RestrictionLawCarrier
      (Measure.map (aux_lem_extension_cell_moment_regField M H N w r')
        (chaosSampleLaw M).toMeasure) := by
  have hmeas := aux_lem_extension_cell_moment_measurable_regField M H hH N w r'
  haveI : IsProbabilityMeasure
      (Measure.map (aux_lem_extension_cell_moment_regField M H N w r')
        (chaosSampleLaw M).toMeasure) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine Homogenization.Book.Ch04.lawCarrier_of_aeLocallyUniformlyElliptic ?_
  rw [Homogenization.Book.Ch04.AELocallyUniformlyEllipticLaw,
    ae_map_iff hmeas.aemeasurable (aux_lem_extension_cell_moment_measurableSet_elliptic d)]
  exact Filter.Eventually.of_forall fun om =>
    aux_lem_extension_cell_moment_regField_elliptic M H N w r' om

section CarrierObservables

open Homogenization Homogenization.Book Homogenization.Book.Ch04
open Homogenization.Book.Ch04.RestrictionLawCarrier
open scoped Matrix.Norms.L2Operator

/-- Per-scale `|b|` maximum over the depth-`n` descendants is a.e.-measurable under a law
carrier (the `q = 2` analogue of the upstream private lemma). -/
theorem aux_lem_extension_cell_moment_aemeasurable_maxB {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (n : ℕ) :
    AEMeasurable (fun a : RegCoeffField d =>
      maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a) P := by
  classical
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  let sDesc := descendantsAtScale Q (Q.scale - (n : ℤ))
  have hsDesc : sDesc.Nonempty :=
    descendantsAtScale_nonempty Q (sub_le_self Q.scale hn)
  have hsup :
      AEMeasurable
        (sDesc.sup' hsDesc
          (fun R (a : RegCoeffField d) =>
            Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft)) P := by
    refine aemeasurable_finset_sup' hsDesc ?_
    intro R _hR
    simpa [Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using
      (hP.aemeasurable_coarseB_cubeSet R).norm
  have hfin :
      AEMeasurable
        (fun a : RegCoeffField d =>
          Ch02.finsetSupReal sDesc
            (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft)) P := by
    convert hsup using 1
    ext a
    rw [Finset.sup'_apply]
    exact finsetSupReal_eq_sup' sDesc hsDesc
      (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft)
  refine hfin.congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  simpa [sDesc] using
    (maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      (a := a) ha Q (Q.scale - (n : ℤ))).symm

/-- Per-scale `|σ_*⁻¹|` maximum over the depth-`n` descendants is a.e.-measurable under a
law carrier. -/
theorem aux_lem_extension_cell_moment_aemeasurable_maxS {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (n : ℕ) :
    AEMeasurable (fun a : RegCoeffField d =>
      maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a) P := by
  classical
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  let sDesc := descendantsAtScale Q (Q.scale - (n : ℤ))
  have hsDesc : sDesc.Nonempty :=
    descendantsAtScale_nonempty Q (sub_le_self Q.scale hn)
  have hsup :
      AEMeasurable
        (sDesc.sup' hsDesc
          (fun R (a : RegCoeffField d) =>
            Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight)) P := by
    refine aemeasurable_finset_sup' hsDesc ?_
    intro R _hR
    simpa [Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using
      (hP.aemeasurable_coarseSigmaStarInv_cubeSet R).norm
  have hfin :
      AEMeasurable
        (fun a : RegCoeffField d =>
          Ch02.finsetSupReal sDesc
            (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight)) P := by
    convert hsup using 1
    ext a
    rw [Finset.sup'_apply]
    exact finsetSupReal_eq_sup' sDesc hsDesc
      (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight)
  refine hfin.congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  simpa [sDesc] using
    (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      (a := a) ha Q (Q.scale - (n : ℤ))).symm

/-- The discounted `q = 2` series of `|b|` maxima is a.e.-measurable under a law carrier. -/
theorem aux_lem_extension_cell_moment_aemeasurable_tsumB {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    AEMeasurable (fun a : RegCoeffField d =>
      ∑' n : ℕ, Ch02.geometricWeight s 2 n *
        maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a) P := by
  refine aemeasurable_of_tendsto_metrizable_ae (Filter.atTop : Filter ℕ)
    (f := fun N a => ∑ n ∈ Finset.range N, Ch02.geometricWeight s 2 n *
      maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a) ?_ ?_
  · intro N
    exact Finset.aemeasurable_fun_sum (μ := P) (Finset.range N) fun n _ =>
      (aux_lem_extension_cell_moment_aemeasurable_maxB hP Q n).const_mul _
  · refine Filter.Eventually.of_forall fun a => HasSum.tendsto_sum_nat (Summable.hasSum ?_)
    classical
    by_cases ha : AELocallyUniformlyEllipticField a
    · have h := Ch02.summable_B_series_pointwiseCoeffField Q
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hs
        (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      simpa [maxDescendantBMatrixNormCoeffFieldAtScale, ha] using h
    · simpa [maxDescendantBMatrixNormCoeffFieldAtScale, ha] using
        (summable_zero : Summable (fun _n : ℕ => (0 : ℝ)))

/-- The discounted `q = 2` series of `|σ_*⁻¹|` maxima is a.e.-measurable under a law
carrier. -/
theorem aux_lem_extension_cell_moment_aemeasurable_tsumS {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    AEMeasurable (fun a : RegCoeffField d =>
      ∑' n : ℕ, Ch02.geometricWeight s 2 n *
        maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a) P := by
  refine aemeasurable_of_tendsto_metrizable_ae (Filter.atTop : Filter ℕ)
    (f := fun N a => ∑ n ∈ Finset.range N, Ch02.geometricWeight s 2 n *
      maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a) ?_ ?_
  · intro N
    exact Finset.aemeasurable_fun_sum (μ := P) (Finset.range N) fun n _ =>
      (aux_lem_extension_cell_moment_aemeasurable_maxS hP Q n).const_mul _
  · refine Filter.Eventually.of_forall fun a => HasSum.tendsto_sum_nat (Summable.hasSum ?_)
    classical
    by_cases ha : AELocallyUniformlyEllipticField a
    · have h := Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hs
        (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      simpa [maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha] using h
    · simpa [maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha] using
        (summable_zero : Summable (fun _n : ℕ => (0 : ℝ)))

end CarrierObservables

/-- The unit root `openCubeSet (originCube d 0)` is the open cube `(-1/2, 1/2)^d`. -/
theorem aux_lem_extension_cell_moment_mem_unit_root {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) (i : Fin d) :
    -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
  have h : ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
    simpa [Homogenization.openCubeSet, Homogenization.originCube,
      Homogenization.cubeScaleFactor] using hx
  exact h i

/-- The affine chart maps the unit root into the cell. -/
theorem aux_lem_extension_cell_moment_affine_mem {d : ℕ} (w : SpatialCoordinates d)
    (r' : ℝ) (hr' : 0 < r') {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    (fun i => w i + r' * x i) ∈ (centeredCube w r' hr' : Set (SpatialCoordinates d)) := by
  rw [centeredCube_eq_pi]
  intro i _
  obtain ⟨h1, h2⟩ := aux_lem_extension_cell_moment_mem_unit_root hx i
  have h1' : r' * (-(1 / 2 : ℝ)) < r' * x i := mul_lt_mul_of_pos_left h1 hr'
  have h2' : r' * x i < r' * (1 / 2 : ℝ) := mul_lt_mul_of_pos_left h2 hr'
  constructor <;> linarith

/-- The affine chart is quasi-measure-preserving for Lebesgue measure. -/
theorem aux_lem_extension_cell_moment_qmp_affine {d : ℕ} (w : SpatialCoordinates d)
    (r' : ℝ) (hr' : 0 < r') :
    Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => fun i => w i + r' * x i)
      volume volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => r' • y)
      volume volume :=
    Measure.quasiMeasurePreserving_smul volume hr'.ne'
  have h2 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => y + w)
      volume volume :=
    (measurePreserving_add_right volume w).quasiMeasurePreserving
  have heq : (fun x : SpatialCoordinates d => fun i => w i + r' * x i) =
      (fun y : SpatialCoordinates d => y + w) ∘ (fun y : SpatialCoordinates d => r' • y) := by
    funext x i
    simp [add_comm]
  rw [heq]
  exact h2.comp h1

/-- Almost-everywhere statements on a set pull back along a quasi-measure-preserving map
that sends a second set into the first. -/
theorem aux_lem_extension_cell_moment_ae_restrict_comp {d : ℕ}
    {f : SpatialCoordinates d → SpatialCoordinates d}
    (hf : Measure.QuasiMeasurePreserving f volume volume) {S S' : Set (SpatialCoordinates d)}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hmaps : ∀ y ∈ S', f y ∈ S)
    {P : SpatialCoordinates d → Prop} (h : ∀ᵐ x ∂volume.restrict S, P x) :
    ∀ᵐ y ∂volume.restrict S', P (f y) := by
  rw [ae_restrict_iff' hS] at h
  rw [ae_restrict_iff' hS']
  filter_upwards [hf.ae h] with y hy hyS'
  exact hy (hmaps y hyS')

/-- The actual root coefficient, read in the chart of a contained cell, is a.e. the rescaled
continuous cutoff field on every triadic sub-cube of the unit root. -/
theorem aux_lem_extension_cell_moment_chart_aeeq {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)))
    (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0))
    (hell : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (aux_lem_extension_cell_moment_regField M H N w r' om)) :
    Homogenization.Book.Ch02.CoeffOn.AEEq
      ((E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r').coeffOn Q)
      ((Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (aux_lem_extension_cell_moment_regField M H N w r' om) hell).coeffOn Q) := by
  haveI : Fact ((centeredCube z0 R hR : Set (SpatialCoordinates d)) ⊆
      (closedCube z0 R hR : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube z0 hR⟩
  have hc := E.chart_eq z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r' hr' hsub Q hQ
  have h0 := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z0 R hR) (closedCube z0 R hR)
    (cutoffCoefficientCM M H om N z0 hR) (cutoffCoefficientCM_pos M H om N z0 hR) 1 one_pos
  have hQmeas : MeasurableSet (Homogenization.openCubeSet Q) :=
    Homogenization.measurableSet_openCubeSet Q
  have hmaps : ∀ x ∈ Homogenization.openCubeSet Q,
      (fun i => w i + r' * x i) ∈ (centeredCube z0 R hR : Set (SpatialCoordinates d)) :=
    fun x hx => hsub (aux_lem_extension_cell_moment_affine_mem w r' hr' (hQ hx))
  have hv := aux_lem_extension_cell_moment_ae_restrict_comp
    (aux_lem_extension_cell_moment_qmp_affine w r' hr')
    (centeredCube z0 R hR).isOpen.measurableSet hQmeas hmaps h0
  unfold Homogenization.Book.Ch02.CoeffOn.AEEq
  change ((E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r').coeffOn
      Q).toCoeffField =ᵐ[volume.restrict (Homogenization.openCubeSet Q)]
    (aux_lem_extension_cell_moment_regField M H N w r' om).toFun
  filter_upwards [hc, hv, ae_restrict_mem hQmeas] with x hcx hvx hxQ
  rw [hcx]
  have hval := hvx (hmaps x hxQ)
  change Homogenization.scalarMatrix
      ((cutoffPositiveCoefficient M H om N z0 hR).val (fun i => w i + r' * x i)) =
    Homogenization.scalarMatrix (cutoffCoefficient M H om N (fun i => w i + r' * x i))
  congr 1
  rw [div_one] at hval
  exact hval

/-- The chart's per-scale `|b|` maximum equals the canonical field's. -/
theorem aux_lem_extension_cell_moment_maxB_chart_eq {d : ℕ} [NeZero d] (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d))) (n : ℕ) :
    Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ))
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r') =
      Homogenization.Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
        (Homogenization.originCube d 0) ((Homogenization.originCube d 0).scale - (n : ℤ))
        (aux_lem_extension_cell_moment_regField M H N w r' om) := by
  classical
  have hell := aux_lem_extension_cell_moment_regField_elliptic M H N w r' om
  have hk : (Homogenization.originCube d 0).scale - (n : ℤ) ≤
      (Homogenization.originCube d 0).scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  simp only [Homogenization.Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dif_pos hell,
    Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale]
  refine Homogenization.Book.Ch02.finsetSupReal_congr _ fun Q hQ => ?_
  unfold Homogenization.Book.Ch02.coarseBMatrixNorm
  rw [Homogenization.Book.Ch02.bCoarse_eq_ofAEEq
    (aux_lem_extension_cell_moment_chart_aeeq E M H om N z0 R hR w r' hr' hsub Q
      (Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk hQ) hell)]

/-- The chart's per-scale `|σ_*⁻¹|` maximum equals the canonical field's. -/
theorem aux_lem_extension_cell_moment_maxS_chart_eq {d : ℕ} [NeZero d] (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d))) (n : ℕ) :
    Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ))
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r') =
      Homogenization.Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (Homogenization.originCube d 0) ((Homogenization.originCube d 0).scale - (n : ℤ))
        (aux_lem_extension_cell_moment_regField M H N w r' om) := by
  classical
  have hell := aux_lem_extension_cell_moment_regField_elliptic M H N w r' om
  have hk : (Homogenization.originCube d 0).scale - (n : ℤ) ≤
      (Homogenization.originCube d 0).scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  simp only [Homogenization.Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale,
    dif_pos hell, Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale]
  refine Homogenization.Book.Ch02.finsetSupReal_congr _ fun Q hQ => ?_
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
  rw [Homogenization.Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq
    (aux_lem_extension_cell_moment_chart_aeeq E M H om N z0 R hR w r' hr' hsub Q
      (Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk hQ) hell)]

/-- **Measurability clause of the target.**  For the actual root cutoff coefficient and any
cell contained in the root, `Λ_{s,2} + λ_{s,2}⁻¹` of the cell is a.e. strongly measurable
under the chaos law.  The observable is transported through the a.e. chart identity to the
canonical rescaled field, whose pushforward law is a Chapter 4 law carrier. -/
theorem aux_lem_extension_cell_moment_aestronglyMeasurable {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredAdmissible M H)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hcell : centeredCube w r' hr' ≤ centeredCube z0 R hR) :
    AEStronglyMeasurable (fun om =>
      E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r' s 2 +
        (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r' s 2)⁻¹)
      (chaosSampleLaw M).toMeasure := by
  haveI : NeZero d := ⟨by omega⟩
  have hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)) := hcell
  have hFm := aux_lem_extension_cell_moment_measurable_regField M H hH.measurable N w r'
  have hP := aux_lem_extension_cell_moment_lawCarrier M H hH.measurable N w r'
  have hB := (aux_lem_extension_cell_moment_aemeasurable_tsumB hP
    (Homogenization.originCube d 0) hs.1).comp_aemeasurable hFm.aemeasurable
  have hS := (aux_lem_extension_cell_moment_aemeasurable_tsumS hP
    (Homogenization.originCube d 0) hs.1).comp_aemeasurable hFm.aemeasurable
  refine (hB.add hS).aestronglyMeasurable.congr (Filter.Eventually.of_forall fun om => ?_)
  simp only [Function.comp_apply]
  rw [aux_lem_extension_cell_moment_Lam_eq_tsum E z0 R hR _ w r' hr' hsub s hs,
    aux_lem_extension_cell_moment_lam_inv_eq_tsum E z0 R hR _ w r' hr' hsub s hs]
  congr 1
  · refine tsum_congr fun n => ?_
    rw [aux_lem_extension_cell_moment_maxB_chart_eq E M H om N z0 R hR w r' hr' hsub n]
  · refine tsum_congr fun n => ?_
    rw [aux_lem_extension_cell_moment_maxS_chart_eq E M H om N z0 R hR w r' hr' hsub n]


section
open MeasureTheory ProbabilityTheory
open SubdiffusiveProcess
open scoped ENNReal

/-- Forget the derivative data of a native potential without changing its field. -/
def aux_lem_extension_cell_moment_forgetField {d : ℕ} :
    C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
  ⟨fun g => g.1.1, continuous_subtype_val.fst⟩

theorem aux_lem_extension_cell_moment_layerScaling_comp {d : ℕ} (a b : ℤ)
    (f : C(SpatialCoordinates d, ℝ)) :
    layerScaling d a (layerScaling d b f) = layerScaling d (a + b) f := by
  ext x
  change f ((3 : ℝ) ^ (-b) • ((3 : ℝ) ^ (-a) • x)) =
    f ((3 : ℝ) ^ (-(a + b)) • x)
  rw [smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  rw [show -b + -a = -(a + b) by omega]

theorem aux_lem_extension_cell_moment_map_layerScaling {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) (a b : ℤ) :
    Measure.map (layerScaling d a) (scaledLayerLaw d ν b).toMeasure =
      (scaledLayerLaw d ν (a + b)).toMeasure := by
  change Measure.map (layerScaling d a)
    (Measure.map (layerScaling d b) ν.toMeasure) =
    Measure.map (layerScaling d (a + b)) ν.toMeasure
  rw [Measure.map_map (layerScaling d a).continuous.measurable
    (layerScaling d b).continuous.measurable]
  congr 1
  funext f
  exact aux_lem_extension_cell_moment_layerScaling_comp a b f

/-- The physical layers, after reversing the finite cutoff and rescaling space,
have the joint law of every microscopic model layer, not just the same marginals.
This includes the ultraviolet block used by the frozen coarse-graining theorem. -/
theorem aux_lem_extension_cell_moment_microscopic_layers_identDistrib {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    IdentDistrib
      (fun om : BilateralField d => fun i : ℕ =>
        layerScaling d (N : ℤ) (om ((i : ℤ) - (N : ℤ))))
      (fun om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => fun i : ℕ =>
        aux_lem_extension_cell_moment_forgetField (om i))
      (chaosSampleLaw M).toMeasure M.P.toMeasure := by
  let ν := chaosRootFieldLaw M
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  have hind : iIndepFun (fun j : ℤ => fun om : BilateralField d => om j)
      (chaosSampleLaw M).toMeasure :=
    iIndepFun_infinitePi (P := laws) (fun _ => measurable_id)
  have hinj : Function.Injective (fun i : ℕ => (i : ℤ) - (N : ℤ)) := by
    intro i j hij
    exact Int.ofNat_inj.mp (sub_left_injective hij)
  have hphys : iIndepFun
      (fun i : ℕ => fun om : BilateralField d =>
        layerScaling d (N : ℤ) (om ((i : ℤ) - (N : ℤ))))
      (chaosSampleLaw M).toMeasure :=
    (hind.precomp hinj).comp (fun _ => layerScaling d (N : ℤ))
      (fun _ => (layerScaling d (N : ℤ)).continuous.measurable)
  have hmodel : iIndepFun
      (fun i : ℕ => fun om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        aux_lem_extension_cell_moment_forgetField (om i)) M.P.toMeasure :=
    M.shellPrefix.independent.comp (fun _ => aux_lem_extension_cell_moment_forgetField)
      (fun _ => (aux_lem_extension_cell_moment_forgetField (d := d)).continuous.measurable)
  apply IdentDistrib.pi _ hphys hmodel
  intro i
  refine ⟨((layerScaling d (N : ℤ)).continuous.measurable.comp
    (measurable_pi_apply _)).aemeasurable,
    ((aux_lem_extension_cell_moment_forgetField (d := d)).continuous.measurable.comp
      (measurable_pi_apply i)).aemeasurable, ?_⟩
  have hphysical :
      Measure.map (fun om : BilateralField d =>
        layerScaling d (N : ℤ) (om ((i : ℤ) - (N : ℤ))))
        (chaosSampleLaw M).toMeasure = (scaledLayerLaw d ν (i : ℤ)).toMeasure := by
    change Measure.map ((layerScaling d (N : ℤ)) ∘
      (fun om : BilateralField d => om ((i : ℤ) - (N : ℤ))))
      (Measure.infinitePi laws) = _
    rw [← Measure.map_map (layerScaling d (N : ℤ)).continuous.measurable
      (measurable_pi_apply _), Measure.infinitePi_map_eval]
    change Measure.map (layerScaling d (N : ℤ))
      (scaledLayerLaw d ν ((i : ℤ) - (N : ℤ))).toMeasure = _
    rw [aux_lem_extension_cell_moment_map_layerScaling]
    congr 2
    omega
  rw [hphysical]
  have hm := congrArg ProbabilityMeasure.toMeasure
    (gmc_marginal_field_law_eq_scaledLayerLaw M i)
  change Measure.map aux_lem_extension_cell_moment_forgetField
      (Measure.map (fun om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => om i)
        M.P.toMeasure) = (scaledLayerLaw d ν (i : ℤ)).toMeasure at hm
  rw [Measure.map_map (aux_lem_extension_cell_moment_forgetField (d := d)).continuous.measurable
    (measurable_pi_apply i)] at hm
  exact hm.symm


/-- Recenter the microscopic field at any deterministic real center. -/
theorem aux_lem_extension_cell_moment_translated_layers_identDistrib {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (z : SpatialCoordinates d) :
    IdentDistrib
      (fun om : BilateralField d => fun i : ℕ =>
        (layerScaling d (N : ℤ) (om ((i : ℤ) - (N : ℤ)))).comp
          ⟨fun x => x + z, continuous_id.add continuous_const⟩)
      (fun om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => fun i : ℕ =>
        aux_lem_extension_cell_moment_forgetField (om i))
      (chaosSampleLaw M).toMeasure M.P.toMeasure := by
  let T : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ
      ⟨fun x => x + z, continuous_id.add continuous_const⟩
  let F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d →
      (ℕ → C(SpatialCoordinates d, ℝ)) :=
    fun om i => aux_lem_extension_cell_moment_forgetField (om i)
  have hF : Measurable F := measurable_pi_lambda _ fun i =>
    (aux_lem_extension_cell_moment_forgetField (d := d)).continuous.measurable.comp
      (measurable_pi_apply i)
  have hT : Measurable (fun fs : ℕ → C(SpatialCoordinates d, ℝ) => fun i => T (fs i)) :=
    measurable_pi_lambda _ fun i => T.continuous.measurable.comp (measurable_pi_apply i)
  have h := (aux_lem_extension_cell_moment_microscopic_layers_identDistrib M N).comp hT
  have hstationary : IdentDistrib
      (fun om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => fun i => T (F om i))
      F M.P.toMeasure M.P.toMeasure := by
    refine ⟨(hT.comp hF).aemeasurable, hF.aemeasurable, ?_⟩
    have heq : (fun om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => fun i => T (F om i)) =
        F ∘ SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample z := by
      funext om i
      ext x
      rfl
    rw [heq, ← Measure.map_map hF
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.measurable_translatePotentialSample z),
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.map_translatePotentialSample]
  exact h.trans hstationary

/-- The transport can be consumed by any measurable real observable of all the
layers, in particular the coefficient-local coarse response observables. -/
theorem aux_lem_extension_cell_moment_translated_observable_eLpNorm {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (z : SpatialCoordinates d)
    (F : (ℕ → C(SpatialCoordinates d, ℝ)) → ℝ) (hF : Measurable F) (p : ℝ≥0∞) :
    eLpNorm (fun om : BilateralField d => F (fun i : ℕ =>
        (layerScaling d (N : ℤ) (om ((i : ℤ) - (N : ℤ)))).comp
          ⟨fun x => x + z, continuous_id.add continuous_const⟩))
      p (chaosSampleLaw M).toMeasure =
    eLpNorm (fun om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        F (fun i : ℕ => aux_lem_extension_cell_moment_forgetField (om i)))
      p M.P.toMeasure :=
  ((aux_lem_extension_cell_moment_translated_layers_identDistrib M N z).comp hF).eLpNorm_eq p
end


section
open MeasureTheory ProbabilityTheory SubdiffusiveProcess

def aux_lem_extension_cell_moment_zoom {d : ℕ} (m : ℤ)
    (c : SpatialCoordinates d) (om : BilateralField d) : BilateralField d :=
  fun j => (layerScaling d m (om (j - m))).comp
    ⟨fun x => x + (3 : ℝ) ^ m • c, continuous_id.add continuous_const⟩

theorem aux_lem_extension_cell_moment_zoom_apply {d : ℕ} (m j : ℤ)
    (c x : SpatialCoordinates d) (om : BilateralField d) :
    aux_lem_extension_cell_moment_zoom m c om j x =
      om (j - m) ((3 : ℝ) ^ (-m) • x + c) := by
  change om (j - m) ((3 : ℝ) ^ (-m) • (x + (3 : ℝ) ^ m • c)) = _
  rw [smul_add, smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
    neg_add_cancel, zpow_zero, one_smul]

/-- The common bilateral law is invariant under simultaneous integer scale shift
and spatial zoom about an arbitrary real center. -/
theorem aux_lem_extension_cell_moment_zoom_measurePreserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (c : SpatialCoordinates d) :
    MeasurePreserving (aux_lem_extension_cell_moment_zoom m c)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  let ν := chaosRootFieldLaw M
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let S : BilateralField d → BilateralField d :=
    fun om j => layerScaling d m (om (j - m))
  have hSmeas : Measurable S := measurable_pi_lambda _ fun j =>
    (layerScaling d m).continuous.measurable.comp (measurable_pi_apply _)
  have hind : iIndepFun (fun j : ℤ => fun om : BilateralField d => om j)
      (chaosSampleLaw M).toMeasure :=
    iIndepFun_infinitePi (P := laws) (fun _ => measurable_id)
  have hinj : Function.Injective (fun j : ℤ => j - m) := sub_left_injective
  have hscaled : iIndepFun (fun j : ℤ => fun om : BilateralField d => S om j)
      (chaosSampleLaw M).toMeasure :=
    (hind.precomp hinj).comp (fun _ => layerScaling d m)
      (fun _ => (layerScaling d m).continuous.measurable)
  have hD : IdentDistrib S (id : BilateralField d → BilateralField d)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
    apply IdentDistrib.pi _ hscaled hind
    intro j
    refine ⟨((measurable_pi_apply j).comp hSmeas).aemeasurable,
      (measurable_pi_apply j).aemeasurable, ?_⟩
    change Measure.map ((layerScaling d m) ∘
      (fun om : BilateralField d => om (j - m))) (Measure.infinitePi laws) =
        Measure.map (fun om : BilateralField d => om j) (Measure.infinitePi laws)
    rw [← Measure.map_map (layerScaling d m).continuous.measurable
      (measurable_pi_apply _), Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]
    change Measure.map (layerScaling d m) (scaledLayerLaw d ν (j - m)).toMeasure =
      (scaledLayerLaw d ν j).toMeasure
    rw [aux_lem_extension_cell_moment_map_layerScaling]
    congr 2
    omega
  have hS : MeasurePreserving S (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    ⟨hSmeas, by simpa using hD.map_eq⟩
  have htrans := aux_stationary_family_product_stationary d ν
    (aux_stationary_family_scaled_layer d ν (gmc_zero_field_law_stationary M))
    ((3 : ℝ) ^ m • c)
  exact htrans.comp hS
end


section
open MeasureTheory Homogenization
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal BigOperators

/-- A cutoff-uniform oscillation envelope on one unit microscopic cube. -/
def aux_lem_extension_cell_moment_nativeOsc {d : ℕ} (N : ℕ)
    (om : PotentialSample d) : ℝ :=
  shellOscillationEnvelope 0 0 om + layerOscSum 0 N om

theorem aux_lem_extension_cell_moment_nativeOsc_nonneg {d : ℕ} (N : ℕ)
    (om : PotentialSample d) :
    0 ≤ aux_lem_extension_cell_moment_nativeOsc N om :=
  add_nonneg (shellOscillationEnvelope_nonneg 0 0 om) (layerOscSum_nonneg 0 N om)

theorem aux_lem_extension_cell_moment_nativeOsc_measurable {d : ℕ} (N : ℕ) :
    Measurable (aux_lem_extension_cell_moment_nativeOsc (d := d) N) :=
  (measurable_shellOscillationEnvelope 0 0).add (measurable_layerOscSum 0 N)

theorem aux_lem_extension_cell_moment_nativeOsc_ogamma {d : ℕ}
    (M : GMCModel d) (N : ℕ) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (3 * oscSumConst d * M.delta)
      (aux_lem_extension_cell_moment_nativeOsc N) := by
  have hδ := M.shellPrefix.delta_pos
  have hC := oscSumConst_pos d
  have h0 : SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (2 * oscSumConst d * M.delta)
      (shellOscillationEnvelope 0 0) := by
    convert ogammaLE_shellOscillationEnvelope M 0 0 using 1
    simp only [Nat.cast_zero, sub_zero, zpow_zero, mul_one]
    unfold oscSumConst
    ring
  have hsum := ogammaLE_two_add
    (by positivity : 0 < 2 * oscSumConst d * M.delta)
    (by positivity : 0 < oscSumConst d * M.delta)
    (measurable_shellOscillationEnvelope 0 0).aemeasurable
    (measurable_layerOscSum 0 N).aemeasurable
    (shellOscillationEnvelope_nonneg 0 0) (layerOscSum_nonneg 0 N)
    h0 (ogammaLE_layerOscSum M 0 N)
  convert hsum using 1
  ring

/-- The point value has central-limit size; the within-cell oscillation has bounded size. -/
def aux_lem_extension_cell_moment_nativeFluctuation {d : ℕ} (N : ℕ)
    (om : PotentialSample d) : ℝ :=
  |cutoffShellSum N (-1) 0 om| + aux_lem_extension_cell_moment_nativeOsc N om

def aux_lem_extension_cell_moment_nativeFluctuationConst (d : ℕ) : ℝ :=
  6 * cutoffGammaConst + 3 * oscSumConst d

theorem aux_lem_extension_cell_moment_nativeFluctuationConst_pos (d : ℕ) :
    0 < aux_lem_extension_cell_moment_nativeFluctuationConst d := by
  unfold aux_lem_extension_cell_moment_nativeFluctuationConst
  have := cutoffGammaConst_pos
  have := oscSumConst_pos d
  positivity

theorem aux_lem_extension_cell_moment_nativeFluctuation_nonneg {d : ℕ} (N : ℕ)
    (om : PotentialSample d) :
    0 ≤ aux_lem_extension_cell_moment_nativeFluctuation N om :=
  add_nonneg (abs_nonneg _) (aux_lem_extension_cell_moment_nativeOsc_nonneg N om)

theorem aux_lem_extension_cell_moment_nativeFluctuation_measurable {d : ℕ} (N : ℕ) :
    Measurable (aux_lem_extension_cell_moment_nativeFluctuation (d := d) N) :=
  (measurable_cutoffShellSum N (-1) 0).abs.add
    (aux_lem_extension_cell_moment_nativeOsc_measurable N)

theorem aux_lem_extension_cell_moment_nativeFluctuation_ogamma {d : ℕ}
    (M : GMCModel d) (N : ℕ) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2
      (aux_lem_extension_cell_moment_nativeFluctuationConst d * M.delta *
        Real.sqrt ((N : ℝ) + 1))
      (aux_lem_extension_cell_moment_nativeFluctuation N) := by
  have hδ := M.shellPrefix.delta_pos
  have hC := cutoffGammaConst_pos
  have hO := oscSumConst_pos d
  have hroot : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hroot1 : 1 ≤ Real.sqrt ((N : ℝ) + 1) := by
    exact Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hsum : Homogenization.IndependentSums.IsBigO M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      (fun om => |cutoffShellSum N (-1) 0 om|)
      (cutoffGammaConst * Real.sqrt ((N : ℝ) + 1) * M.delta) := by
    simpa [Homogenization.IndependentSums.IsBigO] using
      (isBigO_gammaTwo_cutoffShellSum_sourceScale M N (-1) 0 (by omega) (by omega))
  have hsum' := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_of_isBigO_gammaTwo_aemeasurable
    (by positivity : 0 < cutoffGammaConst * Real.sqrt ((N : ℝ) + 1) * M.delta)
    (measurable_cutoffShellSum N (-1) 0).abs.aemeasurable hsum
  have hadd := ogammaLE_two_add
    (by positivity : 0 < 6 * (cutoffGammaConst * Real.sqrt ((N : ℝ) + 1) * M.delta))
    (by positivity : 0 < 3 * oscSumConst d * M.delta)
    (measurable_cutoffShellSum N (-1) 0).abs.aemeasurable
    (aux_lem_extension_cell_moment_nativeOsc_measurable N).aemeasurable
    (fun _ => abs_nonneg _) (aux_lem_extension_cell_moment_nativeOsc_nonneg N)
    hsum' (aux_lem_extension_cell_moment_nativeOsc_ogamma M N)
  apply SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ogammaLE_mono_scale'
    (by norm_num) (by positivity) _ hadd
  unfold aux_lem_extension_cell_moment_nativeFluctuationConst
  have hscale := mul_le_mul_of_nonneg_left hroot1
    (by positivity : 0 ≤ 3 * oscSumConst d * M.delta)
  nlinarith only [hscale]

theorem aux_lem_extension_cell_moment_nativeOsc_bounds {d : ℕ} (N : ℕ)
    (om : PotentialSample d) (x : Homogenization.Vec d) (hx : x ∈ openCubeSet (originCube d 0)) :
    |(∑ i ∈ Finset.range (N + 1), om i x) -
      ∑ i ∈ Finset.range (N + 1), om i 0| ≤
      aux_lem_extension_cell_moment_nativeOsc N om := by
  have hx' : x - 0 ∈ openCubeSet (originCube d 0) := by simpa only [sub_zero] using hx
  have hterm : ∀ i : ℕ, |om i x - om i 0| ≤ shellOscillationEnvelope i 0 om := by
    intro i
    simpa only [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.translatePotentialSample_zero]
      using abs_shell_sub_le_shellOscillationEnvelope om i 0 0 x hx'
  calc
    |(∑ i ∈ Finset.range (N + 1), om i x) - ∑ i ∈ Finset.range (N + 1), om i 0|
        = |∑ i ∈ Finset.range (N + 1), (om i x - om i 0)| := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.range (N + 1), |om i x - om i 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (N + 1), shellOscillationEnvelope i 0 om :=
      Finset.sum_le_sum fun i _ => hterm i
    _ ≤ aux_lem_extension_cell_moment_nativeOsc N om := by
      rw [Finset.sum_range_succ']
      unfold aux_lem_extension_cell_moment_nativeOsc layerOscSum
      simp only [zero_add]
      have hsub : Finset.range N ⊆ Finset.range (N + 1) := Finset.range_mono (Nat.le_succ N)
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => shellOscillationEnvelope_nonneg (1 + i) 0 om)
      simpa only [Nat.add_comm, Nat.cast_zero, add_comm] using
        add_le_add (le_refl (shellOscillationEnvelope 0 0 om)) hle

/-- A logarithmic envelope of the normalized coefficient on a single microscopic cell.
Its deterministic normalization costs only `delta^2 (N+1)`. -/
def aux_lem_extension_cell_moment_nativeLogEnvelope {d : ℕ}
    (M : GMCModel d) (N : ℕ) (om : PotentialSample d) : ℝ :=
  Real.log 2 * M.delta ^ 2 * ((N : ℝ) + 1) +
    aux_lem_extension_cell_moment_nativeFluctuation N om

theorem aux_lem_extension_cell_moment_nativeLogEnvelope_measurable {d : ℕ}
    (M : GMCModel d) (N : ℕ) :
    Measurable (aux_lem_extension_cell_moment_nativeLogEnvelope M N) :=
  measurable_const.add (aux_lem_extension_cell_moment_nativeFluctuation_measurable N)

theorem aux_lem_extension_cell_moment_nativeLogEnvelope_bounds {d : ℕ}
    (M : GMCModel d) (N : ℕ) (om : PotentialSample d) (x : Homogenization.Vec d)
    (hx : x ∈ openCubeSet (originCube d 0)) :
    |Real.log ((ahom M N)⁻¹ * aCutoff M N om x)| ≤
      aux_lem_extension_cell_moment_nativeLogEnvelope M N om := by
  have hsum0 : cutoffShellSum N (-1) 0 om = ∑ i ∈ Finset.range (N + 1), om i 0 := by
    unfold cutoffShellSum cutoffShellIndices
    simp only [neg_add_cancel, Int.toNat_zero]
    congr 1
    ext i
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  have hs : |∑ i ∈ Finset.range (N + 1), om i x| ≤
      aux_lem_extension_cell_moment_nativeFluctuation N om := by
    have hb := aux_lem_extension_cell_moment_nativeOsc_bounds N om x hx
    have ha := abs_add_le
      ((∑ i ∈ Finset.range (N + 1), om i x) - ∑ i ∈ Finset.range (N + 1), om i 0)
      (∑ i ∈ Finset.range (N + 1), om i 0)
    rw [sub_add_cancel] at ha
    unfold aux_lem_extension_cell_moment_nativeFluctuation
    rw [hsum0]
    linarith
  have hlog : Real.log ((ahom M N)⁻¹ * aCutoff M N om x) =
      -Real.log (ahom M N) + (∑ i ∈ Finset.range (N + 1), om i x) -
        ((N : ℝ) + 1) * tauSq M.P := by
    rw [Real.log_mul (inv_ne_zero (ahom_pos M N).ne') (aCutoff_pos M N om x).ne',
      Real.log_inv, aCutoff, Real.log_exp, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [hlog]
  have htriangle := (abs_sub
      (-Real.log (ahom M N) + ∑ i ∈ Finset.range (N + 1), om i x)
      (((N : ℝ) + 1) * tauSq M.P)).trans
    (add_le_add (abs_add_le _ _) (le_refl _))
  rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) + 1),
    abs_of_nonneg M.G4.tauSq_pos.le] at htriangle
  have htau := mul_le_mul_of_nonneg_left (tauSq_le_delta_sq M)
    (by positivity : 0 ≤ (N : ℝ) + 1)
  have hahom := SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.abs_log_ahom_le M N
  unfold aux_lem_extension_cell_moment_nativeLogEnvelope
  nlinarith only [htriangle, htau, hahom, hs]

/-- Exponential moments of the one-cell envelope. No threshold depends on the root
or cutoff. The growth in the number of layers is quadratic in the disorder. -/
theorem aux_lem_extension_cell_moment_nativeLogEnvelope_exp_moment {d : ℕ}
    (M : GMCModel d) (N : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun om => Real.exp
      (p * aux_lem_extension_cell_moment_nativeLogEnvelope M N om)) M.P.toMeasure ∧
    (∫ om, Real.exp (p * aux_lem_extension_cell_moment_nativeLogEnvelope M N om)
      ∂M.P.toMeasure) ≤
      2 * Real.exp ((p * Real.log 2 + p ^ 2 *
        (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 / 4) *
        M.delta ^ 2 * ((N : ℝ) + 1)) := by
  have hδ := M.shellPrefix.delta_pos
  have hC := aux_lem_extension_cell_moment_nativeFluctuationConst_pos d
  have hroot : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨hi, hbound⟩ := aux_finite_cutoff_log_abs_majorant_exp_of_ogamma
    M.P.toMeasure (aux_lem_extension_cell_moment_nativeFluctuation N)
    (aux_lem_extension_cell_moment_nativeFluctuation_measurable N)
    (aux_lem_extension_cell_moment_nativeFluctuation_nonneg N)
    (aux_lem_extension_cell_moment_nativeFluctuationConst d * M.delta *
      Real.sqrt ((N : ℝ) + 1)) p (by positivity) hp
    (aux_lem_extension_cell_moment_nativeFluctuation_ogamma M N)
  have heq : (fun om => Real.exp
      (p * aux_lem_extension_cell_moment_nativeLogEnvelope M N om)) =
      fun om => Real.exp (p * (Real.log 2 * M.delta ^ 2 * ((N : ℝ) + 1))) *
        Real.exp (p * aux_lem_extension_cell_moment_nativeFluctuation N om) := by
    funext om
    rw [aux_lem_extension_cell_moment_nativeLogEnvelope, mul_add, Real.exp_add]
  rw [heq]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left hbound
    (Real.exp_pos (p * (Real.log 2 * M.delta ^ 2 * ((N : ℝ) + 1)))).le
  refine hb.trans_eq ?_
  rw [← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, ← Real.exp_add]
  congr 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) + 1)]
  ring
end


section
open MeasureTheory TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal BigOperators

/-- A fixed compact cube containing every microscopic below-wavelength descendant
after recentering, and strictly contained in the open unit cube. -/
def aux_lem_extension_cell_moment_smallCompact (d : ℕ) : Compacts (SpatialCoordinates d) :=
  ⟨Metric.closedBall (0 : SpatialCoordinates d) (1 / 3), isCompact_closedBall _ _⟩

theorem aux_lem_extension_cell_moment_smallCompact_sub {d : ℕ}
    {x : SpatialCoordinates d}
    (hx : x ∈ (aux_lem_extension_cell_moment_smallCompact d : Set (SpatialCoordinates d))) :
    x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
  rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
  change dist x 0 ≤ (1 / 3 : ℝ) at hx
  have hc : Homogenization.cubeCenter (Homogenization.originCube d 0) =
      (0 : SpatialCoordinates d) := by
    ext i
    simp [Homogenization.cubeCenter, Homogenization.originCube]
  rw [Metric.mem_ball, hc]
  simpa [Homogenization.cubeRadius, Homogenization.cubeScaleFactor,
    Homogenization.originCube] using (show dist x 0 < (1 / 2 : ℝ) by linarith)

/-- The logarithm of the normalized cutoff as a continuous function of all its layers. -/
def aux_lem_extension_cell_moment_logField {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (fs : ℕ → C(SpatialCoordinates d, ℝ)) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
    ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) + ∑ i ∈ Finset.range (N + 1), fs i

theorem aux_lem_extension_cell_moment_logField_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Measurable (aux_lem_extension_cell_moment_logField M N) :=
  measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)

def aux_lem_extension_cell_moment_logNorm {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (fs : ℕ → C(SpatialCoordinates d, ℝ)) : ℝ :=
  ‖(aux_lem_extension_cell_moment_logField M N fs).restrict
    (aux_lem_extension_cell_moment_smallCompact d : Set (SpatialCoordinates d))‖

theorem aux_lem_extension_cell_moment_logNorm_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Measurable (aux_lem_extension_cell_moment_logNorm M N) :=
  ((ContinuousMap.continuous_restrict
    (aux_lem_extension_cell_moment_smallCompact d : Set (SpatialCoordinates d))).norm.measurable).comp
      (aux_lem_extension_cell_moment_logField_measurable M N)

theorem aux_lem_extension_cell_moment_logField_native {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : SpatialCoordinates d) :
    aux_lem_extension_cell_moment_logField M N
      (fun i => aux_lem_extension_cell_moment_forgetField (om i)) x =
      Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M N om x) := by
  rw [Real.log_mul (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M N om x).ne', Real.log_inv,
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff, Real.log_exp, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    aux_lem_extension_cell_moment_logField, ContinuousMap.add_apply, ContinuousMap.const_apply,
    ContinuousMap.sum_apply, aux_lem_extension_cell_moment_forgetField, ContinuousMap.coe_mk]
  ring

theorem aux_lem_extension_cell_moment_logNorm_native_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    aux_lem_extension_cell_moment_logNorm M N
      (fun i => aux_lem_extension_cell_moment_forgetField (om i)) ≤
      aux_lem_extension_cell_moment_nativeLogEnvelope M N om := by
  have hnonneg : 0 ≤ aux_lem_extension_cell_moment_nativeLogEnvelope M N om := by
    unfold aux_lem_extension_cell_moment_nativeLogEnvelope
    exact add_nonneg (by positivity)
      (aux_lem_extension_cell_moment_nativeFluctuation_nonneg N om)
  apply (ContinuousMap.norm_le _ hnonneg).mpr
  intro x
  change |aux_lem_extension_cell_moment_logField M N
    (fun i => aux_lem_extension_cell_moment_forgetField (om i)) x.1| ≤ _
  rw [aux_lem_extension_cell_moment_logField_native]
  exact aux_lem_extension_cell_moment_nativeLogEnvelope_bounds M N om x.1
    (aux_lem_extension_cell_moment_smallCompact_sub x.2)

def aux_lem_extension_cell_moment_physicalLogNorm {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (z : SpatialCoordinates d)
    (om : BilateralField d) : ℝ :=
  aux_lem_extension_cell_moment_logNorm M N (fun i : ℕ =>
    (layerScaling d (N : ℤ) (om ((i : ℤ) - (N : ℤ)))).comp
      ⟨fun x => x + z, continuous_id.add continuous_const⟩)

theorem aux_lem_extension_cell_moment_physicalLogNorm_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (z : SpatialCoordinates d) :
    Measurable (aux_lem_extension_cell_moment_physicalLogNorm M N z) := by
  apply (aux_lem_extension_cell_moment_logNorm_measurable M N).comp
  apply measurable_pi_lambda
  intro i
  exact (ContinuousMap.continuous_precomp
    ⟨fun x : SpatialCoordinates d => x + z, continuous_id.add continuous_const⟩).measurable.comp
      ((layerScaling d (N : ℤ)).continuous.measurable.comp (measurable_pi_apply _))

/-- The actual physical ultraviolet coefficient has the same local exponential
bound, uniformly over every deterministic real center. -/
theorem aux_lem_extension_cell_moment_physicalLogNorm_exp_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (z : SpatialCoordinates d)
    (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun om => Real.exp
      (p * aux_lem_extension_cell_moment_physicalLogNorm M N z om))
      (chaosSampleLaw M).toMeasure ∧
    (∫ om, Real.exp (p * aux_lem_extension_cell_moment_physicalLogNorm M N z om)
      ∂(chaosSampleLaw M).toMeasure) ≤
      2 * Real.exp ((p * Real.log 2 + p ^ 2 *
        (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 / 4) *
        M.delta ^ 2 * ((N : ℝ) + 1)) := by
  let f : (ℕ → C(SpatialCoordinates d, ℝ)) → ℝ := fun fs =>
    Real.exp (p * aux_lem_extension_cell_moment_logNorm M N fs)
  have hf : Measurable f := (measurable_const.mul
    (aux_lem_extension_cell_moment_logNorm_measurable M N)).exp
  have hD := (aux_lem_extension_cell_moment_translated_layers_identDistrib M N z).comp hf
  obtain ⟨hi, hb⟩ := aux_lem_extension_cell_moment_nativeLogEnvelope_exp_moment M N p hp
  have hfnative : Measurable (fun om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      f (fun i => aux_lem_extension_cell_moment_forgetField (om i))) :=
    hf.comp (measurable_pi_lambda _ fun i =>
      (aux_lem_extension_cell_moment_forgetField (d := d)).continuous.measurable.comp
        (measurable_pi_apply i))
  have hle : ∀ om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      f (fun i => aux_lem_extension_cell_moment_forgetField (om i)) ≤
      Real.exp (p * aux_lem_extension_cell_moment_nativeLogEnvelope M N om) :=
    fun om => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (aux_lem_extension_cell_moment_logNorm_native_le M N om) hp)
  have hif : Integrable (fun om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      f (fun i => aux_lem_extension_cell_moment_forgetField (om i))) M.P.toMeasure := by
    apply hi.mono' hfnative.aestronglyMeasurable
    filter_upwards with om
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hle om
  refine ⟨hD.integrable_iff.mpr hif, ?_⟩
  exact hD.integral_eq.trans_le ((integral_mono hif hi hle).trans hb)

/-- Local exponential `L^p` bound with the exact disorder rate exposed. -/
theorem aux_lem_extension_cell_moment_physicalLogNorm_eLpNorm {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (z : SpatialCoordinates d)
    (a p : ℝ) (ha : 0 ≤ a) (hp : 0 < p) :
    eLpNorm (fun om => Real.exp
      (a * aux_lem_extension_cell_moment_physicalLogNorm M N z om))
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (Real.log 2 / p +
        (a * Real.log 2 + p * a ^ 2 *
          (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 / 4) *
          M.delta ^ 2 * ((N : ℝ) + 1))) := by
  obtain ⟨hi, hb⟩ := aux_lem_extension_cell_moment_physicalLogNorm_exp_moment
    M N z (p * a) (mul_nonneg hp.le ha)
  have heq : (fun om => Real.exp (p * (a *
      aux_lem_extension_cell_moment_physicalLogNorm M N z om))) =
      fun om => Real.exp ((p * a) *
        aux_lem_extension_cell_moment_physicalLogNorm M N z om) := by
    funext om
    rw [mul_assoc]
  apply (aux_finite_cutoff_log_abs_majorant_eLpNorm_exp (chaosSampleLaw M).toMeasure
    (fun om => a * aux_lem_extension_cell_moment_physicalLogNorm M N z om)
    (measurable_const.mul (aux_lem_extension_cell_moment_physicalLogNorm_measurable M N z))
    p hp (by rw [heq]; exact hi) _ _).2
  rw [heq]
  refine hb.trans_eq ?_
  rw [show p * (Real.log 2 / p +
      (a * Real.log 2 + p * a ^ 2 * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 / 4) *
        M.delta ^ 2 * ((N : ℝ) + 1)) = Real.log 2 +
      ((p * a) * Real.log 2 + (p * a) ^ 2 *
        (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 / 4) *
        M.delta ^ 2 * ((N : ℝ) + 1) by field_simp]
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
end


section
open MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped ENNReal BigOperators

/-- Compact infrared control combined with a recentered microscopic ultraviolet norm.
The sole spatial dependence is in the prefactor `C K`. -/
theorem aux_lem_extension_cell_moment_totalLogNorm_eLpNorm {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H →
      ∀ (K : Compacts (SpatialCoordinates d)) (N : ℕ) (z : SpatialCoordinates d)
        (a p : ℝ), 0 ≤ a → 0 < p →
      eLpNorm (fun om => Real.exp (a *
          (‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
            aux_lem_extension_cell_moment_physicalLogNorm M N z om)))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Real.exp (Real.log 4 / p + 4 * p * a ^ 2 * C K * M.delta ^ 2 +
          (2 * a * Real.log 2 + p * a ^ 2 *
            (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
            M.delta ^ 2 * ((N : ℝ) + 1))) := by
  obtain ⟨C, hC, hCM⟩ :=
    exists_uniform_compactExponentialMoment_of_admissible hd
  refine ⟨C, hC, ?_⟩
  intro M H hH K N z a p ha hp
  let A : BilateralField d → ℝ := fun om =>
    ‖(H om).restrict (K : Set (SpatialCoordinates d))‖
  let E : BilateralField d → ℝ := aux_lem_extension_cell_moment_physicalLogNorm M N z
  let u : ℝ := C K * (2 * p * a) ^ 2 * M.delta ^ 2
  let v : ℝ := ((2 * p * a) * Real.log 2 + (2 * p * a) ^ 2 *
    (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 / 4) *
      M.delta ^ 2 * ((N : ℝ) + 1)
  have hCK := hC K
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hAm : Measurable A :=
    ((ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).norm.measurable).comp hH.measurable
  have hEm : Measurable E :=
    aux_lem_extension_cell_moment_physicalLogNorm_measurable M N z
  have hVm : Measurable (fun om => a * (A om + E om)) :=
    measurable_const.mul (hAm.add hEm)
  obtain ⟨hAi, hAb⟩ := hCM M H hH K (2 * p * a) (by positivity)
  obtain ⟨hEi, hEb⟩ := aux_lem_extension_cell_moment_physicalLogNorm_exp_moment
    M N z (2 * p * a) (by positivity)
  have hpoint : ∀ om, Real.exp (p * (a * (A om + E om))) ≤
      Real.exp ((2 * p * a) * A om) + Real.exp ((2 * p * a) * E om) := by
    intro om
    rcases le_total (A om) (E om) with h | h
    · have h' := mul_le_mul_of_nonneg_left h (mul_nonneg hp.le ha)
      have he : Real.exp (p * (a * (A om + E om))) ≤ Real.exp ((2 * p * a) * E om) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact he.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
    · have h' := mul_le_mul_of_nonneg_left h (mul_nonneg hp.le ha)
      have he : Real.exp (p * (a * (A om + E om))) ≤ Real.exp ((2 * p * a) * A om) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact he.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  have hsumI : Integrable (fun om => Real.exp ((2 * p * a) * A om) +
      Real.exp ((2 * p * a) * E om)) (chaosSampleLaw M).toMeasure := hAi.add hEi
  have hVi : Integrable (fun om => Real.exp (p * (a * (A om + E om))))
      (chaosSampleLaw M).toMeasure := by
    apply hsumI.mono' (measurable_const.mul hVm).exp.aestronglyMeasurable
    filter_upwards with om
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hpoint om
  have hVb : (∫ om, Real.exp (p * (a * (A om + E om)))
      ∂(chaosSampleLaw M).toMeasure) ≤ 4 * Real.exp (u + v) := by
    calc
      _ ≤ ∫ om, (Real.exp ((2 * p * a) * A om) +
          Real.exp ((2 * p * a) * E om)) ∂(chaosSampleLaw M).toMeasure :=
        integral_mono hVi hsumI hpoint
      _ = (∫ om, Real.exp ((2 * p * a) * A om) ∂(chaosSampleLaw M).toMeasure) +
          ∫ om, Real.exp ((2 * p * a) * E om) ∂(chaosSampleLaw M).toMeasure :=
        integral_add hAi hEi
      _ ≤ 2 * Real.exp u + 2 * Real.exp v := add_le_add hAb hEb
      _ ≤ 4 * Real.exp (u + v) := by
        have hu' := Real.exp_le_exp.mpr (le_add_of_nonneg_right hv : u ≤ u + v)
        have hv' := Real.exp_le_exp.mpr (le_add_of_nonneg_left hu : v ≤ u + v)
        linarith
  apply (aux_finite_cutoff_log_abs_majorant_eLpNorm_exp (chaosSampleLaw M).toMeasure
    (fun om => a * (A om + E om)) hVm p hp hVi _ _).2
  refine hVb.trans_eq ?_
  rw [show p * (Real.log 4 / p + 4 * p * a ^ 2 * C K * M.delta ^ 2 +
      (2 * a * Real.log 2 + p * a ^ 2 *
        (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
          M.delta ^ 2 * ((N : ℝ) + 1)) = Real.log 4 + (u + v) by
      dsimp [u, v]
      field_simp
      <;> ring]
  rw [Real.exp_add (Real.log 4), Real.exp_log (by norm_num : (0 : ℝ) < 4)]
end


section
open MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped ENNReal BigOperators

/-- The physical ultraviolet logarithm is the transported continuous layer observable. -/
theorem aux_lem_extension_cell_moment_logField_physical {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (z ξ : SpatialCoordinates d) (om : BilateralField d) :
    Real.log (cutoffCoefficient M H om N ((3 : ℝ) ^ (-(N : ℤ)) • (ξ + z))) =
      H om ((3 : ℝ) ^ (-(N : ℤ)) • (ξ + z)) +
      aux_lem_extension_cell_moment_logField M N (fun i : ℕ =>
        (layerScaling d (N : ℤ) (om ((i : ℤ) - (N : ℤ)))).comp
          ⟨fun x => x + z, continuous_id.add continuous_const⟩) ξ := by
  let y := (3 : ℝ) ^ (-(N : ℤ)) • (ξ + z)
  have hsum : (∑ i ∈ Finset.range (N + 1), om ((i : ℤ) - (N : ℤ)) y) =
      ∑ j ∈ Finset.range (N + 1), om (-(j : ℤ)) y := by
    rw [← Finset.sum_range_reflect (fun j : ℕ => om (-(j : ℤ)) y) (N + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    congr 2
    omega
  rw [cutoffCoefficient, Real.log_mul
    (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne') (Real.exp_pos _).ne',
    Real.log_inv, Real.log_exp]
  simp only [cutoffPotential, aux_lem_extension_cell_moment_logField,
    ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.sum_apply,
    ContinuousMap.comp_apply]
  change -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
    (H om y + (∑ j ∈ Finset.range (N + 1), om (-(j : ℤ)) y) -
      ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
    H om y + (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
      ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
      (∑ i ∈ Finset.range (N + 1), om ((i : ℤ) - (N : ℤ)) y))
  rw [hsum]
  ring

theorem aux_lem_extension_cell_moment_physicalLogNorm_bounds {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (z ξ : SpatialCoordinates d)
    (hξ : ξ ∈ (aux_lem_extension_cell_moment_smallCompact d : Set (SpatialCoordinates d)))
    (om : BilateralField d) :
    |Real.log (cutoffCoefficient M H om N ((3 : ℝ) ^ (-(N : ℤ)) • (ξ + z)))| ≤
      |H om ((3 : ℝ) ^ (-(N : ℤ)) • (ξ + z))| +
        aux_lem_extension_cell_moment_physicalLogNorm M N z om := by
  rw [aux_lem_extension_cell_moment_logField_physical]
  refine (abs_add_le _ _).trans (add_le_add (le_refl _) ?_)
  exact ContinuousMap.norm_coe_le_norm
    ((aux_lem_extension_cell_moment_logField M N _).restrict
      (aux_lem_extension_cell_moment_smallCompact d : Set (SpatialCoordinates d))) ⟨ξ, hξ⟩

/-- Every sub-wavelength descendant fits into the fixed compact microscopic cube. -/
theorem aux_lem_extension_cell_moment_descendant_micro_mem {d : ℕ}
    (N k n : ℕ) (hbelow : N < k + n) (Q : Homogenization.TriadicCube d)
    (hQ : Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ)))
    (x : SpatialCoordinates d) (hx : x ∈ Homogenization.openCubeSet Q) :
    (3 : ℝ) ^ ((N : ℤ) - (k : ℤ)) • (x - Homogenization.cubeCenter Q) ∈
      (aux_lem_extension_cell_moment_smallCompact d : Set (SpatialCoordinates d)) := by
  have hscale : Q.scale = -(n : ℤ) := by
    simpa [Homogenization.originCube] using
      Homogenization.scale_eq_of_mem_descendantsAtScale hQ
  have hx' : ‖x - Homogenization.cubeCenter Q‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ (-(n : ℤ)) := by
    rw [← Homogenization.ball_cubeCenter_eq_openCubeSet] at hx
    simpa only [Metric.mem_ball, dist_eq_norm, Homogenization.cubeRadius,
      Homogenization.cubeScaleFactor, hscale] using hx
  change dist ((3 : ℝ) ^ ((N : ℤ) - (k : ℤ)) •
    (x - Homogenization.cubeCenter Q)) 0 ≤ (1 / 3 : ℝ)
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hmul := mul_lt_mul_of_pos_left hx'
    (by positivity : 0 < (3 : ℝ) ^ ((N : ℤ) - (k : ℤ)))
  have hprod : (3 : ℝ) ^ ((N : ℤ) - (k : ℤ)) *
      ((1 / 2 : ℝ) * (3 : ℝ) ^ (-(n : ℤ))) =
      (1 / 2 : ℝ) * (3 : ℝ) ^ ((N : ℤ) - (k : ℤ) - (n : ℤ)) := by
    rw [mul_left_comm, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp only [sub_eq_add_neg]
  rw [hprod] at hmul
  have hpow : (3 : ℝ) ^ ((N : ℤ) - (k : ℤ) - (n : ℤ)) ≤ (3 : ℝ) ^ (-1 : ℤ) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
    omega
  have := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
  norm_num at this
  linarith

theorem aux_lem_extension_cell_moment_descendant_micro_identity {d : ℕ}
    (N k : ℕ) (Q : Homogenization.TriadicCube d) (w x : SpatialCoordinates d) :
    (3 : ℝ) ^ (-(N : ℤ)) •
      ((3 : ℝ) ^ ((N : ℤ) - (k : ℤ)) • (x - Homogenization.cubeCenter Q) +
        (3 : ℝ) ^ (N : ℤ) • (w + (3 : ℝ) ^ (-(k : ℤ)) • Homogenization.cubeCenter Q)) =
      fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i := by
  have hmul1 : (3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ ((N : ℤ) - (k : ℤ)) =
      (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have hmul2 : (3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ (N : ℤ) = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply]
  calc
    _ = ((3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ ((N : ℤ) - (k : ℤ))) *
        (x i - Homogenization.cubeCenter Q i) +
      ((3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ (N : ℤ)) *
        (w i + (3 : ℝ) ^ (-(k : ℤ)) * Homogenization.cubeCenter Q i) := by ring
    _ = _ := by rw [hmul1, hmul2]; ring
end


section
open MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped ENNReal BigOperators

theorem aux_lem_extension_cell_moment_cellAffine_mem {d : ℕ}
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    (fun i => w i + r * x i) ∈ (centeredCube w r hr : Set (SpatialCoordinates d)) := by
  rw [centeredCube_eq_pi]
  have hx' : ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
    simpa [Homogenization.openCubeSet, Homogenization.originCube,
      Homogenization.cubeScaleFactor] using hx
  intro i _
  have h1 := mul_lt_mul_of_pos_left (hx' i).1 hr
  have h2 := mul_lt_mul_of_pos_left (hx' i).2 hr
  constructor <;> linarith

/-- The below-wavelength residual with the repaired quantifier order.  No response
assumption is needed; it is a bound on the actual cutoff coefficient itself. -/
theorem aux_lem_extension_cell_moment_below_extremes {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ δ0 →
      ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      ∃ C0 : ℝ, 0 < C0 ∧
        ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
          (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
        ∀ n : ℕ, N < k + n →
        ∀ Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
            ((Homogenization.originCube d 0).scale - (n : ℤ)),
        ∃ lo hi : BilateralField d → ℝ,
          (∀ om, 0 < lo om ∧ lo om ≤ hi om ∧
            ∀ x ∈ Homogenization.openCubeSet Q,
              lo om ≤ cutoffCoefficient M H om N
                  (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∧
                cutoffCoefficient M H om N
                  (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ≤ hi om) ∧
          eLpNorm (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 +
              4 * (d : ℝ) * (lo om)⁻¹)
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) := by
  let B : ℝ := 6 * Real.log 2 + 9 * p *
    (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  let δ0 := Real.sqrt (ε / B)
  have hδ0 : 0 < δ0 := Real.sqrt_pos.2 (div_pos hε hB)
  obtain ⟨C, _hC, hCM⟩ := aux_lem_extension_cell_moment_totalLogNorm_eLpNorm hd
  refine ⟨δ0, B, hδ0, hB, ?_⟩
  intro M H hH hδ z0 R hR
  have hrate : B * M.delta ^ 2 ≤ ε := by
    have hsq : M.delta ^ 2 ≤ δ0 ^ 2 :=
      pow_le_pow_left₀ M.shellPrefix.delta_pos.le hδ 2
    calc
      B * M.delta ^ 2 ≤ B * δ0 ^ 2 := mul_le_mul_of_nonneg_left hsq hB.le
      _ = ε := by
        dsimp [δ0]
        rw [Real.sq_sqrt (div_pos hε hB).le]
        field_simp
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall z0 R, isCompact_closedBall _ _⟩
  let P : ℝ := Real.log 4 / p + 36 * p * C K * M.delta ^ 2
  let C0 : ℝ := 8 * (d : ℝ) * Real.exp P
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  refine ⟨C0, by dsimp [C0]; positivity, ?_⟩
  intro w N k _hk hcell n hbelow Q hQ
  let z : SpatialCoordinates d :=
    (3 : ℝ) ^ (N : ℤ) • (w + (3 : ℝ) ^ (-(k : ℤ)) • Homogenization.cubeCenter Q)
  let G : BilateralField d → ℝ := fun om =>
    ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
      aux_lem_extension_cell_moment_physicalLogNorm M N z om
  have hG0 : ∀ om, 0 ≤ G om := by
    intro om
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  let lo : BilateralField d → ℝ := fun om => Real.exp (-G om)
  let hi : BilateralField d → ℝ := fun om => Real.exp (G om)
  have hloinv : ∀ om, (lo om)⁻¹ = hi om := by
    intro om
    dsimp [lo, hi]
    rw [Real.exp_neg, inv_inv]
  refine ⟨lo, hi, ?_, ?_⟩
  · intro om
    refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr (by have := hG0 om; linarith), ?_⟩
    intro x hx
    let ξ : SpatialCoordinates d :=
      (3 : ℝ) ^ ((N : ℤ) - (k : ℤ)) • (x - Homogenization.cubeCenter Q)
    have hξ := aux_lem_extension_cell_moment_descendant_micro_mem N k n hbelow Q hQ x hx
    have hid := aux_lem_extension_cell_moment_descendant_micro_identity N k Q w x
    have hxroot : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) :=
      Homogenization.openCubeSet_subset_of_mem_descendantsAtScale (by simp) hQ hx
    have hyroot : (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈
        (centeredCube z0 R hR : Set (SpatialCoordinates d)) :=
      hcell (aux_lem_extension_cell_moment_cellAffine_mem w _ (by positivity) hxroot)
    have hyK : (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈
        (K : Set (SpatialCoordinates d)) := by
      change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 ≤ R
      change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 < R / 2 at hyroot
      linarith
    have hHpt : |H om (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i)| ≤
        ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
      ContinuousMap.norm_coe_le_norm ((H om).restrict (K : Set (SpatialCoordinates d))) ⟨_, hyK⟩
    have hlog := aux_lem_extension_cell_moment_physicalLogNorm_bounds M H N z ξ hξ om
    rw [hid] at hlog
    have hbound : |Real.log (cutoffCoefficient M H om N
        (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i))| ≤ G om :=
      hlog.trans (add_le_add hHpt (le_refl _))
    have hpos : 0 < cutoffCoefficient M H om N
        (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) :=
      mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
    constructor
    · exact (Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log hpos)
    · exact (Real.exp_log hpos).symm.trans_le (Real.exp_le_exp.mpr hhi)
  · have henv : ∀ om,
        4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 + 4 * (d : ℝ) * (lo om)⁻¹ ≤
          (8 * (d : ℝ)) * Real.exp (3 * G om) := by
      intro om
      have hh : hi om * hi om ^ 2 = Real.exp (3 * G om) := by
        change Real.exp (G om) * Real.exp (G om) ^ 2 = Real.exp (3 * G om)
        rw [show 3 * G om = G om + G om + G om by ring,
          Real.exp_add (G om + G om) (G om), Real.exp_add (G om) (G om)]
        ring
      have hh' : hi om ≤ Real.exp (3 * G om) :=
        Real.exp_le_exp.mpr (by have := hG0 om; linarith)
      rw [hloinv]
      calc
        _ = 4 * (d : ℝ) * (hi om * hi om ^ 2) + 4 * (d : ℝ) * hi om := by ring
        _ ≤ 4 * (d : ℝ) * Real.exp (3 * G om) + 4 * (d : ℝ) * Real.exp (3 * G om) := by
          rw [hh]
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hh' (by positivity))
        _ = _ := by ring
    have hnorm : eLpNorm (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 +
        4 * (d : ℝ) * (lo om)⁻¹) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (8 * (d : ℝ)) *
          eLpNorm (fun om => Real.exp (3 * G om)) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards with om
      rw [Real.norm_of_nonneg (by dsimp [lo, hi]; positivity),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact henv om
    have hGe : eLpNorm (fun om => Real.exp (3 * G om)) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * ((N : ℝ) + 1))) := by
      have h := hCM M H hH K N z 3 p (by norm_num) hp
      convert h using 2 <;> dsimp [G, P, B] <;> congr 1 <;> ring
    have hNl : (N : ℝ) + 1 ≤ (k : ℝ) + (n : ℝ) := by
      exact_mod_cast (show N + 1 ≤ k + n by omega)
    have hgrowth : B * M.delta ^ 2 * ((N : ℝ) + 1) ≤
        B * M.delta ^ 2 * k + ε * n := by
      calc
        _ ≤ B * M.delta ^ 2 * ((k : ℝ) + n) :=
          mul_le_mul_of_nonneg_left hNl (by positivity)
        _ = B * M.delta ^ 2 * k + (B * M.delta ^ 2) * n := by ring
        _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hrate (by positivity))
    calc
      _ ≤ ENNReal.ofReal (8 * (d : ℝ)) *
          ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * ((N : ℝ) + 1))) :=
        hnorm.trans (mul_le_mul_left' hGe _)
      _ = ENNReal.ofReal (C0 * Real.exp (B * M.delta ^ 2 * ((N : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.exp_add]
        dsimp [C0]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgrowth) (by dsimp [C0]; positivity))
end


section
open MeasureTheory
open Homogenization Homogenization.Book.Ch02
open Homogenization.Internal.Ch02.BookCh02

theorem aux_lem_extension_cell_moment_dirichlet_integrable {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (u : H1Function (U : Set (Vec d))) :
    Integrable (fun x => (1 / 2 : ℝ) *
      vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (volumeMeasureOn (U : Set (Vec d))) := by
  have hi := integrableOn_symmetricDirichletIntegrand_of_isEllipticFieldOn
    (pointwiseCoeffField_isEllipticFieldOn U a) u
  apply hi.congr
  filter_upwards [pointwiseCoeffField_ae_eq U a] with x hx
  rw [hx]

theorem aux_lem_extension_cell_moment_neumann_integrable {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (q : Vec d)
    (u : H1Function (U : Set (Vec d))) :
    Integrable (fun x => vecDot q (u.grad x) - (1 / 2 : ℝ) *
      vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (volumeMeasureOn (U : Set (Vec d))) :=
  (integrableOn_vecDot_const_h1Grad q u).sub
    (aux_lem_extension_cell_moment_dirichlet_integrable U a u)

/-- Increasing a symmetric coefficient increases the Dirichlet coarse matrix.
The order assumption concerns the coefficient itself, and the variational
minimizers are produced by the library theorem. -/
theorem aux_lem_extension_cell_moment_sigma_mono {d : ℕ}
    (U : Domain d) (a b : CoeffOn U)
    (ha : CoeffOn.IsSymmetric a) (hb : CoeffOn.IsSymmetric b)
    (hab : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      MatLoewnerLE (a.toCoeffField x) (b.toCoeffField x)) :
    MatLoewnerLE (Homogenization.Book.Ch02.sigmaCoarse U a)
      (Homogenization.Book.Ch02.sigmaCoarse U b) := by
  have hTa := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hTb := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U b hb
  intro p
  rw [← hTa.dirichlet_value_by_sigma p, ← hTb.dirichlet_value_by_sigma p]
  obtain ⟨ua, hua⟩ := hTa.dirichlet_minimizer_exists p
  obtain ⟨ub, hub⟩ := hTb.dirichlet_minimizer_exists p
  rw [symmetricDirichletNu_eq_of_minimizer hua,
    symmetricDirichletNu_eq_of_minimizer hub]
  refine (hua.2 ub hub.1).trans ?_
  unfold symmetricDirichletEnergyValue Homogenization.Book.Ch02.average
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  exact integral_mono_ae
    (aux_lem_extension_cell_moment_dirichlet_integrable U a ub)
    (aux_lem_extension_cell_moment_dirichlet_integrable U b ub)
    (hab.mono fun x hx => hx (ub.grad x))

/-- Increasing a symmetric coefficient decreases the inverse Neumann coarse matrix. -/
theorem aux_lem_extension_cell_moment_sigmaStarInv_antitone {d : ℕ}
    (U : Domain d) (a b : CoeffOn U)
    (ha : CoeffOn.IsSymmetric a) (hb : CoeffOn.IsSymmetric b)
    (hab : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      MatLoewnerLE (a.toCoeffField x) (b.toCoeffField x)) :
    MatLoewnerLE (Homogenization.Book.Ch02.sigmaStarInvCoarse U b)
      (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) := by
  have hTa := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hTb := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U b hb
  intro q
  rw [← hTb.neumann_value_by_sigmaStarInv q, ← hTa.neumann_value_by_sigmaStarInv q]
  obtain ⟨ua, _, hua⟩ := hTa.neumann_meanZero_maximizer_exists q
  obtain ⟨ub, _, hub⟩ := hTb.neumann_meanZero_maximizer_exists q
  rw [symmetricNeumannNu_eq_of_maximizer hua,
    symmetricNeumannNu_eq_of_maximizer hub]
  refine le_trans ?_ (hua ub)
  unfold symmetricNeumannEnergyValue Homogenization.Book.Ch02.average
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  exact integral_mono_ae
    (aux_lem_extension_cell_moment_neumann_integrable U b q ub)
    (aux_lem_extension_cell_moment_neumann_integrable U a q ub)
    (hab.mono fun x hx => sub_le_sub_left (hx (ub.grad x)) _)

/-- The `b` matrix is the Dirichlet matrix for symmetric coefficients. -/
theorem aux_lem_extension_cell_moment_b_mono {d : ℕ}
    (U : Domain d) (a b : CoeffOn U)
    (ha : CoeffOn.IsSymmetric a) (hb : CoeffOn.IsSymmetric b)
    (hab : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      MatLoewnerLE (a.toCoeffField x) (b.toCoeffField x)) :
    MatLoewnerLE (Homogenization.Book.Ch02.bCoarse U a)
      (Homogenization.Book.Ch02.bCoarse U b) := by
  rw [(Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha).derived_matrices.2.2,
    (Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U b hb).derived_matrices.2.2]
  exact aux_lem_extension_cell_moment_sigma_mono U a b ha hb hab

theorem aux_lem_extension_cell_moment_b_norm_mono {d : ℕ}
    (U : Domain d) (a b : CoeffOn U)
    (ha : CoeffOn.IsSymmetric a) (hb : CoeffOn.IsSymmetric b)
    (hab : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      MatLoewnerLE (a.toCoeffField x) (b.toCoeffField x)) :
    matrixNorm (Homogenization.Book.Ch02.bCoarse U a) ≤
      matrixNorm (Homogenization.Book.Ch02.bCoarse U b) :=
  matrixNorm_le_of_matLoewnerLE_of_posSemidef
    (Homogenization.Book.Ch02.bCoarse_posSemidef U a)
    (Homogenization.Book.Ch02.bCoarse_posSemidef U b)
    (aux_lem_extension_cell_moment_b_mono U a b ha hb hab)

theorem aux_lem_extension_cell_moment_sigmaStarInv_norm_antitone {d : ℕ}
    (U : Domain d) (a b : CoeffOn U)
    (ha : CoeffOn.IsSymmetric a) (hb : CoeffOn.IsSymmetric b)
    (hab : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      MatLoewnerLE (a.toCoeffField x) (b.toCoeffField x)) :
    matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse U b) ≤
      matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) :=
  matrixNorm_le_of_matLoewnerLE_of_posSemidef
    (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef U b).posSemidef
    (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef U a).posSemidef
    (aux_lem_extension_cell_moment_sigmaStarInv_antitone U a b ha hb hab)
end


section
open MeasureTheory
open Homogenization Homogenization.Book.Ch02
open Homogenization.Internal.Ch02.BookCh02

theorem aux_lem_extension_cell_moment_matrixNorm_smul {d : ℕ} (c : ℝ) (A : Mat d) :
    matrixNorm (c • A) = |c| * matrixNorm A := by
  change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (c • A)‖ =
    |c| * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖
  rw [map_smul, norm_smul, Real.norm_eq_abs]

/-- Multiplicative comparison of the Dirichlet energy, without introducing an
extra coefficient carrier or a variational hypothesis. -/
theorem aux_lem_extension_cell_moment_sigma_le_smul {d : ℕ}
    (U : Domain d) (a b : CoeffOn U)
    (ha : CoeffOn.IsSymmetric a) (hb : CoeffOn.IsSymmetric b)
    (c : ℝ) (hc : 0 < c)
    (hab : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      MatLoewnerLE (a.toCoeffField x) (c • b.toCoeffField x)) :
    MatLoewnerLE (Homogenization.Book.Ch02.sigmaCoarse U a)
      (c • Homogenization.Book.Ch02.sigmaCoarse U b) := by
  have hTa := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hTb := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U b hb
  intro p
  rw [smul_matVecMul, vecDot_smul_right, ← mul_assoc,
    mul_comm (1 / 2 : ℝ) c, mul_assoc,
    ← hTa.dirichlet_value_by_sigma p, ← hTb.dirichlet_value_by_sigma p]
  obtain ⟨ua, hua⟩ := hTa.dirichlet_minimizer_exists p
  obtain ⟨ub, hub⟩ := hTb.dirichlet_minimizer_exists p
  rw [symmetricDirichletNu_eq_of_minimizer hua,
    symmetricDirichletNu_eq_of_minimizer hub]
  refine (hua.2 ub hub.1).trans ?_
  unfold symmetricDirichletEnergyValue Homogenization.Book.Ch02.average
  rw [← mul_assoc, mul_comm c, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  rw [← integral_const_mul]
  apply integral_mono_ae
    (aux_lem_extension_cell_moment_dirichlet_integrable U a ub)
    ((aux_lem_extension_cell_moment_dirichlet_integrable U b ub).const_mul c)
  filter_upwards [hab] with x hx
  have h := hx (ub.grad x)
  rw [smul_matVecMul, vecDot_smul_right] at h
  nlinarith

/-- Multiplicative inverse Neumann comparison.  The proof changes the flux
from `q` to `c*q` in the actual Neumann variational principle. -/
theorem aux_lem_extension_cell_moment_sigmaStarInv_le_smul {d : ℕ}
    (U : Domain d) (a b : CoeffOn U)
    (ha : CoeffOn.IsSymmetric a) (hb : CoeffOn.IsSymmetric b)
    (c : ℝ) (hc : 0 < c)
    (hba : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      MatLoewnerLE (b.toCoeffField x) (c • a.toCoeffField x)) :
    MatLoewnerLE (Homogenization.Book.Ch02.sigmaStarInvCoarse U a)
      (c • Homogenization.Book.Ch02.sigmaStarInvCoarse U b) := by
  have hTa := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hTb := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U b hb
  intro q
  have hcompare : symmetricNeumannNu U a q ≤ c⁻¹ * symmetricNeumannNu U b (c • q) := by
    obtain ⟨ua, _, hua⟩ := hTa.neumann_meanZero_maximizer_exists q
    obtain ⟨ub, _, hub⟩ := hTb.neumann_meanZero_maximizer_exists (c • q)
    rw [symmetricNeumannNu_eq_of_maximizer hua,
      symmetricNeumannNu_eq_of_maximizer hub]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (hub ua) (inv_pos.mpr hc).le)
    unfold symmetricNeumannEnergyValue Homogenization.Book.Ch02.average
    rw [← mul_assoc, mul_comm c⁻¹, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
    rw [← integral_const_mul]
    apply integral_mono_ae
      (aux_lem_extension_cell_moment_neumann_integrable U a q ua)
      ((aux_lem_extension_cell_moment_neumann_integrable U b (c • q) ua).const_mul c⁻¹)
    filter_upwards [hba] with x hx
    have h := hx (ua.grad x)
    rw [smul_matVecMul, vecDot_smul_right] at h
    rw [vecDot_smul_left]
    apply (mul_le_mul_iff_right₀ hc).mp
    field_simp
    nlinarith
  rw [hTa.neumann_value_by_sigmaStarInv, hTb.neumann_value_by_sigmaStarInv,
    matVecMul_smul, vecDot_smul_left, vecDot_smul_right] at hcompare
  rw [smul_matVecMul, vecDot_smul_right]
  convert hcompare using 1 <;> field_simp <;> ring

theorem aux_lem_extension_cell_moment_b_norm_le_mul {d : ℕ}
    (U : Domain d) (a b : CoeffOn U)
    (ha : CoeffOn.IsSymmetric a) (hb : CoeffOn.IsSymmetric b)
    (c : ℝ) (hc : 0 < c)
    (hab : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      MatLoewnerLE (a.toCoeffField x) (c • b.toCoeffField x)) :
    matrixNorm (Homogenization.Book.Ch02.bCoarse U a) ≤
      c * matrixNorm (Homogenization.Book.Ch02.bCoarse U b) := by
  rw [(Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha).derived_matrices.2.2,
    (Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U b hb).derived_matrices.2.2]
  have h := aux_lem_extension_cell_moment_sigma_le_smul U a b ha hb c hc hab
  have ha' := Homogenization.Book.Ch02.bCoarse_posSemidef U a
  have hb' := Homogenization.Book.Ch02.bCoarse_posSemidef U b
  rw [(Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha).derived_matrices.2.2] at ha'
  rw [(Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U b hb).derived_matrices.2.2] at hb'
  have hcb' : (c • Homogenization.Book.Ch02.sigmaCoarse U b).PosSemidef := hb'.smul hc.le
  have hnorm := matrixNorm_le_of_matLoewnerLE_of_posSemidef ha' hcb' h
  simpa [aux_lem_extension_cell_moment_matrixNorm_smul, abs_of_pos hc] using hnorm

theorem aux_lem_extension_cell_moment_sigmaStarInv_norm_le_mul {d : ℕ}
    (U : Domain d) (a b : CoeffOn U)
    (ha : CoeffOn.IsSymmetric a) (hb : CoeffOn.IsSymmetric b)
    (c : ℝ) (hc : 0 < c)
    (hba : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      MatLoewnerLE (b.toCoeffField x) (c • a.toCoeffField x)) :
    matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) ≤
      c * matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse U b) := by
  have h := aux_lem_extension_cell_moment_sigmaStarInv_le_smul U a b ha hb c hc hba
  have ha' := (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef U a).posSemidef
  have hb' := (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef U b).posSemidef
  have hcb' : (c • Homogenization.Book.Ch02.sigmaStarInvCoarse U b).PosSemidef := hb'.smul hc.le
  have hnorm := matrixNorm_le_of_matLoewnerLE_of_posSemidef ha' hcb' h
  simpa [aux_lem_extension_cell_moment_matrixNorm_smul, abs_of_pos hc] using hnorm
end


section
open MeasureTheory Homogenization Homogenization.Book.Ch02
open Homogenization.Internal.Ch02.BookCh02

/-- A unit-sphere response bound controls both coarse ellipticities for a symmetric
coefficient; positivity of the other quadratic form is enough. -/
theorem aux_lem_extension_cell_moment_norms_le_response {d : ℕ} [NeZero d]
    (U : Domain d) (a : CoeffOn U) (ha : CoeffOn.IsSymmetric a)
    (J : ℝ) (hJ : 0 ≤ J)
    (hresp : ∀ e : Vec d, vecNormSq e = 1 → responseJ U a e e ≤ J) :
    matrixNorm (Homogenization.Book.Ch02.bCoarse U a) ≤ 2 * (J + 1) ∧
      matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) ≤ 2 * (J + 1) := by
  have hT := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hB := bCoarse_posSemidef U a
  have hS := (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef U a).posSemidef
  have hquad : ∀ e : Vec d, vecNormSq e = 1 →
      vecDot e (matVecMul (Homogenization.Book.Ch02.bCoarse U a) e) +
        vecDot e (matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) e) ≤
          2 * (J + 1) := by
    intro e he
    have h := hresp e he
    rw [hT.response_dirichlet_neumann_split, hT.dirichlet_value_by_sigma,
      hT.neumann_value_by_sigmaStarInv] at h
    rw [hT.derived_matrices.2.2]
    change vecDot e e = 1 at he
    linarith
  constructor
  · apply SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.matrixNorm_le_of_forall_unit
      hB (by positivity)
    intro e he
    have hn : 0 ≤ vecDot e (matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) e) :=
      hS.dotProduct_mulVec_nonneg e
    linarith [hquad e he]
  · apply SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.matrixNorm_le_of_forall_unit
      hS (by positivity)
    intro e he
    have hn : 0 ≤ vecDot e (matVecMul (Homogenization.Book.Ch02.bCoarse U a) e) :=
      hB.dotProduct_mulVec_nonneg e
    linarith [hquad e he]

def aux_lem_extension_cell_moment_cubeNormalize {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) : Vec d :=
  (3 : ℝ) ^ (-Q.scale) • x - (fun i => (Q.index i : ℝ))

/-- Put a positive continuous unit-cube reference field onto any triadic cube.
The response is unchanged, via genuine translation and dilation of the public
variational response, not an assumed covariance. -/
theorem aux_lem_extension_cell_moment_reference_on_cube {d : ℕ}
    (Q : TriadicCube d) (f : C(Vec d, ℝ)) (hf : ∀ x, 0 < f x)
    (a0 : CoeffOn (cubeDomain (originCube d 0)))
    (ha0 : ∀ᵐ x ∂volumeMeasureOn (openCubeSet (originCube d 0)),
      a0.toCoeffField x = scalarMatrix (f x)) :
    ∃ aQ : CoeffOn (cubeDomain Q),
      (∀ x, aQ.toCoeffField x = scalarMatrix (f (aux_lem_extension_cell_moment_cubeNormalize Q x))) ∧
      CoeffOn.IsSymmetric aQ ∧
      ∀ p q, responseJ (cubeDomain Q) aQ p q =
        responseJ (cubeDomain (originCube d 0)) a0 p q := by
  let v : Vec d := fun i => (Q.index i : ℝ)
  let g : Vec d → ℝ := fun x => f (aux_lem_extension_cell_moment_cubeNormalize Q x)
  have hg : Continuous g := f.continuous.comp
    ((continuous_const.smul continuous_id).sub continuous_const)
  let aQ := (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
    hg (fun x => hf _) (cubeDomain Q)).toCoeffOn
  let QD := dilateCube (-Q.scale) Q
  let gD : Vec d → ℝ := fun x => f (x - v)
  let aD := (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos (a := gD)
    (f.continuous.comp (continuous_id.sub continuous_const)) (fun x => hf _) (cubeDomain QD)).toCoeffOn
  let aZ := (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
    f.continuous hf (cubeDomain (originCube d 0))).toCoeffOn
  have haZ : CoeffOn.AEEq a0 aZ := ha0
  have hDil := CoeffOn.dilate_isCubeDilation (-Q.scale) aQ
  have hAE : CoeffOn.AEEq (aQ.dilate (-Q.scale)) aD := by
    refine hDil.coeff_ae_eq.trans (Filter.Eventually.of_forall ?_)
    intro x
    change scalarMatrix (f (aux_lem_extension_cell_moment_cubeNormalize Q
      (undilateVec (-Q.scale) x))) = scalarMatrix (f (x - v))
    congr 2
    unfold aux_lem_extension_cell_moment_cubeNormalize undilateVec triadicDilationFactor
    rw [smul_smul, mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ (-Q.scale) ≠ 0), one_smul]
  have hQDscale : QD.scale = 0 := by simp [QD, dilateCube]
  have hQDshift : triadicCubeShift QD = v := by
    ext i
    simp [triadicCubeShift, cubeScaleFactor, QD, dilateCube, v]
  have hQDset : openCubeSet QD = translateSet v (openCubeSet (originCube d 0)) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube, hQDscale, hQDshift]
  refine ⟨aQ, fun _ => rfl, Filter.Eventually.of_forall (fun _ => ?_), ?_⟩
  · change (scalarMatrix (g _)).IsSymm
    simp [scalarMatrix, Matrix.IsSymm]
  · intro p q
    calc
      responseJ (cubeDomain Q) aQ p q = responseJ (cubeDomain QD) (aQ.dilate (-Q.scale)) p q :=
        (responseJ_dilate hDil p q).symm
      _ = responseJ (cubeDomain QD) aD p q := responseJ_eq_ofAEEq hAE p q
      _ = responseJ (cubeDomain (originCube d 0)) aZ p q := by
        rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ,
          Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
        change ResponseJ (openCubeSet QD) p q (fun x => scalarMatrix (f (x - v))) =
          ResponseJ (openCubeSet (originCube d 0)) p q (fun x => scalarMatrix (f x))
        rw [hQDset, ResponseJ_translateSet_eq_translateCoeffField]
        congr 1
        funext x
        change scalarMatrix (f ((x + v) - v)) = scalarMatrix (f x)
        rw [add_sub_cancel_right]
      _ = _ := (responseJ_eq_ofAEEq haZ p q).symm
end


section
open MeasureTheory SubdiffusiveProcess
open scoped BigOperators

theorem aux_lem_extension_cell_moment_cutoff_log {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    Real.log (cutoffCoefficient M H om N x) =
      -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) + H om x +
        (∑ j ∈ Finset.range (N + 1), om (-(j : ℤ)) x) -
          ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
  rw [cutoffCoefficient, Real.log_mul
    (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne') (Real.exp_pos _).ne',
    Real.log_inv, Real.log_exp, cutoffPotential]
  change -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
    (H om x + (∑ j ∈ Finset.range (N + 1), om (-(j : ℤ)) x) -
      ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) = _
  ring

/-- Exact separation into a matched-scale fine field and the long layers. -/
theorem aux_lem_extension_cell_moment_cutoff_log_split {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N m : ℕ) (hmN : m ≤ N)
    (c x : SpatialCoordinates d) :
    Real.log (cutoffCoefficient M H om N ((3 : ℝ) ^ (-(m : ℤ)) • x + c)) -
      Real.log (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_lem_extension_cell_moment_zoom (m : ℤ) c om) (N - m) x) =
      H om ((3 : ℝ) ^ (-(m : ℤ)) • x + c) +
        (∑ j ∈ Finset.range m, om (-(j : ℤ)) ((3 : ℝ) ^ (-(m : ℤ)) • x + c)) -
          (m : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - m)) -
          Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := by
  let y := (3 : ℝ) ^ (-(m : ℤ)) • x + c
  have hsum : (∑ j ∈ Finset.range (N + 1), om (-(j : ℤ)) y) =
      (∑ j ∈ Finset.range m, om (-(j : ℤ)) y) +
        ∑ j ∈ Finset.range (N - m + 1), om (-(j : ℤ) - (m : ℤ)) y := by
    rw [show N + 1 = m + (N - m + 1) by omega, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    push_cast
    omega
  rw [aux_lem_extension_cell_moment_cutoff_log,
    aux_lem_extension_cell_moment_cutoff_log]
  simp only [ContinuousMap.zero_apply, aux_lem_extension_cell_moment_zoom_apply]
  change (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) + H om y +
      (∑ j ∈ Finset.range (N + 1), om (-(j : ℤ)) y) -
        ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) -
      (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - m)) + 0 +
        (∑ j ∈ Finset.range (N - m + 1), om (-(j : ℤ) - (m : ℤ)) y) -
          ((N - m : ℕ) + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) = _
  rw [hsum, Nat.cast_sub hmN]
  ring

theorem aux_lem_extension_cell_moment_cutoff_log_split_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N m : ℕ) (hmN : m ≤ N) (hm : 0 < m)
    (c x : SpatialCoordinates d) :
    Real.log (cutoffCoefficient M H om N ((3 : ℝ) ^ (-(m : ℤ)) • x + c)) -
      Real.log (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_lem_extension_cell_moment_zoom (m : ℤ) c om) (N - m) x) =
      Real.log (cutoffCoefficient M H om (m - 1) ((3 : ℝ) ^ (-(m : ℤ)) • x + c)) +
        Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m - 1)) +
        Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - m)) -
        Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := by
  rw [aux_lem_extension_cell_moment_cutoff_log_split M H om N m hmN,
    aux_lem_extension_cell_moment_cutoff_log,
    show m - 1 + 1 = m by omega]
  have hmr : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast (show m - 1 + 1 = m by omega)
  rw [hmr]
  ring

/-- The deterministic normalizers cost only the number of removed layers, never
the full cutoff. -/
theorem aux_lem_extension_cell_moment_normalizer_gap {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N m : ℕ) (hmN : m ≤ N) (hm : 0 < m) :
    |Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m - 1)) +
        Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - m)) -
        Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)| ≤
      (2 * Real.log 2) * M.delta ^ 2 * m := by
  have herr := SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.abs_normalizerLogError_le_of_le
    M (Nat.sub_le N m)
  have hgap : N - (N - m) = m := by omega
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.normalizerLogError, hgap,
    Real.log_div (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - m)).ne'
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne'] at herr
  have hlong := SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.abs_log_ahom_le M (m - 1)
  have hmr : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast (show m - 1 + 1 = m by omega)
  rw [hmr] at hlong
  have htau := mul_le_mul_of_nonneg_right (SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M)
    (show (0 : ℝ) ≤ (m : ℝ) by positivity)
  have htau0 : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (m : ℝ) :=
    mul_nonneg M.G4.tauSq_pos.le (by positivity)
  have hratio : |Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - m)) -
      Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)| ≤ Real.log 2 * M.delta ^ 2 * m := by
    have hab := abs_add_le
      (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - m)) -
        Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * m)
      (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * m)
    rw [sub_add_cancel] at hab
    rw [abs_of_nonneg htau0] at hab
    nlinarith
  have hab := abs_add_le (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m - 1)))
    (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - m)) -
      Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))
  rw [← add_sub_assoc] at hab
  have hx : 0 ≤ Real.log 2 * M.delta ^ 2 * (m : ℝ) := by positivity
  nlinarith
end


section
open MeasureTheory TopologicalSpace SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal BigOperators

theorem aux_lem_extension_cell_moment_cubeNormalize_scale {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) (hscale : Q.scale = -(n : ℤ)) (x : Vec d) :
    aux_lem_extension_cell_moment_cubeNormalize Q x =
      (3 : ℝ) ^ (n : ℤ) • (x - cubeCenter Q) := by
  ext i
  simp only [aux_lem_extension_cell_moment_cubeNormalize, cubeCenter, cubeScaleFactor,
    hscale, neg_neg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zpow_neg]
  field_simp
  <;> ring

theorem aux_lem_extension_cell_moment_cubeNormalize_physical {d : ℕ}
    (Q : TriadicCube d) (k n : ℕ) (hscale : Q.scale = -(n : ℤ)) (w x : Vec d) :
    (3 : ℝ) ^ (-((k + n : ℕ) : ℤ)) • aux_lem_extension_cell_moment_cubeNormalize Q x +
      (w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q) =
        fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i := by
  rw [aux_lem_extension_cell_moment_cubeNormalize_scale Q n hscale, smul_smul]
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have he : -((k + n : ℕ) : ℤ) + (n : ℤ) = -(k : ℤ) := by omega
  rw [he]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The explicit long-layer factor on one above-wavelength descendant. -/
def aux_lem_extension_cell_moment_aboveLogEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : Compacts (SpatialCoordinates d)) (m : ℕ) (c : SpatialCoordinates d)
    (om : BilateralField d) : ℝ :=
  ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
    aux_lem_extension_cell_moment_physicalLogNorm M (m - 1)
      ((3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) • c) om +
    (2 * Real.log 2) * M.delta ^ 2 * m

theorem aux_lem_extension_cell_moment_aboveLogEnvelope_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : Compacts (SpatialCoordinates d)) (m : ℕ) (c : SpatialCoordinates d)
    (om : BilateralField d) :
    0 ≤ aux_lem_extension_cell_moment_aboveLogEnvelope M H K m c om := by
  unfold aux_lem_extension_cell_moment_aboveLogEnvelope
  exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)

theorem aux_lem_extension_cell_moment_aboveLogEnvelope_bounds {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : Compacts (SpatialCoordinates d)) (N k n : ℕ) (habove : k + n ≤ N)
    (Q : TriadicCube d)
    (hQ : Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)))
    (w : SpatialCoordinates d)
    (hK : ∀ x ∈ openCubeSet Q,
      (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈ (K : Set (SpatialCoordinates d)))
    (om : BilateralField d) (x : SpatialCoordinates d) (hx : x ∈ openCubeSet Q) :
    |Real.log (cutoffCoefficient M H om N
        (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i)) -
      Real.log (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_lem_extension_cell_moment_zoom ((k + n : ℕ) : ℤ)
          (w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q) om) (N - (k + n))
        (aux_lem_extension_cell_moment_cubeNormalize Q x))| ≤
      aux_lem_extension_cell_moment_aboveLogEnvelope M H K (k + n)
        (w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q) om := by
  let m := k + n
  let c := w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q
  let y : SpatialCoordinates d := fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i
  have hscale : Q.scale = -(n : ℤ) := by
    simpa [originCube] using scale_eq_of_mem_descendantsAtScale hQ
  have hid := aux_lem_extension_cell_moment_cubeNormalize_physical Q k n hscale w x
  have hHpt : |H om y| ≤ ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
    ContinuousMap.norm_coe_le_norm ((H om).restrict (K : Set (SpatialCoordinates d)))
      ⟨y, hK x hx⟩
  by_cases hm : m = 0
  · have hsplit := aux_lem_extension_cell_moment_cutoff_log_split
      M H om N m habove c (aux_lem_extension_cell_moment_cubeNormalize Q x)
    rw [hid] at hsplit
    have hsplit0 : Real.log (cutoffCoefficient M H om N y) -
        Real.log (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          (aux_lem_extension_cell_moment_zoom (m : ℤ) c om) (N - m)
          (aux_lem_extension_cell_moment_cubeNormalize Q x)) = H om y := by
      simpa only [hm, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul,
        add_zero, sub_zero, Nat.sub_zero, add_sub_cancel_right] using hsplit
    change |Real.log (cutoffCoefficient M H om N y) - _| ≤ _
    rw [hsplit0]
    unfold aux_lem_extension_cell_moment_aboveLogEnvelope
    have hE0 : 0 ≤ aux_lem_extension_cell_moment_physicalLogNorm M (k + n - 1)
        ((3 : ℝ) ^ ((k + n - 1 : ℕ) : ℤ) •
          (w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q)) om := norm_nonneg _
    have hD0 : 0 ≤ (2 * Real.log 2) * M.delta ^ 2 * ((k + n : ℕ) : ℝ) := by positivity
    linarith
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hsplit := aux_lem_extension_cell_moment_cutoff_log_split_pos
      M H om N m habove hmpos c (aux_lem_extension_cell_moment_cubeNormalize Q x)
    rw [hid] at hsplit
    have hξ := aux_lem_extension_cell_moment_descendant_micro_mem
      (m - 1) k n (by dsimp [m]; omega) Q hQ x hx
    have hlong := aux_lem_extension_cell_moment_physicalLogNorm_bounds M H (m - 1)
      ((3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) • c)
      ((3 : ℝ) ^ (((m - 1 : ℕ) : ℤ) - (k : ℤ)) • (x - cubeCenter Q)) hξ om
    rw [aux_lem_extension_cell_moment_descendant_micro_identity] at hlong
    have hlong' := hlong.trans (add_le_add hHpt (le_refl _))
    have hnorm := aux_lem_extension_cell_moment_normalizer_gap M N m habove hmpos
    change |Real.log (cutoffCoefficient M H om N y) - _| ≤ _
    rw [hsplit]
    calc
      _ = |Real.log (cutoffCoefficient M H om (m - 1) y) +
        (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m - 1)) +
          Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - m)) -
          Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hlong' hnorm)

theorem aux_lem_extension_cell_moment_ratio_of_log {a b G : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : |Real.log a - Real.log b| ≤ G) :
    a ≤ Real.exp G * b ∧ b ≤ Real.exp G * a := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  constructor
  · have he := Real.exp_le_exp.mpr (show Real.log a ≤ G + Real.log b by linarith)
    simpa only [Real.exp_add, Real.exp_log ha, Real.exp_log hb] using he
  · have he := Real.exp_le_exp.mpr (show Real.log b ≤ G + Real.log a by linarith)
    simpa only [Real.exp_add, Real.exp_log ha, Real.exp_log hb] using he
end


section
open MeasureTheory SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal BigOperators

/-- A convenient explicit sufficient disorder threshold for the frozen moment range. -/
theorem aux_lem_extension_cell_moment_response_admissible {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C p : ℝ) (hC : 0 < C) (hp : 0 < p)
    (hδ : M.delta ≤ (C * p)⁻¹) :
    p ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
  have hdelta := M.shellPrefix.delta_pos
  have hdelta1 : M.delta ≤ 1 := M.shellPrefix.delta_le_half.trans (by norm_num)
  have hlogpos : 0 < |Real.log M.delta| :=
    abs_pos.mpr (Real.log_neg hdelta (M.shellPrefix.delta_le_half.trans_lt (by norm_num))).ne
  have hlogloss := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.delta_sq_mul_abs_log_le_self
    hdelta hdelta1
  have hprod : C * p * (M.delta ^ 2 * |Real.log M.delta|) ≤ 1 := by
    calc
      _ ≤ (C * p) * M.delta := mul_le_mul_of_nonneg_left hlogloss (mul_pos hC hp).le
      _ ≤ (C * p) * (C * p)⁻¹ := mul_le_mul_of_nonneg_left hδ (mul_pos hC hp).le
      _ = 1 := mul_inv_cancel₀ (mul_pos hC hp).ne'
  rw [show C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
      (C * (M.delta ^ 2) * |Real.log M.delta|)⁻¹ by
    field_simp [hC.ne', hdelta.ne', hlogpos.ne']]
  have hden : 0 < C * (M.delta ^ 2) * |Real.log M.delta| := by positivity
  rw [show (C * (M.delta ^ 2) * |Real.log M.delta|)⁻¹ =
      (C * (M.delta ^ 2) * |Real.log M.delta|)⁻¹ * 1 by ring,
    le_inv_mul_iff₀ hden]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

/-- The normalized infrared-free physical family has a bounded matched-scale
response at any prescribed finite moment.  All constants precede the model. -/
theorem aux_lem_extension_cell_moment_matched_response {d : ℕ} (hd : 2 ≤ d)
    (I : in_J d) (p : ℝ) (hp : 1 ≤ p) :
    ∃ δ0 C0 : ℝ, 0 < δ0 ∧ 0 < C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ δ0 →
      ∃ family : ℕ → BilateralField d → TriadicCoeffFamily d,
      ∃ J : ℕ → BilateralField d → ℝ,
        (∀ N om Q, ∀ᵐ x ∂volume.restrict (openCubeSet Q),
          ((family N om).coeffOn Q).toCoeffField x = scalarMatrix
            (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x)) ∧
        (∀ N om, IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
          (∑ i : Fin d, e i ^ 2) = 1 ∧
            v = responseJ (cubeDomain (originCube d 0))
              ((family N om).coeffOn (originCube d 0)) e e} (J N om)) ∧
        (∀ N, AEStronglyMeasurable (J N) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (J N) (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal C0) := by
  obtain ⟨Cresp, hCresp, hresp⟩ := in_moments_response_moment d hd I
  let ξ : ℕ := 2 * (Nat.ceil (2 * p) + 128 * d + 1)
  have hξeven : Even ξ := even_two_mul _
  have hξdim : 128 * d ≤ ξ := by dsimp [ξ]; omega
  have hξpos : 0 < (ξ : ℝ) := by exact_mod_cast (show 0 < ξ by dsimp [ξ]; omega)
  have hξp : 2 * p ≤ (ξ : ℝ) := by
    have hceil := Nat.le_ceil (2 * p)
    dsimp [ξ]
    push_cast
    nlinarith [show (0 : ℝ) ≤ (Nat.ceil (2 * p) : ℝ) by positivity,
      show (0 : ℝ) ≤ (d : ℝ) by positivity]
  obtain ⟨δresp, hδresp, hRM⟩ := hresp ξ hξeven hξdim
  let δ0 := min δresp (Cresp * (ξ : ℝ))⁻¹
  let C0 := Cresp * (ξ : ℝ) * Real.log (2 + (ξ : ℝ))
  have hlogξ : 0 < Real.log (2 + (ξ : ℝ)) := Real.log_pos (by linarith)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨δ0, C0, lt_min hδresp (by positivity), hC0, ?_⟩
  intro _ _ M hδ
  obtain ⟨family, hfamily⟩ := in_moments_family_transport d hd M
  have hδrespM : M.delta ≤ δresp := hδ.trans (min_le_left _ _)
  have hadm := aux_lem_extension_cell_moment_response_admissible M Cresp ξ hCresp hξpos
    (hδ.trans (min_le_right _ _))
  obtain ⟨J, hJgreat, hJmeas, hJnorm⟩ := hRM M hδrespM family hfamily hadm
  refine ⟨family, fun N => J N 0, hfamily, ?_, fun N => hJmeas N 0, ?_⟩
  · intro N om
    simpa only [Nat.cast_zero] using hJgreat N 0 om
  · intro N
    have hδ1 : M.delta ≤ 1 := M.shellPrefix.delta_le_half.trans (by norm_num)
    have hδsq : M.delta ^ 2 ≤ 1 := by nlinarith [M.shellPrefix.delta_pos]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hξp)
      (hJmeas N 0)).trans ((hJnorm N 0).trans (ENNReal.ofReal_le_ofReal (by
        dsimp [C0]
        simpa using mul_le_mul_of_nonneg_left hδsq hC0.le)))
end


section
open MeasureTheory TopologicalSpace SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal BigOperators

/-- Actual coefficient identity plus variational monotonicity gives the needed
above-wavelength comparison to a matched-scale response. -/
theorem aux_lem_extension_cell_moment_above_coarse_pointwise {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : Compacts (SpatialCoordinates d)) (N k n : ℕ) (habove : k + n ≤ N)
    (Q : TriadicCube d)
    (hQ : Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)))
    (w : SpatialCoordinates d)
    (hK : ∀ x ∈ openCubeSet Q,
      (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈ (K : Set (SpatialCoordinates d)))
    (om : BilateralField d) (a : CoeffOn (cubeDomain Q))
    (ha : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), a.toCoeffField x =
      scalarMatrix (cutoffCoefficient M H om N (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i)))
    (a0 : CoeffOn (cubeDomain (originCube d 0)))
    (ha0 : ∀ᵐ x ∂volumeMeasureOn (openCubeSet (originCube d 0)), a0.toCoeffField x =
      scalarMatrix (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_lem_extension_cell_moment_zoom ((k + n : ℕ) : ℤ)
          (w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q) om) (N - (k + n)) x))
    (J : ℝ) (hJ : IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧ v = responseJ (cubeDomain (originCube d 0)) a0 e e} J) :
    matrixNorm (Homogenization.Book.Ch02.bCoarse (cubeDomain Q) a) ≤
        2 * (Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K (k + n)
          (w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q) om) * (J + 1)) ∧
      matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain Q) a) ≤
        2 * (Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K (k + n)
          (w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q) om) * (J + 1)) := by
  let om' := aux_lem_extension_cell_moment_zoom ((k + n : ℕ) : ℤ)
    (w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q) om
  let f : C(SpatialCoordinates d, ℝ) :=
    ⟨cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om' (N - (k + n)),
      SubdiffusiveProcess.Lane4.cutoffCoefficient_continuous M _ om' _⟩
  have hf : ∀ x, 0 < f x :=
    SubdiffusiveProcess.Lane4.cutoffCoefficient_pos M _ om' _
  obtain ⟨b, hbfield, hbsym, hbeq⟩ :=
    aux_lem_extension_cell_moment_reference_on_cube Q f hf a0 ha0
  have hasym : CoeffOn.IsSymmetric a := ha.mono fun x hx => by
    rw [hx]
    exact scalarMatrix_isSymm _
  have hJ0 : 0 ≤ J := by
    obtain ⟨e, _, he⟩ := hJ.1
    rw [he]
    exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
  have hbresp : ∀ e : Vec d, vecNormSq e = 1 → responseJ (cubeDomain Q) b e e ≤ J := by
    intro e he
    rw [hbeq]
    apply hJ.2
    refine ⟨e, ?_, rfl⟩
    simpa [vecNormSq, vecDot, pow_two] using he
  obtain ⟨hbB, hbS⟩ := aux_lem_extension_cell_moment_norms_le_response
    (cubeDomain Q) b hbsym J hJ0 hbresp
  let c : ℝ := Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K (k + n)
    (w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q) om)
  have hc : 0 < c := Real.exp_pos _
  have hident : ∀ e : Vec d, matVecMul (1 : Mat d) e = e := by
    intro e
    ext i
    simp [matVecMul, Matrix.one_apply]
  have horders : (∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      MatLoewnerLE (a.toCoeffField x) (c • b.toCoeffField x)) ∧
      (∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
        MatLoewnerLE (b.toCoeffField x) (c • a.toCoeffField x)) := by
    have hpoint : ∀ x ∈ openCubeSet Q,
        cutoffCoefficient M H om N (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ≤
            c * f (aux_lem_extension_cell_moment_cubeNormalize Q x) ∧
          f (aux_lem_extension_cell_moment_cubeNormalize Q x) ≤
            c * cutoffCoefficient M H om N (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) := by
      intro x hx
      exact aux_lem_extension_cell_moment_ratio_of_log
        (SubdiffusiveProcess.Lane4.cutoffCoefficient_pos M H om N _) (hf _)
        (aux_lem_extension_cell_moment_aboveLogEnvelope_bounds M H K N k n habove Q hQ w hK om x hx)
    constructor <;> filter_upwards [ha, ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx hxQ
    · intro e
      simp only [hx, hbfield, smul_matVecMul, hident, vecDot_smul_right]
      have h := mul_le_mul_of_nonneg_right (hpoint x hxQ).1 (vecNormSq_nonneg e)
      change _ ≤ _
      change _ * vecDot e e ≤ _ * vecDot e e at h
      nlinarith
    · intro e
      simp only [hx, hbfield, smul_matVecMul, hident, vecDot_smul_right]
      have h := mul_le_mul_of_nonneg_right (hpoint x hxQ).2 (vecNormSq_nonneg e)
      change _ * vecDot e e ≤ _ * vecDot e e at h
      nlinarith
  have hAB := aux_lem_extension_cell_moment_b_norm_le_mul (cubeDomain Q) a b hasym hbsym c hc horders.1
  have hAS := aux_lem_extension_cell_moment_sigmaStarInv_norm_le_mul (cubeDomain Q) a b hasym hbsym c hc horders.2
  constructor
  · exact (hAB.trans (mul_le_mul_of_nonneg_left hbB hc.le)).trans_eq (by dsimp [c]; ring)
  · exact (hAS.trans (mul_le_mul_of_nonneg_left hbS hc.le)).trans_eq (by dsimp [c]; ring)
end


section
open MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped ENNReal BigOperators

def aux_lem_extension_cell_moment_aboveRate (d : ℕ) (p : ℝ) : ℝ :=
  4 * Real.log 2 + p * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2

theorem aux_lem_extension_cell_moment_aboveRate_pos (d : ℕ) (p : ℝ) (hp : 0 < p) :
    0 < aux_lem_extension_cell_moment_aboveRate d p := by
  unfold aux_lem_extension_cell_moment_aboveRate
  positivity

theorem aux_lem_extension_cell_moment_aboveEnvelope_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (K : Compacts (SpatialCoordinates d)) (m : ℕ) (c : SpatialCoordinates d) :
    Measurable (aux_lem_extension_cell_moment_aboveLogEnvelope M H K m c) := by
  exact ((((ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).norm.measurable).comp hH).add
    (aux_lem_extension_cell_moment_physicalLogNorm_measurable M (m - 1) _)).add measurable_const

/-- Above-wavelength multiplier moment, uniform in cutoff and microscopic center. -/
theorem aux_lem_extension_cell_moment_aboveEnvelope_moment {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredAdmissible M H →
      ∀ (K : Compacts (SpatialCoordinates d)) (m : ℕ) (c : SpatialCoordinates d)
        (p : ℝ), 0 < p →
      eLpNorm (fun om => Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K m c om))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (Real.log 4 / p + 4 * p * C K * M.delta ^ 2 +
        aux_lem_extension_cell_moment_aboveRate d p * M.delta ^ 2 +
        aux_lem_extension_cell_moment_aboveRate d p * M.delta ^ 2 * m)) := by
  obtain ⟨C, hC, hCM⟩ := aux_lem_extension_cell_moment_totalLogNorm_eLpNorm hd
  refine ⟨C, hC, ?_⟩
  intro M H hH K m c p hp
  let D := (2 * Real.log 2) * M.delta ^ 2 * m
  let F : BilateralField d → ℝ := fun om => Real.exp
    (‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
      aux_lem_extension_cell_moment_physicalLogNorm M (m - 1)
        ((3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) • c) om)
  have heq : (fun om => Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K m c om)) =
      Real.exp D • F := by
    funext om
    change Real.exp (_ + D) = Real.exp D * F om
    rw [Real.exp_add]
    exact mul_comm _ _
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
  have h := hCM M H hH K (m - 1) ((3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) • c) 1 p (by norm_num) hp
  simp only [one_mul, one_pow, mul_one] at h
  refine (mul_le_mul_left' h (ENNReal.ofReal (Real.exp D))).trans ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hlen : ((m - 1 : ℕ) : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast (show m - 1 + 1 ≤ m + 1 by omega)
  have hB0 : 0 ≤ 2 * Real.log 2 + p * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 :=
    by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlen (mul_nonneg hB0 (sq_nonneg M.delta))
  have hlog : 0 ≤ Real.log 2 * M.delta ^ 2 := by positivity
  dsimp [D, aux_lem_extension_cell_moment_aboveRate]
  nlinarith

theorem aux_lem_extension_cell_moment_eLpNorm_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℝ) (hp : 0 < p) (f g : α → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x * g x) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * p)) μ * eLpNorm g (ENNReal.ofReal (2 * p)) μ := by
  have hp2 : 0 < 2 * p := by positivity
  haveI : ENNReal.HolderTriple (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal (2 * p)) (ENNReal.ofReal p) := by
    constructor
    rw [← ENNReal.ofReal_inv_of_pos hp2, ← ENNReal.ofReal_inv_of_pos hp,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    <;> ring
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (eLpNorm_smul_le_mul_eLpNorm hg hf :
      eLpNorm (f • g) (ENNReal.ofReal p) μ ≤
        eLpNorm f (ENNReal.ofReal (2 * p)) μ * eLpNorm g (ENNReal.ofReal (2 * p)) μ)
end


section
open MeasureTheory TopologicalSpace SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal BigOperators

/-- The above-wavelength moment estimate for any public coefficient representative
of the actual physical cutoff on the descendant.  Its only extra premise is the
literal a.e. representative identity, supplied by the frozen chart identity. -/
theorem aux_lem_extension_cell_moment_above_core {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (p ε : ℝ) (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ δ0 →
      ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      ∃ C0 : ℝ, 0 < C0 ∧
        ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
          (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
        ∀ n : ℕ, k + n ≤ N →
        ∀ Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)),
        ∀ a : BilateralField d → CoeffOn (cubeDomain Q),
          (∀ om, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
            (a om).toCoeffField x = scalarMatrix (cutoffCoefficient M H om N
              (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i))) →
          eLpNorm (fun om => matrixNorm (Homogenization.Book.Ch02.bCoarse (cubeDomain Q) (a om)))
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) ∧
          eLpNorm (fun om => matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain Q) (a om)))
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < 2 * p := by positivity
  obtain ⟨δresp, CJ, hδresp, hCJ, hresponse⟩ :=
    aux_lem_extension_cell_moment_matched_response hd I p hp
  obtain ⟨CH, _hCH, hHM⟩ := aux_lem_extension_cell_moment_aboveEnvelope_moment hd
  let B := aux_lem_extension_cell_moment_aboveRate d (2 * p)
  have hB : 0 < B := aux_lem_extension_cell_moment_aboveRate_pos d (2 * p) hp2
  let δrate := Real.sqrt (ε / B)
  have hδrate : 0 < δrate := Real.sqrt_pos.2 (div_pos hε hB)
  refine ⟨min δresp δrate, B, lt_min hδresp hδrate, hB, ?_⟩
  intro M H hH hδ z0 R hR
  have hrate : B * M.delta ^ 2 ≤ ε := by
    have hsq : M.delta ^ 2 ≤ δrate ^ 2 :=
      pow_le_pow_left₀ M.shellPrefix.delta_pos.le (hδ.trans (min_le_right _ _)) 2
    calc
      _ ≤ B * δrate ^ 2 := mul_le_mul_of_nonneg_left hsq hB.le
      _ = ε := by dsimp [δrate]; rw [Real.sq_sqrt (div_pos hε hB).le]; field_simp
  obtain ⟨family, J, hfamily, hJgreat, hJmeas, hJnorm⟩ :=
    hresponse M (hδ.trans (min_le_left _ _))
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall z0 R, isCompact_closedBall _ _⟩
  let P := Real.log 4 / (2 * p) + 4 * (2 * p) * CH K * M.delta ^ 2 + B * M.delta ^ 2
  let C0 := 2 * (CJ + 1) * Real.exp P
  refine ⟨C0, by dsimp [C0]; positivity, ?_⟩
  intro w N k _hk hcell n habove Q hQ a ha
  let m := k + n
  let c := w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q
  let T := aux_lem_extension_cell_moment_zoom (m : ℤ) c
  have hT : MeasurePreserving T (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    aux_lem_extension_cell_moment_zoom_measurePreserving M (m : ℤ) c
  let F : BilateralField d → ℝ := fun om =>
    Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K m c om)
  let X : BilateralField d → ℝ := fun om => J (N - m) (T om) + 1
  have hJ0 : ∀ om, 0 ≤ J (N - m) (T om) := by
    intro om
    obtain ⟨e, _, he⟩ := (hJgreat (N - m) (T om)).1
    rw [he]
    exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
  have hX0 : ∀ om, 0 ≤ X om := fun om => by dsimp [X]; linarith [hJ0 om]
  have hJTm : AEStronglyMeasurable (fun om => J (N - m) (T om))
      (chaosSampleLaw M).toMeasure := (hJmeas (N - m)).comp_measurePreserving hT
  have hXm : AEStronglyMeasurable X (chaosSampleLaw M).toMeasure :=
    hJTm.add aestronglyMeasurable_const
  have hFm : AEStronglyMeasurable F (chaosSampleLaw M).toMeasure :=
    (aux_lem_extension_cell_moment_aboveEnvelope_measurable M H hH.measurable K m c).exp.aestronglyMeasurable
  have hXnorm : eLpNorm X (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CJ + 1) := by
    have hJT : eLpNorm (fun om => J (N - m) (T om)) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CJ := by
      change eLpNorm (J (N - m) ∘ T) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CJ
      rw [eLpNorm_comp_measurePreserving (hJmeas (N - m)) hT]
      exact hJnorm (N - m)
    have hone : eLpNorm (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure = 1 := by
      rw [eLpNorm_const' _ (ENNReal.ofReal_ne_zero_iff.mpr hp2) ENNReal.ofReal_ne_top]
      simp
    have hpone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2 * p by linarith))
    have hadd := eLpNorm_add_le hJTm
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : BilateralField d => (1 : ℝ))
        (chaosSampleLaw M).toMeasure) hpone
    refine hadd.trans ?_
    rw [hone, ENNReal.ofReal_add hCJ.le zero_le_one, ENNReal.ofReal_one]
    exact add_le_add hJT (le_refl _)
  have hFnorm : eLpNorm F (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * m)) := hHM M H hH K m c (2 * p) hp2
  have hproduct : eLpNorm (fun om => F om * X om) (ENNReal.ofReal p)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * m)) * ENNReal.ofReal (CJ + 1) :=
    (aux_lem_extension_cell_moment_eLpNorm_mul (chaosSampleLaw M).toMeasure p hp0 F X hFm hXm).trans
      (mul_le_mul' hFnorm hXnorm)
  have hK : ∀ x ∈ openCubeSet Q,
      (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈ (K : Set (SpatialCoordinates d)) := by
    intro x hx
    have hxroot : x ∈ openCubeSet (originCube d 0) :=
      openCubeSet_subset_of_mem_descendantsAtScale (by simp) hQ hx
    have hyroot := hcell (aux_lem_extension_cell_moment_cellAffine_mem w _ (by positivity) hxroot)
    change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 ≤ R
    change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 < R / 2 at hyroot
    linarith
  have hpoint : ∀ om,
      matrixNorm (Homogenization.Book.Ch02.bCoarse (cubeDomain Q) (a om)) ≤ 2 * (F om * X om) ∧
        matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain Q) (a om)) ≤
          2 * (F om * X om) := by
    intro om
    exact aux_lem_extension_cell_moment_above_coarse_pointwise M H K N k n habove Q hQ w hK
      om (a om) (ha om) ((family (N - m) (T om)).coeffOn (originCube d 0))
      (hfamily (N - m) (T om) (originCube d 0)) (J (N - m) (T om)) (hJgreat (N - m) (T om))
  have hgrowth : B * M.delta ^ 2 * (m : ℝ) ≤ B * M.delta ^ 2 * k + ε * n := by
    dsimp [m]
    rw [Nat.cast_add, mul_add]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hrate (by positivity))
  have hfinish : ENNReal.ofReal 2 *
      (ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * m)) * ENNReal.ofReal (CJ + 1)) ≤
      ENNReal.ofReal (C0 * Real.exp (B * M.delta ^ 2 * k + ε * n)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_add]
    calc
      _ = C0 * Real.exp (B * M.delta ^ 2 * m) := by dsimp [C0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgrowth) (by dsimp [C0]; positivity)
  have hbound : ∀ Z : BilateralField d → ℝ, (∀ om, 0 ≤ Z om) →
      (∀ om, Z om ≤ 2 * (F om * X om)) →
      eLpNorm Z (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C0 * Real.exp (B * M.delta ^ 2 * k + ε * n)) := by
    intro Z hZ0 hZ
    have hz : eLpNorm Z (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal 2 * eLpNorm (fun om => F om * X om) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards with om
      rw [Real.norm_of_nonneg (hZ0 om), Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hX0 om))]
      exact hZ om
    exact (hz.trans (mul_le_mul_left' hproduct _)).trans hfinish
  constructor
  · exact hbound _ (fun _ => matrixNorm_nonneg _) (fun om => (hpoint om).1)
  · exact hbound _ (fun _ => matrixNorm_nonneg _) (fun om => (hpoint om).2)
end


section
open MeasureTheory TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal BigOperators

/-- The frozen chart is the literal physical cutoff field almost everywhere on
every contained descendant. -/
theorem aux_lem_extension_cell_moment_chart_scalar_identity {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hsub : (centeredCube w r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)))
    (Q : TriadicCube d) (hQ : openCubeSet Q ⊆ openCubeSet (originCube d 0)) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      ((E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r).coeffOn Q).toCoeffField x =
        scalarMatrix (cutoffCoefficient M H om N (fun i => w i + r * x i)) := by
  haveI : Fact ((centeredCube z0 R hR : Set (SpatialCoordinates d)) ⊆
      (closedCube z0 R hR : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube z0 hR⟩
  let f : SpatialCoordinates d → SpatialCoordinates d := fun x => fun i => w i + r * x i
  have hqmp : Measure.QuasiMeasurePreserving f volume volume := by
    have hscale : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => r • y)
        volume volume := Measure.quasiMeasurePreserving_smul volume hr.ne'
    have htrans : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => y + w)
        volume volume := (measurePreserving_add_right volume w).quasiMeasurePreserving
    have heq : f = (fun y : SpatialCoordinates d => y + w) ∘
        (fun y : SpatialCoordinates d => r • y) := by
      funext x i
      simp [f, add_comm]
    rw [heq]
    exact htrans.comp hscale
  have hc := E.chart_eq z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r hr hsub Q hQ
  have hrep := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z0 R hR) (closedCube z0 R hR)
    (cutoffCoefficientCM M H om N z0 hR) (cutoffCoefficientCM_pos M H om N z0 hR) 1 one_pos
  rw [ae_restrict_iff' (centeredCube z0 R hR).isOpen.measurableSet] at hrep
  have hpull := ae_restrict_of_ae (s := openCubeSet Q) (hqmp.ae hrep)
  have hmaps : ∀ x ∈ openCubeSet Q, f x ∈ (centeredCube z0 R hR : Set (SpatialCoordinates d)) :=
    fun x hx => hsub (aux_lem_extension_cell_moment_cellAffine_mem w r hr (hQ hx))
  filter_upwards [hc, hpull, ae_restrict_mem (measurableSet_openCubeSet Q)] with x hcx hvx hxQ
  rw [hcx]
  have hval := hvx (hmaps x hxQ) (hmaps x hxQ)
  congr 1
  rw [div_one] at hval
  exact hval

/-- The exact above-wavelength residual, including its unused published-response
input binder and the exact chart observables. -/
theorem aux_lem_extension_cell_moment_above_chart {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (p ε : ℝ) (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ δ0 →
      ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      ∃ C0 : ℝ, 0 < C0 ∧
        ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
          (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
        ∀ n : ℕ, k + n ≤ N →
        ∀ Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)),
          eLpNorm (fun om => coarseBMatrixNorm Q
            (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
              ((3 : ℝ) ^ (-(k : ℤ)))))
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) ∧
          eLpNorm (fun om => coarseSigmaStarInvMatrixNorm Q
            (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
              ((3 : ℝ) ^ (-(k : ℤ)))))
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) := by
  obtain ⟨δ0, C1, hδ0, hC1, hcore⟩ := aux_lem_extension_cell_moment_above_core hd E p ε hp hε
  refine ⟨δ0, C1, hδ0, hC1, ?_⟩
  intro M _Rm H hH hδ z0 R hR
  obtain ⟨C0, hC0, hbound⟩ := hcore M H hH hδ z0 R hR
  refine ⟨C0, hC0, ?_⟩
  intro w N k hk hcell n habove Q hQ
  apply hbound w N k hk hcell n habove Q hQ
    (fun om => (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
      ((3 : ℝ) ^ (-(k : ℤ)))).coeffOn Q)
  intro om
  exact aux_lem_extension_cell_moment_chart_scalar_identity E M H om N z0 R hR w _
    (by positivity) hcell Q (openCubeSet_subset_of_mem_descendantsAtScale (by simp) hQ)

/-- The exact below-wavelength residual, with the same unused response-input binder. -/
theorem aux_lem_extension_cell_moment_below_chart {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ δ0 →
      ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      ∃ C0 : ℝ, 0 < C0 ∧
        ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
          (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
        ∀ n : ℕ, N < k + n →
        ∀ Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)),
        ∃ lo hi : BilateralField d → ℝ,
          (∀ om, 0 < lo om ∧ lo om ≤ hi om ∧
            ∀ x ∈ openCubeSet Q,
              lo om ≤ cutoffCoefficient M H om N
                  (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∧
                cutoffCoefficient M H om N
                  (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ≤ hi om) ∧
          eLpNorm (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 +
              4 * (d : ℝ) * (lo om)⁻¹)
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) := by
  obtain ⟨δ0, C1, hδ0, hC1, h⟩ := aux_lem_extension_cell_moment_below_extremes hd p ε hp hε
  refine ⟨δ0, C1, hδ0, hC1, ?_⟩
  intro M _Rm
  exact h M
end

/-! ### Summation: from per-scale chart moments to the cell moment

Paper lines 494--498 ("repeating the summation of the previous proof on each grid cube").
The `q = 2` discounted series of `in_J` are summed in `L^p` by Minkowski's inequality; a
per-scale moment growing at most like `exp (C₁ δ² k + ε n)` with `ε = s log 3` is beaten by
the discount `3^{-2sn}`.  The helpers below are sorry-free and generic in the cell. -/

/-- Minkowski's inequality for a pointwise-summable series in `L^p`, with measurability of
the sum. -/
theorem aux_lem_extension_cell_moment_eLpNorm_tsum_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℕ → α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hsum : ∀ᵐ x ∂μ, Summable (fun n => f n x))
    {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n) (hbs : Summable b)
    (hb : ∀ n, eLpNorm (f n) p μ ≤ ENNReal.ofReal (b n)) :
    AEStronglyMeasurable (fun x => ∑' n, f n x) μ ∧
      eLpNorm (fun x => ∑' n, f n x) p μ ≤ ENNReal.ofReal (∑' n, b n) := by
  have hmeasN : ∀ N : ℕ, AEStronglyMeasurable (fun x => ∑ n ∈ Finset.range N, f n x) μ :=
    fun N => (Finset.range N).aestronglyMeasurable_fun_sum fun n _ => hf n
  have hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, f n x)
      Filter.atTop (nhds (∑' n, f n x)) := by
    filter_upwards [hsum] with x hx
    exact hx.hasSum.tendsto_sum_nat
  refine ⟨aestronglyMeasurable_of_tendsto_ae _ hmeasN hlim, ?_⟩
  refine Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop)
    (f := fun N x => ∑ n ∈ Finset.range N, f n x) ?_ hmeasN hlim
  refine Filter.Eventually.of_forall fun N => ?_
  have hfun : (fun x => ∑ n ∈ Finset.range N, f n x) = ∑ n ∈ Finset.range N, f n := by
    funext x
    simp [Finset.sum_apply]
  have h1 : eLpNorm (fun x => ∑ n ∈ Finset.range N, f n x) p μ ≤
      ∑ n ∈ Finset.range N, eLpNorm (f n) p μ := by
    rw [hfun]
    exact eLpNorm_sum_le (fun i _ => hf i) hp
  refine h1.trans ?_
  calc ∑ n ∈ Finset.range N, eLpNorm (f n) p μ
      ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (b n) := Finset.sum_le_sum fun n _ => hb n
    _ = ENNReal.ofReal (∑ n ∈ Finset.range N, b n) :=
        (ENNReal.ofReal_sum_of_nonneg fun n _ => hb0 n).symm
    _ ≤ ENNReal.ofReal (∑' n, b n) :=
        ENNReal.ofReal_le_ofReal (hbs.sum_le_tsum _ fun n _ => hb0 n)

/-- The discounted weight `c_{s,2} 3^{-2sn}` is at most `exp (-(2 s log 3) n)`. -/
theorem aux_lem_extension_cell_moment_weight_le_exp (s : ℝ) (n : ℕ) :
    Homogenization.Book.Ch02.geometricWeight s 2 n ≤
      Real.exp (-(2 * s * Real.log 3) * n) := by
  unfold Homogenization.Book.Ch02.geometricWeight Homogenization.Book.Ch02.geometricDiscount
  have h1 : 0 ≤ Real.rpow (3 : ℝ) (-s * 2) := Real.rpow_nonneg (by norm_num) _
  have h2 : Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ)) = Real.exp (-(2 * s * Real.log 3) * n) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have h3 : 0 ≤ Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc (1 - Real.rpow (3 : ℝ) (-s * 2)) * Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ))
      ≤ 1 * Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) h3
    _ = Real.exp (-(2 * s * Real.log 3) * n) := by rw [one_mul, h2]

/-- One term of the discounted series: a per-scale moment `C₀ exp (A + s log 3 · n)` times the
weight is at most `C₀ e^A r^n` with `r = exp (-(s log 3)) < 1`. -/
theorem aux_lem_extension_cell_moment_weighted_term_le {s : ℝ} {C0 A : ℝ}
    (hC0 : 0 ≤ C0) (n : ℕ) :
    Homogenization.Book.Ch02.geometricWeight s 2 n *
        (C0 * Real.exp (A + s * Real.log 3 * n)) ≤
      C0 * Real.exp A * Real.exp (-(s * Real.log 3)) ^ n := by
  have hw := aux_lem_extension_cell_moment_weight_le_exp s n
  have hpos : 0 ≤ C0 * Real.exp (A + s * Real.log 3 * n) := by positivity
  calc Homogenization.Book.Ch02.geometricWeight s 2 n *
        (C0 * Real.exp (A + s * Real.log 3 * n))
      ≤ Real.exp (-(2 * s * Real.log 3) * n) * (C0 * Real.exp (A + s * Real.log 3 * n)) :=
        mul_le_mul_of_nonneg_right hw hpos
    _ = C0 * Real.exp A * Real.exp (-(s * Real.log 3)) ^ n := by
        rw [← Real.exp_nat_mul]
        have : Real.exp (-(2 * s * Real.log 3) * n) * (C0 * Real.exp (A + s * Real.log 3 * n)) =
            C0 * (Real.exp (-(2 * s * Real.log 3) * n) * Real.exp (A + s * Real.log 3 * n)) := by
          ring
        rw [this, ← Real.exp_add, mul_assoc C0, ← Real.exp_add]
        congr 2
        ring

/-- The per-scale `|b|` maximum of the actual chart is a.e.-strongly measurable. -/
theorem aux_lem_extension_cell_moment_aesm_maxB_chart {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d))) (n : ℕ) :
    AEStronglyMeasurable (fun om =>
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ))
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r'))
      (chaosSampleLaw M).toMeasure := by
  haveI : NeZero d := ⟨by omega⟩
  have hFm := aux_lem_extension_cell_moment_measurable_regField M H hH N w r'
  have hP := aux_lem_extension_cell_moment_lawCarrier M H hH N w r'
  have h := (aux_lem_extension_cell_moment_aemeasurable_maxB hP
    (Homogenization.originCube d 0) n).comp_aemeasurable hFm.aemeasurable
  refine h.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun om => ?_)
  simp only [Function.comp_apply]
  rw [aux_lem_extension_cell_moment_maxB_chart_eq E M H om N z0 R hR w r' hr' hsub n]

/-- The per-scale `|σ_*⁻¹|` maximum of the actual chart is a.e.-strongly measurable. -/
theorem aux_lem_extension_cell_moment_aesm_maxS_chart {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d))) (n : ℕ) :
    AEStronglyMeasurable (fun om =>
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ))
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r'))
      (chaosSampleLaw M).toMeasure := by
  haveI : NeZero d := ⟨by omega⟩
  have hFm := aux_lem_extension_cell_moment_measurable_regField M H hH N w r'
  have hP := aux_lem_extension_cell_moment_lawCarrier M H hH N w r'
  have h := (aux_lem_extension_cell_moment_aemeasurable_maxS hP
    (Homogenization.originCube d 0) n).comp_aemeasurable hFm.aemeasurable
  refine h.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun om => ?_)
  simp only [Function.comp_apply]
  rw [aux_lem_extension_cell_moment_maxS_chart_eq E M H om N z0 R hR w r' hr' hsub n]


/-- **Per-cell summation core.**  If the per-scale `|b|` and `|σ_*⁻¹|` maxima of the actual
chart have `L^p` moments `≤ C₀ exp (A + s log 3 · n)`, then the target observable
`Λ_{s,2} + λ_{s,2}⁻¹` of the cell has `L^p` moment `≤ 2 C₀ e^A / (1 - 3^{-s})`. -/
theorem aux_lem_extension_cell_moment_cell_bound_of_scale {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)))
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) {p : ℝ} (hp : 1 ≤ p) {C0 A : ℝ} (hC0 : 0 ≤ C0)
    (hB : ∀ n : ℕ, eLpNorm (fun om =>
        Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ))
          (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r'))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (C0 * Real.exp (A + s * Real.log 3 * n)))
    (hS : ∀ n : ℕ, eLpNorm (fun om =>
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ))
          (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r'))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (C0 * Real.exp (A + s * Real.log 3 * n))) :
    eLpNorm (fun om =>
        E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r' s 2 +
          (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r' s 2)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (C0 * Real.exp A * (1 - Real.exp (-(s * Real.log 3)))⁻¹)) := by
  set r : ℝ := Real.exp (-(s * Real.log 3)) with hr_def
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr
    (neg_neg_of_pos (mul_pos hs.1 (Real.log_pos (by norm_num))))
  set b : ℕ → ℝ := fun n => C0 * Real.exp A * r ^ n with hb_def
  have hb0 : ∀ n, 0 ≤ b n := fun n => by positivity
  have hbs : Summable b := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hbsum : ∑' n, b n = C0 * Real.exp A * (1 - r)⁻¹ := by
    simp only [hb_def]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hw0 : ∀ n : ℕ, 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 n :=
    aux_lem_extension_cell_moment_weight_nonneg hs.1.le
  -- one weighted term
  have hterm : ∀ (X : BilateralField d → ℝ) (n : ℕ),
      eLpNorm X (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C0 * Real.exp (A + s * Real.log 3 * n)) →
      eLpNorm (fun om => Homogenization.Book.Ch02.geometricWeight s 2 n * X om)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (b n) := by
    intro X n hX
    have h1 : eLpNorm (Homogenization.Book.Ch02.geometricWeight s 2 n • X)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ‖Homogenization.Book.Ch02.geometricWeight s 2 n‖ₑ *
          eLpNorm X (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure :=
      eLpNorm_const_smul_le
    refine (h1.trans ?_)
    rw [Real.enorm_eq_ofReal (hw0 n)]
    calc ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 n) *
          eLpNorm X (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 n) *
          ENNReal.ofReal (C0 * Real.exp (A + s * Real.log 3 * n)) := by gcongr
      _ = ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 n *
          (C0 * Real.exp (A + s * Real.log 3 * n))) := (ENNReal.ofReal_mul (hw0 n)).symm
      _ ≤ ENNReal.ofReal (b n) := ENNReal.ofReal_le_ofReal
          (aux_lem_extension_cell_moment_weighted_term_le hC0 n)
  -- the `Λ` series
  have hLam := aux_lem_extension_cell_moment_eLpNorm_tsum_le (μ := (chaosSampleLaw M).toMeasure)
    hp1 (f := fun n om => Homogenization.Book.Ch02.geometricWeight s 2 n *
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ))
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r'))
    (fun n => (aux_lem_extension_cell_moment_aesm_maxB_chart hd E M H hH N z0 R hR w r' hr'
      hsub n).const_mul _)
    (Filter.Eventually.of_forall fun om => by
      by_contra hns
      have h0 := tsum_eq_zero_of_not_summable hns
      rw [← aux_lem_extension_cell_moment_Lam_eq_tsum E z0 R hR _ w r' hr' hsub s hs] at h0
      exact (E.Lam_pos _ _ _ _ _ _ _ _).ne' h0)
    hb0 hbs (fun n => hterm _ n (hB n))
  have hlam := aux_lem_extension_cell_moment_eLpNorm_tsum_le (μ := (chaosSampleLaw M).toMeasure)
    hp1 (f := fun n om => Homogenization.Book.Ch02.geometricWeight s 2 n *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ))
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r'))
    (fun n => (aux_lem_extension_cell_moment_aesm_maxS_chart hd E M H hH N z0 R hR w r' hr'
      hsub n).const_mul _)
    (Filter.Eventually.of_forall fun om => by
      by_contra hns
      have h0 := tsum_eq_zero_of_not_summable hns
      rw [← aux_lem_extension_cell_moment_lam_inv_eq_tsum E z0 R hR _ w r' hr' hsub s hs] at h0
      exact (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)).ne' h0)
    hb0 hbs (fun n => hterm _ n (hS n))
  have hfunL : (fun om => E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r' s 2) =
      fun om => ∑' n, Homogenization.Book.Ch02.geometricWeight s 2 n *
        Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ))
          (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r') :=
    funext fun om => aux_lem_extension_cell_moment_Lam_eq_tsum E z0 R hR _ w r' hr' hsub s hs
  have hfunl : (fun om =>
      (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r' s 2)⁻¹) =
      fun om => ∑' n, Homogenization.Book.Ch02.geometricWeight s 2 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ))
          (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r') :=
    funext fun om => aux_lem_extension_cell_moment_lam_inv_eq_tsum E z0 R hR _ w r' hr' hsub s hs
  rw [← hfunL] at hLam
  rw [← hfunl] at hlam
  have hadd := eLpNorm_add_le hLam.1 hlam.1 hp1
  refine hadd.trans ?_
  rw [hbsum] at hLam hlam
  calc _ ≤ ENNReal.ofReal (C0 * Real.exp A * (1 - r)⁻¹) +
        ENNReal.ofReal (C0 * Real.exp A * (1 - r)⁻¹) := add_le_add hLam.2 hlam.2
    _ = ENNReal.ofReal (2 * (C0 * Real.exp A * (1 - r)⁻¹)) := by
        have hnn : 0 ≤ C0 * Real.exp A * (1 - r)⁻¹ := by
          have : 0 < 1 - r := by linarith
          positivity
        rw [← ENNReal.ofReal_add hnn hnn, two_mul]



def aux_lem_extension_cell_moment_ScaleBridge (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (p ε : ℝ) : Prop :=
  ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ δ0 →
    ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
      ∀ n : ℕ,
        eLpNorm (fun om =>
            Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
              (Homogenization.originCube d 0)
              ((Homogenization.originCube d 0).scale - (n : ℤ))
              (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
                ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) ∧
        eLpNorm (fun om =>
            Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              (Homogenization.originCube d 0)
              ((Homogenization.originCube d 0).scale - (n : ℤ))
              (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
                ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n))



theorem aux_lem_extension_cell_moment_of_scaleBridge {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) {beta q : ℝ} (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) (hq : 1 ≤ q)
    (hbr : aux_lem_extension_cell_moment_ScaleBridge d E q
      ((beta - 1 / 2) / 4 * Real.log 3)) :
    ∃ deltaq Cd : ℝ, 0 < deltaq ∧ 0 < Cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ deltaq →
      ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      ∃ Cq : ℝ, 0 < Cq ∧
        ∀ (J : ℕ) (origins : Fin J → SpatialCoordinates d),
        ∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ), k ≤ N →
          (centeredCube
              (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
              ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
          eLpNorm
              (fun om =>
                E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                    (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                    ((3 : ℝ) ^ (-(k : ℤ)))
                    ((beta - 1 / 2) / 4) 2 +
                  (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                    (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                    ((3 : ℝ) ^ (-(k : ℤ)))
                    ((beta - 1 / 2) / 4) 2)⁻¹)
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal
              (Cq * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
  obtain ⟨δ0, C1, hδ0, hC1, hb⟩ := hbr
  have hqq : 0 < q + q ^ 2 := by positivity
  refine ⟨δ0, C1 / (q + q ^ 2), hδ0, div_pos hC1 hqq, ?_⟩
  intro M _Rm H hH hδ z0 R hR
  obtain ⟨C0, hC0, hc⟩ := hb M _Rm H hH hδ z0 R hR
  have hs := aux_lem_extension_cell_moment_order hbeta
  set s : ℝ := (beta - 1 / 2) / 4 with hs_def
  set r : ℝ := Real.exp (-(s * Real.log 3)) with hr_def
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr
    (neg_neg_of_pos (mul_pos hs.1 (Real.log_pos (by norm_num))))
  have h1r : 0 < 1 - r := by linarith
  refine ⟨2 * (C0 * (1 - r)⁻¹), by positivity, ?_⟩
  intro J origins N k index nidx hk hcell
  have hsub : (centeredCube (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
      ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)) := hcell
  have hmain := aux_lem_extension_cell_moment_cell_bound_of_scale hd E M H hH.measurable N z0 R hR
    (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ)))
    (by positivity) hsub hs (p := q) hq (C0 := C0) (A := C1 * M.delta ^ 2 * k) hC0.le
    (fun n => by
      have := (hc (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) N k hk hcell n).1
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this)
    (fun n => by
      have := (hc (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) N k hk hcell n).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this)
  refine hmain.trans (le_of_eq ?_)
  congr 1
  have hCd : C1 / (q + q ^ 2) * (q + q ^ 2) * M.delta ^ 2 * (k : ℝ) =
      C1 * M.delta ^ 2 * k := by
    field_simp
  rw [hCd]
  ring


/-! ### Finite-grid maximum: from per-descendant moments to per-scale moments

Paper line 438 ("at most `3^{d|k|}` cells at depth `k`, so `‖max_z ·‖_{L^q} ≤ 3^{d|k|/q}·…`"). -/

/-- `L^p` norm of a finite maximum of real observables: at most `card^{1/p}` times the
largest individual bound. -/
theorem aux_lem_extension_cell_moment_eLpNorm_finsetSup_le {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (S : Finset ι) (f : ι → α → ℝ)
    (hf : ∀ i ∈ S, AEStronglyMeasurable (f i) μ)
    {p : ℝ} (hp : 0 < p) {B : ℝ}
    (hB : ∀ i ∈ S, eLpNorm (f i) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => Homogenization.Book.Ch02.finsetSupReal S (fun i => f i x))
        (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ((S.card : ℝ) ^ (1 / p) * B) := by
  classical
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero, not_le] using hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop, hpr]
  have hpt : ∀ x, ‖Homogenization.Book.Ch02.finsetSupReal S (fun i => f i x)‖ₑ ^ p ≤
      ∑ i ∈ S, ‖f i x‖ₑ ^ p := by
    intro x
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      simp [Homogenization.Book.Ch02.finsetSupReal, ENNReal.zero_rpow_of_pos hp]
    · obtain ⟨j, hj, hjmax⟩ := S.exists_max_image (fun i => f i x) hS
      have hsup : Homogenization.Book.Ch02.finsetSupReal S (fun i => f i x) = f j x := by
        refine le_antisymm ?_ (aux_lem_extension_cell_moment_le_finsetSupReal S (fun i => f i x) hj)
        exact Homogenization.Book.Ch02.finsetSupReal_le S hS (fun i hi => hjmax i hi)
      rw [hsup]
      exact Finset.single_le_sum (f := fun i => ‖f i x‖ₑ ^ p) (fun i _ => zero_le _) hj
  have hint : ∫⁻ x, ‖Homogenization.Book.Ch02.finsetSupReal S (fun i => f i x)‖ₑ ^ p ∂μ ≤
      ∑ i ∈ S, ∫⁻ x, ‖f i x‖ₑ ^ p ∂μ := by
    calc _ ≤ ∫⁻ x, ∑ i ∈ S, ‖f i x‖ₑ ^ p ∂μ := lintegral_mono hpt
      _ = ∑ i ∈ S, ∫⁻ x, ‖f i x‖ₑ ^ p ∂μ :=
          lintegral_finset_sum' S (fun i hi => (hf i hi).enorm.pow_const p)
  have hi : ∀ i ∈ S, ∫⁻ x, ‖f i x‖ₑ ^ p ∂μ ≤ ENNReal.ofReal B ^ p := by
    intro i hi
    have h1 := hB i hi
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop, hpr] at h1
    have h2 := ENNReal.rpow_le_rpow h1 hp.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one] at h2
  have hp' : 0 ≤ 1 / p := by positivity
  calc (∫⁻ x, ‖Homogenization.Book.Ch02.finsetSupReal S (fun i => f i x)‖ₑ ^ p ∂μ) ^ (1 / p)
      ≤ (∑ i ∈ S, ENNReal.ofReal B ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (hint.trans (Finset.sum_le_sum hi)) hp'
    _ = ((S.card : ℝ≥0∞) * ENNReal.ofReal B ^ p) ^ (1 / p) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((S.card : ℝ) ^ (1 / p) * B) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp', ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
          ENNReal.rpow_one, ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp', ENNReal.ofReal_natCast]

/-- The unit root has `(3^d)^n` descendants at depth `n`. -/
theorem aux_lem_extension_cell_moment_card_desc (d n : ℕ) :
    (Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ))).card = (3 ^ d) ^ n := by
  rw [Homogenization.descendantsAtScale_eq_descendantsAtDepth _
    (sub_le_self _ (by exact_mod_cast Nat.zero_le n)),
    Homogenization.descendantsAtDepth_card]
  congr 1
  simp

/-- `card^{1/p'} ≤ exp (ε/2 · n)` for the depth-`n` descendants once `p' ≥ 2 d log 3 / ε`. -/
theorem aux_lem_extension_cell_moment_card_rpow_le (d n : ℕ) {p ε : ℝ} (hε : 0 < ε)
    (hp : 2 * d * Real.log 3 / ε ≤ p) (hp0 : 0 < p) :
    (((3 ^ d) ^ n : ℕ) : ℝ) ^ (1 / p) ≤ Real.exp (ε / 2 * n) := by
  have hpos : (0 : ℝ) < (((3 ^ d) ^ n : ℕ) : ℝ) := by positivity
  rw [Real.rpow_def_of_pos hpos]
  refine Real.exp_le_exp.mpr ?_
  have hlog : Real.log (((3 ^ d) ^ n : ℕ) : ℝ) = n * (d * Real.log 3) := by
    push_cast
    rw [Real.log_pow, Real.log_pow]
  rw [hlog]
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hkey : (d : ℝ) * Real.log 3 * (1 / p) ≤ ε / 2 := by
    rw [mul_one_div, div_le_iff₀ hp0]
    rw [div_le_iff₀ hε] at hp
    linarith
  have hn : (0 : ℝ) ≤ n := by positivity
  calc (n : ℝ) * (d * Real.log 3) * (1 / p) = n * ((d : ℝ) * Real.log 3 * (1 / p)) := by ring
    _ ≤ n * (ε / 2) := mul_le_mul_of_nonneg_left hkey hn
    _ = ε / 2 * n := by ring

section DescendantObservables

open scoped Matrix.Norms.L2Operator

/-- The single-descendant `|b|` of the actual chart as a function of the sample is
a.e.-strongly measurable. -/
theorem aux_lem_extension_cell_moment_aesm_coarseB_chart {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)))
    (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    AEStronglyMeasurable (fun om =>
      Homogenization.Book.Ch02.coarseBMatrixNorm Q
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r'))
      (chaosSampleLaw M).toMeasure := by
  haveI : NeZero d := ⟨by omega⟩
  have hFm := aux_lem_extension_cell_moment_measurable_regField M H hH N w r'
  have hP := aux_lem_extension_cell_moment_lawCarrier M H hH N w r'
  have h0 : AEMeasurable (fun a : Homogenization.RegCoeffField d =>
      Homogenization.Book.Ch02.matrixNorm
        (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a.toFun).upperLeft)
      (Measure.map (aux_lem_extension_cell_moment_regField M H N w r')
        (chaosSampleLaw M).toMeasure) := by
    simpa [Homogenization.Book.Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using
      (hP.aemeasurable_coarseB_cubeSet Q).norm
  have h := h0.comp_aemeasurable hFm.aemeasurable
  refine h.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun om => ?_)
  simp only [Function.comp_apply]
  have hell := aux_lem_extension_cell_moment_regField_elliptic M H N w r' om
  have hmat := Homogenization.Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    hell Q
  have hupper := congrArg (fun A => Homogenization.Book.Ch02.matrixNorm A.upperLeft) hmat
  unfold Homogenization.Book.Ch02.coarseBMatrixNorm
  rw [Homogenization.Book.Ch02.bCoarse_eq_ofAEEq
    (aux_lem_extension_cell_moment_chart_aeeq E M H om N z0 R hR w r' hr' hsub Q hQ hell)]
  simpa [Homogenization.Book.Ch02.coarseBMatrixNorm] using hupper

/-- The single-descendant `|σ_*⁻¹|` of the actual chart is a.e.-strongly measurable. -/
theorem aux_lem_extension_cell_moment_aesm_coarseS_chart {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)))
    (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    AEStronglyMeasurable (fun om =>
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r'))
      (chaosSampleLaw M).toMeasure := by
  haveI : NeZero d := ⟨by omega⟩
  have hFm := aux_lem_extension_cell_moment_measurable_regField M H hH N w r'
  have hP := aux_lem_extension_cell_moment_lawCarrier M H hH N w r'
  have h0 : AEMeasurable (fun a : Homogenization.RegCoeffField d =>
      Homogenization.Book.Ch02.matrixNorm
        (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
          a.toFun).lowerRight)
      (Measure.map (aux_lem_extension_cell_moment_regField M H N w r')
        (chaosSampleLaw M).toMeasure) := by
    simpa [Homogenization.Book.Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using
      (hP.aemeasurable_coarseSigmaStarInv_cubeSet Q).norm
  have h := h0.comp_aemeasurable hFm.aemeasurable
  refine h.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun om => ?_)
  simp only [Function.comp_apply]
  have hell := aux_lem_extension_cell_moment_regField_elliptic M H N w r' om
  have hmat := Homogenization.Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    hell Q
  have hlower := congrArg (fun A => Homogenization.Book.Ch02.matrixNorm A.lowerRight) hmat
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
  rw [Homogenization.Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq
    (aux_lem_extension_cell_moment_chart_aeeq E M H om N z0 R hR w r' hr' hsub Q hQ hell)]
  simpa [Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm] using hlower

end DescendantObservables




def aux_lem_extension_cell_moment_DescBridge (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (p ε : ℝ) : Prop :=
  ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ δ0 →
    ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
      ∀ n : ℕ, ∀ Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)),
        eLpNorm (fun om =>
            Homogenization.Book.Ch02.coarseBMatrixNorm Q
              (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
                ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) ∧
        eLpNorm (fun om =>
            Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
              (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
                ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n))



theorem aux_lem_extension_cell_moment_scaleBridge_of_descBridge {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε)
    (h : aux_lem_extension_cell_moment_DescBridge d E (max p (2 * d * Real.log 3 / ε))
      (ε / 2)) :
    aux_lem_extension_cell_moment_ScaleBridge d E p ε := by
  obtain ⟨δ0, C1, hδ0, hC1, hb⟩ := h
  refine ⟨δ0, C1, hδ0, hC1, ?_⟩
  intro M _Rm H hH hδ z0 R hR
  obtain ⟨C0, hC0, hc⟩ := hb M _Rm H hH hδ z0 R hR
  refine ⟨C0, hC0, ?_⟩
  intro w N k hk hcell n
  set p' : ℝ := max p (2 * d * Real.log 3 / ε) with hp'_def
  have hp'pos : 0 < p' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hpp' : ENNReal.ofReal p ≤ ENNReal.ofReal p' :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hsub : (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
      Set (SpatialCoordinates d)) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)) := hcell
  have hk' : (Homogenization.originCube d 0).scale - (n : ℤ) ≤
      (Homogenization.originCube d 0).scale := sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hcard := aux_lem_extension_cell_moment_card_rpow_le d n hε (le_max_right _ _) hp'pos
  set A : ℝ := C1 * M.delta ^ 2 * k with hA
  have key : ∀ X : Homogenization.TriadicCube d → BilateralField d → ℝ,
      (∀ Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)),
        AEStronglyMeasurable (X Q) (chaosSampleLaw M).toMeasure) →
      (∀ Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)),
        eLpNorm (X Q) (ENNReal.ofReal p') (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0 * Real.exp (A + ε / 2 * n))) →
      AEStronglyMeasurable (fun om => Homogenization.Book.Ch02.finsetSupReal
          (Homogenization.descendantsAtScale (Homogenization.originCube d 0)
            ((Homogenization.originCube d 0).scale - (n : ℤ))) (fun Q => X Q om))
        (chaosSampleLaw M).toMeasure →
      eLpNorm (fun om => Homogenization.Book.Ch02.finsetSupReal
          (Homogenization.descendantsAtScale (Homogenization.originCube d 0)
            ((Homogenization.originCube d 0).scale - (n : ℤ))) (fun Q => X Q om))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C0 * Real.exp (A + ε * n)) := by
    intro X hX hXb hmax
    refine (eLpNorm_le_eLpNorm_of_exponent_le hpp' hmax).trans ?_
    refine (aux_lem_extension_cell_moment_eLpNorm_finsetSup_le _ X hX hp'pos hXb).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [aux_lem_extension_cell_moment_card_desc]
    calc ((((3 ^ d) ^ n : ℕ) : ℝ)) ^ (1 / p') * (C0 * Real.exp (A + ε / 2 * n))
        ≤ Real.exp (ε / 2 * n) * (C0 * Real.exp (A + ε / 2 * n)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = C0 * Real.exp (A + ε * n) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hdesc : ∀ Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ)),
      Homogenization.openCubeSet Q ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) :=
    fun Q hQ => Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
  constructor
  · exact key (fun Q om => Homogenization.Book.Ch02.coarseBMatrixNorm Q
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
      (fun Q hQ => aux_lem_extension_cell_moment_aesm_coarseB_chart hd E M H hH.measurable N z0 R hR w
        _ (by positivity) hsub Q (hdesc Q hQ))
      (fun Q hQ => (hc w N k hk hcell n Q hQ).1)
      (aux_lem_extension_cell_moment_aesm_maxB_chart hd E M H hH.measurable N z0 R hR w _
        (by positivity) hsub n)
  · exact key (fun Q om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
      (fun Q hQ => aux_lem_extension_cell_moment_aesm_coarseS_chart hd E M H hH.measurable N z0 R hR w
        _ (by positivity) hsub Q (hdesc Q hQ))
      (fun Q hQ => (hc w N k hk hcell n Q hQ).2)
      (aux_lem_extension_cell_moment_aesm_maxS_chart hd E M H hH.measurable N z0 R hR w _
        (by positivity) hsub n)


/-! ### Deterministic single-cube envelope (below-wavelength step, paper lines 440--443)

On a descendant `Q` where the chart field lies in `[λ, Λ]`, the canonical coarse matrices obey
`|b(Q)| ≤ 4dΛ²/λ` and `|σ_*⁻¹(Q)| ≤ 4d/λ`.  The field is clamped to `[λ, Λ]` globally (which
does not change it on `Q`), so that the Chapter 5 uniform-ellipticity family applies. -/

section Envelope

open Homogenization Homogenization.Book

/-- The continuous field clamped to `[λ, Λ]`. -/
def aux_lem_extension_cell_moment_clampCM {d : ℕ} (f : C(SpatialCoordinates d, ℝ))
    (lam Lam : ℝ) : C(SpatialCoordinates d, ℝ) :=
  ⟨fun x => max lam (min Lam (f x)), continuous_const.max (continuous_const.min f.continuous)⟩

theorem aux_lem_extension_cell_moment_clampCM_apply {d : ℕ} (f : C(SpatialCoordinates d, ℝ))
    (lam Lam : ℝ) (x : SpatialCoordinates d) :
    aux_lem_extension_cell_moment_clampCM f lam Lam x = max lam (min Lam (f x)) := rfl

/-- The clamped scalar field is uniformly elliptic on every triadic cube. -/
theorem aux_lem_extension_cell_moment_clamp_aeElliptic {d : ℕ} (f : C(SpatialCoordinates d, ℝ))
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam) (T : TriadicCube d) :
    Ch04.AEEllipticOn lam Lam (openCubeSet T)
      (aux_lem_extension_cell_moment_scalarReg (aux_lem_extension_cell_moment_clampCM f lam Lam)) := by
  classical
  let g := aux_lem_extension_cell_moment_clampCM f lam Lam
  let W : Set (SpatialCoordinates d) := openCubeSet T
  have hmeas : Measurable (fun x : SpatialCoordinates d => if x ∈ W then g x else 0) := by
    simpa [Set.piecewise] using
      Measurable.piecewise (isOpenBoundedConvexDomain_openCubeSet T).isOpen.measurableSet
        g.continuous.measurable measurable_const
  have hEll : IsEllipticFieldOn lam Lam W (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField g) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds
      hlam hmeas (fun x _ => le_max_left _ _) (fun x _ => max_le hle (min_le_left _ _))
  change IsAEEllipticFieldOn lam Lam W
    (aux_lem_extension_cell_moment_scalarReg g).toFun
  apply IsAEEllipticFieldOn.of_isEllipticFieldOn
  simpa [W, aux_lem_extension_cell_moment_scalarReg,
    SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField] using hEll

/-- **Single-cube envelope.**  If a triadic family agrees a.e. on `Q` with the scalar field
`f`, and `λ ≤ f ≤ Λ` on `Q`, then `|b(Q)| ≤ 4dΛ²/λ` and `|σ_*⁻¹(Q)| ≤ 4d/λ`. -/
theorem aux_lem_extension_cell_moment_coarse_envelope {d : ℕ} [NeZero d]
    (F : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (f : C(SpatialCoordinates d, ℝ))
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hbd : ∀ x ∈ openCubeSet Q, lam ≤ f x ∧ f x ≤ Lam)
    (hae : (F.coeffOn Q).toCoeffField =ᵐ[volume.restrict (openCubeSet Q)]
      (aux_lem_extension_cell_moment_scalarReg f).toFun) :
    Ch02.coarseBMatrixNorm Q F ≤ 4 * (d : ℝ) * lam⁻¹ * Lam ^ 2 ∧
      Ch02.coarseSigmaStarInvMatrixNorm Q F ≤ 4 * (d : ℝ) * lam⁻¹ := by
  classical
  let g := aux_lem_extension_cell_moment_clampCM f lam Lam
  have hall : ∀ T : TriadicCube d, Ch04.AEEllipticOn lam Lam (openCubeSet T)
      (aux_lem_extension_cell_moment_scalarReg g) :=
    aux_lem_extension_cell_moment_clamp_aeElliptic f hlam hle
  let F' : Ch02.TriadicCoeffFamily d :=
    Ch05.Section57.triadicCoeffFamilyOfUniformEllipticity
      (aux_lem_extension_cell_moment_scalarReg g) hlam hle hall
  have hAE : Ch02.CoeffOn.AEEq (F.coeffOn Q) (F'.coeffOn Q) := by
    unfold Ch02.CoeffOn.AEEq
    change (F.coeffOn Q).toCoeffField =ᵐ[volume.restrict (openCubeSet Q)]
      (aux_lem_extension_cell_moment_scalarReg g).toFun
    filter_upwards [hae, ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx hxQ
    rw [hx]
    change scalarMatrix (f x) = scalarMatrix (g x)
    rw [aux_lem_extension_cell_moment_clampCM_apply, min_eq_right (hbd x hxQ).2,
      max_eq_right (hbd x hxQ).1]
  have hk : Q.scale - ((0 : ℕ) : ℤ) ≤ Q.scale := by simp
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (F'.coeffOn Q)
  have hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) A := by
    simpa [A, F', Ch05.Section57.triadicCoeffFamilyOfUniformEllipticity,
      Ch05.Section57.coeffOnOfUniformAEEllipticOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (F'.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using Ch02.pointwiseCoeffField_openCube_descendant_data Q (F'.coeffOn Q)
  constructor
  · have heq : Ch02.coarseBMatrixNorm Q F = Ch02.coarseBMatrixNorm Q F' := by
      unfold Ch02.coarseBMatrixNorm
      rw [Ch02.bCoarse_eq_ofAEEq hAE]
    rw [heq]
    calc Ch02.coarseBMatrixNorm Q F'
        ≤ Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) F' :=
          Ch02.coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale Q hk F'
      _ ≤ maxDescendantBBlockNormAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) A :=
          Ch02.maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale F' Q hk
      _ ≤ 4 * (d : ℝ) * lam⁻¹ * Lam ^ 2 := by
          simpa [A] using
            maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
              Q A hEll hData 0
  · have heq : Ch02.coarseSigmaStarInvMatrixNorm Q F =
        Ch02.coarseSigmaStarInvMatrixNorm Q F' := by
      unfold Ch02.coarseSigmaStarInvMatrixNorm
      rw [Ch02.sigmaStarInvCoarse_eq_ofAEEq hAE]
    rw [heq]
    calc Ch02.coarseSigmaStarInvMatrixNorm Q F'
        ≤ Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) F' :=
          Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale Q hk F'
      _ ≤ maxDescendantSigmaStarInvNormAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) A :=
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
            F' Q hk
      _ ≤ 4 * (d : ℝ) * lam⁻¹ := by
          simpa [A] using
            maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
              Q A hEll hData 0

end Envelope


/-- **Chart envelope.**  For the actual chart and a descendant `Q` of the unit root, pointwise
bounds `λ ≤ A_N(w + r'x) ≤ Λ` on `Q` give `|b(Q)| ≤ 4dΛ²/λ` and `|σ_*⁻¹(Q)| ≤ 4d/λ`. -/
theorem aux_lem_extension_cell_moment_chart_envelope {d : ℕ} [NeZero d] (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)))
    (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0))
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hbd : ∀ x ∈ Homogenization.openCubeSet Q,
      lam ≤ cutoffCoefficient M H om N (fun i => w i + r' * x i) ∧
        cutoffCoefficient M H om N (fun i => w i + r' * x i) ≤ Lam) :
    Homogenization.Book.Ch02.coarseBMatrixNorm Q
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r') ≤
        4 * (d : ℝ) * lam⁻¹ * Lam ^ 2 ∧
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r') ≤
        4 * (d : ℝ) * lam⁻¹ := by
  have hell := aux_lem_extension_cell_moment_regField_elliptic M H N w r' om
  have h := aux_lem_extension_cell_moment_chart_aeeq E M H om N z0 R hR w r' hr' hsub Q hQ hell
  unfold Homogenization.Book.Ch02.CoeffOn.AEEq at h
  exact aux_lem_extension_cell_moment_coarse_envelope _ Q
    (aux_lem_extension_cell_moment_chartCM M H om N w r') hlam hle hbd h






def aux_lem_extension_cell_moment_AboveBridge (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (p ε : ℝ) : Prop :=
  ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ δ0 →
    ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
      ∀ n : ℕ, k + n ≤ N →
      ∀ Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)),
        eLpNorm (fun om =>
            Homogenization.Book.Ch02.coarseBMatrixNorm Q
              (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
                ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) ∧
        eLpNorm (fun om =>
            Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
              (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
                ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n))



def aux_lem_extension_cell_moment_BelowBridge (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (p ε : ℝ) : Prop :=
  ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ δ0 →
    ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
      ∀ n : ℕ, N < k + n →
      ∀ Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)),
      ∃ lo hi : BilateralField d → ℝ,
        (∀ om, 0 < lo om ∧ lo om ≤ hi om ∧
          ∀ x ∈ Homogenization.openCubeSet Q,
            lo om ≤ cutoffCoefficient M H om N
                (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∧
              cutoffCoefficient M H om N (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ≤
                hi om) ∧
        eLpNorm (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 + 4 * (d : ℝ) * (lo om)⁻¹)
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * k + ε * n))



theorem aux_lem_extension_cell_moment_descBridge_of_split {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) {p ε : ℝ}
    (hA : aux_lem_extension_cell_moment_AboveBridge d E p ε)
    (hB : aux_lem_extension_cell_moment_BelowBridge d p ε) :
    aux_lem_extension_cell_moment_DescBridge d E p ε := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨δa, Ca, hδa, hCa, hA⟩ := hA
  obtain ⟨δb, Cb, hδb, hCb, hB⟩ := hB
  refine ⟨min δa δb, max Ca Cb, lt_min hδa hδb, lt_max_of_lt_left hCa, ?_⟩
  intro M _Rm H hH hδ z0 R hR
  obtain ⟨C0a, hC0a, hA⟩ := hA M _Rm H hH (hδ.trans (min_le_left _ _)) z0 R hR
  obtain ⟨C0b, hC0b, hB⟩ := hB M _Rm H hH (hδ.trans (min_le_right _ _)) z0 R hR
  refine ⟨max C0a C0b, lt_max_of_lt_left hC0a, ?_⟩
  intro w N k hk hcell n Q hQ
  have hmono : ∀ {C0' C1' : ℝ}, 0 ≤ C0' → C0' ≤ max C0a C0b → C1' ≤ max Ca Cb →
      ENNReal.ofReal (C0' * Real.exp (C1' * M.delta ^ 2 * k + ε * n)) ≤
        ENNReal.ofReal (max C0a C0b * Real.exp (max Ca Cb * M.delta ^ 2 * k + ε * n)) := by
    intro C0' C1' h0 hC0' hC1'
    refine ENNReal.ofReal_le_ofReal ?_
    have hδk : 0 ≤ M.delta ^ 2 * (k : ℝ) := by positivity
    have hexp : Real.exp (C1' * M.delta ^ 2 * k + ε * n) ≤
        Real.exp (max Ca Cb * M.delta ^ 2 * k + ε * n) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_right hC1' hδk
      nlinarith [this]
    exact mul_le_mul hC0' hexp (Real.exp_pos _).le (le_trans h0 hC0')
  rcases le_or_gt (k + n) N with hkn | hkn
  · obtain ⟨h1, h2⟩ := hA w N k hk hcell n hkn Q hQ
    exact ⟨h1.trans (hmono hC0a.le (le_max_left _ _) (le_max_left _ _)),
      h2.trans (hmono hC0a.le (le_max_left _ _) (le_max_left _ _))⟩
  · obtain ⟨lo, hi, hbd, hmom⟩ := hB w N k hk hcell n hkn Q hQ
    have hk' : (Homogenization.originCube d 0).scale - (n : ℤ) ≤
        (Homogenization.originCube d 0).scale := sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hQsub := Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
    have hsub : (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
        Set (SpatialCoordinates d)) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)) :=
      hcell
    have henv := fun om => aux_lem_extension_cell_moment_chart_envelope E M H om N z0 R hR w
      ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) hsub Q hQsub (hbd om).1 (hbd om).2.1 (hbd om).2.2
    have hnn : ∀ om, 0 ≤ 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 := fun om => by
      have := (hbd om).1
      positivity
    have hnn' : ∀ om, 0 ≤ 4 * (d : ℝ) * (lo om)⁻¹ := fun om => by
      have := (hbd om).1
      positivity
    constructor
    · refine le_trans (eLpNorm_mono_real fun om => ?_) (hmom.trans
        (hmono hC0b.le (le_max_right _ _) (le_max_right _ _)))
      rw [Real.norm_of_nonneg (Homogenization.Book.Ch02.coarseBMatrixNorm_nonneg _ _)]
      linarith [(henv om).1, hnn' om]
    · refine le_trans (eLpNorm_mono_real fun om => ?_) (hmom.trans
        (hmono hC0b.le (le_max_right _ _) (le_max_right _ _)))
      rw [Real.norm_of_nonneg (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg _ _)]
      linarith [(henv om).2, hnn om]



theorem lem_extension_cell_moment :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d)
    (beta eta q : ℝ), beta ∈ Set.Ioo (1 / 2 : ℝ) 1 → 0 < eta → 1 ≤ q →
      q * eta > (d : ℝ) →
  ∃ deltaq Cd : ℝ, 0 < deltaq ∧ 0 < Cd ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ deltaq →
    ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (J : ℕ) (origins : Fin J → SpatialCoordinates d),
      ∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ), k ≤ N →
        (centeredCube
            (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
        AEStronglyMeasurable
            (fun om =>
              E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                  ((3 : ℝ) ^ (-(k : ℤ)))
                  ((beta - 1 / 2) / 4) 2 +
                (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                  ((3 : ℝ) ^ (-(k : ℤ)))
                  ((beta - 1 / 2) / 4) 2)⁻¹)
            (chaosSampleLaw M).toMeasure ∧
        eLpNorm
            (fun om =>
              E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                  ((3 : ℝ) ^ (-(k : ℤ)))
                  ((beta - 1 / 2) / 4) 2 +
                (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                  ((3 : ℝ) ^ (-(k : ℤ)))
                  ((beta - 1 / 2) / 4) 2)⁻¹)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal
              (Cq * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
  intro d hd _ _ E beta eta q hbeta _heta _hq _hqeta
  obtain ⟨deltaq, Cd, hdeltaq, hCd, hbound⟩ :
      ∃ deltaq Cd : ℝ, 0 < deltaq ∧ 0 < Cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ deltaq →
      ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      ∃ Cq : ℝ, 0 < Cq ∧
        ∀ (J : ℕ) (origins : Fin J → SpatialCoordinates d),
        ∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ), k ≤ N →
          (centeredCube
              (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
              ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
          eLpNorm
              (fun om =>
                E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                    (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                    ((3 : ℝ) ^ (-(k : ℤ)))
                    ((beta - 1 / 2) / 4) 2 +
                  (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                    (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                    ((3 : ℝ) ^ (-(k : ℤ)))
                    ((beta - 1 / 2) / 4) 2)⁻¹)
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal
              (Cq * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
    
    -- 417--443, read in the chart of the cell).  Everything downstream of it -- the `q = 2`
    -- discounted series, Minkowski in `L^q`, the discount `3^{-2sn}` against `e^{εn}`, and the
    -- choice `deltaq = δ₀`, `Cd = C₁/(q+q²)` before the model and `Cq` after the root -- is
    -- proved in `aux_lem_extension_cell_moment_of_scaleBridge`.
    have hε : 0 < (beta - 1 / 2) / 4 * Real.log 3 :=
      mul_pos (aux_lem_extension_cell_moment_order hbeta).1 (Real.log_pos (by norm_num))
    have habove : aux_lem_extension_cell_moment_AboveBridge d E
        (max q (2 * d * Real.log 3 / ((beta - 1 / 2) / 4 * Real.log 3)))
        ((beta - 1 / 2) / 4 * Real.log 3 / 2) := by
      exact aux_lem_extension_cell_moment_above_chart hd E _ _
        (_hq.trans (le_max_left _ _)) (by positivity)
    have hbelow : aux_lem_extension_cell_moment_BelowBridge d
        (max q (2 * d * Real.log 3 / ((beta - 1 / 2) / 4 * Real.log 3)))
        ((beta - 1 / 2) / 4 * Real.log 3 / 2) := by
      exact aux_lem_extension_cell_moment_below_chart hd _ _
        (lt_of_lt_of_le (by linarith [_hq]) (le_max_left _ _)) (by positivity)
    have hdesc : aux_lem_extension_cell_moment_DescBridge d E
        (max q (2 * d * Real.log 3 / ((beta - 1 / 2) / 4 * Real.log 3)))
        ((beta - 1 / 2) / 4 * Real.log 3 / 2) :=
      aux_lem_extension_cell_moment_descBridge_of_split hd E habove hbelow
    have hbridge : aux_lem_extension_cell_moment_ScaleBridge d E q
        ((beta - 1 / 2) / 4 * Real.log 3) :=
      aux_lem_extension_cell_moment_scaleBridge_of_descBridge hd E _hq hε hdesc
    exact aux_lem_extension_cell_moment_of_scaleBridge hd E hbeta _hq hbridge
  refine ⟨deltaq, Cd, hdeltaq, hCd, ?_⟩
  intro M _Rm H hH hδ z0 R hR
  obtain ⟨Cq, hCq, hcellbound⟩ := hbound M _Rm H hH hδ z0 R hR
  refine ⟨Cq, hCq, fun J origins N k index nidx hk hcell =>
    ⟨?_, hcellbound J origins N k index nidx hk hcell⟩⟩
  exact aux_lem_extension_cell_moment_aestronglyMeasurable hd E M H hH _
    (aux_lem_extension_cell_moment_order hbeta) z0 R hR N _ _ _ hcell

end Paper
