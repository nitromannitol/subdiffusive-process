module

public import SubdiffusiveProcess.Paper.inputs_det_interior_comparison
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.Frozen.Section2.GeneralCoarseGraining
public import SubdiffusiveProcess.Frozen.Section2.CoarseGrainedCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridComposeAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.OffGridFrame
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PaperErrorBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import Homogenization.Internal.Ch02.Representatives

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

/-- The harmonic replacement on a translated cube exists and is unique in
the a.e. sense used by the interior comparison estimate. -/
theorem aux_inputs_deterministic_interior_harmonic_replacement
    (d : ℕ) [NeZero d] (n : ℕ) (y : Vec d)
    (uD : H1Function (translatedCube d (n - 2) y)) :
    (∃ v : H1Function (translatedCube d (n - 2) y),
      IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
        HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
    (∀ v v' : H1Function (translatedCube d (n - 2) y),
      (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
          HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
      (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
          HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
      v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
        v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) := by
  constructor
  · exact SubdiffusiveProcess.CoarseGrainingVocab.exists_isWeaklyHarmonicOn_one_translatedCube
      (n - 2) y uD
  · intro v v' hv hv'
    exact SubdiffusiveProcess.CoarseGrainingVocab.ae_eq_of_isWeaklyHarmonicOn_one_translatedCube
      (n - 2) y hv.1 hv.2 hv'.1 hv'.2

/-- The cube-wise scalar certificates provide the symmetry required by the
chapter 2 deterministic comparison theorem. -/
theorem aux_inputs_deterministic_interior_coeff_symmetric
    (d : ℕ) (a : Vec d → ℝ) (data : ScalarTriadicCoeffData a) :
    ∀ Q : Homogenization.TriadicCube d,
      Homogenization.Book.Ch02.CoeffOn.IsSymmetric
        (data.toTriadicCoeffFamily.coeffOn Q) := by
  intro Q
  exact (data.onCube Q).isSymmetric

/-- Convert the paper's extended-valued error bound into the corresponding
real-valued Chapter 2 error bound. -/
theorem aux_inputs_deterministic_interior_anchored_error_bound
    (d : ℕ) [NeZero d] (n : ℕ) (s Cerr a0 : ℝ)
    (a : Vec d → ℝ) (data : ScalarTriadicCoeffData a)
    (hs : 0 < s) (hCerr : 0 ≤ Cerr) (ha0 : 0 < a0)
    (herr : paperHomogenizationError (originCube d ((n : ℤ) + 2))
      ((n : ℤ) + 2) (s / 8)
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr) :
    Homogenization.Book.Ch02.HomogenizationErrorOnCube
      (originCube d ((n : ℤ) + 2)) (s / 8)
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily (scalarMatrix (d := d) a0) ≤ Cerr := by
  have hs8 : 0 < s / 8 := by positivity
  have hcompare :=
    ofReal_homogenizationErrorOnCube_infinity_two_le_paper
      (originCube d ((n : ℤ) + 2)) data.toTriadicCoeffFamily
      (aux_inputs_deterministic_interior_coeff_symmetric d a data)
      hs8 ha0
  have hpaper :
      paperHomogenizationError (originCube d ((n : ℤ) + 2))
        (originCube d ((n : ℤ) + 2)).scale (s / 8)
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr := by
    simpa [Homogenization.originCube] using herr
  have hreal :
      ENNReal.ofReal
          (Homogenization.Book.Ch02.HomogenizationErrorOnCube
            (originCube d ((n : ℤ) + 2)) (s / 8)
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
            data.toTriadicCoeffFamily (scalarMatrix (d := d) a0)) ≤
        ENNReal.ofReal Cerr := hcompare.trans hpaper
  exact (ENNReal.ofReal_le_ofReal_iff hCerr).mp hreal

/-- Stability transports the anchored coefficient error to an off-grid local
cube without changing the data family or the reference matrix. -/
theorem aux_inputs_deterministic_interior_offgrid_error_cap
    {d : ℕ} [NeZero d] (P K : Homogenization.TriadicCube d)
    (s Cerr : ℝ) (A : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (a0 : Homogenization.Mat d) (w : Vec d)
    (g : Homogenization.CoeffField d) {lam Lam : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hrepresentative : ∀ Q : Homogenization.TriadicCube d,
      (A.coeffOn Q).toCoeffField = g)
    (hEll : Homogenization.IsEllipticFieldOn lam Lam
      (translateSet w (Homogenization.cubeSet P)) g)
    (hcontain : translateSet w (Homogenization.cubeSet P) ⊆
      Homogenization.cubeSet K)
    (herror : Homogenization.Book.Ch02.HomogenizationErrorOnCube K (s / 8)
      .infinity (.finite 2) A a0 ≤ Cerr) :
    offGridErrorFunctional w P (s / 6) g a0 ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 *
          (((K.scale - P.scale).toNat : ℕ) : ℝ)) * Cerr) := by
  have hstable := offGridErrorFunctional_le_slot
    (A := A) (a0 := a0) hs hs1 hrepresentative hEll hcontain
  calc
    offGridErrorFunctional w P (s / 6) g a0 ≤
        Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 *
            (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
            Homogenization.Book.Ch02.HomogenizationErrorOnCube K
              (s / 8) .infinity (.finite 2) A a0) := hstable
    _ ≤ Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 *
            (((K.scale - P.scale).toNat : ℕ) : ℝ)) * Cerr) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left herror
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
        (Real.sqrt_nonneg _)

/-- The paper's error cap reaches the off-grid replacement cube. -/
theorem aux_inputs_deterministic_interior_offgrid_anchor_cap
    (d : ℕ) [NeZero d] (n : ℕ) (s Cerr a0 : ℝ)
    (a : Vec d → ℝ) (z y : Vec d)
    (data : ScalarTriadicCoeffData (fun q => a (q + z)))
    (hs : 0 < s) (hs1 : s ≤ 1) (hCerr : 0 < Cerr) (ha0 : 0 < a0)
    (herr : paperHomogenizationError
      (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr)
    {lam Lam : ℝ}
    (hEll : Homogenization.IsEllipticFieldOn lam Lam
      (translateSet (y - z)
        (Homogenization.cubeSet (originCube d ((n : ℤ) - 2))))
      (scalarCoeffField (fun q => a (q + z))))
    (hcontain : translateSet (y - z)
      (Homogenization.cubeSet (originCube d ((n : ℤ) - 2))) ⊆
        Homogenization.cubeSet (originCube d ((n : ℤ) + 2))) :
    offGridErrorFunctional (y - z) (originCube d ((n : ℤ) - 2))
        (s / 6) (scalarCoeffField (fun q => a (q + z)))
        (Homogenization.scalarMatrix a0) ≤
      Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 2) * Cerr) := by
  have hroot := aux_inputs_deterministic_interior_anchored_error_bound
    d n s Cerr a0 (fun q => a (q + z)) data hs hCerr.le ha0 herr
  have hdepth :
      ((((originCube d ((n : ℤ) + 2)).scale -
          (originCube d ((n : ℤ) - 2)).scale).toNat : ℕ) : ℝ) = 4 := by
    simp [Homogenization.originCube]
  have hcap := aux_inputs_deterministic_interior_offgrid_error_cap
    (P := originCube d ((n : ℤ) - 2))
    (K := originCube d ((n : ℤ) + 2)) s Cerr
    data.toTriadicCoeffFamily (Homogenization.scalarMatrix a0) (y - z)
    (scalarCoeffField (fun q => a (q + z))) hs hs1
    (fun Q => rfl) hEll hcontain hroot
  simpa [hdepth, Real.sqrt_mul, show s / 8 * 4 = s / 2 by ring] using hcap

/-- Replace an a.e.-elliptic public cube coefficient by the library's
pointwise-elliptic representative on that cube. -/
theorem aux_inputs_deterministic_interior_pointwise_elliptic_representative
    {d : ℕ} (Q : Homogenization.TriadicCube d)
    (c : Homogenization.Book.Ch02.CoeffOn
      (Homogenization.Book.Ch02.cubeDomain Q)) :
    ∃ b : Homogenization.CoeffField d,
      Homogenization.IsEllipticFieldOn c.lam c.Lam
        (Homogenization.cubeSet Q) b ∧
      b =ᵐ[volume.restrict (Homogenization.cubeSet Q)] c.toCoeffField := by
  refine ⟨Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
      (Homogenization.Book.Ch02.cubeDomain Q) c,
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet
      Q c, ?_⟩
  simpa [Homogenization.volumeMeasureOn,
    Homogenization.Book.Ch02.cubeDomain,
    Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using!
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
        (Homogenization.Book.Ch02.cubeDomain Q) c)

/-- The root cube's pointwise representative remains elliptic on the translated
interior cube whenever that cube lies in the root cube. -/
theorem aux_inputs_deterministic_interior_rootRep_local_elliptic
    {d : ℕ} (Q : Homogenization.TriadicCube d)
    (c : Homogenization.Book.Ch02.CoeffOn
      (Homogenization.Book.Ch02.cubeDomain Q))
    (W : Set (Vec d)) (hWmeas : MeasurableSet W)
    (hWsub : W ⊆ Homogenization.cubeSet Q) :
    Homogenization.IsEllipticFieldOn c.lam c.Lam W
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
        (Homogenization.Book.Ch02.cubeDomain Q) c) := by
  have hb := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet
    Q c
  exact Homogenization.IsEllipticFieldOn.mono hb hWmeas hWsub

/-- Translate the root representative back to physical coordinates.  On any
subset of the translated root cube it agrees a.e. with the original scalar
coefficient. -/
theorem aux_inputs_deterministic_interior_rootRep_translated_ae
    {d : ℕ} (Q : Homogenization.TriadicCube d) (z : Vec d)
    (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun q => a (q + z)))
    (W : Set (Vec d)) (hWsub : W ⊆ translateSet z (Homogenization.cubeSet Q)) :
    Homogenization.translateCoeffField (-z)
        (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (Homogenization.Book.Ch02.cubeDomain Q)
          ((data.onCube Q).toCoeffOn)) =ᵐ[volume.restrict W]
      scalarCoeffField a := by
  let c : Homogenization.Book.Ch02.CoeffOn
      (Homogenization.Book.Ch02.cubeDomain Q) := (data.onCube Q).toCoeffOn
  let b : Homogenization.CoeffField d :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
      (Homogenization.Book.Ch02.cubeDomain Q) c
  have hroot : b =ᵐ[volume.restrict (Homogenization.cubeSet Q)]
      scalarCoeffField (fun q => a (q + z)) := by
    simpa [b, c, Homogenization.volumeMeasureOn,
      Homogenization.Book.Ch02.cubeDomain,
      Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using!
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
        (Homogenization.Book.Ch02.cubeDomain Q) c)
  have htranslated :=
    (Homogenization.measurePreserving_subRight_restrict_translateSet
      (d := d) z (Homogenization.cubeSet Q)).quasiMeasurePreserving.ae_eq hroot
  have hfield : Homogenization.translateCoeffField (-z) b =ᵐ[
      volume.restrict (translateSet z (Homogenization.cubeSet Q))]
      scalarCoeffField a := by
    filter_upwards [htranslated] with x hx
    simpa [Homogenization.translateCoeffField, scalarCoeffField,
      Function.comp_def] using! hx
  exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset hWsub hfield

/-- Rooting the paper family at its parent cube changes the coefficient only
on null sets of every descendant, so its anchored Chapter 2 error is unchanged. -/
theorem aux_inputs_deterministic_interior_root_error_eq
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (A : Homogenization.Book.Ch02.TriadicCoeffFamily d) (s : ℝ)
    (a0 : Homogenization.Mat d) :
    Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2)
        (Homogenization.Book.Ch03.ABK26.rootPointwiseCoeffFamily Q (A.coeffOn Q)) a0 =
      Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2)
        A a0 := by
  apply homogenizationErrorOnCube_eq_of_descendantAEEq
  intro k S hS
  exact rootPointwiseCoeffFamily_descendant_aeeq_family Q A
    (descendant_scale_le_of_mem_descendantsAtScale hS) hS

/-- The paper's anchor error controls the off-grid error when it is evaluated
using the pointwise elliptic representative of the root coefficient. -/
theorem aux_inputs_deterministic_interior_rootRepresentative_offgrid_cap
    (d : ℕ) [NeZero d] (n : ℕ) (s Cerr a0 : ℝ)
    (a : Vec d → ℝ) (z y : Vec d)
    (data : ScalarTriadicCoeffData (fun q => a (q + z)))
    (hs : 0 < s) (hs1 : s ≤ 1) (hCerr : 0 < Cerr) (ha0 : 0 < a0)
    (herr : paperHomogenizationError
      (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr)
    (hcontain : translateSet (y - z)
      (Homogenization.cubeSet (originCube d ((n : ℤ) - 2))) ⊆
        Homogenization.cubeSet (originCube d ((n : ℤ) + 2))) :
    ∃ b : Homogenization.CoeffField d,
      Homogenization.IsEllipticFieldOn
        (data.onCube (originCube d ((n : ℤ) + 2))).lam
        (data.onCube (originCube d ((n : ℤ) + 2))).Lam
        (translateSet (y - z)
          (Homogenization.cubeSet (originCube d ((n : ℤ) - 2)))) b ∧
      offGridErrorFunctional (y - z) (originCube d ((n : ℤ) - 2))
        (s / 6) b (Homogenization.scalarMatrix a0) ≤
        Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 2) * Cerr) := by
  let K : Homogenization.TriadicCube d := originCube d ((n : ℤ) + 2)
  let P : Homogenization.TriadicCube d := originCube d ((n : ℤ) - 2)
  let A : Homogenization.Book.Ch02.TriadicCoeffFamily d := data.toTriadicCoeffFamily
  let c : Homogenization.Book.Ch02.CoeffOn (Homogenization.Book.Ch02.cubeDomain K) :=
    (data.onCube K).toCoeffOn
  let b : Homogenization.CoeffField d :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
      (Homogenization.Book.Ch02.cubeDomain K) c
  let R : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Homogenization.Book.Ch03.ABK26.rootPointwiseCoeffFamily K (A.coeffOn K)
  have hW : MeasurableSet (translateSet (y - z)
      (Homogenization.cubeSet P)) := by
    rw [← Homogenization.preimage_subRight_eq_translateSet]
    exact (Homogenization.measurableSet_cubeSet P).preimage
      (measurable_id.sub measurable_const)
  have hEll := aux_inputs_deterministic_interior_rootRep_local_elliptic
    K c (translateSet (y - z) (Homogenization.cubeSet P)) hW
    (by simpa [K, P] using hcontain)
  have hroot := aux_inputs_deterministic_interior_anchored_error_bound
    d n s Cerr a0 (fun q => a (q + z)) data hs hCerr.le ha0 herr
  have hrootEq : Homogenization.Book.Ch02.HomogenizationErrorOnCube K (s / 8)
      .infinity (.finite 2) R (Homogenization.scalarMatrix a0) =
    Homogenization.Book.Ch02.HomogenizationErrorOnCube K (s / 8)
      .infinity (.finite 2) A (Homogenization.scalarMatrix a0) := by
    exact aux_inputs_deterministic_interior_root_error_eq K A (s / 8)
      (Homogenization.scalarMatrix a0)
  have herror : Homogenization.Book.Ch02.HomogenizationErrorOnCube K (s / 8)
      .infinity (.finite 2) R (Homogenization.scalarMatrix a0) ≤ Cerr := by
    rw [hrootEq]
    exact hroot
  have hcap := aux_inputs_deterministic_interior_offgrid_error_cap
    (P := P) (K := K) s Cerr R (Homogenization.scalarMatrix a0) (y - z)
    b hs hs1 (fun S => by
      change Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
        (Homogenization.Book.Ch02.cubeDomain K) c = b
      rfl) hEll hcontain herror
  have hdepth : ((((K.scale - P.scale).toNat : ℕ) : ℝ)) = 4 := by
    simp [K, P, Homogenization.originCube]
  refine ⟨b, hEll, ?_⟩
  simpa [hdepth, Real.sqrt_mul, show s / 8 * 4 = s / 2 by ring] using hcap

/-- The remaining analytic clause of the interior deterministic input, with
the unconditional harmonic well-posedness clauses removed.  The imported
Section 6 sharp-loop comparison has powers `s⁻²` and `s⁻⁸`, which do not close
this clause's requested `s^(-3/2)` and `s^(-15/2)` powers directly.  The
separate smooth-dual estimate with those powers is specialized to `aCutoff`
and a GMC model, so it does not instantiate this arbitrary coefficient-data
statement. -/
def aux_inputs_deterministic_interior_comparison (d : ℕ) [NeZero d] : Prop :=
  ∀ Cerr : ℝ, 0 < Cerr → ∃ C : ℝ, 0 < C ∧
    ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
    ∀ m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
    ∀ x ∈ truncatedCube d m (n - 3) z,
    ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
    ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + z)),
    ∀ a0 : ℝ, 0 < a0 →
    let err : ENNReal :=
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0;
    err ≤ ENNReal.ofReal Cerr →
    ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
      IsDivFormWeakSolutionOn a (cube d m) u g →
      (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
        Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d m) sOrder FiniteLpExponent.two g) →
      ∀ y ∈ cube d m,
        truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        ∀ uD : H1Function (translatedCube d (n - 2) y),
          (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            normalizedL2On (truncatedCube d m (n - 4) x)
                (fun q => u.toFun q - v.toFun q) ≤
              C * s ^ (-3 / 2 : ℝ) * err.toReal *
                  normalizedL2On (truncatedCube d m n x)
                    (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                C * s ^ (-15 / 2 : ℝ) * (a0)⁻¹ *
                  (3 : ℝ) ^ ((1 + s) * n) *
                  (fractionalSeminormOn (truncatedCube d m n x) s g).toReal

theorem inputs_deterministic_interior (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ Cerr : ℝ, 0 < Cerr → ∃ C : ℝ, 0 < C ∧
      ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + z)),
      ∀ a0 : ℝ, 0 < a0 →
      let err : ENNReal :=
        paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0;
      err ≤ ENNReal.ofReal Cerr →
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn a (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          (∃ v : H1Function (translatedCube d (n - 2) y),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
          (∀ v v' : H1Function (translatedCube d (n - 2) y),
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
            v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
              v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            normalizedL2On (truncatedCube d m (n - 4) x)
                (fun q => u.toFun q - v.toFun q) ≤
              C * s ^ (-3 / 2 : ℝ) * err.toReal *
                  normalizedL2On (truncatedCube d m n x)
                    (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                C * s ^ (-15 / 2 : ℝ) * (a0)⁻¹ *
                  (3 : ℝ) ^ ((1 + s) * n) *
                  (fractionalSeminormOn (truncatedCube d m n x) s g).toReal) := by
  have hcomparison : aux_inputs_deterministic_interior_comparison d := by
    exact inputs_det_interior_comparison d hd
  intro Cerr hCerr
  obtain ⟨C, hC, hEstimate⟩ := hcomparison Cerr hCerr
  refine ⟨C, hC, ?_⟩
  intro s hs hs1 m n hnm z hz x hx hbd a data a0 ha0 err herr u g hweak hgex
    y hy hsub1 hsub2 uD huval hugrad
  have hwell := aux_inputs_deterministic_interior_harmonic_replacement d n y uD
  refine ⟨hwell.1, hwell.2, ?_⟩
  intro v hv htrace
  exact hEstimate s hs hs1 m n hnm z hz x hx hbd a data a0 ha0 herr
    u g hweak hgex y hy hsub1 hsub2 uD huval hugrad v hv htrace

end Paper
