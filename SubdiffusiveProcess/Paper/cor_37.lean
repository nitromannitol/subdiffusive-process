module

public import Homogenization.Book.Ch04.Theorems.CoarseObservables
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRestrictionLaw
public import SubdiffusiveProcess.Paper.in_moments_response_moment
public import SubdiffusiveProcess.Paper.annealed_limit_response_transport
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_moments
public import SubdiffusiveProcess.Paper.thm_eta
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.Geometry.UpstreamCube
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic


@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A positive semidefinite quadratic form on a Euclidean unit vector is
bounded by the trace. -/
private theorem cor_37_psd_quadratic_le_trace (d : ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosSemidef)
    (e : Fin d → ℝ) (he : ∑ i, e i ^ 2 = 1) :
    e ⬝ᵥ M.mulVec e ≤ M.trace := by
  classical
  obtain ⟨B, rfl⟩ : ∃ B : Matrix (Fin d) (Fin d) ℝ, M = B.conjTranspose * B := by
    open scoped MatrixOrder in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have hrow (i : Fin d) :
      (∑ j, B i j * e j) ^ 2 ≤ ∑ j, B i j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
      (fun j => e j) (fun j => B i j)
    rw [he, one_mul] at h
    simpa only [mul_comm] using h
  have hsum :
      (∑ i, (∑ j, B i j * e j) ^ 2) ≤
        ∑ i, ∑ j, B i j ^ 2 :=
    Finset.sum_le_sum (fun i _ => hrow i)
  convert hsum using 1
  · simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply,
      Matrix.conjTranspose_apply, star_trivial]
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    calc
      (∑ x, ∑ x_1, ∑ i, e x * (B i x * B i x_1 * e x_1)) =
          ∑ i, ∑ x, ∑ x_1, e x * (B i x * B i x_1 * e x_1) := by
            calc
              _ = ∑ x, ∑ i, ∑ x_1, e x * (B i x * B i x_1 * e x_1) := by
                congr 1
                ext x
                rw [Finset.sum_comm]
              _ = _ := by rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, ∑ k, B i j * e j * (B i k * e k) := by
        congr 1
        ext i
        congr 1
        ext j
        congr 1
        ext k
        ring
      _ = _ := by
        congr 1
        ext i
        rw [Finset.sum_comm]
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, star_trivial, sq]
    rw [Finset.sum_comm]

/-- The scalar field in `thm_eta` is the zero-infrared coefficient used by the
Sobolev response in the calibration statement. -/
private theorem cor_37_cutoff_coefficient (d N : ℕ)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : BilateralField d) (x : SpatialCoordinates d) :
    cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x =
      (Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x) := by
  unfold cutoffCoefficient cutoffPotential
  simp only [ContinuousMap.zero_apply, inv_mul_eq_div]
  rw [Real.exp_sub]
  simp
  ring

/-- The public Chapter 2 domain of the actual cube of side `3^k`. -/
private def cor_37_domain (d k : ℕ) : Homogenization.Book.Ch02.Domain d :=
  Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ))

/-- The cutoff coefficient packaged on the exact cube used by `thm_eta`. -/
private def cor_37_scalar_data (d : ℕ)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ)
    (omega : BilateralField d) :
    SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData (cor_37_domain d k)
      (cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N) :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
    (SubdiffusiveProcess.Lane4.cutoffCoefficient_continuous model
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N)
    (SubdiffusiveProcess.Lane4.cutoffCoefficient_pos model
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N)
    (cor_37_domain d k)



private theorem cor_37_scalar_data_field (d : ℕ)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ)
    (omega : BilateralField d) (x : SpatialCoordinates d) :
    (cor_37_scalar_data d model N k omega).toCoeffOn.toCoeffField x =
      ((Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
        (1 : Homogenization.Mat d) := by
  rw [← cor_37_cutoff_coefficient d N model omega x]
  rfl

/-- The moment family and the concrete scalar data represent the same coefficient
almost everywhere on the actual origin cube. -/
private theorem cor_37_family_coeff_ae (d : ℕ)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hfamily : ∀ (N : ℕ) (omega : BilateralField d)
        (Q : Homogenization.TriadicCube d),
      ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
        ((family N omega).coeffOn Q).toCoeffField x =
          Homogenization.scalarMatrix
            (cutoffCoefficient model
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x))
    (N k : ℕ) (omega : BilateralField d) :
    Homogenization.Book.Ch02.CoeffOn.AEEq
      ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ)))
      (cor_37_scalar_data d model N k omega).toCoeffOn := by
  unfold Homogenization.Book.Ch02.CoeffOn.AEEq
  change ((family N omega).coeffOn
      (Homogenization.originCube d (k : ℤ))).toCoeffField =ᵐ[
        volume.restrict (Homogenization.openCubeSet
          (Homogenization.originCube d (k : ℤ)))]
      (cor_37_scalar_data d model N k omega).toCoeffOn.toCoeffField
  filter_upwards [hfamily N omega (Homogenization.originCube d (k : ℤ))] with x hx
  rw [hx]
  rfl

/-- The response of the moment family agrees with that of the concrete scalar
coefficient, for every pair of directions. -/
private theorem cor_37_family_responseJ_eq (d : ℕ)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hfamily : ∀ (N : ℕ) (omega : BilateralField d)
        (Q : Homogenization.TriadicCube d),
      ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
        ((family N omega).coeffOn Q).toCoeffField x =
          Homogenization.scalarMatrix
            (cutoffCoefficient model
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x))
    (N k : ℕ) (omega : BilateralField d)
    (p q : Homogenization.Vec d) :
    Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
      ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ))) p q =
    Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
      (cor_37_scalar_data d model N k omega).toCoeffOn p q := by
  exact Homogenization.Book.Ch02.responseJ_eq_ofAEEq
    (cor_37_family_coeff_ae d model family hfamily N k omega) p q

/-- The domain carrier is the very same centred cube as in `cor_37`. -/
private theorem cor_37_domain_set (d k : ℕ) :
    (cor_37_domain d k : Set (Homogenization.Vec d)) =
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)) := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := by positivity
  simpa [cor_37_domain, Homogenization.Book.Ch02.cubeDomain_coe, zpow_natCast]
    using (SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube
      (d := d) (k : ℤ) hr).symm

/-- The manuscript matrix-deviation estimate at the unit reference coefficient. -/
private theorem cor_37_deviation_at_one (d : ℕ) (hJ : in_J d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Homogenization.Book.Ch02.Domain d)
        (b : Homogenization.Book.Ch02.CoeffOn U),
        Homogenization.Book.Ch02.CoeffOn.IsSymmetric b →
      ∀ Jmax : ℝ,
        IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
          Homogenization.vecNormSq e = 1 ∧
          t = Homogenization.Book.Ch02.responseJ U b e e} Jmax →
      ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
        (Homogenization.vecDot e
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U b) e) - 1) ^ 2 +
        (Homogenization.vecDot e
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse U b) e) - 1) ^ 2 ≤
          C * Jmax * (1 + Jmax) := by
  obtain ⟨C, hC, hdev⟩ := hJ.deviation_by_J
  refine ⟨C, hC, ?_⟩
  intro U b hb Jmax hmax e he
  have hmax' : IsGreatest {t : ℝ | ∃ v : Homogenization.Vec d,
      Homogenization.vecNormSq v = 1 ∧
      t = Homogenization.Book.Ch02.responseJ U b
        ((Real.sqrt (1 : ℝ))⁻¹ • v) (Real.sqrt (1 : ℝ) • v)} Jmax := by
    simpa only [Real.sqrt_one, inv_one, one_smul] using hmax
  simpa only [Real.sqrt_one, inv_one, one_smul, one_mul] using
    hdev U b hb 1 one_pos Jmax hmax' e he

/-- The unit-direction maximum of `J` is bounded by its coordinate trace. -/
private theorem cor_37_Jmax_le_basis_sum (d : ℕ) (hJ : in_J d)
    (U : Homogenization.Book.Ch02.Domain d)
    (b : Homogenization.Book.Ch02.CoeffOn U)
    (hb : Homogenization.Book.Ch02.CoeffOn.IsSymmetric b)
    (Jmax : ℝ)
    (hmax : IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
      Homogenization.vecNormSq e = 1 ∧
      t = Homogenization.Book.Ch02.responseJ U b e e} Jmax) :
    Jmax ≤ ∑ i : Fin d,
      Homogenization.Book.Ch02.responseJ U b (Pi.single i 1) (Pi.single i 1) := by
  classical
  let M : Homogenization.Mat d :=
    (1 / 2 : ℝ) • Homogenization.Book.Ch02.sigmaCoarse U b +
      (1 / 2 : ℝ) • Homogenization.Book.Ch02.sigmaStarInvCoarse U b - 1
  have hformula (e : Homogenization.Vec d) :
      Homogenization.Book.Ch02.responseJ U b e e = e ⬝ᵥ M.mulVec e := by
    rw [hJ.responseJ_split U b hb e e]
    simp only [Homogenization.vecDot, Homogenization.matVecMul, M,
      Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul]
    simp only [smul_eq_mul, dotProduct, Matrix.mulVec]
  have hsym : M.IsSymm := by
    dsimp [M]
    exact ((Homogenization.Book.Ch02.sigmaCoarse_isSymm U b).smul _).add
      ((Homogenization.Book.Ch02.sigmaStarInvCoarse_isSymm U b).smul _) |>.sub
        Matrix.isSymm_one
  have hpsd : M.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · simpa [Matrix.IsHermitian, Matrix.IsSymm] using hsym
    · intro e
      simpa only [star_trivial, ← hformula] using
        (Homogenization.Book.Ch02.responseJ_nonneg U b e e)
  obtain ⟨e, he, heq⟩ := hmax.1
  have hunit : ∑ i : Fin d, e i ^ 2 = 1 := by
    simpa [Homogenization.vecNormSq, Homogenization.vecDot, sq] using he
  calc
    Jmax = e ⬝ᵥ M.mulVec e := by rw [← hformula, ← heq]
    _ ≤ M.trace := cor_37_psd_quadratic_le_trace d M hpsd e hunit
    _ = ∑ i : Fin d,
      Homogenization.Book.Ch02.responseJ U b (Pi.single i 1) (Pi.single i 1) := by
        rw [Matrix.trace]
        apply Finset.sum_congr rfl
        intro i _
        rw [hformula]
        simp [Matrix.diag, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Cauchy--Schwarz for the square-root product used in calibration. -/
private theorem cor_37_integral_sqrt_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : 0 ≤ᵐ[μ] f) (hgn : 0 ≤ᵐ[μ] g) :
    Integrable (fun x => Real.sqrt (f x * g x)) μ ∧
      (∫ x, Real.sqrt (f x * g x) ∂μ) ≤
        Real.sqrt (∫ x, f x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
  have hflp : MemLp f 1 μ := memLp_one_iff_integrable.mpr hf
  have hglp : MemLp g 1 μ := memLp_one_iff_integrable.mpr hg
  have hrootf : MemLp (fun x => |f x| ^ (1 / 2 : ℝ)) 2 μ := by
    convert hflp.norm_rpow_div (2⁻¹ : ℝ≥0∞) using 1 <;>
      norm_num [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  have hrootg : MemLp (fun x => |g x| ^ (1 / 2 : ℝ)) 2 μ := by
    convert hglp.norm_rpow_div (2⁻¹ : ℝ≥0∞) using 1 <;>
      norm_num [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  have hproduct : Integrable
      (fun x => |f x| ^ (1 / 2 : ℝ) * |g x| ^ (1 / 2 : ℝ)) μ :=
    hrootf.integrable_mul hrootg
  have hroot : Integrable (fun x => Real.sqrt (f x * g x)) μ := by
    apply hproduct.congr
    filter_upwards [hfn, hgn] with x hfx hgx
    rw [Real.sqrt_mul hfx, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      abs_of_nonneg hfx, abs_of_nonneg hgx]
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (p := (2 : ℝ)) (q := (2 : ℝ))
    (f := fun x => |f x| ^ (1 / 2 : ℝ))
    (g := fun x => |g x| ^ (1 / 2 : ℝ))
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
    (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
    (by simpa using hrootf) (by simpa using hrootg)
  have hfpow : (∫ x, (|f x| ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ) = ∫ x, f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hfn] with x hx
    rw [← Real.rpow_mul (abs_nonneg _), abs_of_nonneg hx]
    norm_num
  have hgpow : (∫ x, (|g x| ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ) = ∫ x, g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hgn] with x hx
    rw [← Real.rpow_mul (abs_nonneg _), abs_of_nonneg hx]
    norm_num
  rw [hfpow, hgpow] at hcs
  refine ⟨hroot, ?_⟩
  calc
    (∫ x, Real.sqrt (f x * g x) ∂μ) =
        ∫ x, |f x| ^ (1 / 2 : ℝ) * |g x| ^ (1 / 2 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hfn, hgn] with x hfx hgx
      rw [Real.sqrt_mul hfx, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        abs_of_nonneg hfx, abs_of_nonneg hgx]
    _ ≤ Real.sqrt (∫ x, f x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
      simpa only [Real.sqrt_eq_rpow] using hcs

/-- A pointwise square-root response bound passes to a calibration bound in
expectation on a probability space. -/
private theorem cor_37_calibration_cs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J err : Ω → ℝ) (hJint : Integrable J μ)
    (hJn : 0 ≤ᵐ[μ] J) (herr : AEStronglyMeasurable err μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hsq : ∀ᵐ x ∂μ, err x ^ 2 ≤ C * J x * (1 + J x)) :
    Integrable (fun x => |err x|) μ ∧
      (∫ x, |err x| ∂μ) ≤
        Real.sqrt C * Real.sqrt (∫ x, J x ∂μ) *
          Real.sqrt (1 + ∫ x, J x ∂μ) := by
  have hGint : Integrable (fun x => 1 + J x) μ :=
    (integrable_const (1 : ℝ)).add hJint
  have hGn : 0 ≤ᵐ[μ] (fun x => 1 + J x) :=
    hJn.mono (fun x hx => by
      have hx0 : 0 ≤ J x := by simpa using hx
      simpa using add_nonneg (zero_le_one : (0 : ℝ) ≤ 1) hx0)
  obtain ⟨hrootInt, hrootBound⟩ :=
    cor_37_integral_sqrt_mul μ J (fun x => 1 + J x) hJint hGint hJn hGn
  have hpoint : ∀ᵐ x ∂μ,
      |err x| ≤ Real.sqrt C * Real.sqrt (J x * (1 + J x)) := by
    filter_upwards [hJn, hsq] with x hx hxsq
    have hx0 : 0 ≤ J x := by simpa using hx
    have hxg : 0 ≤ 1 + J x := add_nonneg (zero_le_one : (0 : ℝ) ≤ 1) hx0
    have hxprod : 0 ≤ J x * (1 + J x) := mul_nonneg hx0 hxg
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hxprod]
    simpa only [mul_assoc] using hxsq
  have herrInt : Integrable err μ := by
    apply Integrable.mono' (hrootInt.const_mul (Real.sqrt C)) herr
    filter_upwards [hpoint] with x hx
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg C),
      abs_of_nonneg (Real.sqrt_nonneg (J x * (1 + J x)))] using hx
  have hAbsInt : Integrable (fun x => |err x|) μ := herrInt.abs
  have hGintegral : (∫ x, 1 + J x ∂μ) = 1 + ∫ x, J x ∂μ := by
    rw [integral_add (integrable_const (1 : ℝ)) hJint]
    simp
  refine ⟨hAbsInt, ?_⟩
  calc
    (∫ x, |err x| ∂μ) ≤
        ∫ x, Real.sqrt C * Real.sqrt (J x * (1 + J x)) ∂μ :=
      integral_mono_ae hAbsInt (hrootInt.const_mul (Real.sqrt C)) hpoint
    _ = Real.sqrt C * ∫ x, Real.sqrt (J x * (1 + J x)) ∂μ := by
      rw [integral_const_mul]
    _ ≤ Real.sqrt C * (Real.sqrt (∫ x, J x ∂μ) *
        Real.sqrt (∫ x, 1 + J x ∂μ)) := by
      exact mul_le_mul_of_nonneg_left hrootBound (Real.sqrt_nonneg C)
    _ = _ := by rw [hGintegral]; ring

/-- Finitely many coordinate bounds share one scale threshold. -/
private theorem cor_37_basis_sum_eventually_small (d : ℕ)
    (f : ℕ → ℕ → Fin d → ℝ)
    (hf : ∀ i : Fin d, ∀ eps : ℝ, 0 < eps →
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ, |f k N i| ≤ eps) :
    ∀ eps : ℝ, 0 < eps →
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
        ∑ i : Fin d, |f k N i| ≤ eps := by
  classical
  intro eps heps
  let δ : ℝ := eps / ((d : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let k0 : Fin d → ℕ := fun i => Classical.choose (hf i δ hδ)
  refine ⟨Finset.univ.sup k0, ?_⟩
  intro k hk N
  have hbound (i : Fin d) : |f k N i| ≤ δ := by
    have hi := Classical.choose_spec (hf i δ hδ)
    exact hi k ((Finset.le_sup (f := k0) (Finset.mem_univ i)).trans hk) N
  have hsum : (∑ i : Fin d, |f k N i|) ≤ (d : ℝ) * δ := by
    calc
      (∑ i : Fin d, |f k N i|) ≤ ∑ _i : Fin d, δ :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = (d : ℝ) * δ := by simp [nsmul_eq_mul]
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hratio : (d : ℝ) / ((d : ℝ) + 1) ≤ 1 :=
    (div_le_iff₀ hd1).2 (by linarith)
  calc
    (∑ i : Fin d, |f k N i|) ≤ (d : ℝ) * δ := hsum
    _ = eps * ((d : ℝ) / ((d : ℝ) + 1)) := by dsimp [δ]; ring
    _ ≤ eps * 1 := mul_le_mul_of_nonneg_left hratio heps.le
    _ = eps := by ring

/-- The Cauchy--Schwarz error bound vanishes as its mean response vanishes. -/
private theorem cor_37_sqrt_response_small (C : ℝ) (_hC : 0 ≤ C) :
    ∀ eps : ℝ, 0 < eps → ∃ δ : ℝ, 0 < δ ∧
      ∀ m : ℝ, 0 ≤ m → m ≤ δ →
        Real.sqrt C * Real.sqrt m * Real.sqrt (1 + m) ≤ eps := by
  intro eps heps
  let a : ℝ := Real.sqrt C
  have ha : 0 ≤ a := Real.sqrt_nonneg C
  let t : ℝ := eps / (2 * a + 1)
  have hden : 0 < 2 * a + 1 := by linarith
  have ht : 0 < t := div_pos heps hden
  let δ : ℝ := min 1 (t ^ 2)
  have hδ : 0 < δ := lt_min one_pos (sq_pos_of_pos ht)
  refine ⟨δ, hδ, ?_⟩
  intro m hm hmδ
  have hm1 : m ≤ 1 := hmδ.trans (min_le_left _ _)
  have hm_t : m ≤ t ^ 2 := hmδ.trans (min_le_right _ _)
  have hsqrtm : Real.sqrt m ≤ t := by
    have h := Real.sqrt_le_sqrt hm_t
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos ht] at h
  have hroot1 : Real.sqrt (1 + m) ≤ 2 := by
    have h := Real.sqrt_le_sqrt (show 1 + m ≤ (4 : ℝ) by linarith)
    norm_num at h ⊢
    exact h
  calc
    Real.sqrt C * Real.sqrt m * Real.sqrt (1 + m)
        ≤ a * t * 2 := by
          dsimp [a]
          gcongr
    _ ≤ eps := by
      dsimp [t]
      calc
        a * (eps / (2 * a + 1)) * 2 =
            (2 * a * eps) / (2 * a + 1) := by ring
        _ ≤ eps := (div_le_iff₀ hden).2 (by nlinarith [heps.le])

/-- The two established variational formulations give the same normalized
Dirichlet quadratic form on one and the same open cube. -/
private theorem cor_37_affine_response_eq_sigma {d : ℕ}
    (Om : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hdom : Homogenization.IsOpenBoundedConvexDomain (Om : Set (SpatialCoordinates d)))
    (hne : (Om : Set (SpatialCoordinates d)).Nonempty)
    (hOm : Bornology.IsBounded (Om : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Om) w‖)
    (a : SpatialCoordinates d → ℝ)
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData
      (⟨(Om : Set (SpatialCoordinates d)), hdom, hne⟩ :
        Homogenization.Book.Ch02.Domain d) a)
    (aP : PositiveCoefficient Om)
    (haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (b : Homogenization.Book.Ch02.CoeffOn
      (⟨(Om : Set (SpatialCoordinates d)), hdom, hne⟩ :
        Homogenization.Book.Ch02.Domain d))
    (hb : Homogenization.Book.Ch02.CoeffOn.AEEq data.toCoeffOn b)
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) :
    affineDirichletResponse hOm hP aP p /
        volume.real (Om : Set (SpatialCoordinates d)) =
      Homogenization.vecDot p
        (Homogenization.matVecMul
          (Homogenization.Book.Ch02.sigmaCoarse
            (⟨(Om : Set (SpatialCoordinates d)), hdom, hne⟩ :
              Homogenization.Book.Ch02.Domain d) b) p) := by
  let U : Homogenization.Book.Ch02.Domain d := ⟨(Om : Set _), hdom, hne⟩
  have htheory := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory
    U data.toCoeffOn data.isSymmetric
  have hnu := htheory.dirichlet_value_by_sigma p
  rw [SubdiffusiveProcess.Lane4.symmetricDirichletNu_eq_affineDirichletResponse
    hdom hne data hOm hP aP haP hvol,
    Homogenization.Book.Ch02.sigmaCoarse_eq_ofAEEq hb] at hnu
  have hv : volume.real (Om : Set (SpatialCoordinates d)) ≠ 0 := ne_of_gt hvol
  calc
    affineDirichletResponse hOm hP aP p /
        volume.real (Om : Set (SpatialCoordinates d)) =
      2 * (affineDirichletResponse hOm hP aP p /
        (2 * volume.real (Om : Set (SpatialCoordinates d)))) := by
          field_simp
    _ = 2 * ((1 / 2 : ℝ) * Homogenization.vecDot p
      (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U b) p)) := by
        rw [hnu]
    _ = _ := by ring

/-- The normalized zero-infrared cutoff field is an a.e.-measurable
continuous-function-valued random variable under the common-scale law. -/
private theorem cor_37_cutoffField_aemeasurable (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    AEMeasurable (aux_in_moments_response_moment_cutoffField model N)
      (chaosSampleLaw model).toMeasure := by
  refine (aux_annealed_limit_response_transport_normalized_field_law
    (model := model) N).aemeasurable_fst.congr
      (Filter.Eventually.of_forall fun omega => ?_)
  ext x
  exact (cor_37_cutoff_coefficient d N model omega x).symm

/-- The unrescaled cutoff coefficient as a regular coefficient field on all of
space. -/
private def cor_37_regField (d : ℕ) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) : Homogenization.RegCoeffField d :=
  aux_annealed_limit_response_transport_scalarRegCoeffField
    (aux_in_moments_response_moment_cutoffField model N omega)

/-- The unrescaled cutoff field is a.e.-measurable in the carrier sigma algebra. -/
private theorem cor_37_regField_aemeasurable (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    AEMeasurable (cor_37_regField d model N) (chaosSampleLaw model).toMeasure :=
  aux_annealed_limit_response_transport_measurable_scalarRegCoeffField.comp_aemeasurable
    (cor_37_cutoffField_aemeasurable d model N)

/-- The Chapter 4 local-ellipticity event is measurable in the carrier. -/
private theorem cor_37_measurableSet_elliptic (d : ℕ) :
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

/-- The pushforward of the common-scale law under the unrescaled cutoff field is
a Chapter 4 law carrier. -/
private theorem cor_37_lawCarrier (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Homogenization.Book.Ch04.RestrictionLawCarrier
      (Measure.map (cor_37_regField d model N) (chaosSampleLaw model).toMeasure) := by
  haveI : IsProbabilityMeasure
      (Measure.map (cor_37_regField d model N) (chaosSampleLaw model).toMeasure) :=
    inferInstance
  refine Homogenization.Book.Ch04.lawCarrier_of_aeLocallyUniformlyElliptic ?_
  rw [Homogenization.Book.Ch04.AELocallyUniformlyEllipticLaw,
    ae_map_iff (cor_37_regField_aemeasurable d model N) (cor_37_measurableSet_elliptic d)]
  exact Filter.Eventually.of_forall fun omega =>
    aux_annealed_limit_response_transport_scalarRegCoeffField_elliptic _
      (fun x => SubdiffusiveProcess.Lane4.cutoffCoefficient_pos model
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x)

/-- The actual cutoff response on the cube of side `3^k` is a.e.-measurable in
the disorder. -/
private theorem cor_37_responseJ_aemeasurable (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ)
    (p q : Homogenization.Vec d) :
    AEMeasurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
        (cor_37_scalar_data d model N k omega).toCoeffOn p q)
      (chaosSampleLaw model).toMeasure := by
  have hJ := ((cor_37_lawCarrier d model N).aemeasurable_ResponseJ_cubeSet
    (Homogenization.originCube d (k : ℤ)) p q).comp_aemeasurable
      (cor_37_regField_aemeasurable d model N)
  refine hJ.congr (Filter.Eventually.of_forall fun omega => ?_)
  simp only [Function.comp_apply]
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ,
    Homogenization.responseJ_cubeSet_eq_openCubeSet_of_triadicCube]
  rfl

/-- The maximizing property of the moment family transfers to the concrete
scalar coefficient. -/
private theorem cor_37_isGreatest_scalar (d : ℕ)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hfamily : ∀ (N : ℕ) (omega : BilateralField d)
        (Q : Homogenization.TriadicCube d),
      ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
        ((family N omega).coeffOn Q).toCoeffField x =
          Homogenization.scalarMatrix
            (cutoffCoefficient model
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x))
    (N k : ℕ) (omega : BilateralField d) (r : ℝ)
    (h : IsGreatest {v : ℝ | ∃ e : Fin d → ℝ, (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = Homogenization.Book.Ch02.responseJ
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)))
          ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ))) e e} r) :
    IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 ∧
        t = Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
          (cor_37_scalar_data d model N k omega).toCoeffOn e e} r := by
  have hnorm (e : Homogenization.Vec d) :
      Homogenization.vecNormSq e = ∑ i : Fin d, e i ^ 2 := by
    simp [Homogenization.vecNormSq, Homogenization.vecDot, sq]
  have hset : {t : ℝ | ∃ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 ∧
        t = Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
          (cor_37_scalar_data d model N k omega).toCoeffOn e e} =
      {v : ℝ | ∃ e : Fin d → ℝ, (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = Homogenization.Book.Ch02.responseJ
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)))
          ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ))) e e} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, (hnorm e).symm.trans he,
        (cor_37_family_responseJ_eq d model family hfamily N k omega e e).symm⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, (hnorm e).trans he,
        cor_37_family_responseJ_eq d model family hfamily N k omega e e⟩
  rw [hset]
  exact h

/-- The abstract calibration core: a pointwise square-root deviation bound
and uniformly small mean response give small mean absolute error. -/
private theorem cor_37_unit_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (J err : ℕ → ℕ → Ω → ℝ)
    (hJint : ∀ N k, Integrable (J N k) μ) (hJn : ∀ N k x, 0 ≤ J N k x)
    (hJsmall : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
      ∫ x, J N k x ∂μ ≤ eps)
    (herr : ∀ N k, AEStronglyMeasurable (err N k) μ)
    (hsq : ∀ N k x, err N k x ^ 2 ≤ C * J N k x * (1 + J N k x)) :
    ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
      ∫ x, |err N k x| ∂μ ≤ eps := by
  intro eps heps
  obtain ⟨δ, hδ, hsmall⟩ := cor_37_sqrt_response_small C hC eps heps
  obtain ⟨k0, hk0⟩ := hJsmall δ hδ
  refine ⟨k0, fun k hk N => ?_⟩
  obtain ⟨_, hbound⟩ := cor_37_calibration_cs μ (J N k) (err N k) (hJint N k)
    (Filter.Eventually.of_forall (hJn N k)) (herr N k) C hC
    (Filter.Eventually.of_forall (hsq N k))
  exact hbound.trans (hsmall _ (integral_nonneg (hJn N k)) (hk0 k hk N))



private theorem cor_37_affine_response_eq_sigma_domain {d : ℕ}
    (Om : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (U : Homogenization.Book.Ch02.Domain d)
    (hUOm : (U : Set (Homogenization.Vec d)) = (Om : Set (SpatialCoordinates d)))
    (hOm : Bornology.IsBounded (Om : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Om) w‖)
    (a : SpatialCoordinates d → ℝ)
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (aP : PositiveCoefficient Om)
    (haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) :
    affineDirichletResponse hOm hP aP p /
        volume.real (Om : Set (SpatialCoordinates d)) =
      Homogenization.vecDot p
        (Homogenization.matVecMul
          (Homogenization.Book.Ch02.sigmaCoarse U data.toCoeffOn) p) := by
  obtain ⟨S, hdom, hne⟩ := U
  change S = (Om : Set (SpatialCoordinates d)) at hUOm
  subst hUOm
  exact cor_37_affine_response_eq_sigma Om hdom hne hOm hP a data aP haP
    data.toCoeffOn Filter.EventuallyEq.rfl hvol p

/-- The project's normalized positive cutoff coefficient is the cutoff
coefficient almost everywhere on the open cube. -/
private theorem cor_37_positive_coefficient_ae (d : ℕ)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ)
    (omega : BilateralField d) :
    ((Lane4.cutoffPositiveCoefficient model
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N 0
        (pow_pos (by norm_num : (0 : ℝ) < 3) k)).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (by norm_num) k) : Set (SpatialCoordinates d))]
      cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ k := pow_pos (by norm_num) k
  letI : Fact ((centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k) hr :
      Set (SpatialCoordinates d)) ⊆
      (↑(closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k) hr) :
        Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube 0 hr⟩
  filter_upwards [normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k) hr)
    (closedCube 0 ((3 : ℝ) ^ k) hr)
    (Lane4.cutoffCoefficientCM model (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
      omega N 0 hr)
    (Lane4.cutoffCoefficientCM_pos model (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
      omega N 0 hr) 1 one_pos,
    ae_restrict_mem (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k) hr).isOpen.measurableSet]
    with x hx hxQ
  have h := hx hxQ
  change (normalizedContinuousPositiveCoefficient
      (closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k) hr)
      (Lane4.cutoffCoefficientCM model (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        omega N 0 hr)
      (Lane4.cutoffCoefficientCM_pos model (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        omega N 0 hr) 1 one_pos).val x = _
  rw [h]
  simp [Lane4.cutoffCoefficientCM]

/-- Quadratic scaling of a nonzero slope to a unit direction. -/
private theorem cor_37_quadratic_scaling {d : ℕ} (M : Homogenization.Mat d)
    (p : Homogenization.Vec d) (s : ℝ) (hs_def : s = ∑ i, p i ^ 2) (hs : 0 < s) :
    Homogenization.vecNormSq ((Real.sqrt s)⁻¹ • p) = 1 ∧
      Homogenization.vecDot p (Homogenization.matVecMul M p) - s =
        s * (Homogenization.vecDot ((Real.sqrt s)⁻¹ • p)
          (Homogenization.matVecMul M ((Real.sqrt s)⁻¹ • p)) - 1) := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hrr : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hpp : Homogenization.vecDot p p = s := by
    rw [hs_def]
    simp [Homogenization.vecDot, sq]
  constructor
  · change Homogenization.vecDot ((Real.sqrt s)⁻¹ • p) ((Real.sqrt s)⁻¹ • p) = 1
    rw [Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right, hpp,
      ← mul_assoc, ← mul_inv, hrr, inv_mul_cancel₀ hs.ne']
  · rw [Homogenization.matVecMul_smul, Homogenization.vecDot_smul_left,
      Homogenization.vecDot_smul_right]
    have hinv : s * ((Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹) = 1 := by
      rw [← mul_inv, hrr, mul_inv_cancel₀ hs.ne']
    calc Homogenization.vecDot p (Homogenization.matVecMul M p) - s =
        s * ((Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹) *
          Homogenization.vecDot p (Homogenization.matVecMul M p) - s := by
            rw [hinv, one_mul]
      _ = _ := by ring

/-- An `L^{128 d}` bound on a probability space gives integrability. -/
private theorem cor_37_integrable_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (J : Ω → ℝ) (hmeas : AEStronglyMeasurable J μ) (B : ℝ)
    (hB : eLpNorm J (ENNReal.ofReal ((128 * d : ℕ) : ℝ)) μ ≤ ENNReal.ofReal B) :
    Integrable J μ := by
  have hmem : MemLp J (ENNReal.ofReal ((128 * d : ℕ) : ℝ)) μ :=
    lt_of_le_of_lt hB ENNReal.ofReal_lt_top
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((128 * d : ℕ) : ℝ) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h1d : (1 : ℕ) ≤ 128 * d := by omega
    exact_mod_cast h1d
  exact memLp_one_iff_integrable.mp (hmem.mono_exponent h1)

/-- The mean maximal unit response is small uniformly in the cutoff. -/
private theorem cor_37_mean_small (d : ℕ) [NeZero d] (hJ : in_J d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Jsup : ℕ → ℕ → BilateralField d → ℝ)
    (hG : ∀ N k omega, IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
      Homogenization.vecNormSq e = 1 ∧
      t = Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
        (cor_37_scalar_data d model N k omega).toCoeffOn e e} (Jsup N k omega))
    (hJint : ∀ N k, Integrable (Jsup N k) (chaosSampleLaw model).toMeasure)
    (hsmall : ∀ e : Fin d → ℝ, (∑ i, e i ^ 2) = 1 →
      ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
        |∫ omega, Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
          (cor_37_scalar_data d model N k omega).toCoeffOn e e
            ∂(chaosSampleLaw model).toMeasure| ≤ eps) :
    ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
      ∫ omega, Jsup N k omega ∂(chaosSampleLaw model).toMeasure ≤ eps := by
  have hunit : ∀ i : Fin d,
      Homogenization.vecNormSq (Pi.single i (1 : ℝ) : Homogenization.Vec d) = 1 := by
    intro i
    simp [Homogenization.vecNormSq, Homogenization.vecDot, Pi.single_apply]
  have hunit' : ∀ i : Fin d,
      (∑ j : Fin d, (Pi.single i (1 : ℝ) : Fin d → ℝ) j ^ 2) = 1 := by
    intro i
    simp [Pi.single_apply]
  have hRint : ∀ N k (e : Homogenization.Vec d), Homogenization.vecNormSq e = 1 →
      Integrable (fun omega => Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
        (cor_37_scalar_data d model N k omega).toCoeffOn e e)
        (chaosSampleLaw model).toMeasure := by
    intro N k e he
    refine (hJint N k).mono'
      (cor_37_responseJ_aemeasurable d model N k e e).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun omega => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Homogenization.Book.Ch02.responseJ_nonneg _ _ e e)]
    exact (hG N k omega).2 ⟨e, he, rfl⟩
  have hbasis := cor_37_basis_sum_eventually_small d
    (fun k N i => ∫ omega, Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
      (cor_37_scalar_data d model N k omega).toCoeffOn (Pi.single i 1) (Pi.single i 1)
        ∂(chaosSampleLaw model).toMeasure)
    (fun i eps heps => hsmall (Pi.single i 1) (hunit' i) eps heps)
  intro eps heps
  obtain ⟨k0, hk0⟩ := hbasis eps heps
  refine ⟨k0, fun k hk N => ?_⟩
  calc
    ∫ omega, Jsup N k omega ∂(chaosSampleLaw model).toMeasure ≤
        ∫ omega, ∑ i : Fin d, Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
          (cor_37_scalar_data d model N k omega).toCoeffOn (Pi.single i 1)
            (Pi.single i 1) ∂(chaosSampleLaw model).toMeasure :=
      integral_mono (hJint N k)
        (integrable_finset_sum _ fun i _ => hRint N k _ (hunit i))
        (fun omega => cor_37_Jmax_le_basis_sum d hJ _ _
          (cor_37_scalar_data d model N k omega).isSymmetric _ (hG N k omega))
    _ = ∑ i : Fin d, ∫ omega, Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
          (cor_37_scalar_data d model N k omega).toCoeffOn (Pi.single i 1)
            (Pi.single i 1) ∂(chaosSampleLaw model).toMeasure :=
      integral_finset_sum _ fun i _ => hRint N k _ (hunit i)
    _ ≤ ∑ i : Fin d, |∫ omega, Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
          (cor_37_scalar_data d model N k omega).toCoeffOn (Pi.single i 1)
            (Pi.single i 1) ∂(chaosSampleLaw model).toMeasure| :=
      Finset.sum_le_sum fun i _ => le_abs_self _
    _ ≤ eps := hk0 k hk N

/-- Calibration of the coarse matrix in every unit direction. -/
private theorem cor_37_unit_small (d : ℕ) [NeZero d] (hJ : in_J d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Jsup : ℕ → ℕ → BilateralField d → ℝ)
    (hG : ∀ N k omega, IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
      Homogenization.vecNormSq e = 1 ∧
      t = Homogenization.Book.Ch02.responseJ (cor_37_domain d k)
        (cor_37_scalar_data d model N k omega).toCoeffOn e e} (Jsup N k omega))
    (hJint : ∀ N k, Integrable (Jsup N k) (chaosSampleLaw model).toMeasure)
    (hJsmall : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
      ∫ omega, Jsup N k omega ∂(chaosSampleLaw model).toMeasure ≤ eps) :
    ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
      ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
        ∫ omega, |Homogenization.vecDot e (Homogenization.matVecMul
          (Homogenization.Book.Ch02.sigmaCoarse (cor_37_domain d k)
            (cor_37_scalar_data d model N k omega).toCoeffOn) e) - 1|
          ∂(chaosSampleLaw model).toMeasure ≤ eps := by
  have hdev0 := cor_37_deviation_at_one d hJ
  rcases hdev0 with ⟨Cdev, hCdev, hdev⟩
  have hJn : ∀ N k omega, 0 ≤ Jsup N k omega := by
    intro N k omega
    obtain ⟨e, _, he⟩ := (hG N k omega).1
    rw [he]
    exact Homogenization.Book.Ch02.responseJ_nonneg _ _ e e
  have hsigma_meas : ∀ N k (e : Homogenization.Vec d), AEStronglyMeasurable
      (fun omega => Homogenization.vecDot e (Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaCoarse (cor_37_domain d k)
          (cor_37_scalar_data d model N k omega).toCoeffOn) e) - 1)
      (chaosSampleLaw model).toMeasure := by
    intro N k e
    refine (((cor_37_responseJ_aemeasurable d model N k e 0).const_mul 2).sub_const
      1).aestronglyMeasurable.congr (Filter.Eventually.of_forall fun omega => ?_)
    simp only
    rw [hJ.responseJ_split _ _ (cor_37_scalar_data d model N k omega).isSymmetric e 0]
    simp only [Homogenization.vecDot_zero_right, Homogenization.matVecMul_zero]
    ring
  intro e he
  exact cor_37_unit_core (chaosSampleLaw model).toMeasure Cdev hCdev.le Jsup
    (fun N k omega => Homogenization.vecDot e (Homogenization.matVecMul
      (Homogenization.Book.Ch02.sigmaCoarse (cor_37_domain d k)
        (cor_37_scalar_data d model N k omega).toCoeffOn) e) - 1)
    hJint hJn hJsmall (fun N k => hsigma_meas N k e)
    (fun N k omega => le_trans (le_add_of_nonneg_right (sq_nonneg _))
      (hdev (cor_37_domain d k) (cor_37_scalar_data d model N k omega).toCoeffOn
        (cor_37_scalar_data d model N k omega).isSymmetric (Jsup N k omega)
        (hG N k omega) e he))

/-- The actual centred cube of side `3^k` has positive finite volume. -/
private theorem cor_37_volume_pos (d k : ℕ) :
    0 < volume.real (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
      (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)) := by
  have hne : (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
      (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)).Nonempty := by
    rw [← cor_37_domain_set d k]
    exact (cor_37_domain d k).nonempty
  rw [measureReal_def]
  exact ENNReal.toReal_pos
    ((centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
      (pow_pos (by norm_num) k)).isOpen.measure_ne_zero volume hne)
    (centeredCube_isBounded 0 (pow_pos (by norm_num) k)).measure_lt_top.ne

/-- The normalized affine response is the coarse quadratic form on the cube. -/
private theorem cor_37_affine_pointwise (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k N : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
        ((3 : ℝ) ^ k) (pow_pos (by norm_num) k)),
      ‖(z : SobolevData (centeredCube (0 : SpatialCoordinates d)
        ((3 : ℝ) ^ k) (pow_pos (by norm_num) k))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
          ((3 : ℝ) ^ k) (pow_pos (by norm_num) k))) z‖)
    (omega : BilateralField d) (p : Fin d → ℝ) :
    affineDirichletResponse
        (centeredCube_isBounded 0 (pow_pos (by norm_num) k)) hPk
        (Lane4.cutoffPositiveCoefficient model
          (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N 0
          (pow_pos (by norm_num) k)) p /
        (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (by norm_num) k) : Set (SpatialCoordinates d))).toReal =
      Homogenization.vecDot p (Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaCoarse (cor_37_domain d k)
          (cor_37_scalar_data d model N k omega).toCoeffOn) p) :=
  cor_37_affine_response_eq_sigma_domain _ (cor_37_domain d k)
    (cor_37_domain_set d k) _ hPk _ (cor_37_scalar_data d model N k omega) _
    (cor_37_positive_coefficient_ae d model N k omega) (cor_37_volume_pos d k) p

/-- Every slope, including zero, is recovered from the unit directions. -/
private theorem cor_37_slope_abstract {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → ℕ → Ω → ℝ) (σ : ℕ → ℕ → Ω → Homogenization.Mat d)
    (p : Fin d → ℝ)
    (hF : ∀ k N x, F k N x =
      Homogenization.vecDot p (Homogenization.matVecMul (σ k N x) p))
    (hunit_small : ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
      ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
        ∫ x, |Homogenization.vecDot e (Homogenization.matVecMul (σ k N x) e) - 1| ∂μ ≤ eps)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
      ∫ x, |F k N x - ∑ i : Fin d, p i ^ 2| ∂μ ≤ eps := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = ∑ i, p i ^ 2 := ⟨_, rfl⟩
  rw [← hs_def]
  simp_rw [hF]
  by_cases hs0 : s = 0
  · have hp : p = 0 := by
      funext i
      have hsum : ∑ j, p j ^ 2 = 0 := hs_def ▸ hs0
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (p j))).mp hsum i (Finset.mem_univ i)
      simpa using hi
    subst hp
    refine ⟨0, fun k _ N => ?_⟩
    simp only [Homogenization.vecDot_zero_left, hs0, sub_zero, abs_zero, integral_zero]
    exact heps.le
  · have hs : 0 < s := lt_of_le_of_ne
      (hs_def ▸ Finset.sum_nonneg fun i _ => sq_nonneg (p i)) (Ne.symm hs0)
    have he := (cor_37_quadratic_scaling 0 p s hs_def hs).1
    obtain ⟨k0, hk0⟩ := hunit_small _ he (eps / s) (div_pos heps hs)
    refine ⟨k0, fun k hk N => ?_⟩
    have hscale : ∀ x : Ω,
        |Homogenization.vecDot p (Homogenization.matVecMul (σ k N x) p) - s| =
          s * |Homogenization.vecDot ((Real.sqrt s)⁻¹ • p)
            (Homogenization.matVecMul (σ k N x) ((Real.sqrt s)⁻¹ • p)) - 1| := by
      intro x
      rw [(cor_37_quadratic_scaling (σ k N x) p s hs_def hs).2, abs_mul, abs_of_pos hs]
    simp only [hscale]
    rw [integral_const_mul]
    calc
      s * ∫ x, |Homogenization.vecDot ((Real.sqrt s)⁻¹ • p)
            (Homogenization.matVecMul (σ k N x) ((Real.sqrt s)⁻¹ • p)) - 1| ∂μ ≤
          s * (eps / s) := mul_le_mul_of_nonneg_left (hk0 k hk N) hs.le
      _ = eps := by field_simp




theorem cor_37
    (d : ℕ) (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
        let Q : ℕ → Opens (SpatialCoordinates d) :=
          fun k => centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
            (pow_pos (by norm_num) k)
        ∀ hP : ∀ k : ℕ, ∃ K : ℝ≥0, ∀ z : killedSobolevGraph (Q k),
          ‖(z : SobolevData (Q k)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (Q k)) z‖,
          ∀ p : Fin d → ℝ, ∀ eps : ℝ, 0 < eps →
            ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
              (∫ omega,
                |affineDirichletResponse
                    (centeredCube_isBounded 0 (pow_pos (by norm_num) k))
                    (hP k)
                    (Lane4.cutoffPositiveCoefficient model
                      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N 0
                      (pow_pos (by norm_num) k)) p /
                    (volume (Q k : Set (SpatialCoordinates d))).toReal -
                    ∑ i : Fin d, p i ^ 2|
                ∂(chaosSampleLaw model).toMeasure) ≤ eps := by
  haveI : NeZero d := ⟨by omega⟩
  have hEta0 := thm_eta d hd hJ
  rcases hEta0 with ⟨dEta, hdEta, hEta⟩
  have hMom0 := in_moments d hd hJ
  rcases hMom0 with ⟨Cc, _hCc, hMomAll⟩
  have hMom1 := hMomAll (128 * d) ⟨64 * d, by ring⟩ le_rfl
  rcases hMom1 with ⟨dMom, hdMom, hMom⟩
  refine ⟨min dEta dMom, lt_min hdEta hdMom, ?_⟩
  intro _ _ model hmodel Q hP p eps heps
  have hMomM := hMom model (hmodel.trans (min_le_right _ _))
  rcases hMomM with ⟨family, Jsup, _hxi, hfamily, hGreat, hJmeas, hJLp, _, _⟩
  have hEtaM := hEta model (hmodel.trans (min_le_left _ _))
    (fun k => cor_37_domain d k) (cor_37_domain_set d)
    (fun N k omega => (cor_37_scalar_data d model N k omega).toCoeffOn)
    (cor_37_scalar_data_field d model)
  rcases hEtaM with ⟨_Fk, _, _, hsmall, _hTraceInt, _hJInt⟩
  have hG := fun N k omega =>
    cor_37_isGreatest_scalar d model family hfamily N k omega _ (hGreat N k omega)
  have hJint : ∀ N k, Integrable (Jsup N k) (chaosSampleLaw model).toMeasure :=
    fun N k => cor_37_integrable_of_eLpNorm _ d (by omega) _ (hJmeas N k) _ (hJLp N k)
  have hJsmall := cor_37_mean_small d hJ model Jsup hG hJint hsmall
  have hunit_small := cor_37_unit_small d hJ model Jsup hG hJint hJsmall
  exact cor_37_slope_abstract (chaosSampleLaw model).toMeasure _ _ p
    (fun k N omega => cor_37_affine_pointwise d model k N (hP k) omega p)
    hunit_small eps heps

end Paper
