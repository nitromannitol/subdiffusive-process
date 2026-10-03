module

public import SubdiffusiveProcess.Paper.in_moments
public import SubdiffusiveProcess.Paper.stationary_family
public import SubdiffusiveProcess.Paper.stationary_defects
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.lem_fmono_annealed_subadditivity
public import Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs
public import Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Book.Ch02.Matrices
public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.Probability.ProductLpContraction
public import SubdiffusiveProcess.CoarseGrainingVocab.DeltaLogSquaredTail
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace Paper

lemma aux_lem_fmono_uniform_bound_threshold (Cc : ℝ) (hCc : 0 < Cc)
    (xi : ℕ) (hxi : 0 < xi) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        (xi : ℝ) ≤ Cc⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹ := by
  have hprodpos : 0 < Cc * (xi : ℝ) := mul_pos hCc (by exact_mod_cast hxi)
  obtain ⟨delta0, hdelta0, hdelta0lt, hsmall⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.exists_smallDelta_mul_abs_log_le
      (eps := (Cc * (xi : ℝ))⁻¹) (inv_pos.mpr hprodpos)
  refine ⟨delta0, hdelta0, ?_⟩
  intro delta hdelta hle
  have hdelta1 : delta ≤ 1 := le_trans hle (le_of_lt hdelta0lt)
  have hdeltalt1 : delta < 1 := lt_of_le_of_lt hle hdelta0lt
  have hlog : Real.log delta ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one hdelta (ne_of_lt hdeltalt1)
  have habspos : 0 < |Real.log delta| := abs_pos.mpr hlog
  have hsmall' : delta * |Real.log delta| ≤ (Cc * (xi : ℝ))⁻¹ :=
    hsmall delta hdelta hle
  have hscaled : Cc * (xi : ℝ) * (delta * |Real.log delta|) ≤ 1 := by
    calc
      Cc * (xi : ℝ) * (delta * |Real.log delta|) ≤
          Cc * (xi : ℝ) * (Cc * (xi : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hsmall' (le_of_lt hprodpos)
      _ = 1 := by field_simp
  have hmain : Cc * (xi : ℝ) * (delta ^ 2 * |Real.log delta|) ≤ 1 := by
    calc
      Cc * (xi : ℝ) * (delta ^ 2 * |Real.log delta|) =
          Cc * (xi : ℝ) * (delta * (delta * |Real.log delta|)) := by ring
      _ ≤ Cc * (xi : ℝ) * (1 * (delta * |Real.log delta|)) := by
        gcongr
      _ = Cc * (xi : ℝ) * (delta * |Real.log delta|) := by ring
      _ ≤ 1 := hscaled
  have hdenpos : 0 < Cc * (delta ^ 2 * |Real.log delta|) := by
    positivity
  have hdiv : (xi : ℝ) ≤ 1 / (Cc * (delta ^ 2 * |Real.log delta|)) := by
    apply (le_div_iff₀ hdenpos).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  calc
    (xi : ℝ) ≤ 1 / (Cc * (delta ^ 2 * |Real.log delta|)) := hdiv
    _ = Cc⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹ := by
      field_simp

lemma aux_lem_fmono_uniform_bound_trace_integral
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (P R : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hP : ∀ i j, Integrable (fun ω => P ω i j) μ)
    (hR : ∀ i j, Integrable (fun ω => R ω i j) μ) :
    Matrix.trace
        ((fun i j => ∫ ω, P ω i j ∂μ) + (fun i j => ∫ ω, R ω i j ∂μ) -
          2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2 =
      (1 / 2 : ℝ) * ∫ ω,
        Matrix.trace (P ω + R ω - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂μ := by
  have hdiag (A B : Matrix (Fin d) (Fin d) ℝ) :
      Matrix.trace (A + B - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) =
        ∑ i : Fin d, (A i i + B i i - 2) := by
    rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
    simp only [Matrix.trace, Matrix.diag, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
    ring
  have hleft : Matrix.trace
      ((fun i j => ∫ ω, P ω i j ∂μ) + (fun i j => ∫ ω, R ω i j ∂μ) -
        2 • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      ∑ i : Fin d, ((∫ ω, P ω i i ∂μ) + (∫ ω, R ω i i ∂μ) - 2) := by
    simpa only using! hdiag (fun i j => ∫ ω, P ω i j ∂μ)
      (fun i j => ∫ ω, R ω i j ∂μ)
  rw [hleft]
  simp_rw [hdiag]
  rw [integral_finset_sum]
  · rw [div_eq_mul_inv, one_div, mul_comm (2⁻¹ : ℝ)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hInt : (∫ ω, P ω i i + R ω i i - 2 ∂μ) =
        (∫ ω, P ω i i ∂μ) + (∫ ω, R ω i i ∂μ) - 2 := by
      calc
        _ = (∫ ω, P ω i i + R ω i i ∂μ) - ∫ _ : Ω, (2 : ℝ) ∂μ := by
          simpa only using! integral_sub ((hP i i).add (hR i i))
            (integrable_const (2 : ℝ))
        _ = _ := by rw [integral_add (hP i i) (hR i i)]; simp
    exact hInt.symm
  · intro i hi
    simpa using! ((hP i i).add (hR i i)).sub (integrable_const (2 : ℝ))

lemma aux_lem_fmono_uniform_bound_quad_integrable
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, Integrable (fun ω => M ω i j) μ)
    (p q : Fin d → ℝ) :
    Integrable (fun ω => Homogenization.vecDot p
      (Homogenization.matVecMul (M ω) q)) μ := by
  unfold Homogenization.vecDot Homogenization.matVecMul
  apply integrable_finset_sum
  intro i hi
  have hinner : Integrable (fun a => ∑ j, M a i j * q j) μ := by
    apply integrable_finset_sum
    intro j hj
    exact (hM i j).mul_const (q j)
  exact hinner.const_mul (p i)



theorem lem_fmono_uniform_bound (d : ℕ) (hd : 2 ≤ d)
    (hJ : Paper.in_J d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
          ∀ (family : ℕ → BilateralField d → TriadicCoeffFamily d),
            (∀ (N : ℕ) (ω : BilateralField d) (Q : TriadicCube d),
              ∀ᵐ x ∂volume.restrict (openCubeSet Q),
                ((family N ω).coeffOn Q).toCoeffField x =
                  scalarMatrix
                    (cutoffCoefficient model
                      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x)) →
              let Qk : ℕ → TriadicCube d := fun k => originCube d (k : ℤ)
              let Pmat : ℕ → ℕ → BilateralField d →
                  Matrix (Fin d) (Fin d) ℝ :=
                fun N k ω =>
                  Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (Qk k))
                    ((family N ω).coeffOn (Qk k))
              let Rmat : ℕ → ℕ → BilateralField d →
                  Matrix (Fin d) (Fin d) ℝ :=
                fun N k ω =>
                  Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (Qk k))
                    ((family N ω).coeffOn (Qk k))
              let EP : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
                fun N k i j =>
                  ∫ ω, Pmat N k ω i j ∂(chaosSampleLaw model).toMeasure
              let ER : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
                fun N k i j =>
                  ∫ ω, Rmat N k ω i j ∂(chaosSampleLaw model).toMeasure
              let f : ℕ → ℕ → ℝ :=
                fun N k =>
                  Matrix.trace
                      (EP N k + ER N k -
                        2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2
              ∀ (N k : ℕ), f N k ≤ C * model.delta ^ 2 := by
  have hxi : 0 < 128 * d := by omega
  have hxi_even : Even (128 * d) := by
    refine ⟨64 * d, by omega⟩
  obtain ⟨Cc, hCc, hmoment0⟩ := in_moments d hd hJ
  obtain ⟨disorderRaw, hdisorderRaw, hmoment⟩ :=
    hmoment0 (128 * d) hxi_even (by rfl)
  obtain ⟨deltaCal, hdeltaCal, hdeltaCal_spec⟩ :=
    aux_lem_fmono_uniform_bound_threshold Cc hCc (128 * d) hxi
  let delta0 := min disorderRaw deltaCal
  have hdelta0 : 0 < delta0 := lt_min hdisorderRaw hdeltaCal
  have hC : 0 < (d : ℝ) * Cc * (128 * d : ℝ) * Real.log (2 + (128 * d : ℝ)) := by
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hlog : 0 < Real.log (2 + (128 * d : ℝ)) := by
      apply Real.log_pos
      nlinarith
    positivity
  refine ⟨delta0, hdelta0, (d : ℝ) * Cc * (128 * d : ℝ) * Real.log (2 + (128 * d : ℝ)), hC, ?_⟩
  intro _ _ model hmodel family hfamily
  dsimp
  let Qk : ℕ → TriadicCube d := fun k => originCube d (k : ℤ)
  let Pmat : ℕ → ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ :=
    fun N k ω => Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (Qk k))
      ((family N ω).coeffOn (Qk k))
  let Rmat : ℕ → ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ :=
    fun N k ω => Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (Qk k))
      ((family N ω).coeffOn (Qk k))
  let EP : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
    fun N k i j => ∫ ω, Pmat N k ω i j ∂(chaosSampleLaw model).toMeasure
  let ER : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
    fun N k i j => ∫ ω, Rmat N k ω i j ∂(chaosSampleLaw model).toMeasure
  let f : ℕ → ℕ → ℝ :=
    fun N k => Matrix.trace (EP N k + ER N k - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2
  change ∀ N k, f N k ≤
    ((d : ℝ) * Cc * (128 * d : ℝ) * Real.log (2 + (128 * d : ℝ))) * model.delta ^ 2
  have hmodelRaw : model.delta ≤ disorderRaw :=
    le_trans hmodel (min_le_left _ _)
  have hmodelCal : model.delta ≤ deltaCal :=
    le_trans hmodel (min_le_right _ _)
  have hmodelpos : 0 < model.delta := model.shellPrefix.delta_pos
  have hcond : (128 * d : ℝ) ≤ Cc⁻¹ * (model.delta ^ 2)⁻¹ *
      |Real.log model.delta|⁻¹ :=
    by simpa using hdeltaCal_spec model.delta hmodelpos hmodelCal
  obtain ⟨family0, Jsup, hxi_cond, hfamily0, hJsup_greatest, hJsup_meas, hJsup_lp,
      _hEll, _hgood⟩ := hmoment model hmodelRaw
  have hsub := lem_fmono_annealed_subadditivity d hd model family hfamily
  have hPint : ∀ N k i j, Integrable (fun ω => Pmat N k ω i j)
      (chaosSampleLaw model).toMeasure := by
    simpa [Pmat] using fun N k i j => (hsub.1 N k i j).1
  have hRint : ∀ N k i j, Integrable (fun ω => Rmat N k ω i j)
      (chaosSampleLaw model).toMeasure := by
    simpa [Rmat] using fun N k i j => (hsub.1 N k i j).2
  intro N k
  let μ := (chaosSampleLaw model).toMeasure
  have hxi_real : (1 : ℝ) ≤ (128 * d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    norm_num
    nlinarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (128 * d : ℝ) := by
    exact ENNReal.one_le_ofReal.mpr hxi_real
  have hJsup_memLp : MemLp (Jsup N k) (ENNReal.ofReal (128 * d : ℝ)) μ := by
    change eLpNorm (Jsup N k) (ENNReal.ofReal (128 * d : ℝ)) μ < ⊤
    simpa [μ] using lt_of_le_of_lt (hJsup_lp N k) ENNReal.ofReal_lt_top
  have hJsup_int : Integrable (Jsup N k) μ :=
    hJsup_memLp.integrable hp1
  let B : ℝ := Cc * (128 * d : ℝ) * Real.log (2 + (128 * d : ℝ)) *
    model.delta ^ 2
  have hBpos : 0 < B := by
    dsimp [B]
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hlog : 0 < Real.log (2 + (128 * d : ℝ)) := by
      apply Real.log_pos
      nlinarith
    positivity
  have hJsup_int_bound : ∫ ω, Jsup N k ω ∂μ ≤ B := by
    have hnorm := SubdiffusiveProcess.enorm_integral_le_eLpNorm
      (μ := μ) (p := ENNReal.ofReal (128 * d : ℝ)) hp1 (hJsup_meas N k)
    have hnorm' : ENNReal.ofReal |∫ ω, Jsup N k ω ∂μ| ≤ ENNReal.ofReal B := by
      calc
        ENNReal.ofReal |∫ ω, Jsup N k ω ∂μ| =
            ‖∫ ω, Jsup N k ω ∂μ‖ₑ := by
              simp only [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        _ ≤ eLpNorm (Jsup N k) (ENNReal.ofReal (128 * d : ℝ)) μ := hnorm
        _ ≤ ENNReal.ofReal B := by
          simpa [B, μ] using hJsup_lp N k
    have habs : |∫ ω, Jsup N k ω ∂μ| ≤ B :=
      (ENNReal.ofReal_le_ofReal_iff hBpos.le).mp hnorm'
    exact (le_abs_self _).trans habs
  have hresp_int : ∀ (e : Fin d → ℝ),
      Integrable
        (fun ω' => Homogenization.Book.Ch02.responseJ
          (cubeDomain (Qk k)) ((family N ω').coeffOn (Qk k)) e e) μ := by
    intro e
    have hsym : ∀ ω' : BilateralField d,
        Homogenization.Book.Ch02.CoeffOn.IsSymmetric
          ((family N ω').coeffOn (Qk k)) := by
      intro ω'
      change ∀ᵐ x ∂volume.restrict (openCubeSet (Qk k)),
        (((family N ω').coeffOn (Qk k)).toCoeffField x).IsSymm
      filter_upwards [hfamily N ω' (Qk k)] with x hx
      rw [hx]
      exact Homogenization.scalarMatrix_isSymm _
    have hquadP := aux_lem_fmono_uniform_bound_quad_integrable μ
      (fun ω' => Pmat N k ω') (fun i j => hPint N k i j) e e
    have hquadR := aux_lem_fmono_uniform_bound_quad_integrable μ
      (fun ω' => Rmat N k ω') (fun i j => hRint N k i j) e e
    have hsum : Integrable
        (fun ω' =>
          (1 / 2 : ℝ) * Homogenization.vecDot e
              (Homogenization.matVecMul (Pmat N k ω') e) +
          (1 / 2 : ℝ) * Homogenization.vecDot e
              (Homogenization.matVecMul (Rmat N k ω') e) -
          Homogenization.vecDot e e) μ := by
      exact ((hquadP.const_mul (1 / 2 : ℝ)).add
        (hquadR.const_mul (1 / 2 : ℝ))).sub (integrable_const _)
    have hactual : Integrable
        (fun ω' => Homogenization.Book.Ch02.responseJ
          (cubeDomain (Qk k)) ((family N ω').coeffOn (Qk k)) e e) μ := by
      apply hsum.congr
      filter_upwards [] with ω'
      symm
      exact hJ.responseJ_split (cubeDomain (Qk k))
        ((family N ω').coeffOn (Qk k)) (hsym ω') e e
    exact hactual
  have hJsup_le_response : ∀ (e : Fin d → ℝ),
      (∑ i : Fin d, e i ^ 2) = 1 →
      ∀ ω : BilateralField d,
        Homogenization.Book.Ch02.responseJ (cubeDomain (Qk k))
          ((family N ω).coeffOn (Qk k)) e e ≤ Jsup N k ω := by
    intro e he ω
    have haeeq : Homogenization.Book.Ch02.CoeffOn.AEEq
        ((family0 N ω).coeffOn (Qk k)) ((family N ω).coeffOn (Qk k)) := by
      change ((family0 N ω).coeffOn (Qk k)).toCoeffField =ᵐ[
        volume.restrict (openCubeSet (Qk k))]
        ((family N ω).coeffOn (Qk k)).toCoeffField
      filter_upwards [hfamily0 N ω (Qk k), hfamily N ω (Qk k)] with x hx0 hx
      rw [hx0, hx]
    calc
      Homogenization.Book.Ch02.responseJ (cubeDomain (Qk k))
          ((family N ω).coeffOn (Qk k)) e e =
          Homogenization.Book.Ch02.responseJ (cubeDomain (Qk k))
            ((family0 N ω).coeffOn (Qk k)) e e :=
        (Homogenization.Book.Ch02.responseJ_eq_ofAEEq haeeq e e).symm
      _ ≤ Jsup N k ω := (hJsup_greatest N k ω).2 ⟨e, he, rfl⟩
  have hstationary := stationary_family d hd model
  dsimp at hstationary
  let U : ℕ → Homogenization.Book.Ch02.Domain d := fun k => cubeDomain (Qk k)
  have hU : ∀ k, (U k : Set (Homogenization.Vec d)) =
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)) := by
    intro k
    dsimp [U]
    simpa [Qk] using
      (SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube
        (d := d) (k : ℤ)
        (by positivity : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ))).symm
  let a0 : (N' k' : ℕ) → BilateralField d →
      Homogenization.Book.Ch02.CoeffOn (U k') :=
    fun N' k' omega =>
      ((Classical.choice
        (SubdiffusiveProcess.Lane4.nonempty_cutoffTriadicData model
          (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N')).onCube
            (Qk k')).toCoeffOn
  have ha0 : ∀ N' k' omega x, (a0 N' k' omega).toCoeffField x =
      ((Real.exp (((N' : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N')⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N' + 1), omega (-(j : ℤ)) x)) •
        (1 : Homogenization.Mat d) := by
    intro N' k' omega x
    dsimp [a0]
    change scalarMatrix (cutoffCoefficient model
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N' x) = _
    rw [hstationary.1 N' omega x]
  have hcanon : ∀ omega : BilateralField d,
      Homogenization.Book.Ch02.CoeffOn.AEEq
        ((family N omega).coeffOn (Qk k)) (a0 N k omega) := by
    intro omega
    change ((family N omega).coeffOn (Qk k)).toCoeffField =ᵐ[
      volume.restrict (openCubeSet (Qk k))]
      (fun x => scalarMatrix (cutoffCoefficient model
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x))
    filter_upwards [hfamily N omega (Qk k)] with x hx
    exact hx
  have hdef := stationary_defects d hd model U hU a0 ha0 hJ
  dsimp at hdef
  have htrace := aux_lem_fmono_uniform_bound_trace_integral μ
    (fun omega => Pmat N k omega) (fun omega => Rmat N k omega)
    (fun i j => hPint N k i j) (fun i j => hRint N k i j)
  have hf_trace : f N k = (1 / 2 : ℝ) * ∫ omega,
      Matrix.trace (Pmat N k omega + Rmat N k omega -
        2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂μ := by
    simpa only [f, EP, ER, μ] using! htrace
  have htrace_ae : ∀ᵐ omega ∂μ, Matrix.trace
      (Pmat N k omega + Rmat N k omega -
        2 • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      Matrix.trace
        (Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) +
          Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) -
          2 • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    filter_upwards [] with omega
    have hc := hcanon omega
    have hp := Homogenization.Book.Ch02.sigmaCoarse_eq_ofAEEq hc
    have hr := Homogenization.Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hc
    simp only [Pmat, Rmat, U]
    rw [hp, hr]
  have htrace_eq : ∫ omega, Matrix.trace
      (Pmat N k omega + Rmat N k omega -
        2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂μ =
      ∫ omega, Matrix.trace
        (Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) +
          Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) -
          2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂μ :=
    integral_congr_ae htrace_ae
  have hresp_canon_int : ∀ e : Fin d → ℝ, Integrable
      (fun omega => Homogenization.Book.Ch02.responseJ (U k)
        (a0 N k omega) e e) μ := by
    intro e
    apply (hresp_int e).congr
    filter_upwards [] with omega
    exact Homogenization.Book.Ch02.responseJ_eq_ofAEEq (hcanon omega) e e
  have hcanon_le : ∀ (j : Fin d) (omega : BilateralField d),
      Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
          (Pi.single j 1) (Pi.single j 1) ≤ Jsup N k omega := by
    intro j omega
    calc
      Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
          (Pi.single j 1) (Pi.single j 1) =
          Homogenization.Book.Ch02.responseJ (cubeDomain (Qk k))
            ((family N omega).coeffOn (Qk k)) (Pi.single j 1) (Pi.single j 1) :=
        (Homogenization.Book.Ch02.responseJ_eq_ofAEEq (hcanon omega)
          (Pi.single j 1) (Pi.single j 1)).symm
      _ ≤ Jsup N k omega := hJsup_le_response (Pi.single j 1)
        (by classical simp [Pi.single_apply]) omega
  have hresp_integral_le : ∀ j : Fin d,
      ∫ omega, Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
          (Pi.single j 1) (Pi.single j 1) ∂μ ≤
        ∫ omega, Jsup N k omega ∂μ := by
    intro j
    apply integral_mono_ae (hresp_canon_int (Pi.single j 1)) hJsup_int
    filter_upwards [] with omega
    exact hcanon_le j omega
  have hsum_le : ∑ j : Fin d,
      ∫ omega, Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
          (Pi.single j 1) (Pi.single j 1) ∂μ ≤
      (d : ℝ) * ∫ omega, Jsup N k omega ∂μ := by
    calc
      _ ≤ ∑ _j : Fin d, ∫ omega, Jsup N k omega ∂μ :=
        Finset.sum_le_sum (fun j hj => hresp_integral_le j)
      _ = (d : ℝ) * ∫ omega, Jsup N k omega ∂μ := by simp
  calc
    f N k = (1 / 2 : ℝ) * ∫ omega, Matrix.trace
        (Pmat N k omega + Rmat N k omega -
          2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂μ := hf_trace
    _ = (1 / 2 : ℝ) * ∫ omega, Matrix.trace
        (Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) +
          Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) -
          2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂μ := by rw [htrace_eq]
    _ = ∑ j : Fin d, ∫ omega,
        Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
          (Pi.single j 1) (Pi.single j 1) ∂μ := hdef N k
    _ ≤ (d : ℝ) * ∫ omega, Jsup N k omega ∂μ := hsum_le
    _ ≤ (d : ℝ) * B := mul_le_mul_of_nonneg_left hJsup_int_bound (by positivity)
    _ = ((d : ℝ) * Cc * (128 * d : ℝ) * Real.log (2 + (128 * d : ℝ))) *
        model.delta ^ 2 := by simp [B]; ring

end Paper

