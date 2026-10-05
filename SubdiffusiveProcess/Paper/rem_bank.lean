module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.lem_compact_responses
public import SubdiffusiveProcess.Paper.lem_neumann_error
public import SubdiffusiveProcess.Paper.prop_neumann_growth
public import SubdiffusiveProcess.Paper.lem_layer_norms
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_15
public import SubdiffusiveProcess.Paper.rem_bank_response_moments
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal NNReal ContDiff
open TopologicalSpace
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

namespace SubdiffusiveProcess.Paper

/-! ### Moment and response helpers -/


theorem aux_rem_bank_dm_solves {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Ω,
      ‖(w : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) w‖)
    (a : PositiveCoefficient Ω) (b : weakSobolevGraph Ω) :
    SolvesDirichlet a (fun _ => 0) b (dirichletMinimizer (killedResponseSpace hP) a b) := by
  refine ⟨dirichletMinimizer_mem_affine (killedResponseSpace hP) a b, ?_⟩
  intro ψ
  rw [dirichletMinimizer_euler (killedResponseSpace hP) a b ψ]
  simp


theorem aux_rem_bank_rs_solves {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Ω,
      ‖(w : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) w‖)
    (a : PositiveCoefficient Ω) (f : SpatialCoordinates d → ℝ) (fL2 : DomainL2 Ω)
    (hf : ((fL2 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] f)) :
    SolvesDirichlet a f 0
      ⟨(responseSolution (killedResponseSpace hP) a
          ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) :
          SobolevData Ω),
        (killedResponseSpace hP).le_weak
          (responseSolution (killedResponseSpace hP) a
            ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL)).property⟩ := by
  let S := killedResponseSpace hP
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad fL2).comp S.space.subtypeL
  let us : S.space := responseSolution S a L
  refine ⟨?_, ?_⟩
  · change (us : SobolevData Ω) - (0 : SobolevData Ω) ∈ killedSobolevGraph Ω
    rw [sub_zero]
    exact us.2
  · intro ψ
    have h : sobolevCoefficientForm a (us : SobolevData Ω) (ψ : SobolevData Ω) =
        sobolevVolumeLoad fL2 (ψ : SobolevData Ω) :=
      responseSolution_spec S a L ψ
    change sobolevCoefficientForm a (us : SobolevData Ω) (ψ : SobolevData Ω) = _
    rw [h, sobolevVolumeLoad_apply]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    rw [hx]


theorem aux_rem_bank_abs_moment {X : Type} [MeasurableSpace X] (mu : Measure X)
    (K : X → ℝ) (e : ℝ≥0∞) (Cb : ℝ) (hK : MemLp K e mu)
    (hKb : eLpNorm K e mu ≤ ENNReal.ofReal Cb) :
    MemLp (fun x => |K x|) e mu ∧ eLpNorm (fun x => |K x|) e mu ≤ ENNReal.ofReal Cb := by
  have h1 := hK.norm
  have h2 := eLpNorm_norm (p := e) (μ := mu) K hK.aestronglyMeasurable
  simp only [Real.norm_eq_abs] at h1 h2
  exact ⟨h1, by rw [h2]; exact hKb⟩


theorem aux_rem_bank_coerc_abs {d : ℕ} (hd : 2 ≤ d)
    (a : PositiveCoefficient (unitNeumannCube d)) (K : ℝ)
    (hK : ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          (v : SobolevData (unitNeumannCube d)).1 ≤
        K * sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
          (v : SobolevData (unitNeumannCube d))) :
    0 ≤ |K| ∧ ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          (v : SobolevData (unitNeumannCube d)).1 ≤
        |K| * sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
          (v : SobolevData (unitNeumannCube d)) := by
  refine ⟨abs_nonneg K, fun v => (hK v).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_abs_self K) (sobolevCoefficientForm_nonneg a _)


theorem aux_rem_bank_source_bound {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ Kf : ℝ, 0 ≤ Kf ∧ AEMeasurable f volume ∧ ∀ x, |f x| ≤ Kf := by
  have hc := hf.continuous
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hfc
  refine ⟨max C 0, le_max_right _ _, hc.aemeasurable, fun x => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hC x).trans (le_max_left _ _)

/-! ### Moment and response helpers -/

/-- The normalized `L²` part of the `H^{3/4}` norm on the unit Neumann cube (volume `1`):
`‖v‖² ≤ ‖v‖²_{H^{3/4}(Q)}`.  (The seminorm part in `eq:mfd-1` is a square.) -/
theorem aux_rem_bank_unit_l2_sq_le_frac {d : ℕ} (hd : 2 ≤ d)
    (v : DomainL2 (unitNeumannCube d)) :
    ‖v‖ ^ 2 ≤
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder v := by
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm
  have hsum : (∑ i : Fin 1, ‖(fun _ => v) i‖ ^ 2) = ‖v‖ ^ 2 := by simp
  have hvol : volume.real (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) = 1 := by
    simpa using centeredCube_volume_real (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
  erw [hsum, hvol, div_one]
  have hsq : 0 ≤ cubeFractionalVecSeminormSq (k := 1) hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
      threeQuarterOrder (fun _ => v) := sq_nonneg _
  nlinarith

/-- The face-bump source `f_ε`  has an `L²(Q)` representative. -/
theorem aux_rem_bank_faceBump_rep {d : ℕ} (rho : ℝ → ℝ) (hrho : Continuous rho)
    (pvec : Fin d → ℝ) (eps : ℝ) :
    ∃ f0 : DomainL2 (unitNeumannCube d),
      ((f0 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
          faceBump rho pvec eps) := by
  set f := faceBump rho pvec eps with hf
  have hcont : Continuous f := aux_rem_resolved_faceBump_continuous rho hrho pvec eps
  have hmeas : AEStronglyMeasurable f
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    hcont.aestronglyMeasurable
  let B : Set (SpatialCoordinates d) := Metric.closedBall (fun _ => (1 / 2 : ℝ)) (1 / 2)
  have hclosed : IsCompact B := isCompact_closedBall (fun _ => (1 / 2 : ℝ)) (1 / 2)
  have hbound : ∃ C, ∀ x ∈ B, ‖f x‖ ≤ C :=
    hclosed.exists_bound_of_continuousOn hcont.continuousOn
  rcases hbound with ⟨C, hC⟩
  have hsubset : (unitNeumannCube d : Set (SpatialCoordinates d)) ⊆ B := by
    intro x hx
    have := centeredCube_subset_closedCube (fun _ : Fin d => (1 / 2 : ℝ)) one_pos hx
    exact this
  have hC' : ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ‖f x‖ ≤ C :=
    fun x hx => hC x (hsubset hx)
  have hmem : MemLp f 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hmeas C
      (ae_restrict_of_forall_mem (unitNeumannCube d).isOpen.measurableSet hC')
  refine ⟨hmem.toLp f, ?_⟩
  simp [hmem.coeFn_toLp]

/-- Triangle step for the affine Neumann load: if `L_p - L_{f0}` is bounded by
`C0 ‖·‖_{H^{3/4}}` then so is `L_p` with constant `C0 + ‖f0‖`. -/
theorem aux_rem_bank_unit_neumann_load_abs_le {d : ℕ} (hd : 2 ≤ d)
    (pvec : Fin d → ℝ) (f0 : DomainL2 (unitNeumannCube d)) (C0 : ℝ)
    (hC0 : ∀ z : meanZeroSobolevGraph (unitNeumannCube d),
      |(((affineNeumannLoad pvec).comp
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
          ((sobolevVolumeLoad f0).comp
            (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL)) z| ≤
        C0 * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
          threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1))
    (z : meanZeroSobolevGraph (unitNeumannCube d)) :
    |((affineNeumannLoad pvec).comp
        (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) z| ≤
      (C0 + ‖f0‖) * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
          threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1) := by
  set L := (affineNeumannLoad pvec).comp
    (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))) with hL
  set Lf0 := (sobolevVolumeLoad f0).comp
    (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL with hLf0
  have htri : L z = (L - Lf0) z + Lf0 z := by
    simp [L, Lf0, sub_apply, add_comm]
  rw [htri]
  have h1 : |(L - Lf0) z| ≤ C0 * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
      threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1) := hC0 z
  have h2 : |Lf0 z| ≤ ‖f0‖ * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
      threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1) := by
    have hLf0_eq : Lf0 z = inner ℝ f0 (z : SobolevData (unitNeumannCube d)).1 := by
      simp [Lf0, sobolevVolumeLoad]
    rw [hLf0_eq]
    calc
      |inner ℝ f0 (z : SobolevData (unitNeumannCube d)).1| ≤ ‖f0‖ * ‖(z : SobolevData (unitNeumannCube d)).1‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖f0‖ * Real.sqrt (‖(z : SobolevData (unitNeumannCube d)).1‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ ‖f0‖ * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
          threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1) := by
        gcongr
        exact aux_rem_bank_unit_l2_sq_le_frac hd (z : SobolevData (unitNeumannCube d)).1
  calc
    |(L - Lf0) z + Lf0 z| ≤ |(L - Lf0) z| + |Lf0 z| := abs_add_le _ _
    _ ≤ (C0 * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
          threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1)) +
        (‖f0‖ * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
          threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1)) := by gcongr
    _ = (C0 + ‖f0‖) * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
          threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1) := by ring

/-- Energy bound for a mean-zero Neumann inverse response from `H^{3/4}` coercivity and an
`H^{3/4}`-bounded load: `inverseResponse ≤ CL² K`. -/
theorem aux_rem_bank_unit_neumann_inverse_le {d : ℕ} (hd : 2 ≤ d)
    (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (a : PositiveCoefficient (unitNeumannCube d)) (K CL : ℝ) (hK : 0 ≤ K) (hCL : 0 ≤ CL)
    (L : meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ)
    (hcoer : ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          (v : SobolevData (unitNeumannCube d)).1 ≤
        K * sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
          (v : SobolevData (unitNeumannCube d)))
    (hL : ∀ z : meanZeroSobolevGraph (unitNeumannCube d),
      |L z| ≤ CL * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
          threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1)) :
    inverseResponse (meanZeroResponseSpace hP) a L ≤ CL ^ 2 * K := by
  set E := inverseResponse (meanZeroResponseSpace hP) a L with hE
  have hE_nonneg : 0 ≤ E := by
    rw [hE]
    exact inverseResponse_nonneg _ _ _
  have hE_eq_form : E = sobolevCoefficientForm a
      (responseSolution (meanZeroResponseSpace hP) a L : SobolevData (unitNeumannCube d))
      (responseSolution (meanZeroResponseSpace hP) a L : SobolevData (unitNeumannCube d)) := by
    rw [hE]
    rfl
  have hL_u : E ≤ |L (responseSolution (meanZeroResponseSpace hP) a L)| := by
    rw [hE, inverseResponse_eq_load (meanZeroResponseSpace hP) a L]
    exact le_abs_self _
  have hL_bound : |L (responseSolution (meanZeroResponseSpace hP) a L)| ≤
      CL * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
        threeQuarterOrder ((responseSolution (meanZeroResponseSpace hP) a L : SobolevData (unitNeumannCube d))).1) :=
    hL (responseSolution (meanZeroResponseSpace hP) a L)
  have hcoer_u : cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
      ((responseSolution (meanZeroResponseSpace hP) a L : SobolevData (unitNeumannCube d))).1 ≤
      K * E := by
    rw [hE_eq_form]
    exact hcoer (responseSolution (meanZeroResponseSpace hP) a L)
  have hA : 0 ≤ CL * Real.sqrt K := mul_nonneg hCL (Real.sqrt_nonneg _)
  have h_sqrt_bound : Real.sqrt (K * E) = Real.sqrt K * Real.sqrt E :=
    Real.sqrt_mul hK E
  have hE_le : E ≤ (CL * Real.sqrt K) * Real.sqrt E := by
    calc
      E ≤ CL * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
            threeQuarterOrder ((responseSolution (meanZeroResponseSpace hP) a L : SobolevData (unitNeumannCube d))).1) :=
        le_trans hL_u hL_bound
      _ ≤ CL * Real.sqrt (K * E) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcoer_u) hCL
      _ = CL * (Real.sqrt K * Real.sqrt E) := by rw [Real.sqrt_mul hK E]
      _ = (CL * Real.sqrt K) * Real.sqrt E := by ring
  have hE_sq : E ≤ (CL * Real.sqrt K) ^ 2 :=
    aux_rem_bank_response_moments_sq_of_le_mul_sqrt hE_nonneg hA hE_le
  calc
    E ≤ (CL * Real.sqrt K) ^ 2 := hE_sq
    _ = (CL ^ 2) * ((Real.sqrt K) ^ 2) := by ring
    _ = CL ^ 2 * K := by rw [Real.sq_sqrt hK]

/-- **G6 (consumer).** Deterministic bound of the affine Neumann inverse response `y_N` and of
the smoothed volume response `y_{N,ε}` by the `H^{3/4}` coercivity constant `K`, with one
constant `Cy` fixed by `(ρ, p)` before the coefficient.  (The bound `y_N ≲ K_N` uses the load bound `eq:mfd-7` at `ε₀ = 1/16` and coercivity `eq:mfd-1`.) -/
theorem aux_rem_bank_unit_neumann_response_le_coerc (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Sfi : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∃ Cy : ℝ, 0 ≤ Cy ∧
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
      (a : PositiveCoefficient (unitNeumannCube d)) (K : ℝ), 0 ≤ K →
      (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
            (v : SobolevData (unitNeumannCube d)).1 ≤
          K * sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
            (v : SobolevData (unitNeumannCube d))) →
      inverseResponse (meanZeroResponseSpace hP) a
          ((affineNeumannLoad pvec).comp
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) ≤ Cy * K ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ fL2 : DomainL2 (unitNeumannCube d),
        ((fL2 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
            faceBump rho pvec eps) →
        inverseResponse (meanZeroResponseSpace hP) a
          ((sobolevVolumeLoad fL2).comp (meanZeroResponseSpace hP).space.subtypeL) ≤
            Cy * K := by
  intro rho hrho hrho0 hrhos hrhoi pvec hpvec
  obtain ⟨Cload, hCload, hLB⟩ := lem_neumann_error_load_bound d hd Sfi
  obtain ⟨f0, hf0⟩ := aux_rem_bank_faceBump_rep rho hrho.continuous pvec (1 / 16)
  have h16 : (0 : ℝ) < 1 / 16 := by norm_num
  have h16' : (1 / 16 : ℝ) < 1 / 8 := by norm_num
  have hC0 : 0 ≤ Cload * (1 / 16 : ℝ) ^ (1 / 4 : ℝ) :=
    mul_nonneg hCload.le (Real.rpow_nonneg (by norm_num) _)
  obtain ⟨CL, hCLdef⟩ : ∃ CL : ℝ, CL = Cload * (1 / 16 : ℝ) ^ (1 / 4 : ℝ) + ‖f0‖ := ⟨_, rfl⟩
  have hCL0 : 0 ≤ CL := by rw [hCLdef]; exact add_nonneg hC0 (norm_nonneg _)
  refine ⟨max (CL ^ 2) (2 * CL ^ 2 + 2 * (8 * Cload) ^ 2),
    le_max_of_le_left (sq_nonneg _), ?_⟩
  intro hP a K hK hcoer
  have hLn : ∀ z : meanZeroSobolevGraph (unitNeumannCube d),
      |((affineNeumannLoad pvec).comp
          (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) z| ≤
        CL * Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
          threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1) := by
    intro z
    rw [hCLdef]
    exact aux_rem_bank_unit_neumann_load_abs_le hd pvec f0 _
      (fun w => hLB rho hrho hrho0 hrhos hrhoi pvec hpvec (1 / 16) h16 h16'
        (fun _ _ => f0) (fun _ _ => hf0) 0 (fun _ => 0) w) z
  have hyn := aux_rem_bank_unit_neumann_inverse_le hd hP a K CL hK hCL0 _ hcoer hLn
  refine ⟨hyn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hK), ?_⟩
  intro eps heps heps8 fL2 hfL2
  have hpt := aux_lem_neumann_error_pointwise hd hP a K Cload eps
    ((affineNeumannLoad pvec).comp
      (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))))
    ((sobolevVolumeLoad fL2).comp (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL)
    hCload heps heps8 hcoer
    (fun w => hLB rho hrho hrho0 hrhos hrhoi pvec hpvec eps heps heps8
      (fun _ _ => fL2) (fun _ _ => hfL2) 0 (fun _ => 0) w)
  have hys := hpt.2.2.2
  have he : eps ^ (1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one heps.le (by linarith) (by norm_num)
  have hB0 : 0 ≤ 2 * (8 * Cload) ^ 2 := by positivity
  calc inverseResponse (meanZeroResponseSpace hP) a
        ((sobolevVolumeLoad fL2).comp (meanZeroResponseSpace hP).space.subtypeL)
      ≤ 2 * inverseResponse (meanZeroResponseSpace hP) a
          ((affineNeumannLoad pvec).comp
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) +
        2 * (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * K := hys
    _ ≤ 2 * (CL ^ 2 * K) + 2 * (8 * Cload) ^ 2 * 1 * K := by
        exact add_le_add (mul_le_mul_of_nonneg_left hyn (by norm_num))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hB0) hK)
    _ = (2 * CL ^ 2 + 2 * (8 * Cload) ^ 2) * K := by ring
    _ ≤ max (CL ^ 2) (2 * CL ^ 2 + 2 * (8 * Cload) ^ 2) * K :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hK

/-! ### Moment and response helpers -/

/-- The layer sup-norm set of `rem_bank` (absolute values) is the image sup of the norms. -/
theorem aux_rem_bank_layer_sSup_eq {d : ℕ} (Q : Set (SpatialCoordinates d))
    (g : C(SpatialCoordinates d, ℝ)) :
    sSup {w : ℝ | ∃ x ∈ Q, w = |g x|} =
      sSup ((fun x : SpatialCoordinates d => ‖g x‖) '' Q) := by
  have h_set : {w : ℝ | ∃ x ∈ Q, w = |g x|} = ((fun x : SpatialCoordinates d => ‖g x‖) '' Q) := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, Real.norm_eq_abs _⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (Real.norm_eq_abs _).symm⟩
  rw [h_set]

/-- A.e.-strong measurability of the fine-layer sup norm under the common scale law
(from the compact-set layer tail `aux_lem_15_u_layer_tail`). -/
theorem aux_rem_bank_layer_aesm (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Set (SpatialCoordinates d)) (hQ : IsCompact Q) (hQne : Q.Nonempty)
    (R : ℝ) (hR : 0 ≤ R) (hQR : ∀ x ∈ Q, ∀ i, |x i| ≤ R)
    (delta : ℝ) (hdelta : 0 < delta)
    (Praw : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
    (hG1 : _root_.SubdiffusiveProcess.Model.ShellLawG1 d Praw)
    (hG2 : _root_.SubdiffusiveProcess.Model.ShellLawG2 d delta Praw) (j : ℕ) :
    AEStronglyMeasurable
      (fun omega : BilateralField d =>
        sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) '' Q))
      (commonScaleLaw d ((_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(_root_.SubdiffusiveProcess.Model.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure := by
  obtain ⟨_, _, _, hmeas, _, _⟩ := aux_lem_15_u_layer_tail d Q hQ hQne R hR hQR delta hdelta Praw hG1 hG2
  simpa using hmeas j

/-- Every finite moment of the fine-layer sup norm is finite under the common scale law
(e.coefficient.field.regularity, `aux_lem_15_u_layer_moment` with
`k = 1`, `lam = 0`). -/
theorem aux_rem_bank_layer_eLpNorm_lt_top (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Set (SpatialCoordinates d)) (hQ : IsCompact Q) (hQne : Q.Nonempty)
    (R : ℝ) (hR : 0 ≤ R) (hQR : ∀ x ∈ Q, ∀ i, |x i| ≤ R)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (Praw : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
    (hG1 : _root_.SubdiffusiveProcess.Model.ShellLawG1 d Praw)
    (hG2 : _root_.SubdiffusiveProcess.Model.ShellLawG2 d delta Praw) (j : ℕ) (v : ℝ) (hv : 0 < v) :
    eLpNorm
      (fun omega : BilateralField d =>
        sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) '' Q))
      (ENNReal.ofReal v)
      (commonScaleLaw d ((_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(_root_.SubdiffusiveProcess.Model.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure < ⊤ := by
  obtain ⟨Cm, _, hCm⟩ := aux_lem_15_u_layer_moment d hd Q hQ hQne R hR hQR v 1 0 1 hv
    zero_le_one le_rfl one_pos
  have hle := hCm delta hdelta hdelta1 Praw hG1 hG2 j
  have h_eq : (fun omega : BilateralField d =>
      sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) '' Q)) =
      (fun omega => (sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) '' Q)) ^ (1 : ℝ) *
        Real.exp ((0 : ℝ) * sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) '' Q))) := by
    ext omega
    simp [Real.rpow_one, zero_mul, Real.exp_zero, mul_one]
  rw [h_eq]
  refine lt_of_le_of_lt hle ?_
  exact ENNReal.ofReal_lt_top

/-- **G9 (consumer).** The `lay` clause of `rem_bank`: all finite moments of the actual
fine-layer sup norms on every closed cube under `chaosSampleLaw M`, for `M.delta ≤ 1`. -/
theorem aux_rem_bank_layer_block (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (hδ1 : M.delta ≤ 1) :
    ∀ z : SpatialCoordinates d, ∀ r : ℝ, ∀ hr : 0 < r, ∀ j : ℕ,
      ∀ v : ℝ, 0 < v →
      MemLp (fun omega : BilateralField d =>
          sSup {w : ℝ |
            ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              w = |omega (-(j : ℤ)) x|})
        (ENNReal.ofReal v) (chaosSampleLaw M).toMeasure := by
  intro z r hr j v hv
  have hfun : (fun omega : BilateralField d =>
      sSup {w : ℝ |
        ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          w = |omega (-(j : ℤ)) x|}) =
      fun omega : BilateralField d =>
        sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) ''
          (closedCube z r hr : Set (SpatialCoordinates d))) :=
    funext fun omega => aux_rem_bank_layer_sSup_eq _ _
  rw [hfun]
  have hQne : (closedCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, Metric.mem_closedBall_self (by linarith)⟩
  have hR : 0 ≤ ‖z‖ + (r / 2 + 1) := by positivity
  have hQR : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), ∀ i,
      |x i| ≤ ‖z‖ + (r / 2 + 1) := fun x hx =>
    aux_lem_15_u_Qt_bound z r x (Metric.closedBall_subset_closedBall (by linarith) hx)
  exact aux_rem_bank_layer_eLpNorm_lt_top d hd _ (closedCube z r hr).isCompact hQne _ hR hQR
      M.delta M.shellPrefix.delta_pos hδ1 M.P M.G1 M.G2 j v hv

/-! ### G1 (Cp-free energy growth), G8 (K13 block), G10 threshold -/

open Set Metric in
/-- **G1.** `prop_growth_energy_assembly` without its unused `CampanatoInput` binder: the
all-radii energy-growth constants `K_N` of `eq:mfd-4`  for the concrete
cutoff coefficient on cubes of side at most `1`.  The proof body is the supplier's body verbatim
(the supplier introduces `_Cp` and never uses it). -/
theorem aux_rem_bank_growth_energy :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_S : SobolevFoundationalInput d hd)
    (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 →
    (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t := by
  intro d hd _ _ E P X W S t alpha k ps ht htd halp halt hps
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨p1, hp1, hp1t⟩ := aux_prop_growth_energy_assembly_p1_choice d hd t htd
  obtain ⟨t1, ht1def⟩ : ∃ s : ℝ, s = (t + d) / 2 := ⟨_, rfl⟩
  have htt1 : t < t1 := by rw [ht1def]; linarith
  have ht1d : t1 < d := by rw [ht1def]; linarith
  obtain ⟨C, hC, hmic, hmom⟩ :=
    aux_prop_growth_energy_assembly_micro_local d hd W p1 t t1 hp1 ht htt1 ht1d hp1t
  obtain ⟨Q0, hQ0def⟩ : ∃ q : ℝ, q = 2 * (1 + ∑ i, ps i) * max 1 t := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg (fun i _ => le_trans zero_le_one (hps i))
  have hmax1 : 1 ≤ max 1 t := le_max_left _ _
  have hQ0 : 1 ≤ Q0 := by
    rw [hQ0def]
    have h1 : 1 ≤ 2 * (1 + ∑ i, ps i) := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 2 * (1 + ∑ i, ps i) * max 1 t := mul_le_mul h1 hmax1 zero_le_one (by linarith)
  have hqi : ∀ i, 2 * ps i * max 1 t ≤ Q0 := by
    intro i
    rw [hQ0def]
    have h1 : ps i ≤ 1 + ∑ j, ps j := by
      have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j))
        (Finset.mem_univ i)
      linarith
    have h2 : 2 * ps i ≤ 2 * (1 + ∑ j, ps j) := by linarith
    exact mul_le_mul_of_nonneg_right h2 (by linarith)
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    aux_prop_growth_energy_assembly_root_extremes d hd Q0 hQ0
  obtain ⟨dM, hdM, hmacro⟩ := prop_growth_macro_energy d hd E P X S t1 1 (fun _ => Q0)
    (by linarith) ht1d (fun _ => hQ0)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrmax : 0 < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := by
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith))) hlog3
  obtain ⟨delta0, aRate, hδ0, hδM, hδc, haR0, haR, hmono⟩ :=
    aux_prop_growth_energy_assembly_threshold Cd Cpe _ dM (cd / (2 * Q0)) hCd hCpe hrmax hdM
      (by positivity)
  refine ⟨delta0, hδ0, ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hr1
  obtain ⟨Kmac, CbM, hKmac0, hKmem, hKnorm, hKae⟩ :=
    hmacro M Rm Sreg It H hH (hδ.trans hδM) z r hr hr1
  obtain ⟨D, Mx, CE, hCE, hDMx0, hae, hmem, hDmom, hMxmom⟩ :=
    hroot M H hH (hδ.trans hδc) z r hr hr1
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ aRate :=
    hmono _ M.shellPrefix.delta_pos.le hδ
  have hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      eLpNorm (fun o => (1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o)
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
      eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
      eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + D N o) ^ t)
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
    intro i
    have hle : ENNReal.ofReal (2 * ps i * max 1 t) ≤ ENNReal.ofReal Q0 :=
      ENNReal.ofReal_le_ofReal (hqi i)
    have hqi1 : 1 ≤ 2 * ps i * max 1 t := by
      have := hps i
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 * ps i * max 1 t := mul_le_mul (by linarith) hmax1 zero_le_one (by linarith)
    have hMxN : ∀ N : ℕ, eLpNorm (fun o => Mx N o + Mx N o)
        (ENNReal.ofReal (2 * ps i * max 1 t)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (2 * CE * Real.exp (aRate * (N : ℝ))) := by
      intro N
      have h1 := aux_prop_growth_energy_assembly_double (chaosSampleLaw M).toMeasure (Mx N)
        (2 * ps i * max 1 t) Q0 (CE * Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N))
        hqi1 (hqi i) (hmem N).2.aestronglyMeasurable (by positivity) (hMxmom N)
      refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have he : Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N) ≤
          Real.exp (aRate * (N : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate hN)
      have := mul_le_mul_of_nonneg_left he hCE
      linarith
    exact hmom (BilateralField d) (chaosSampleLaw M).toMeasure (ps i) (hps i) D Mx Mx Kmac
      Cpe (2 * CE) (max (CbM 0) 0) aRate hCpe.le (by positivity) (le_max_right _ _) haR0 haR
      (fun N o => ⟨(hDMx0 N o).1, (hDMx0 N o).2, (hDMx0 N o).2, hKmac0 N o⟩)
      (fun N => ⟨(hmem N).1.mono_exponent hle, (hmem N).2.mono_exponent hle,
        (hmem N).2.mono_exponent hle, (hKmem 0 N).mono_exponent hle⟩)
      (fun N => (eLpNorm_le_eLpNorm_of_exponent_le hle).trans (hDmom N))
      hMxN
      (fun N => (eLpNorm_le_eLpNorm_of_exponent_le hle).trans
        ((hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  have hKps : ∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (max (CbM 0) 0) := by
    intro i N
    have hle : ENNReal.ofReal (ps i) ≤ ENNReal.ofReal Q0 := by
      refine ENNReal.ofReal_le_ofReal ?_
      have := hqi i
      have h2 : ps i ≤ 2 * ps i * max 1 t := by
        have hp := hps i
        calc ps i = ps i * 1 * 1 := by ring
          _ ≤ ps i * 2 * max 1 t := by
            apply mul_le_mul _ hmax1 zero_le_one (by linarith)
            exact mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
          _ = 2 * ps i * max 1 t := by ring
      linarith
    exact (eLpNorm_le_eLpNorm_of_exponent_le hle).trans
      ((hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have h2r : 0 ≤ (2 / r) ^ t := Real.rpow_nonneg (by positivity) _
  obtain ⟨K, Cbound, hKmem', hKnorm', hK1, hKdom⟩ :=
    aux_prop_growth_energy_assembly_final (chaosSampleLaw M).toMeasure k ps hps t t1 (d : ℝ)
      ((2 / r) ^ t) (aux_prop_growth_energy_assembly_Cr d r t t1 C) (max (CbM 0) 0) h2r
      (aux_prop_growth_energy_assembly_Cr_nonneg d r t t1 C hr hC.le) (le_max_right _ _)
      Kmac D Mx (fun N => (hKmem 0 N).aestronglyMeasurable)
      (fun N => (hmem N).1.aestronglyMeasurable) (fun N => (hmem N).2.aestronglyMeasurable)
      hKps hB
  refine ⟨K, Cbound, hKmem', hKnorm', Filter.Eventually.of_forall (fun om N => hK1 N om), ?_⟩
  filter_upwards [hKae, hae] with om hmac hen
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad0 hrad1
  obtain ⟨hMxpos, henvN, hlipN⟩ := hen N
  have hphys := aux_prop_growth_energy_assembly_physical t t1 C ht0 htt1 ht1d hC hmic M H om N
    z r hr hr1 (Kmac N om) (D N om) (Mx N om) (hKmac0 N om) (hDMx0 N om).1 hMxpos henvN hlipN
    (hmac N) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad0 hrad1
  refine hphys.trans ?_
  have hE : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have hradt : 0 ≤ rad ^ t := Real.rpow_nonneg hrad0.le _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hKdom N om) hE) hradt

/-- **G10 threshold.** Selection-function trick: a positive threshold read off the bank
`{3p, 2p, 12p, 4(2p)}` without recovering `p`, below `δ p`.  (Triage probe
`aux_probe_threshold`, renamed.) -/
theorem aux_rem_bank_threshold (δ : ℝ → ℝ) (hδ : ∀ x, 0 < δ x) (p : ℝ) :
    let bank : Finset ℝ := {3 * p, 2 * p, 12 * p, 4 * (2 * p)}
    let th : Finset ℝ → ℝ := fun b =>
      if h : b.Nonempty then b.inf' h (fun x => δ (x / 3)) else 1
    0 < th bank ∧ th bank ≤ δ p := by
  intro bank th
  have hne : bank.Nonempty := by simp [bank]
  have h3 : 3 * p ∈ bank := by simp [bank]
  refine ⟨?_, ?_⟩
  · simp only [th, dite_eq_left hne]
    exact (Finset.lt_inf'_iff hne).2 (fun x _ => hδ _)
  · simp only [th, dite_eq_left hne]
    have := Finset.inf'_le (fun x => δ (x / 3)) h3
    have he : 3 * p / 3 = p := by ring
    rw [he] at this
    exact this

/-- **G8.** The `eq:mfd-13` clause of `rem_bank` : the `eps^-2`
all-radii Neumann constant `K13` with its order-`3p` moments, on the common full-measure
event, from `prop_neumann_growth`, which consumes the carried deterministic one-step input
`D`.  `K13 := |K|`. -/
theorem aux_rem_bank_neumann_growth_block (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (P : _root_.SubdiffusiveProcess.Paper.in_poincare d hd E) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd E)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (ht0 : (d : ℝ) - 1 < t) (ht1 : t < (d : ℝ)) (p : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ (2 ≤ p →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M) (Sreg : in_6_16 d M)
        (It : in_iteration d M E Sreg) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ →
        ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho → (∀ v : ℝ, 0 ≤ rho v) →
          (∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) → (∫ v, rho v) = 1 →
          ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
          ∃ K13 : ℕ → BilateralField d → ℝ, ∃ B13 : ℝ, 0 ≤ B13 ∧
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N, 0 ≤ K13 N omega ∧
              (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
                ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
                SolvesNeumann (cutoffPositiveCoefficient M H omega N
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) (faceBump rho pvec eps) v →
                ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rad : ℝ,
                  0 < rad → rad ≤ 1 →
                  localGradientEnergy (cutoffPositiveCoefficient M H omega N
                      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                    (show MeasurableSet (Metric.ball x rad ∩
                        (unitNeumannCube d : Set (SpatialCoordinates d))) from
                      (Metric.isOpen_ball.inter (unitNeumannCube d).isOpen).measurableSet)
                    (sobolevGradient v.val) ≤
                    K13 N omega * eps ^ (-2 : ℝ) * rad ^ t)) ∧
            (∀ N, MemLp (K13 N) (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure ∧
              eLpNorm (K13 N) (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure ≤
                ENNReal.ofReal B13)) := by
  by_cases hp : 2 ≤ p
  swap
  · exact ⟨1, one_pos, fun h => absurd h hp⟩
  obtain ⟨δ, hδ, hmain⟩ := prop_neumann_growth d hd E P X W D t 1 (fun _ => 3 * p) ht0 ht1
    (fun _ => by linarith)
  refine ⟨δ, hδ, fun _ M Rm Sreg It H hIC hle rho hrho hrho0 hrhos hrhoi pvec hpvec => ?_⟩
  obtain ⟨K, Cb, hKmem, hKnorm, hae⟩ :=
    hmain M Rm Sreg It H hIC hle rho hrho hrho0 hrhos hrhoi pvec hpvec
  refine ⟨fun N omega => |K N omega|, max 0 (Cb 0), le_max_left _ _, ?_, ?_⟩
  · filter_upwards [hae] with omega hom N
    refine ⟨abs_nonneg _, fun eps heps heps8 v hv x hx rad hrad0 hrad1 => ?_⟩
    have h := hom N eps heps heps8 v hv x rad hx hrad0 hrad1
    refine h.trans ?_
    have hnn : 0 ≤ eps ^ (-2 : ℝ) * rad ^ t :=
      mul_nonneg (Real.rpow_nonneg heps.le _) (Real.rpow_nonneg hrad0.le _)
    calc K N omega * eps ^ (-2 : ℝ) * rad ^ t
        = K N omega * (eps ^ (-2 : ℝ) * rad ^ t) := by ring
      _ ≤ |K N omega| * (eps ^ (-2 : ℝ) * rad ^ t) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hnn
      _ = |K N omega| * eps ^ (-2 : ℝ) * rad ^ t := by ring
  · intro N
    exact aux_rem_bank_abs_moment _ (K N) (ENNReal.ofReal (3 * p)) (max 0 (Cb 0)) (hKmem 0 N)
      ((hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))

/-! ### Auxiliary proof steps: G2 (Dirichlet block), G7 (Neumann-coercive block) -/

/-- **Dirichlet and killed moment bounds.** The Dirichlet/killed clause of `rem_bank` (`eq:mfd-4`, with the response moments) for fixed orders `p < q`,
with one threshold `δ` chosen before the model.  The conclusion after `let Pm` is `rem_bank`'s
`dir` clause verbatim.  Route: `δ := min δE δR` with `aux_rem_bank_growth_energy` at
`ps := ![3 * p]`, `alpha := 1/2` and `rem_bank_response_moments`; the two `SolvesDirichlet`
bridges `aux_rem_bank_dm_solves` / `aux_rem_bank_rs_solves`; `aux_rem_bank_source_bound`;
`KD := K * c2Norm(phi)^2`, `KK := K * Kf^2` (with `c2Norm 0` ≥ 0 added); moment transfer by
`aux_rem_bank_response_moments_memLp_of_envelope`. -/
theorem aux_rem_bank_dirichlet_block (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (P : _root_.SubdiffusiveProcess.Paper.in_poincare d hd E) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd E)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Sfi : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (t : ℝ) (ht0 : (d : ℝ) - 1 < t) (ht1 : t < (d : ℝ)) (p q : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ (2 ≤ p → p < q →
          ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
            (_Rm : in_responses d M) (Sreg : in_6_16 d M)
            (_It : in_iteration d M E Sreg),
            ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ),
            InfraredCharacterization M H → M.delta ≤ min 1 δ →
            let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
            ((∀ z : SpatialCoordinates d, ∀ r : ℝ, ∀ hr : 0 < r, r ≤ 1 →
                let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
                ∀ hP : (∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
                    ‖(w : SobolevData Q).1‖ ≤
                      K * ‖subspaceGradient (killedSobolevGraph Q) w‖),
                ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
                ∀ b : weakSobolevGraph Q,
                    (b.val.1 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi) →
                ∀ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
                    tsupport f ⊆ (Q : Set (SpatialCoordinates d)) →
                ∀ fL2 : DomainL2 Q,
                    ((fL2 : SpatialCoordinates d → ℝ)
                      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f) →
                let S : ResponseSpace Q := killedResponseSpace hP
                let a : ℕ → BilateralField d → PositiveCoefficient Q :=
                    fun N omega => cutoffPositiveCoefficient M H omega N z hr
                let load : S.space →L[ℝ] ℝ :=
                    (sobolevVolumeLoad fL2).comp S.space.subtypeL
                let uD : ℕ → BilateralField d → weakSobolevGraph Q :=
                    fun N omega => dirichletMinimizer S (a N omega) b
                let uK : ℕ → BilateralField d → S.space :=
                    fun N omega => responseSolution S (a N omega) load
                let RD : ℕ → BilateralField d → ℝ :=
                    fun N omega => dirichletResponse S (a N omega) b
                let RK : ℕ → BilateralField d → ℝ :=
                    fun N omega => inverseResponse S (a N omega) load
                ∃ KD KK : ℕ → BilateralField d → ℝ, ∃ B : ℝ, 0 ≤ B ∧
                  (∀ᵐ omega ∂Pm, ∀ N, 0 ≤ KD N omega ∧ 0 ≤ KK N omega ∧
                    (∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rad : ℝ,
                        0 < rad → rad ≤ 1 →
                        localGradientEnergy (a N omega)
                          (show MeasurableSet
                              (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) from
                            (Metric.isOpen_ball.inter Q.isOpen).measurableSet)
                          (sobolevGradient (uD N omega).val) ≤ KD N omega * rad ^ t) ∧
                    (∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rad : ℝ,
                        0 < rad → rad ≤ 1 →
                        localGradientEnergy (a N omega)
                          (show MeasurableSet
                              (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) from
                            (Metric.isOpen_ball.inter Q.isOpen).measurableSet)
                          (sobolevGradient (uK N omega).val) ≤ KK N omega * rad ^ t)) ∧
                  (∀ N, MemLp (KD N) (ENNReal.ofReal (3 * p)) Pm ∧
                        MemLp (KK N) (ENNReal.ofReal (3 * p)) Pm ∧
                        MemLp (RD N) (ENNReal.ofReal (3 * p)) Pm ∧
                        MemLp (RK N) (ENNReal.ofReal (3 * p)) Pm ∧
                        MemLp (RD N) (ENNReal.ofReal q) Pm ∧
                        MemLp (RK N) (ENNReal.ofReal q) Pm) ∧
                  (∀ N, eLpNorm (KD N) (ENNReal.ofReal (3 * p)) Pm +
                        eLpNorm (KK N) (ENNReal.ofReal (3 * p)) Pm +
                        eLpNorm (RD N) (ENNReal.ofReal (3 * p)) Pm +
                        eLpNorm (RK N) (ENNReal.ofReal (3 * p)) Pm +
                        eLpNorm (RD N) (ENNReal.ofReal q) Pm +
                        eLpNorm (RK N) (ENNReal.ofReal q) Pm ≤ ENNReal.ofReal B)))) := by
  by_cases hc : 2 ≤ p ∧ p < q
  · obtain ⟨delta0, hδ0pos, hδ0⟩ :=
      aux_rem_bank_growth_energy d hd E P X W Sfi t (1 / 2) 1 (fun _ : Fin 1 => 3 * p) ht0 ht1
        (by norm_num) (by norm_num) (fun _ => by linarith [hc.1])
    obtain ⟨deltaResp, hδRpos, hδR⟩ :=
      rem_bank_response_moments d hd E P X W t ht0 ht1 p q hc.1 hc.2
    refine ⟨min delta0 deltaResp, lt_min hδ0pos hδRpos, ?_⟩
    intro hp hpq M Rm Sreg It H hIC hδ
    have hδ0' : M.delta ≤ delta0 :=
      le_trans hδ (le_trans (min_le_right (1 : ℝ) (min delta0 deltaResp)) (min_le_left delta0 deltaResp))
    have hδR' : M.delta ≤ min 1 deltaResp :=
      le_min (le_trans hδ (min_le_left (1 : ℝ) (min delta0 deltaResp)))
        (le_trans hδ (le_trans (min_le_right (1 : ℝ) (min delta0 deltaResp))
          (min_le_right delta0 deltaResp)))
    intro Pm z r hr hr1 Q hP phi hphi b hb f hf hfc hfsub fL2 hfL2 S a load uD uK RD RK
    obtain ⟨K, Cbound, hKmem, hKnorm, hKae, hKgrow⟩ := hδ0 M Rm Sreg It H hIC hδ0' z r hr hr1
    obtain ⟨Bresp, hBresp0, hResp⟩ :=
      hδR M Rm Sreg It H hIC hδR' z r hr hP phi hphi b hb f hf hfc hfsub fL2 hfL2
    obtain ⟨Kf0, hKf0nn, _, hKf0bd⟩ := aux_rem_bank_source_bound f hf hfc
    let Cφ : ℝ := max (c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi) 0
    let Cψ : ℝ := max (c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) (fun _ => 0)) 0
    have hCφle : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cφ := le_max_left _ _
    have hCψle : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) (fun _ => 0) ≤ Cψ := le_max_left _ _
    have hb0 : (((0 : ↥(weakSobolevGraph (centeredCube z r hr))) : SobolevData (centeredCube z r hr)).1
        : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (fun _ => 0) := by
      exact Lp.coeFn_zero ℝ 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
    have hae : ∀ᵐ omega ∂Pm, ∀ N : ℕ,
        0 ≤ Cφ ^ 2 * K N omega ∧ 0 ≤ (Kf0 + Cψ) ^ 2 * K N omega ∧
        (∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
          localGradientEnergy (a N omega)
            (show MeasurableSet (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) from
              (Metric.isOpen_ball.inter Q.isOpen).measurableSet)
            (sobolevGradient (uD N omega).val) ≤ Cφ ^ 2 * K N omega * rad ^ t) ∧
        (∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
          localGradientEnergy (a N omega)
            (show MeasurableSet (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) from
              (Metric.isOpen_ball.inter Q.isOpen).measurableSet)
            (sobolevGradient (uK N omega).val) ≤ (Kf0 + Cψ) ^ 2 * K N omega * rad ^ t) := by
      filter_upwards [hKae, hKgrow] with omega h1 h2
      intro N
      have hK1 : 0 ≤ K N omega := le_trans zero_le_one (h1 N)
      refine ⟨mul_nonneg (sq_nonneg Cφ) hK1, mul_nonneg (sq_nonneg (Kf0 + Cψ)) hK1, ?_, ?_⟩
      · intro x hx rad hrad0 hrad1
        have h := h2 N (fun _ : SpatialCoordinates d => 0) 0 (le_refl 0)
          measurable_const.aemeasurable
          (Filter.Eventually.of_forall (fun _ => by simp))
          phi Cφ (hphi.of_le (WithTop.coe_le_coe.2 le_top)) hCφle
          b (uD N omega) hb (aux_rem_bank_dm_solves hP (a N omega) b)
          x rad hx hrad0 hrad1
        exact h.trans (le_of_eq (by ring))
      · intro x hx rad hrad0 hrad1
        have h := h2 N f Kf0 hKf0nn hf.continuous.aemeasurable
          (Filter.Eventually.of_forall hKf0bd)
          (fun _ : SpatialCoordinates d => 0) Cψ contDiff_const hCψle
          (0 : ↥(weakSobolevGraph (centeredCube z r hr)))
          ⟨(uK N omega : SobolevData (centeredCube z r hr)), S.le_weak (uK N omega).property⟩
          hb0 (aux_rem_bank_rs_solves hP (a N omega) f fL2 hfL2)
          x rad hx hrad0 hrad1
        exact h.trans (le_of_eq (by ring))
    have hmem : ∀ N : ℕ,
        MemLp (fun omega => Cφ ^ 2 * K N omega) (ENNReal.ofReal (3 * p)) Pm ∧
        MemLp (fun omega => (Kf0 + Cψ) ^ 2 * K N omega) (ENNReal.ofReal (3 * p)) Pm ∧
        MemLp (RD N) (ENNReal.ofReal (3 * p)) Pm ∧ MemLp (RK N) (ENNReal.ofReal (3 * p)) Pm ∧
        MemLp (RD N) (ENNReal.ofReal q) Pm ∧ MemLp (RK N) (ENNReal.ofReal q) Pm := by
      intro N
      exact ⟨(hKmem 0 N).const_mul (Cφ ^ 2), (hKmem 0 N).const_mul ((Kf0 + Cψ) ^ 2),
        (hResp N).1, (hResp N).2.1, (hResp N).2.2.1, (hResp N).2.2.2.1⟩
    have hKDn (N : ℕ) : eLpNorm (fun omega => Cφ ^ 2 * K N omega)
        (ENNReal.ofReal (3 * p)) Pm ≤ ENNReal.ofReal (Cφ ^ 2 * max (Cbound 0) 0) := by
      rw [show (fun omega => Cφ ^ 2 * K N omega) = (Cφ ^ 2) • (K N) from rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal (sq_nonneg Cφ), ENNReal.ofReal_mul (sq_nonneg Cφ)]
      gcongr
      exact (hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hKKn (N : ℕ) : eLpNorm (fun omega => (Kf0 + Cψ) ^ 2 * K N omega)
        (ENNReal.ofReal (3 * p)) Pm ≤ ENNReal.ofReal ((Kf0 + Cψ) ^ 2 * max (Cbound 0) 0) := by
      rw [show (fun omega => (Kf0 + Cψ) ^ 2 * K N omega) = ((Kf0 + Cψ) ^ 2) • (K N) from rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal (sq_nonneg (Kf0 + Cψ)),
        ENNReal.ofReal_mul (sq_nonneg (Kf0 + Cψ))]
      gcongr
      exact (hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    let a3 : ℝ := Cφ ^ 2 * max (Cbound 0) 0
    let a4 : ℝ := (Kf0 + Cψ) ^ 2 * max (Cbound 0) 0
    have ha3 : 0 ≤ a3 := mul_nonneg (sq_nonneg Cφ) (le_max_right _ _)
    have ha4 : 0 ≤ a4 := mul_nonneg (sq_nonneg (Kf0 + Cψ)) (le_max_right _ _)
    refine ⟨fun N omega => Cφ ^ 2 * K N omega, fun N omega => (Kf0 + Cψ) ^ 2 * K N omega,
      a3 + a4 + 4 * Bresp,
      add_nonneg (add_nonneg ha3 ha4) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hBresp0), hae, hmem, ?_⟩
    intro N
    let t3 : ℝ≥0∞ := eLpNorm (RD N) (ENNReal.ofReal (3 * p)) Pm
    let t4 : ℝ≥0∞ := eLpNorm (RK N) (ENNReal.ofReal (3 * p)) Pm
    let t5 : ℝ≥0∞ := eLpNorm (RD N) (ENNReal.ofReal q) Pm
    let t6 : ℝ≥0∞ := eLpNorm (RK N) (ENNReal.ofReal q) Pm
    change eLpNorm (fun omega => Cφ ^ 2 * K N omega) (ENNReal.ofReal (3 * p)) Pm +
        eLpNorm (fun omega => (Kf0 + Cψ) ^ 2 * K N omega) (ENNReal.ofReal (3 * p)) Pm +
        t3 + t4 + t5 + t6 ≤ ENNReal.ofReal (a3 + a4 + 4 * Bresp)
    have h1 : eLpNorm (fun omega => Cφ ^ 2 * K N omega) (ENNReal.ofReal (3 * p)) Pm ≤
        ENNReal.ofReal a3 := hKDn N
    have h2 : eLpNorm (fun omega => (Kf0 + Cψ) ^ 2 * K N omega) (ENNReal.ofReal (3 * p)) Pm ≤
        ENNReal.ofReal a4 := hKKn N
    have hsum4 : t3 + t4 + t5 + t6 ≤ ENNReal.ofReal Bresp := (hResp N).2.2.2.2
    have h34 : t3 ≤ t3 + t4 := le_add_of_nonneg_right zero_le
    have h345 : t3 + t4 ≤ t3 + t4 + t5 := le_add_of_nonneg_right zero_le
    have h3456 : t3 + t4 + t5 ≤ t3 + t4 + t5 + t6 := le_add_of_nonneg_right zero_le
    have h3 : t3 ≤ ENNReal.ofReal Bresp := h34.trans (h345.trans (h3456.trans hsum4))
    have h4 : t4 ≤ ENNReal.ofReal Bresp :=
      ((le_add_of_nonneg_left zero_le).trans h345).trans (h3456.trans hsum4)
    have h5 : t5 ≤ ENNReal.ofReal Bresp :=
      ((le_add_of_nonneg_left zero_le).trans
        (le_add_of_nonneg_right zero_le)).trans hsum4
    have h6 : t6 ≤ ENNReal.ofReal Bresp :=
      (le_add_of_nonneg_left zero_le).trans hsum4
    refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6).trans ?_
    rw [← ENNReal.ofReal_add ha3 ha4,
      ← ENNReal.ofReal_add (add_nonneg ha3 ha4) hBresp0,
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg ha3 ha4) hBresp0) hBresp0,
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg ha3 ha4) hBresp0) hBresp0) hBresp0,
      ← ENNReal.ofReal_add
        (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha3 ha4) hBresp0) hBresp0) hBresp0) hBresp0]
    rw [show ((((a3 + a4) + Bresp) + Bresp) + Bresp) + Bresp = a3 + a4 + 4 * Bresp by ring]
  · exact ⟨1, one_pos, fun hp hpq => absurd ⟨hp, hpq⟩ hc⟩

/-- **Neumann coercivity and response moments.** The `H^{3/4}`-coercivity half of `rem_bank`'s Neumann clause
(`eq:mfd-1`  and `eq:mfd-9` ) for fixed orders `p < q`: a
coercivity constant with its actual inequality for EVERY `(N, omega)`, its moments together
with those of `y_N` at orders `12p, 4q`, and the smoothed responses `y_{N,eps}` at orders
`3p, q`, uniformly in `N` and `eps`.  The moment conjuncts are `rem_bank`'s text verbatim.
Route: `lem_coercivity` at `z = 1/2`, `r = 1`; `Kcoerc := |K|` (`aux_rem_bank_coerc_abs`,
`aux_rem_bank_abs_moment`); `y_N, y_{N,eps} ≤ Cy * |K|` by
`aux_rem_bank_unit_neumann_response_le_coerc`; measurability by
`aux_rem_bank_response_moments_measurable_inverseResponse`; transfer by
`aux_rem_bank_response_moments_memLp_of_envelope`. -/
theorem aux_rem_bank_neumann_coercive_block (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (P : _root_.SubdiffusiveProcess.Paper.in_poincare d hd E)
    (Sfi : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) (p q : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ (2 ≤ p → p < q →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ min 1 δ →
        let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
              ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho → (∀ v : ℝ, 0 ≤ rho v) →
                (∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) → (∫ v, rho v) = 1 →
                ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
                let Qn : Opens (SpatialCoordinates d) := unitNeumannCube d
                let zn : SpatialCoordinates d := fun _ : Fin d => (1 / 2 : ℝ)
                ∀ hPn : (∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Qn,
                    ‖(w : SobolevData Qn).1‖ ≤
                      K * ‖subspaceGradient (meanZeroSobolevGraph Qn) w‖),
                let Sn : ResponseSpace Qn := meanZeroResponseSpace hPn
                let an : ℕ → BilateralField d → PositiveCoefficient Qn :=
                    fun N omega => cutoffPositiveCoefficient M H omega N zn one_pos
                let Lp : Sn.space →L[ℝ] ℝ :=
                    (affineNeumannLoad pvec).comp
                      (subspaceGradient (meanZeroSobolevGraph Qn))
                let yn : ℕ → BilateralField d → ℝ :=
                    fun N omega => inverseResponse Sn (an N omega) Lp
                ∃ Kcoerc : ℕ → BilateralField d → ℝ, ∃ B9 Bsm : ℝ,
                  0 ≤ B9 ∧ 0 ≤ Bsm ∧
                  (∀ N, ∀ omega, 0 ≤ Kcoerc N omega ∧
                    (∀ v : meanZeroSobolevGraph Qn,
                        cubeFractionalSqNorm hd zn 1 one_pos threeQuarterOrder v.val.1 ≤
                          Kcoerc N omega *
                            sobolevCoefficientForm (an N omega) v.val v.val)) ∧
                  (∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm ∧
                        MemLp (yn N) (ENNReal.ofReal (12 * p)) Pm ∧
                        MemLp (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm ∧
                        MemLp (yn N) (ENNReal.ofReal (4 * q)) Pm) ∧
                  (∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm +
                        eLpNorm (yn N) (ENNReal.ofReal (12 * p)) Pm +
                        eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm +
                        eLpNorm (yn N) (ENNReal.ofReal (4 * q)) Pm ≤
                          ENNReal.ofReal B9) ∧
                  (∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ fL2 : DomainL2 Qn,
                      ((fL2 : SpatialCoordinates d → ℝ)
                        =ᵐ[volume.restrict (Qn : Set (SpatialCoordinates d))]
                        faceBump rho pvec eps) →
                      let ys : ℕ → BilateralField d → ℝ :=
                        fun N omega => inverseResponse Sn (an N omega)
                          ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL)
                      ∀ N, MemLp (ys N) (ENNReal.ofReal (3 * p)) Pm ∧
                           MemLp (ys N) (ENNReal.ofReal q) Pm ∧
                           eLpNorm (ys N) (ENNReal.ofReal (3 * p)) Pm +
                             eLpNorm (ys N) (ENNReal.ofReal q) Pm ≤
                               ENNReal.ofReal Bsm)) := by
  obtain ⟨delta0_coerc, hδcoerc_pos, h_coerc_inner⟩ := aux_lem_coercivity_compat d hd E P Sfi
  have hA_1 : (1:ℝ) ≤ 12 * max p (1/12 : ℝ) := by have := le_max_right p (1/12 : ℝ); nlinarith
  have hA_2 : (1:ℝ) ≤ 4 * max q (1/4 : ℝ) := by have := le_max_right q (1/4 : ℝ); nlinarith
  have hA_3 : (1:ℝ) ≤ 3 * max p (1/3 : ℝ) := by have := le_max_right p (1/3 : ℝ); nlinarith
  have hA_4 : (1:ℝ) ≤ max q 1 := le_max_right q 1
  refine ⟨min 1 (min (min (min (delta0_coerc (12 * max p (1/12 : ℝ))) (delta0_coerc (4 * max q (1/4 : ℝ)))) (delta0_coerc (3 * max p (1/3 : ℝ)))) (delta0_coerc (max q 1))), ?_, ?_⟩
  · exact lt_min_iff.mpr ⟨by norm_num, lt_min_iff.mpr ⟨lt_min_iff.mpr
      ⟨lt_min_iff.mpr ⟨hδcoerc_pos _ hA_1, hδcoerc_pos _ hA_2⟩, hδcoerc_pos _ hA_3⟩,
      hδcoerc_pos _ hA_4⟩⟩
  · intro hp2 hpq M Rm H hIC hδ_le Pm0 rho hrho hrho0 hrhos hrhoi pvec hpvec Qn zn hPn Sn an Lp yn
    have hq2 : (2:ℝ) ≤ q := by linarith
    have hmax_p : max p (1/12 : ℝ) = p := max_eq_left (by nlinarith)
    have hmax_q : max q (1/4 : ℝ) = q := max_eq_left (by nlinarith)
    have hmax_p3 : max p (1/3 : ℝ) = p := max_eq_left (by nlinarith)
    have hmax_q1 : max q 1 = q := max_eq_left (by linarith)
    have h1 := hδ_le.trans (min_le_right 1 _)
    have h2 := h1.trans (min_le_right 1 _)
    have hP := h2.trans (min_le_left _ _)
    have hQ := hP.trans (min_le_left _ _)
    have hM12 : M.delta ≤ delta0_coerc (12 * p) := by
      have h3 := hQ.trans (min_le_left _ _)
      rwa [hmax_p] at h3
    have hM4 : M.delta ≤ delta0_coerc (4 * q) := by
      have h3 := hQ.trans (min_le_right _ _)
      rwa [hmax_q] at h3
    have hM3 : M.delta ≤ delta0_coerc (3 * p) := by
      have h3 := hP.trans (min_le_right _ _)
      rwa [hmax_p3] at h3
    have hMq : M.delta ≤ delta0_coerc q := by
      have h3 := h2.trans (min_le_right _ _)
      rwa [hmax_q1] at h3
    clear h1 h2 hP hQ hδ_le
    have h1_12 : (1:ℝ) ≤ 12 * p := by nlinarith
    have h1_4 : (1:ℝ) ≤ 4 * q := by nlinarith
    have h1_3 : (1:ℝ) ≤ 3 * p := by nlinarith
    have h1_q : (1:ℝ) ≤ q := by linarith
    obtain ⟨K, hK_coerc, hK_mom⟩ :=
      h_coerc_inner M Rm H hIC (fun _ : Fin d => (1/2:ℝ)) 1 one_pos le_rfl
    have hHmeas : Measurable H := hIC.1
    clear hIC
    have hcoerc : ∀ N omega, ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        cubeFractionalSqNorm hd (fun _ : Fin d => (1/2:ℝ)) 1 one_pos threeQuarterOrder v.val.1 ≤
          |K N omega| * sobolevCoefficientForm
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1/2:ℝ)) one_pos) v.val v.val := by
      intro N omega v
      exact (((hK_coerc N omega).2 v).2).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (sobolevCoefficientForm_nonneg _ _))
    clear hK_coerc
    have hK12 := hK_mom (12*p) h1_12 hM12
    obtain ⟨Cb12, hK12mem, hK12norm⟩ := hK12
    have hK4 := hK_mom (4*q) h1_4 hM4
    obtain ⟨Cb4, hK4mem, hK4norm⟩ := hK4
    have hK3 := hK_mom (3*p) h1_3 hM3
    obtain ⟨Cb3, hK3mem, hK3norm⟩ := hK3
    have hKq := hK_mom q h1_q hMq
    obtain ⟨Cbq, hKqmem, hKqnorm⟩ := hKq
    clear hK_mom
    obtain ⟨Cy, hCy0, hCyb⟩ :=
      aux_rem_bank_unit_neumann_response_le_coerc d hd Sfi rho hrho hrho0 hrhos hrhoi pvec hpvec
    let Kcoerc : ℕ → BilateralField d → ℝ := fun N omega => |K N omega|
    have hKcoerc0 : ∀ N omega, 0 ≤ Kcoerc N omega := fun N omega => abs_nonneg _
    have hynb : ∀ N omega, yn N omega ≤ Kcoerc N omega * Cy := by
      intro N omega
      exact (hCyb hPn (an N omega) |K N omega| (abs_nonneg _) (hcoerc N omega)).1.trans
        (le_of_eq (mul_comm Cy (|K N omega|)))
    have hKabs12mem : ∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (12*p)) Pm0 := by
      intro N
      exact (aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (12*p)) Cb12 (hK12mem N) (hK12norm N)).1
    have hKabs12norm : ∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (12*p)) Pm0 ≤ ENNReal.ofReal (max Cb12 0) := by
      intro N
      exact ((aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (12*p)) Cb12 (hK12mem N) (hK12norm N)).2).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hKabs4mem : ∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (4*q)) Pm0 := by
      intro N
      exact (aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (4*q)) Cb4 (hK4mem N) (hK4norm N)).1
    have hKabs4norm : ∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (4*q)) Pm0 ≤ ENNReal.ofReal (max Cb4 0) := by
      intro N
      exact ((aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (4*q)) Cb4 (hK4mem N) (hK4norm N)).2).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hKabs3mem : ∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (3*p)) Pm0 := by
      intro N
      exact (aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (3*p)) Cb3 (hK3mem N) (hK3norm N)).1
    have hKabs3norm : ∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (3*p)) Pm0 ≤ ENNReal.ofReal (max Cb3 0) := by
      intro N
      exact ((aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (3*p)) Cb3 (hK3mem N) (hK3norm N)).2).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hKabsqmem : ∀ N, MemLp (Kcoerc N) (ENNReal.ofReal q) Pm0 := by
      intro N
      exact (aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal q) Cbq (hKqmem N) (hKqnorm N)).1
    have hKabsqnorm : ∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal q) Pm0 ≤ ENNReal.ofReal (max Cbq 0) := by
      intro N
      exact ((aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal q) Cbq (hKqmem N) (hKqnorm N)).2).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hyn_as : ∀ N, AEStronglyMeasurable (yn N) Pm0 := by
      intro N
      exact (aux_rem_bank_response_moments_measurable_inverseResponse M H hHmeas N zn one_pos Sn Lp).aestronglyMeasurable
    have hyn12 : ∀ N, MemLp (yn N) (ENNReal.ofReal (12*p)) Pm0 ∧
        eLpNorm (yn N) (ENNReal.ofReal (12*p)) Pm0 ≤ ENNReal.ofReal (Cy * max Cb12 0) := by
      intro N
      refine aux_rem_bank_response_moments_memLp_of_envelope Pm0 (yn N) (Kcoerc N) Cy (max Cb12 0)
        hCy0 (ENNReal.ofReal (12*p)) (hyn_as N) (hKabs12mem N) (hKabs12norm N) ?_
      filter_upwards with omega
      exact ⟨inverseResponse_nonneg Sn (an N omega) Lp, hKcoerc0 N omega, hynb N omega⟩
    have hyn4 : ∀ N, MemLp (yn N) (ENNReal.ofReal (4*q)) Pm0 ∧
        eLpNorm (yn N) (ENNReal.ofReal (4*q)) Pm0 ≤ ENNReal.ofReal (Cy * max Cb4 0) := by
      intro N
      refine aux_rem_bank_response_moments_memLp_of_envelope Pm0 (yn N) (Kcoerc N) Cy (max Cb4 0)
        hCy0 (ENNReal.ofReal (4*q)) (hyn_as N) (hKabs4mem N) (hKabs4norm N) ?_
      filter_upwards with omega
      exact ⟨inverseResponse_nonneg Sn (an N omega) Lp, hKcoerc0 N omega, hynb N omega⟩
    have hA12 : 0 ≤ max Cb12 0 := le_max_right _ _
    have hA4 : 0 ≤ max Cb4 0 := le_max_right _ _
    have hA3 : 0 ≤ max Cb3 0 := le_max_right _ _
    have hAq : 0 ≤ max Cbq 0 := le_max_right _ _
    refine ⟨Kcoerc, (max Cb12 0 + Cy * max Cb12 0) + (max Cb4 0 + Cy * max Cb4 0),
      Cy * max Cb3 0 + Cy * max Cbq 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact add_nonneg (add_nonneg hA12 (mul_nonneg hCy0 hA12)) (add_nonneg hA4 (mul_nonneg hCy0 hA4))
    · exact add_nonneg (mul_nonneg hCy0 hA3) (mul_nonneg hCy0 hAq)
    · intro N omega
      exact ⟨abs_nonneg _, fun v => hcoerc N omega v⟩
    · intro N
      exact ⟨hKabs12mem N, (hyn12 N).1, hKabs4mem N, (hyn4 N).1⟩
    · intro N
      have h1 := hKabs12norm N
      have h2 := (hyn12 N).2
      have h3 := hKabs4norm N
      have h4 := (hyn4 N).2
      have h12' : eLpNorm (Kcoerc N) (ENNReal.ofReal (12*p)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (12*p)) Pm0
          ≤ ENNReal.ofReal (max Cb12 0 + Cy * max Cb12 0) :=
        (add_le_add h1 h2).trans (le_of_eq (ENNReal.ofReal_add hA12 (mul_nonneg hCy0 hA12)).symm)
      have h34' : eLpNorm (Kcoerc N) (ENNReal.ofReal (4*q)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (4*q)) Pm0
          ≤ ENNReal.ofReal (max Cb4 0 + Cy * max Cb4 0) :=
        (add_le_add h3 h4).trans (le_of_eq (ENNReal.ofReal_add hA4 (mul_nonneg hCy0 hA4)).symm)
      calc eLpNorm (Kcoerc N) (ENNReal.ofReal (12*p)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (12*p)) Pm0
            + eLpNorm (Kcoerc N) (ENNReal.ofReal (4*q)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (4*q)) Pm0
          = (eLpNorm (Kcoerc N) (ENNReal.ofReal (12*p)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (12*p)) Pm0)
            + (eLpNorm (Kcoerc N) (ENNReal.ofReal (4*q)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (4*q)) Pm0) := by
              rw [add_assoc]
        _ ≤ ENNReal.ofReal (max Cb12 0 + Cy * max Cb12 0) + ENNReal.ofReal (max Cb4 0 + Cy * max Cb4 0) :=
              add_le_add h12' h34'
        _ = ENNReal.ofReal ((max Cb12 0 + Cy * max Cb12 0) + (max Cb4 0 + Cy * max Cb4 0)) :=
              (ENNReal.ofReal_add (add_nonneg hA12 (mul_nonneg hCy0 hA12)) (add_nonneg hA4 (mul_nonneg hCy0 hA4))).symm
    · intro eps heps heps8 fL2 hfL2 ys N
      have hysb : ∀ omega, ys N omega ≤ Kcoerc N omega * Cy := by
        intro omega
        exact ((hCyb hPn (an N omega) |K N omega| (abs_nonneg _) (hcoerc N omega)).2 eps heps heps8 fL2 hfL2).trans
          (le_of_eq (mul_comm Cy (|K N omega|)))
      have hys_as : AEStronglyMeasurable (ys N) Pm0 :=
        (aux_rem_bank_response_moments_measurable_inverseResponse M H hHmeas N zn one_pos Sn
          ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL)).aestronglyMeasurable
      have hys3 := aux_rem_bank_response_moments_memLp_of_envelope Pm0 (ys N) (Kcoerc N) Cy (max Cb3 0) hCy0 (ENNReal.ofReal (3*p)) hys_as (hKabs3mem N) (hKabs3norm N) (by
        filter_upwards with omega
        exact ⟨inverseResponse_nonneg Sn (an N omega) ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL), hKcoerc0 N omega, hysb omega⟩)
      have hysq := aux_rem_bank_response_moments_memLp_of_envelope Pm0 (ys N) (Kcoerc N) Cy (max Cbq 0) hCy0 (ENNReal.ofReal q) hys_as (hKabsqmem N) (hKabsqnorm N) (by
        filter_upwards with omega
        exact ⟨inverseResponse_nonneg Sn (an N omega) ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL), hKcoerc0 N omega, hysb omega⟩)
      exact ⟨hys3.1, hysq.1,
        (add_le_add hys3.2 hysq.2).trans
          (le_of_eq (ENNReal.ofReal_add (mul_nonneg hCy0 hA3) (mul_nonneg hCy0 hAq)).symm)⟩



theorem rem_bank (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (P : _root_.SubdiffusiveProcess.Paper.in_poincare d hd E) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd E)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (ht0 : (d : ℝ) - 1 < t) (ht1 : t < (d : ℝ)) :
    ∃ (aexpOf : ℕ → ℝ → ℝ) (qOf : ℝ → ℕ → ℝ → ℝ)
      (ordersOf : ℝ → ℕ → ℝ → Finset ℝ) (thresholdOf : ℕ → ℝ → Finset ℝ → ℝ),
    (d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧ 0 < aexpOf d t ∧
      aexpOf d t = t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) ∧
      (∀ p : ℝ, 2 ≤ p →
        let q : ℝ := qOf p d t
        let bank : Finset ℝ := ordersOf p d t
        let delta0 : ℝ := thresholdOf d t bank
        p < q ∧ 0 < delta0 ∧ (3 * p ∈ bank) ∧ (q ∈ bank) ∧
          (12 * p ∈ bank) ∧ (4 * q ∈ bank) ∧
          (∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
            (Rm : in_responses d M) (Sreg : in_6_16 d M)
            (It : in_iteration d M E Sreg),
            ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ),
            InfraredCharacterization M H → M.delta ≤ min 1 delta0 →
            let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
            ((∀ z : SpatialCoordinates d, ∀ r : ℝ, ∀ hr : 0 < r, r ≤ 1 →
                let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
                ∀ hP : (∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
                    ‖(w : SobolevData Q).1‖ ≤
                      K * ‖subspaceGradient (killedSobolevGraph Q) w‖),
                ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
                ∀ b : weakSobolevGraph Q,
                    (b.val.1 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi) →
                ∀ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
                    tsupport f ⊆ (Q : Set (SpatialCoordinates d)) →
                ∀ fL2 : DomainL2 Q,
                    ((fL2 : SpatialCoordinates d → ℝ)
                      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f) →
                let S : ResponseSpace Q := killedResponseSpace hP
                let a : ℕ → BilateralField d → PositiveCoefficient Q :=
                    fun N omega => cutoffPositiveCoefficient M H omega N z hr
                let load : S.space →L[ℝ] ℝ :=
                    (sobolevVolumeLoad fL2).comp S.space.subtypeL
                let uD : ℕ → BilateralField d → weakSobolevGraph Q :=
                    fun N omega => dirichletMinimizer S (a N omega) b
                let uK : ℕ → BilateralField d → S.space :=
                    fun N omega => responseSolution S (a N omega) load
                let RD : ℕ → BilateralField d → ℝ :=
                    fun N omega => dirichletResponse S (a N omega) b
                let RK : ℕ → BilateralField d → ℝ :=
                    fun N omega => inverseResponse S (a N omega) load
                ∃ KD KK : ℕ → BilateralField d → ℝ, ∃ B : ℝ, 0 ≤ B ∧
                  (∀ᵐ omega ∂Pm, ∀ N, 0 ≤ KD N omega ∧ 0 ≤ KK N omega ∧
                    (∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rad : ℝ,
                        0 < rad → rad ≤ 1 →
                        localGradientEnergy (a N omega)
                          (show MeasurableSet
                              (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) from
                            (Metric.isOpen_ball.inter Q.isOpen).measurableSet)
                          (sobolevGradient (uD N omega).val) ≤ KD N omega * rad ^ t) ∧
                    (∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rad : ℝ,
                        0 < rad → rad ≤ 1 →
                        localGradientEnergy (a N omega)
                          (show MeasurableSet
                              (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) from
                            (Metric.isOpen_ball.inter Q.isOpen).measurableSet)
                          (sobolevGradient (uK N omega).val) ≤ KK N omega * rad ^ t)) ∧
                  (∀ N, MemLp (KD N) (ENNReal.ofReal (3 * p)) Pm ∧
                        MemLp (KK N) (ENNReal.ofReal (3 * p)) Pm ∧
                        MemLp (RD N) (ENNReal.ofReal (3 * p)) Pm ∧
                        MemLp (RK N) (ENNReal.ofReal (3 * p)) Pm ∧
                        MemLp (RD N) (ENNReal.ofReal q) Pm ∧
                        MemLp (RK N) (ENNReal.ofReal q) Pm) ∧
                  (∀ N, eLpNorm (KD N) (ENNReal.ofReal (3 * p)) Pm +
                        eLpNorm (KK N) (ENNReal.ofReal (3 * p)) Pm +
                        eLpNorm (RD N) (ENNReal.ofReal (3 * p)) Pm +
                        eLpNorm (RK N) (ENNReal.ofReal (3 * p)) Pm +
                        eLpNorm (RD N) (ENNReal.ofReal q) Pm +
                        eLpNorm (RK N) (ENNReal.ofReal q) Pm ≤ ENNReal.ofReal B))) ∧
              (∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho → (∀ v : ℝ, 0 ≤ rho v) →
                (∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) → (∫ v, rho v) = 1 →
                ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
                let Qn : Opens (SpatialCoordinates d) := unitNeumannCube d
                let zn : SpatialCoordinates d := fun _ : Fin d => (1 / 2 : ℝ)
                ∀ hPn : (∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Qn,
                    ‖(w : SobolevData Qn).1‖ ≤
                      K * ‖subspaceGradient (meanZeroSobolevGraph Qn) w‖),
                let Sn : ResponseSpace Qn := meanZeroResponseSpace hPn
                let an : ℕ → BilateralField d → PositiveCoefficient Qn :=
                    fun N omega => cutoffPositiveCoefficient M H omega N zn one_pos
                let Lp : Sn.space →L[ℝ] ℝ :=
                    (affineNeumannLoad pvec).comp
                      (subspaceGradient (meanZeroSobolevGraph Qn))
                let yn : ℕ → BilateralField d → ℝ :=
                    fun N omega => inverseResponse Sn (an N omega) Lp
                ∃ Kcoerc K13 : ℕ → BilateralField d → ℝ, ∃ B9 B13 Bsm : ℝ,
                  0 ≤ B9 ∧ 0 ≤ B13 ∧ 0 ≤ Bsm ∧
                  (∀ᵐ omega ∂Pm, ∀ N, 0 ≤ Kcoerc N omega ∧ 0 ≤ K13 N omega ∧
                    (∀ v : meanZeroSobolevGraph Qn,
                        cubeFractionalSqNorm hd zn 1 one_pos threeQuarterOrder v.val.1 ≤
                          Kcoerc N omega *
                            sobolevCoefficientForm (an N omega) v.val v.val) ∧
                    (∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ v : meanZeroSobolevGraph Qn,
                        SolvesNeumann (an N omega) (faceBump rho pvec eps) v →
                        ∀ x ∈ (Qn : Set (SpatialCoordinates d)), ∀ rad : ℝ,
                            0 < rad → rad ≤ 1 →
                            localGradientEnergy (an N omega)
                              (show MeasurableSet
                                  (Metric.ball x rad ∩ (Qn : Set (SpatialCoordinates d))) from
                                (Metric.isOpen_ball.inter Qn.isOpen).measurableSet)
                              (sobolevGradient v.val) ≤
                              K13 N omega * eps ^ (-2 : ℝ) * rad ^ t)) ∧
                  (∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm ∧
                        MemLp (yn N) (ENNReal.ofReal (12 * p)) Pm ∧
                        MemLp (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm ∧
                        MemLp (yn N) (ENNReal.ofReal (4 * q)) Pm) ∧
                  (∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm +
                        eLpNorm (yn N) (ENNReal.ofReal (12 * p)) Pm +
                        eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm +
                        eLpNorm (yn N) (ENNReal.ofReal (4 * q)) Pm ≤
                          ENNReal.ofReal B9) ∧
                  (∀ N, MemLp (K13 N) (ENNReal.ofReal (3 * p)) Pm ∧
                        eLpNorm (K13 N) (ENNReal.ofReal (3 * p)) Pm ≤
                          ENNReal.ofReal B13) ∧
                  (∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ fL2 : DomainL2 Qn,
                      ((fL2 : SpatialCoordinates d → ℝ)
                        =ᵐ[volume.restrict (Qn : Set (SpatialCoordinates d))]
                        faceBump rho pvec eps) →
                      let ys : ℕ → BilateralField d → ℝ :=
                        fun N omega => inverseResponse Sn (an N omega)
                          ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL)
                      ∀ N, MemLp (ys N) (ENNReal.ofReal (3 * p)) Pm ∧
                           MemLp (ys N) (ENNReal.ofReal q) Pm ∧
                           eLpNorm (ys N) (ENNReal.ofReal (3 * p)) Pm +
                             eLpNorm (ys N) (ENNReal.ofReal q) Pm ≤
                               ENNReal.ofReal Bsm)) ∧
              (∀ z : SpatialCoordinates d, ∀ r : ℝ, ∀ hr : 0 < r, ∀ j : ℕ,
                ∀ v : ℝ, 0 < v →
                MemLp (fun omega : BilateralField d =>
                    sSup {w : ℝ |
                      ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                        w = |omega (-(j : ℤ)) x|})
                  (ENNReal.ofReal v) Pm))) := by
  choose δ2 hδ2pos hδ2 using aux_rem_bank_dirichlet_block d hd E P X W S t ht0 ht1
  choose δ7 hδ7pos hδ7 using aux_rem_bank_neumann_coercive_block d hd E P S
  choose δ8 hδ8pos hδ8 using aux_rem_bank_neumann_growth_block d hd E P X W D t ht0 ht1
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : 0 < t := by linarith
  have hth := aux_rem_bank_threshold
    (fun x => min (min (δ2 x (2 * x)) (δ7 x (2 * x))) (δ8 x))
    (fun x => lt_min (lt_min (hδ2pos x (2 * x)) (hδ7pos x (2 * x))) (hδ8pos x))
  refine ⟨fun d t => t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3),
    fun p _ _ => 2 * p,
    fun p _ _ => {3 * p, 2 * p, 12 * p, 4 * (2 * p)},
    fun _ _ bank => if h : bank.Nonempty then
      bank.inf' h (fun x => min (min (δ2 (x / 3) (2 * (x / 3))) (δ7 (x / 3) (2 * (x / 3))))
        (δ8 (x / 3))) else 1,
    ht0, ht1, ?_, rfl, ?_⟩
  · have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
    exact div_pos (div_pos (mul_pos ht (by linarith)) (by linarith)) (by positivity)
  intro p hp q bank delta0
  have hpq : p < 2 * p := by linarith
  obtain ⟨hth0, hthle⟩ := hth p
  refine ⟨hpq, hth0, by simp [bank], by simp [bank, q], by simp [bank], by simp [bank, q], ?_⟩
  intro M Rm Sreg It H hIC hδ Pm
  have hle : M.delta ≤ min 1 (min (min (δ2 p (2 * p)) (δ7 p (2 * p))) (δ8 p)) :=
    hδ.trans (min_le_min_left 1 hthle)
  have h1 : M.delta ≤ 1 := hle.trans (min_le_left _ _)
  have hA : M.delta ≤ min (min (δ2 p (2 * p)) (δ7 p (2 * p))) (δ8 p) :=
    hle.trans (min_le_right _ _)
  have h2 : M.delta ≤ min 1 (δ2 p (2 * p)) :=
    le_min h1 (hA.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have h7 : M.delta ≤ min 1 (δ7 p (2 * p)) :=
    le_min h1 (hA.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have h8 : M.delta ≤ δ8 p := hA.trans (min_le_right _ _)
  refine ⟨?dir, ?neu, ?lay⟩
  case dir =>
    exact hδ2 p (2 * p) hp hpq M Rm Sreg It H hIC h2
  case neu =>
    intro rho hrho hrho0 hrhos hrhoi pvec hpvec Qn zn hPn Sn an Lp yn
    obtain ⟨Kcoerc, B9, Bsm, hB9, hBsm, hcoer, hmom9, hnorm9, hys⟩ :=
      hδ7 p (2 * p) hp hpq M Rm H hIC h7 rho hrho hrho0 hrhos hrhoi pvec hpvec hPn
    obtain ⟨K13, B13, hB13, hK13ae, hK13mom⟩ :=
      hδ8 p hp M Rm Sreg It H hIC h8 rho hrho hrho0 hrhos hrhoi pvec hpvec
    refine ⟨Kcoerc, K13, B9, B13, Bsm, hB9, hB13, hBsm, ?_, hmom9, hnorm9, hK13mom, hys⟩
    filter_upwards [hK13ae] with omega hom N
    exact ⟨(hcoer N omega).1, (hom N).1, (hcoer N omega).2, (hom N).2⟩
  case lay =>
    exact aux_rem_bank_layer_block d hd M h1

end SubdiffusiveProcess.Paper
