module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452DiagonalFubini

@[expose] public section

/-!
#  conclusion, the integrated Dynkin second moment

The integrated identity is:

```text
∫ₓ E_x[(φ(B_T) − φ(B_0) − ∫₀ᵀ Δφ(B_r)dr)²] dx = −2T⟨φ, Δφ⟩  ( = 2T·E(φ) ).
```

Everything mathematical is already proved; what this file adds is the six-term expansion and the
six integrability-in-`x` facts that let `∫ₓ` be distributed over it.  Five of the six majorants are
trivial because `B = φ(B_0)` turns the term into a function of `x` with **compact support**:

| term | value at `x` | majorant |
|---|---|---|
| `E_x[A²]` | `(P_T φ²)(x)` | itself, `integrable_semigroup_apply` |
| `E_x[B²]` | `φ(x)²` | itself |
| `E_x[C²]` | — | `T‖Δφ‖ ∫₀ᵀ (P_r\|Δφ\|)(x) dr`, `integrable_timeIntegral_semigroup` |
| `E_x[AB]` | `φ(x)(P_Tφ)(x)` | `‖φ‖·\|φ(x)\|` |
| `E_x[AC]` | — | `T‖Δφ‖·(P_T\|φ\|)(x)` |
| `E_x[BC]` | `∫₀ᵀ φ(x)(P_rΔφ)(x)dr` | `T‖Δφ‖·\|φ(x)\|` |

Only `E_x[C²]` needs more, and it reuses the product integrability of `(x,t) ↦ (P_t u)(x)` through
`Integrable.integral_prod_left`.

The two cross terms `∫ₓE_x[AC]dx` and `∫ₓE_x[BC]dx` are **both** `∫₀ᵀ⟨φ, P_uΔφ⟩du` -- the first by
`integral_cross_terms_cancel` (Markov + invariance + the substitution `u = T−r`), the second
because `B` is `𝓕₀`-measurable so no invariance is needed at all -- and they cancel.  What is left,
`2‖φ‖₂² − 2⟨φ,P_Tφ⟩ + Q`, is closed by `semigroup_pairing_nested_ftc` (§2.3) and
`integral_x_sq_timeIntegralPath` (§2.2/§2.4): `Q` is *exactly twice* the triangle integral that
§2.3 produces, so the two cancel and only `−2T⟨φ,Δφ⟩` survives.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## Integrability helpers -/

/-- The dominating function of the `x`-Fubini, as a standalone product-integrability statement. -/
theorem integrable_prod_semigroup_apply (T : ℝ≥0) (u : C₀(Vec d, ℝ))
    (hunn : ∀ z, 0 ≤ u z) (huint : Integrable (u : Vec d → ℝ)) :
    Integrable (fun p : Vec d × ℝ => (brownianSemigroup d) (Real.toNNReal p.2) u p.1)
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) := by
  have hdomcont : Continuous fun p : Vec d × ℝ =>
      (brownianSemigroup d) (Real.toNNReal p.2) u p.1 := by
    have h1 : Continuous fun t : ℝ => ((brownianSemigroup d) (Real.toNNReal t) u).toBCF :=
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp
        ((Semigroup.StronglyContinuousContractionSemigroup.continuous_operator_apply
          (brownianSemigroup d) continuous_id continuous_const).comp continuous_real_toNNReal)
    exact ContinuousEval.continuous_eval.comp ((h1.comp continuous_snd).prodMk continuous_fst)
  refine (integrable_prod_iff' hdomcont.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact integrable_semigroup_apply ht.1 u hunn huint
  · refine Integrable.congr (integrable_const (∫ z, (u : Vec d → ℝ) z ∂volume)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hrw : ∀ x : Vec d, ‖(brownianSemigroup d) (Real.toNNReal t) u x‖
        = (brownianSemigroup d) (Real.toNNReal t) u x := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (semigroup_apply_nonneg u hunn x)]
    simp only [hrw]
    rw [integral_semigroup_apply_eq ht.1 u huint]

/-- `x ↦ ∫₀ᵀ (P_t u)(x) dt` is integrable. -/
theorem integrable_timeIntegral_semigroup (T : ℝ≥0) (u : C₀(Vec d, ℝ))
    (hunn : ∀ z, 0 ≤ u z) (huint : Integrable (u : Vec d → ℝ)) :
    Integrable (fun x => ∫ t in (0 : ℝ)..(T : ℝ),
      (brownianSemigroup d) (Real.toNNReal t) u x) volume := by
  refine ((integrable_prod_semigroup_apply T u hunn huint).integral_prod_left).congr
    (Eventually.of_forall fun x => ?_)
  exact (intervalIntegral.integral_of_le T.coe_nonneg).symm

/-- Every bounded strongly measurable path functional has an integrable path expectation, when the
functional is dominated by a `C₀` observable at a single time. -/
theorem stronglyMeasurable_pathIntegral {F : ContinuousPath (Vec d) → ℝ}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable fun x : Vec d => ∫ ω, F ω ∂(laplacianContinuousLaw d x) :=
  StronglyMeasurable.integral_kernel_prod_right'
    (κ := laplacianContinuousLaw d) (hF.comp_measurable measurable_snd)

theorem integrable_pathIntegral_of_le {F : ContinuousPath (Vec d) → ℝ} {G : Vec d → ℝ}
    (hF : StronglyMeasurable F) (hG : Integrable G)
    (hle : ∀ x : Vec d, ‖∫ ω, F ω ∂(laplacianContinuousLaw d x)‖ ≤ G x) :
    Integrable (fun x => ∫ ω, F ω ∂(laplacianContinuousLaw d x)) volume :=
  Integrable.mono' hG (stronglyMeasurable_pathIntegral hF).aestronglyMeasurable
    (Eventually.of_forall hle)

/-! ## Readouts at a single time -/

theorem brownianSemigroup_zero (u : C₀(Vec d, ℝ)) : (brownianSemigroup d) 0 u = u := by
  rw [Semigroup.StronglyContinuousContractionSemigroup.operator_zero]
  rfl

theorem integral_semigroup_zero (v : C₀(Vec d, ℝ)) (x : Vec d) :
    (∫ z, (v : Vec d → ℝ) z ∂(laplacianSemigroup d 0 x)) = v x := by
  have hker : (laplacianSemigroup d (0 : ℝ≥0)) x = Measure.dirac x := by
    show ((laplacianSemigroup d).kernel 0) x = Measure.dirac x
    rw [(laplacianSemigroup d).kernel_zero, Kernel.id_apply]
  rw [hker, integral_dirac' _ _ (map_continuous v).stronglyMeasurable]

theorem integral_path_eval_zero (v : C₀(Vec d, ℝ)) (x : Vec d) :
    (∫ ω, (v : Vec d → ℝ) (ω 0) ∂(laplacianContinuousLaw d x)) = v x := by
  rw [integral_c0_eval 0 v x, integral_semigroup_zero v x]

theorem integral_path_sq_eval (u : C₀(Vec d, ℝ)) (t : ℝ≥0) (x : Vec d) :
    (∫ ω, (u (ω t)) ^ 2 ∂(laplacianContinuousLaw d x)) = (brownianSemigroup d) t (u * u) x := by
  have hrw : ∀ ω : ContinuousPath (Vec d), (u (ω t)) ^ 2 = (u * u) (ω t) := by
    intro ω
    rw [ZeroAtInftyContinuousMap.coe_mul]
    simp [sq]
  simp only [hrw]
  exact integral_c0_eval t (u * u) x

/-- The `𝓕₀`-anchored product: no invariance and no Markov property beyond the one step. -/
theorem integral_path_eval_zero_mul (h u : C₀(Vec d, ℝ)) (t : ℝ≥0) (x : Vec d) :
    (∫ ω, h (ω 0) * u (ω t) ∂(laplacianContinuousLaw d x))
      = (h : Vec d → ℝ) x * (brownianSemigroup d) t u x := by
  rw [integral_markov_split (r := 0) (T := t) (zero_le) x (map_continuous h).measurable
    (fun y => abs_c0_apply_le h y) u, tsub_zero]
  have hrw : ∀ ω : ContinuousPath (Vec d),
      h (ω 0) * (∫ z, (u : Vec d → ℝ) z ∂(laplacianSemigroup d t (ω 0)))
        = (h * (brownianSemigroup d) t u) (ω 0) := by
    intro ω
    rw [ZeroAtInftyContinuousMap.coe_mul]
    rfl
  simp only [hrw]
  rw [integral_path_eval_zero (h * (brownianSemigroup d) t u) x,
    ZeroAtInftyContinuousMap.coe_mul]
  rfl

theorem abs_timeIntegralPath_le_abs (ψ : C₀(Vec d, ℝ))
    (hsupp : HasCompactSupport (ψ : Vec d → ℝ)) (T : ℝ≥0) (ω : ContinuousPath (Vec d)) :
    |timeIntegralPath ψ T ω| ≤ timeIntegralPath (absC0 ψ hsupp) T ω := by
  refine (intervalIntegral.abs_integral_le_integral_abs T.coe_nonneg).trans_eq ?_
  exact intervalIntegral.integral_congr fun s _ => rfl

theorem integral_path_timeIntegral (ψ : C₀(Vec d, ℝ)) (T : ℝ≥0) (x : Vec d) :
    (∫ ω, timeIntegralPath ψ T ω ∂(laplacianContinuousLaw d x))
      = ∫ t in (0 : ℝ)..(T : ℝ), (brownianSemigroup d) (Real.toNNReal t) ψ x := by
  rw [show (∫ ω, timeIntegralPath ψ T ω ∂(laplacianContinuousLaw d x))
      = ∫ ω, (∫ s in (0 : ℝ)..(T : ℝ), ψ (ω (Real.toNNReal s)))
        ∂(laplacianContinuousLaw d x) from rfl,
    ← intervalIntegral_integral_swap_path ψ T x]
  exact intervalIntegral.integral_congr fun t _ => integral_c0_eval (Real.toNNReal t) ψ x

/-! ## The six-term expansion -/

private theorem integrable_of_bounded {F : ContinuousPath (Vec d) → ℝ} {CF : ℝ}
    (hF : StronglyMeasurable F) (hb : ∀ ω, |F ω| ≤ CF) (x : Vec d) :
    Integrable F (laplacianContinuousLaw d x) :=
  Integrable.of_bound hF.aestronglyMeasurable CF
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using! hb ω)

/-- **The integrated Dynkin second moment**, §2's conclusion. -/
theorem integral_x_sq_dynkin_increment (f g : C₀(Vec d, ℝ))
    (hf2 : ContDiff ℝ 2 (f : Vec d → ℝ)) (hfsupp : HasCompactSupport (f : Vec d → ℝ))
    (hgsupp : HasCompactSupport (g : Vec d → ℝ))
    (hgdef : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
    {T : ℝ≥0} (hT : 0 < (T : ℝ)) :
    (∫ x, (∫ ω, ((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g T ω) ^ 2
        ∂(laplacianContinuousLaw d x)) ∂volume)
      = -2 * (T : ℝ) * ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume := by
  classical
  have hfint : Integrable (f : Vec d → ℝ) :=
    (map_continuous f).integrable_of_hasCompactSupport hfsupp
  have hgint : Integrable (g : Vec d → ℝ) :=
    (map_continuous g).integrable_of_hasCompactSupport hgsupp
  set A : ContinuousPath (Vec d) → ℝ := fun ω => (f : Vec d → ℝ) (ω T) with hAdef
  set B : ContinuousPath (Vec d) → ℝ := fun ω => (f : Vec d → ℝ) (ω 0) with hBdef
  set C : ContinuousPath (Vec d) → ℝ := timeIntegralPath g T with hCdef
  have hAsm : StronglyMeasurable A :=
    (map_continuous f).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess T).stronglyMeasurable
  have hBsm : StronglyMeasurable B :=
    (map_continuous f).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess 0).stronglyMeasurable
  have hCsm : StronglyMeasurable C := stronglyMeasurable_timeIntegralPath g T
  have hAb : ∀ ω, |A ω| ≤ ‖f‖ := fun ω => abs_c0_apply_le f _
  have hBb : ∀ ω, |B ω| ≤ ‖f‖ := fun ω => abs_c0_apply_le f _
  have hCb : ∀ ω, |C ω| ≤ ‖g‖ * (T : ℝ) := abs_timeIntegralPath_le g T
  have hA2sm : StronglyMeasurable fun ω => A ω ^ 2 := hAsm.pow 2
  have hB2sm : StronglyMeasurable fun ω => B ω ^ 2 := hBsm.pow 2
  have hC2sm : StronglyMeasurable fun ω => C ω ^ 2 := hCsm.pow 2
  have hABsm : StronglyMeasurable fun ω => A ω * B ω := hAsm.mul hBsm
  have hACsm : StronglyMeasurable fun ω => A ω * C ω := hAsm.mul hCsm
  have hBCsm : StronglyMeasurable fun ω => B ω * C ω := hBsm.mul hCsm
  -- pointwise expansion under each `P_x`
  have hexp : ∀ x : Vec d,
      (∫ ω, (A ω - B ω - C ω) ^ 2 ∂(laplacianContinuousLaw d x))
        = (∫ ω, A ω ^ 2 ∂(laplacianContinuousLaw d x))
          + (∫ ω, B ω ^ 2 ∂(laplacianContinuousLaw d x))
          + (∫ ω, C ω ^ 2 ∂(laplacianContinuousLaw d x))
          - 2 * (∫ ω, A ω * B ω ∂(laplacianContinuousLaw d x))
          - 2 * (∫ ω, A ω * C ω ∂(laplacianContinuousLaw d x))
          + 2 * (∫ ω, B ω * C ω ∂(laplacianContinuousLaw d x)) := by
    intro x
    have iA2 : Integrable (fun ω => A ω ^ 2) (laplacianContinuousLaw d x) :=
      integrable_of_bounded hA2sm (CF := ‖f‖ ^ 2)
        (fun ω => by
          simp only [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hAb ω) 2) x
    have iB2 : Integrable (fun ω => B ω ^ 2) (laplacianContinuousLaw d x) :=
      integrable_of_bounded hB2sm (CF := ‖f‖ ^ 2)
        (fun ω => by
          simp only [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hBb ω) 2) x
    have iC2 : Integrable (fun ω => C ω ^ 2) (laplacianContinuousLaw d x) :=
      integrable_of_bounded hC2sm (CF := (‖g‖ * (T : ℝ)) ^ 2)
        (fun ω => by
          simp only [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hCb ω) 2) x
    have iAB : Integrable (fun ω => A ω * B ω) (laplacianContinuousLaw d x) :=
      integrable_of_bounded hABsm (CF := ‖f‖ * ‖f‖)
        (fun ω => by
          simp only [abs_mul]
          exact mul_le_mul (hAb ω) (hBb ω) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hAb ω))) x
    have iAC : Integrable (fun ω => A ω * C ω) (laplacianContinuousLaw d x) :=
      integrable_of_bounded hACsm (CF := ‖f‖ * (‖g‖ * (T : ℝ)))
        (fun ω => by
          simp only [abs_mul]
          exact mul_le_mul (hAb ω) (hCb ω) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hAb ω))) x
    have iBC : Integrable (fun ω => B ω * C ω) (laplacianContinuousLaw d x) :=
      integrable_of_bounded hBCsm (CF := ‖f‖ * (‖g‖ * (T : ℝ)))
        (fun ω => by
          simp only [abs_mul]
          exact mul_le_mul (hBb ω) (hCb ω) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hBb ω))) x
    have hpt : ∀ ω, (A ω - B ω - C ω) ^ 2
        = A ω ^ 2 + B ω ^ 2 + C ω ^ 2 - 2 * (A ω * B ω) - 2 * (A ω * C ω)
          + 2 * (B ω * C ω) := fun ω => by ring
    have i1 : Integrable (fun ω => A ω ^ 2 + B ω ^ 2) (laplacianContinuousLaw d x) :=
      iA2.add iB2
    have i2 : Integrable (fun ω => A ω ^ 2 + B ω ^ 2 + C ω ^ 2) (laplacianContinuousLaw d x) :=
      i1.add iC2
    have i3 : Integrable (fun ω => 2 * (A ω * B ω)) (laplacianContinuousLaw d x) :=
      iAB.const_mul 2
    have i4 : Integrable (fun ω => A ω ^ 2 + B ω ^ 2 + C ω ^ 2 - 2 * (A ω * B ω))
        (laplacianContinuousLaw d x) := i2.sub i3
    have i5 : Integrable (fun ω => 2 * (A ω * C ω)) (laplacianContinuousLaw d x) :=
      iAC.const_mul 2
    have i6 : Integrable
        (fun ω => A ω ^ 2 + B ω ^ 2 + C ω ^ 2 - 2 * (A ω * B ω) - 2 * (A ω * C ω))
        (laplacianContinuousLaw d x) := i4.sub i5
    have i7 : Integrable (fun ω => 2 * (B ω * C ω)) (laplacianContinuousLaw d x) :=
      iBC.const_mul 2
    simp only [hpt]
    rw [integral_add i6 i7, integral_sub i4 i5, integral_sub i2 i3,
      integral_add i1 iC2, integral_add iA2 iB2,
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hgoalrw : (∫ x, (∫ ω, ((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0)
        - timeIntegralPath g T ω) ^ 2 ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ x, (∫ ω, (A ω - B ω - C ω) ^ 2 ∂(laplacianContinuousLaw d x)) ∂volume := rfl
  rw [hgoalrw]
  simp only [hexp]
  -- the `C₀` building blocks
  set uf : C₀(Vec d, ℝ) := absC0 f hfsupp with huf
  set ug : C₀(Vec d, ℝ) := absC0 g hgsupp with hug
  have hufint : Integrable (uf : Vec d → ℝ) :=
    (map_continuous uf).integrable_of_hasCompactSupport (hasCompactSupport_absC0 f hfsupp)
  have hugint : Integrable (ug : Vec d → ℝ) :=
    (map_continuous ug).integrable_of_hasCompactSupport (hasCompactSupport_absC0 g hgsupp)
  set uff : C₀(Vec d, ℝ) := f * f with huff
  have huffcoe : ((uff : C₀(Vec d, ℝ)) : Vec d → ℝ) = (f : Vec d → ℝ) * (f : Vec d → ℝ) := by
    rw [huff, ZeroAtInftyContinuousMap.coe_mul]
  have huffsupp : HasCompactSupport (uff : Vec d → ℝ) := by
    rw [huffcoe]; exact hfsupp.mul_right
  have huffint : Integrable (uff : Vec d → ℝ) :=
    (map_continuous uff).integrable_of_hasCompactSupport huffsupp
  have huffnn : ∀ z, 0 ≤ (uff : Vec d → ℝ) z := by
    intro z; rw [huffcoe]; exact mul_self_nonneg _
  have hN : (∫ z, (uff : Vec d → ℝ) z ∂volume) = ∫ x, (f : Vec d → ℝ) x ^ 2 ∂volume := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    rw [huffcoe]
    simp [sq]
  have hsemint : ∀ u : C₀(Vec d, ℝ), (∀ z, 0 ≤ (u : Vec d → ℝ) z) →
      Integrable (u : Vec d → ℝ) →
      Integrable (fun x => (brownianSemigroup d) T u x) volume := by
    intro u hunn huint
    have h := integrable_semigroup_apply (t := (T : ℝ)) hT u hunn huint
    rwa [Real.toNNReal_coe] at h
  have hseminteg : ∀ u : C₀(Vec d, ℝ), Integrable (u : Vec d → ℝ) →
      (∫ x, (brownianSemigroup d) T u x ∂volume) = ∫ z, (u : Vec d → ℝ) z ∂volume := by
    intro u huint
    have h := integral_semigroup_apply_eq (t := (T : ℝ)) hT u huint
    rwa [Real.toNNReal_coe] at h
  -- term values
  have e1 : ∀ x : Vec d, (∫ ω, A ω ^ 2 ∂(laplacianContinuousLaw d x))
      = (brownianSemigroup d) T uff x := fun x => integral_path_sq_eval f T x
  have e2 : ∀ x : Vec d, (∫ ω, B ω ^ 2 ∂(laplacianContinuousLaw d x))
      = (uff : Vec d → ℝ) x := by
    intro x
    rw [integral_path_sq_eval f 0 x, brownianSemigroup_zero]
  have e4 : ∀ x : Vec d, (∫ ω, A ω * B ω ∂(laplacianContinuousLaw d x))
      = (f : Vec d → ℝ) x * (brownianSemigroup d) T f x := by
    intro x
    have hc : ∀ ω : ContinuousPath (Vec d), A ω * B ω = B ω * A ω := fun ω => mul_comm _ _
    simp only [hc]
    exact integral_path_eval_zero_mul f f T x
  -- integrability in `x`
  have j1 : Integrable (fun x => ∫ ω, A ω ^ 2 ∂(laplacianContinuousLaw d x)) volume :=
    (hsemint uff huffnn huffint).congr (Eventually.of_forall fun x => (e1 x).symm)
  have j2 : Integrable (fun x => ∫ ω, B ω ^ 2 ∂(laplacianContinuousLaw d x)) volume :=
    huffint.congr (Eventually.of_forall fun x => (e2 x).symm)
  have j4 : Integrable (fun x => ∫ ω, A ω * B ω ∂(laplacianContinuousLaw d x)) volume := by
    refine Integrable.congr ?_ (Eventually.of_forall fun x => (e4 x).symm)
    exact ((map_continuous f).mul (map_continuous ((brownianSemigroup d) T f))
      |>.integrable_of_hasCompactSupport hfsupp.mul_right)
  have hCabs : ∀ ω, |C ω| ≤ timeIntegralPath ug T ω := abs_timeIntegralPath_le_abs g hgsupp T
  have j3 : Integrable (fun x => ∫ ω, C ω ^ 2 ∂(laplacianContinuousLaw d x)) volume := by
    refine integrable_pathIntegral_of_le hC2sm
      ((integrable_timeIntegral_semigroup T ug (absC0_nonneg g hgsupp) hugint).const_mul
        (‖g‖ * (T : ℝ))) fun x => ?_
    have hmaj : Integrable (fun ω => (‖g‖ * (T : ℝ)) * timeIntegralPath ug T ω)
        (laplacianContinuousLaw d x) :=
      (integrable_of_bounded (stronglyMeasurable_timeIntegralPath ug T)
        (abs_timeIntegralPath_le ug T) x).const_mul _
    have hint2 : Integrable (fun ω => C ω ^ 2) (laplacianContinuousLaw d x) :=
      integrable_of_bounded hC2sm (CF := (‖g‖ * (T : ℝ)) ^ 2)
        (fun ω => (abs_pow (C ω) 2).trans_le
          (pow_le_pow_left₀ (abs_nonneg _) (hCb ω) 2)) x
    calc ‖∫ ω, C ω ^ 2 ∂(laplacianContinuousLaw d x)‖
        ≤ ∫ ω, ‖C ω ^ 2‖ ∂(laplacianContinuousLaw d x) := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (‖g‖ * (T : ℝ)) * timeIntegralPath ug T ω ∂(laplacianContinuousLaw d x) := by
          refine integral_mono hint2.norm hmaj fun ω => ?_
          have h1 : ‖C ω ^ 2‖ = |C ω| * |C ω| := by
            rw [Real.norm_eq_abs, abs_pow]
            ring
          rw [h1]
          exact mul_le_mul (hCb ω) (hCabs ω) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hCb ω))
      _ = (‖g‖ * (T : ℝ)) * ∫ t in (0 : ℝ)..(T : ℝ),
            (brownianSemigroup d) (Real.toNNReal t) ug x := by
          rw [integral_const_mul, integral_path_timeIntegral ug T x]
  have j5 : Integrable (fun x => ∫ ω, A ω * C ω ∂(laplacianContinuousLaw d x)) volume := by
    refine integrable_pathIntegral_of_le hACsm
      ((hsemint uf (absC0_nonneg f hfsupp) hufint).const_mul (‖g‖ * (T : ℝ))) fun x => ?_
    have hint2 : Integrable (fun ω => A ω * C ω) (laplacianContinuousLaw d x) :=
      integrable_of_bounded hACsm (CF := ‖f‖ * (‖g‖ * (T : ℝ)))
        (fun ω => by
          simp only [abs_mul]
          exact mul_le_mul (hAb ω) (hCb ω) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hAb ω))) x
    have hmaj : Integrable (fun ω => (‖g‖ * (T : ℝ)) * (uf : Vec d → ℝ) (ω T))
        (laplacianContinuousLaw d x) :=
      (integrable_of_bounded ((map_continuous uf).comp_stronglyMeasurable
        (ContinuousPath.measurable_coordinateProcess T).stronglyMeasurable)
        (fun ω => abs_c0_apply_le uf _) x).const_mul _
    calc ‖∫ ω, A ω * C ω ∂(laplacianContinuousLaw d x)‖
        ≤ ∫ ω, ‖A ω * C ω‖ ∂(laplacianContinuousLaw d x) := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (‖g‖ * (T : ℝ)) * (uf : Vec d → ℝ) (ω T) ∂(laplacianContinuousLaw d x) := by
          refine integral_mono hint2.norm hmaj fun ω => ?_
          rw [Real.norm_eq_abs, abs_mul]
          show |A ω| * |C ω| ≤ (‖g‖ * (T : ℝ)) * |A ω|
          calc |A ω| * |C ω| ≤ |A ω| * (‖g‖ * (T : ℝ)) :=
                mul_le_mul_of_nonneg_left (hCb ω) (abs_nonneg _)
            _ = (‖g‖ * (T : ℝ)) * |A ω| := mul_comm _ _
      _ = (‖g‖ * (T : ℝ)) * (brownianSemigroup d) T uf x := by
          rw [integral_const_mul, integral_c0_eval T uf x]
          rfl
  have j6 : Integrable (fun x => ∫ ω, B ω * C ω ∂(laplacianContinuousLaw d x)) volume := by
    refine integrable_pathIntegral_of_le hBCsm
      (hufint.const_mul (‖g‖ * (T : ℝ))) fun x => ?_
    have hint2 : Integrable (fun ω => B ω * C ω) (laplacianContinuousLaw d x) :=
      integrable_of_bounded hBCsm (CF := ‖f‖ * (‖g‖ * (T : ℝ)))
        (fun ω => by
          simp only [abs_mul]
          exact mul_le_mul (hBb ω) (hCb ω) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hBb ω))) x
    have hmaj : Integrable (fun ω => (‖g‖ * (T : ℝ)) * (uf : Vec d → ℝ) (ω 0))
        (laplacianContinuousLaw d x) :=
      (integrable_of_bounded ((map_continuous uf).comp_stronglyMeasurable
        (ContinuousPath.measurable_coordinateProcess 0).stronglyMeasurable)
        (fun ω => abs_c0_apply_le uf _) x).const_mul _
    calc ‖∫ ω, B ω * C ω ∂(laplacianContinuousLaw d x)‖
        ≤ ∫ ω, ‖B ω * C ω‖ ∂(laplacianContinuousLaw d x) := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (‖g‖ * (T : ℝ)) * (uf : Vec d → ℝ) (ω 0) ∂(laplacianContinuousLaw d x) := by
          refine integral_mono hint2.norm hmaj fun ω => ?_
          rw [Real.norm_eq_abs, abs_mul]
          show |B ω| * |C ω| ≤ (‖g‖ * (T : ℝ)) * |B ω|
          calc |B ω| * |C ω| ≤ |B ω| * (‖g‖ * (T : ℝ)) :=
                mul_le_mul_of_nonneg_left (hCb ω) (abs_nonneg _)
            _ = (‖g‖ * (T : ℝ)) * |B ω| := mul_comm _ _
      _ = (‖g‖ * (T : ℝ)) * (uf : Vec d → ℝ) x := by
          rw [integral_const_mul, integral_path_eval_zero uf x]
  -- split the `x`-integral
  have J1 : Integrable (fun x => (∫ ω, A ω ^ 2 ∂(laplacianContinuousLaw d x))
      + ∫ ω, B ω ^ 2 ∂(laplacianContinuousLaw d x)) volume := j1.add j2
  have J2 : Integrable (fun x => (∫ ω, A ω ^ 2 ∂(laplacianContinuousLaw d x))
      + (∫ ω, B ω ^ 2 ∂(laplacianContinuousLaw d x))
      + ∫ ω, C ω ^ 2 ∂(laplacianContinuousLaw d x)) volume := J1.add j3
  have J3 : Integrable (fun x => 2 * ∫ ω, A ω * B ω ∂(laplacianContinuousLaw d x)) volume :=
    j4.const_mul 2
  have J4 : Integrable (fun x => (∫ ω, A ω ^ 2 ∂(laplacianContinuousLaw d x))
      + (∫ ω, B ω ^ 2 ∂(laplacianContinuousLaw d x))
      + (∫ ω, C ω ^ 2 ∂(laplacianContinuousLaw d x))
      - 2 * ∫ ω, A ω * B ω ∂(laplacianContinuousLaw d x)) volume := J2.sub J3
  have J5 : Integrable (fun x => 2 * ∫ ω, A ω * C ω ∂(laplacianContinuousLaw d x)) volume :=
    j5.const_mul 2
  have J6 : Integrable (fun x => (∫ ω, A ω ^ 2 ∂(laplacianContinuousLaw d x))
      + (∫ ω, B ω ^ 2 ∂(laplacianContinuousLaw d x))
      + (∫ ω, C ω ^ 2 ∂(laplacianContinuousLaw d x))
      - 2 * (∫ ω, A ω * B ω ∂(laplacianContinuousLaw d x))
      - 2 * ∫ ω, A ω * C ω ∂(laplacianContinuousLaw d x)) volume := J4.sub J5
  have J7 : Integrable (fun x => 2 * ∫ ω, B ω * C ω ∂(laplacianContinuousLaw d x)) volume :=
    j6.const_mul 2
  rw [integral_add J6 J7, integral_sub J4 J5, integral_sub J2 J3,
    integral_add J1 j3, integral_add j1 j2,
    integral_const_mul, integral_const_mul, integral_const_mul]
  -- the six values
  have v1 : (∫ x, (∫ ω, A ω ^ 2 ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ x, (f : Vec d → ℝ) x ^ 2 ∂volume :=
    (integral_congr_ae (Eventually.of_forall e1)).trans
      ((hseminteg uff huffint).trans hN)
  have v2 : (∫ x, (∫ ω, B ω ^ 2 ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ x, (f : Vec d → ℝ) x ^ 2 ∂volume :=
    (integral_congr_ae (Eventually.of_forall e2)).trans hN
  have v3 : (∫ x, (∫ ω, C ω ^ 2 ∂(laplacianContinuousLaw d x)) ∂volume)
      = 2 * ∫ v in (0 : ℝ)..(T : ℝ), ((T : ℝ) - v) *
          ∫ y, (g : Vec d → ℝ) y * (brownianSemigroup d) (Real.toNNReal v) g y ∂volume :=
    integral_x_sq_timeIntegralPath g hgsupp T
  have v4 : (∫ x, (∫ ω, A ω * B ω ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ x, (f : Vec d → ℝ) x * (brownianSemigroup d) T f x ∂volume :=
    integral_congr_ae (Eventually.of_forall e4)
  have v5 : (∫ x, (∫ ω, A ω * C ω ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ u in (0 : ℝ)..(T : ℝ),
          ∫ x, (f : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal u) g x ∂volume := by
    have h5 : ∀ x : Vec d, (∫ ω, A ω * C ω ∂(laplacianContinuousLaw d x))
        = ∫ r in (0 : ℝ)..(T : ℝ),
            ∫ ω, A ω * g (ω (Real.toNNReal r)) ∂(laplacianContinuousLaw d x) := fun x =>
      (intervalIntegral_integral_swap_path_mul g T x hAsm hAb).symm
    simp only [h5]
    rw [integral_integral_swap_x_time T hAsm hAb g hgsupp,
      ← integral_cross_terms_cancel T g f hgsupp]
    refine intervalIntegral.integral_congr fun r _ => ?_
    exact integral_congr_ae (Eventually.of_forall fun x =>
      integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _))
  have v6 : (∫ x, (∫ ω, B ω * C ω ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ u in (0 : ℝ)..(T : ℝ),
          ∫ x, (f : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal u) g x ∂volume := by
    have h6 : ∀ x : Vec d, (∫ ω, B ω * C ω ∂(laplacianContinuousLaw d x))
        = ∫ r in (0 : ℝ)..(T : ℝ),
            ∫ ω, B ω * g (ω (Real.toNNReal r)) ∂(laplacianContinuousLaw d x) := fun x =>
      (intervalIntegral_integral_swap_path_mul g T x hBsm hBb).symm
    simp only [h6]
    rw [integral_integral_swap_x_time T hBsm hBb g hgsupp]
    refine intervalIntegral.integral_congr fun r _ => ?_
    exact integral_congr_ae (Eventually.of_forall fun x =>
      integral_path_eval_zero_mul f g (Real.toNNReal r) x)
  rw [v1, v2, v3, v4, v5, v6]
  -- §2.3 closes it
  have hnested := semigroup_pairing_nested_ftc f g hf2 hfsupp hgsupp hgdef
    (T := (T : ℝ)) hT.le
  rw [Real.toNNReal_coe] at hnested
  linarith [hnested]

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
