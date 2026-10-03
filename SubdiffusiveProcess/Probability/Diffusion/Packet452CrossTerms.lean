module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452Markov
public import SubdiffusiveProcess.Probability.Diffusion.Packet452NestedFTC

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- The `x`-average of a one-time path average is the plain integral: invariance in path form,
for a `C₀` observable that is integrable. -/
theorem integral_path_eval_invariant_real {r : ℝ≥0} (hr : 0 < (r : ℝ)) (F : C₀(Vec d, ℝ))
    (hFint : Integrable (F : Vec d → ℝ)) :
    (∫ x, (∫ ω, F (ω r) ∂(laplacianContinuousLaw d x)) ∂volume) = ∫ y, F y ∂volume := by
  have hrw : ∀ x : Vec d, (∫ ω, F (ω r) ∂(laplacianContinuousLaw d x))
      = ∫ z, F z ∂(laplacianSemigroup d (Real.toNNReal (r : ℝ)) x) := by
    intro x
    rw [Real.toNNReal_coe]
    exact integral_c0_eval r F x
  simp only [hrw]
  exact integral_semigroup_invariant hr (map_continuous F).measurable hFint

/-- **The `AC` cross term at time `r`.**  `h` carries the compact support (it is `Δφ`), `g` need
only be `C₀` (it is `φ`). -/
theorem integral_cross_term_eval {r T : ℝ≥0} (hrT : r ≤ T) (hr : 0 < (r : ℝ))
    (h g : C₀(Vec d, ℝ)) (hhsupp : HasCompactSupport (h : Vec d → ℝ)) :
    (∫ x, (∫ ω, h (ω r) * g (ω T) ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ y, (h : Vec d → ℝ) y * (brownianSemigroup d) (T - r) g y ∂volume := by
  set F : C₀(Vec d, ℝ) := h * (brownianSemigroup d) (T - r) g with hFdef
  have hFsupp : HasCompactSupport (F : Vec d → ℝ) := by
    rw [hFdef, ZeroAtInftyContinuousMap.coe_mul]
    exact hhsupp.mul_right
  have hFint : Integrable (F : Vec d → ℝ) :=
    (map_continuous F).integrable_of_hasCompactSupport hFsupp
  have hsplit : ∀ x : Vec d, (∫ ω, h (ω r) * g (ω T) ∂(laplacianContinuousLaw d x))
      = ∫ ω, F (ω r) ∂(laplacianContinuousLaw d x) := by
    intro x
    rw [integral_markov_split hrT x (map_continuous h).measurable
      (fun y => abs_c0_apply_le h y) g]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    rw [hFdef, ZeroAtInftyContinuousMap.coe_mul]
    rfl
  simp only [hsplit]
  rw [integral_path_eval_invariant_real hr F hFint, hFdef]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  rw [ZeroAtInftyContinuousMap.coe_mul]
  rfl

/-- **The `BC` cross term at time `r`.**  No Markov property and no invariance: a one-time path
average is a semigroup average. -/
theorem integral_weight_eval {r : ℝ≥0} (w : Vec d → ℝ) (h : C₀(Vec d, ℝ)) :
    (∫ x, w x * (∫ ω, h (ω r) ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ x, w x * (brownianSemigroup d) r h x ∂volume := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [integral_c0_eval r h x]
  rfl

/-- **The two cross terms are the same function of the elapsed time.**  This is §2.1's
cancellation, with only the `dr` integration and the substitution `u = T − r` left outside. -/
theorem integral_cross_term_eq_weight {r T : ℝ≥0} (hrT : r ≤ T) (hr : 0 < (r : ℝ))
    (h g : C₀(Vec d, ℝ)) (hhsupp : HasCompactSupport (h : Vec d → ℝ)) :
    (∫ x, (∫ ω, h (ω r) * g (ω T) ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ x, (g : Vec d → ℝ) x * (brownianSemigroup d) (T - r) h x ∂volume := by
  rw [integral_cross_term_eval hrT hr h g hhsupp]
  have hhint : Integrable (h : Vec d → ℝ) :=
    (map_continuous h).integrable_of_hasCompactSupport hhsupp
  have hsymm := integral_semigroup_symm_toNNReal (t := ((T - r : ℝ≥0) : ℝ))
    (map_continuous h).measurable hhint (map_continuous g).measurable
    (fun y => abs_c0_apply_le g y)
  rw [Real.toNNReal_coe] at hsymm
  exact hsymm

/-! ## The `dr` integration: §2.1's cancellation, complete -/

/-- Truncated subtraction in `ℝ≥0` agrees with real subtraction inside `[0, T]`. -/
theorem sub_toNNReal_eq {T : ℝ≥0} {r : ℝ} (hr : 0 ≤ r) (hrT : r ≤ (T : ℝ)) :
    T - Real.toNNReal r = Real.toNNReal ((T : ℝ) - r) := by
  have hle : Real.toNNReal r ≤ T := by
    have h := Real.toNNReal_mono hrT
    rwa [Real.toNNReal_coe] at h
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_sub hle, Real.coe_toNNReal r hr, Real.coe_toNNReal _ (by linarith)]

/-- **§2.1's cross-term cancellation.**  The two cross terms of the expansion of
`∫ₓ E_x M_T² dx` are the same `dr` integral: the `AC` term becomes the `BC` term under the
substitution `u = T − r`.  Nothing but interval-integral algebra is left outside
`integral_cross_term_eq_weight`. -/
theorem integral_cross_terms_cancel (T : ℝ≥0) (h g : C₀(Vec d, ℝ))
    (hhsupp : HasCompactSupport (h : Vec d → ℝ)) :
    (∫ r in (0 : ℝ)..(T : ℝ),
        ∫ x, (∫ ω, h (ω (Real.toNNReal r)) * g (ω T) ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ u in (0 : ℝ)..(T : ℝ),
          ∫ x, (g : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal u) h x ∂volume := by
  set F : ℝ → ℝ := fun u =>
    ∫ x, (g : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal u) h x ∂volume with hF
  have hcongr : ∀ᵐ r : ℝ, r ∈ Set.uIoc (0 : ℝ) (T : ℝ) →
      (∫ x, (∫ ω, h (ω (Real.toNNReal r)) * g (ω T) ∂(laplacianContinuousLaw d x)) ∂volume)
        = F ((T : ℝ) - r) := by
    refine Eventually.of_forall fun r hrmem => ?_
    rw [Set.uIoc_of_le T.coe_nonneg] at hrmem
    have hr0 : (0 : ℝ) < r := hrmem.1
    have hrT : r ≤ (T : ℝ) := hrmem.2
    have hle : Real.toNNReal r ≤ T := by
      have h' := Real.toNNReal_mono hrT
      rwa [Real.toNNReal_coe] at h'
    have hpos : (0 : ℝ) < ((Real.toNNReal r : ℝ≥0) : ℝ) := by
      rw [Real.coe_toNNReal r hr0.le]; exact hr0
    rw [integral_cross_term_eq_weight hle hpos h g hhsupp, hF, sub_toNNReal_eq hr0.le hrT]
  rw [intervalIntegral.integral_congr_ae hcongr,
    intervalIntegral.integral_comp_sub_left F (T : ℝ)]
  simp

/-! ## The diagonal term's time integral -/

/-- **`∫₀ᵀ∫₀ᵀ K(|r−s|) dr ds = 2∫₀ᵀ (T−v)K(v) dv`**, the time-integral half of §2.2/§2.4 -- the
"exactly twice the triangle integral, no missing factor of `2` or `½`" both soldiers checked.

The proof never splits a two-dimensional domain: the inner integral is cut at `s` by
`integral_add_adjacent_intervals`, each piece is a one-dimensional change of variables
(`integral_comp_sub_left` on `[0,s]`, `integral_comp_sub_right` on `[s,T]`), and the outer
integral of `G s + G (T−s)` is `2∫₀ᵀG` by the same reflection.  `integral_integral_triangle`
(`Packet452NestedFTC`) then turns `∫₀ᵀ G` into the `(T−v)` weight. -/
theorem integral_integral_abs_sub {K : ℝ → ℝ} (hK : Continuous K) {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in (0 : ℝ)..T, ∫ r in (0 : ℝ)..T, K |r - s|)
      = 2 * ∫ v in (0 : ℝ)..T, (T - v) * K v := by
  set G : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, K v with hG
  have hGcont : Continuous G :=
    continuous_iff_continuousAt.2 fun t =>
      (intervalIntegral.integral_hasDerivAt_right (hK.intervalIntegrable 0 t)
        hK.aestronglyMeasurable.stronglyMeasurableAtFilter hK.continuousAt).continuousAt
  have hinner : ∀ s : ℝ, 0 ≤ s → s ≤ T →
      (∫ r in (0 : ℝ)..T, K |r - s|) = G s + G (T - s) := by
    intro s hs0 hsT
    have hsplit : (∫ r in (0 : ℝ)..T, K |r - s|)
        = (∫ r in (0 : ℝ)..s, K |r - s|) + ∫ r in s..T, K |r - s| :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((hK.comp (continuous_abs.comp (continuous_id.sub continuous_const))).intervalIntegrable
          0 s)
        ((hK.comp (continuous_abs.comp (continuous_id.sub continuous_const))).intervalIntegrable
          s T)).symm
    have hleft : (∫ r in (0 : ℝ)..s, K |r - s|) = ∫ r in (0 : ℝ)..s, K (s - r) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le hs0] at hr
      rw [abs_of_nonpos (by linarith [hr.2]), neg_sub]
    have hright : (∫ r in s..T, K |r - s|) = ∫ r in s..T, K (r - s) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le hsT] at hr
      rw [abs_of_nonneg (by linarith [hr.1])]
    rw [hsplit, hleft, hright, intervalIntegral.integral_comp_sub_left K s,
      intervalIntegral.integral_comp_sub_right K s]
    simp [hG]
  have houter : (∫ s in (0 : ℝ)..T, ∫ r in (0 : ℝ)..T, K |r - s|)
      = ∫ s in (0 : ℝ)..T, (G s + G (T - s)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hT] at hs
    exact hinner s hs.1 hs.2
  have hint1 : IntervalIntegrable G volume 0 T := hGcont.intervalIntegrable 0 T
  have hint2 : IntervalIntegrable (fun s : ℝ => G (T - s)) volume 0 T :=
    (hGcont.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 T
  rw [houter, intervalIntegral.integral_add hint1 hint2,
    intervalIntegral.integral_comp_sub_left G T]
  simp only [sub_self, sub_zero]
  rw [hG, integral_integral_triangle hK T]
  ring

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
