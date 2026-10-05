module

public import SubdiffusiveProcess.Probability.Diffusion.HuntContinuityStart
public import SubdiffusiveProcess.Probability.Diffusion.HuntDensity
public import SubdiffusiveProcess.Probability.Diffusion.HuntIdentity

@[expose] public section

/-!
# The joint-continuity route: the first two steps

Steps B0 and B2 of the recommended route to
`BrownianHuntContinuity d`.  Both are independent of the killed Chapman-Kolmogorov identity (B1)
and of the form problem, so they are proved first.

* `continuousOn_huntCorrection_end`, `continuous_laplacianDensity_end` — the fixed-start
  continuity of `HuntContinuityStart.lean`, read in the terminal variable alone.
* `huntDensity_eq_sub` (**B0**) — on the interior the truncation in `huntDensity` is inactive:
  `huntDensity U t x y = laplacianDensity t x y - huntCorrection U t x y` for `x, y ∈ U`,
  `t > 0`.  The route: the inequality `H ≤ g` holds almost everywhere on `U` by the
  Hunt identity (`huntCorrection_le_gaussian_ae`, now discharged with
  `brownian_hunt_identity` rather than carried as a hypothesis), and both sides are continuous on
  the open set `U`, so `Measure.eqOn_open_of_ae_eq` promotes it to every point.  No continuity in
  the starting variable is used — which is the point, since that is what the route is trying to
  establish.
* `exists_time_forall_mem_of_isCompact` (**B2**) — a compact family of paths all starting inside
  an open set stays inside it for a common positive time.  This is the tube lemma applied to
  `C × {0}` inside the preimage of `U` under path evaluation; the evaluation
  `C(NNReal, Vec d) × NNReal → Vec d` is jointly continuous because `NNReal` is locally compact
  (`continuous_eval` for the compact-open topology).  Nothing about `∂U` is used, and no
  translated Brownian law is constructed.

B2 is stated for an arbitrary compact set of paths so that B3 can feed it the tightness compact
set of `SubMarkovKernelSemigroup.IsConservative.exists_isCompact_measure_compl_le`.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The exit correction, as a function of the terminal point alone, is continuous on the
domain. -/
theorem continuousOn_huntCorrection_end {U : Set (Vec d)} (hU : IsOpen U)
    {x : Vec d} (hx : x ∈ U) {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun y : Vec d => huntCorrection U t x y) U := by
  have hmaps : MapsTo (fun y : Vec d => ((t, y) : ℝ × Vec d)) U (Ioi 0 ×ˢ U) :=
    fun y hy => ⟨ht, hy⟩
  exact (continuousOn_huntCorrection_start hU hx).comp
    (Continuous.continuousOn (by fun_prop)) hmaps

/-- The free Gaussian, as a function of the terminal point alone, is continuous. -/
theorem continuous_laplacianDensity_end (t : ℝ) (x : Vec d) :
    Continuous (fun y : Vec d => laplacianDensity t x y) := by
  unfold laplacianDensity gaussianPDFReal
  fun_prop

/-- **B0 of the continuity route.**  On the interior the truncation in the definition of
`huntDensity` is inactive: the exit correction never exceeds the free Gaussian there.  The
inequality holds almost everywhere by the proved Hunt identity, and both sides are continuous on
the open set `U`, so it holds at every point. -/
theorem huntDensity_eq_sub {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) {y : Vec d} (hy : y ∈ U) :
    huntDensity U t x y = laplacianDensity t x y - huntCorrection U t x y := by
  have hae0 := huntCorrection_le_gaussian_ae (brownian_hunt_identity d) hU hUb ht hx
  have hae : (fun w : Vec d => huntDensity U t x w) =ᵐ[volume.restrict U]
      fun w : Vec d => laplacianDensity t x w - huntCorrection U t x w := by
    filter_upwards [hae0] with w hw
    have hreal : huntCorrection U t x w ≤ laplacianDensity t x w :=
      (ENNReal.ofReal_le_ofReal_iff (laplacianDensity_nonneg t x w)).mp hw
    rw [huntDensity, max_eq_left (by linarith)]
  have hcont2 : ContinuousOn
      (fun w : Vec d => laplacianDensity t x w - huntCorrection U t x w) U :=
    ContinuousOn.sub (continuous_laplacianDensity_end t x).continuousOn
      (continuousOn_huntCorrection_end hU hx ht)
  have hcont1 : ContinuousOn (fun w : Vec d => huntDensity U t x w) U := by
    have hsup : ContinuousOn
        (fun w : Vec d => (laplacianDensity t x w - huntCorrection U t x w) ⊔ (0:ℝ)) U :=
      ContinuousOn.sup hcont2 continuousOn_const
    exact hsup
  exact Measure.eqOn_open_of_ae_eq hae hU hcont1 hcont2 hy

/-- **B2 of the continuity route.**  A compact family of paths that all start inside the
open set stays inside it for a common positive time.  This is the tube lemma applied to
`{0} × C` inside the preimage of `U` under path evaluation, which is jointly continuous because
`NNReal` is locally compact. -/
theorem exists_time_forall_mem_of_isCompact {U : Set (Vec d)} (hU : IsOpen U)
    (C : Set (ContinuousPath (Vec d))) (hC : IsCompact C) (h0 : ∀ w ∈ C, w 0 ∈ U) :
    ∃ a : NNReal, 0 < a ∧ ∀ w ∈ C, ∀ t : NNReal, t ≤ a → w t ∈ U := by
  set n : Set (ContinuousPath (Vec d) × NNReal) := {p | p.1 p.2 ∈ U} with hn
  have hnopen : IsOpen n := by
    have hev : Continuous fun p : ContinuousPath (Vec d) × NNReal => p.1 p.2 :=
      continuous_eval
    exact hev.isOpen_preimage U hU
  have hsub : C ×ˢ ({0} : Set NNReal) ⊆ n := by
    rintro ⟨w, t⟩ ⟨hw, ht⟩
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact h0 w hw
  obtain ⟨u, v, -, hvopen, hCu, hv0, huv⟩ :=
    generalized_tube_lemma hC isCompact_singleton hnopen hsub
  have hv : v ∈ nhds (0 : NNReal) := hvopen.mem_nhds (hv0 rfl)
  obtain ⟨b, hb, hbv⟩ := (nhds_bot_basis (α := NNReal)).mem_iff.mp hv
  refine ⟨b / 2, by simpa using half_pos hb, fun w hw t ht => ?_⟩
  have htb : t ∈ Set.Iio b := lt_of_le_of_lt ht (by simpa using NNReal.half_lt_self hb.ne')
  have hmem : ((w, t) : ContinuousPath (Vec d) × NNReal) ∈ n :=
    huv (Set.mk_mem_prod (hCu hw) (hbv htb))
  exact hmem

end SubdiffusiveProcess.Probability.Diffusion
