module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssembly
public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousLipschitzNullity
public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousLipschitzApproximation
public import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblyContinuity

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] {m : Measure X}

theorem EnergyFamily.quasiContinuous_nullity {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {K : Set ℝ}
    (hK : IsCompact K) (hK0 : volume K = 0) :
    Γ.measure u ((q.rep u hu) ⁻¹' K) = 0 := by
  by_cases hKne : K.Nonempty
  · obtain ⟨T, hTc, hTL, hT0, hTd, hTK, hTlim⟩ :=
      lipschitz_null_primitives hK.isClosed hKne hK0
    let w : ℕ → Lp ℝ 2 m := fun n => (hTL n).compLp (hT0 n) u
    have hw : ∀ n, w n ∈ F.domain := fun n =>
      (lipschitz_comp_mem F (hTL n) (hT0 n) hu
        (LipschitzWith.coeFn_compLp (hTL n) (hT0 n) u)).1
    have hwenergy : ∀ n, F.form (w n) (w n) ≤ F.form u u := fun n => by
      simpa only [NNReal.coe_one, one_pow, one_mul] using!
        (lipschitz_comp_mem F (hTL n) (hT0 n) hu
          (LipschitzWith.coeFn_compLp (hTL n) (hT0 n) u)).2
    have hwrep : ∀ n, ⇑(w n) =ᵐ[m] fun x => T n (q.rep u hu x) := by
      intro n
      filter_upwards [LipschitzWith.coeFn_compLp (hTL n) (hT0 n) u,
        q.ae_rep u hu] with x hx hu'
      rw [hx]
      change T n (u x) = T n (q.rep u hu x)
      rw [hu']
    have hwlim : Tendsto w atTop (𝓝 (0 : Lp ℝ 2 m)) := by
      apply tendsto_Lp_of_tendsto_comp (K := 1)
        (fun n => LipschitzWith.coeFn_compLp (hTL n) (hT0 n) u)
        (Lp.coeFn_zero ℝ 2 m) hTlim
      intro n s
      have hb := (hTL n).dist_le_mul s 0
      simpa only [hT0 n, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] using! hb
    have hweak := EnergyHilbert.weak_null_form_tendsto_zero F.toClosedForm w hw
      (F.form u u) hwenergy
      (by simpa only [norm_zero] using! (continuous_norm.tendsto (0 : Lp ℝ 2 m)).comp hwlim)
      u hu
    letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
    let A : Set X := (q.rep u hu) ⁻¹' K
    have hA : MeasurableSet A := q.measurable u hu hK.measurableSet
    have hbound : ∀ n, (Γ.measure u A).toReal ≤ F.form u (w n) := by
      intro n
      rw [Γ.quasiContinuous_first_derivative h q hu (T n) (hTc n)
        (hTL n) (hT0 n) (hw n) (hwrep n)]
      let d : X → ℝ := fun x => deriv (T n) (q.rep u hu x)
      have hd : Integrable d (Γ.measure u) := by
        apply (integrable_const (1 : ℝ)).mono'
          (((hTc n).continuous_deriv (by norm_num)).measurable.comp
            (q.measurable u hu)).aestronglyMeasurable
        refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, Function.comp_def, abs_of_nonneg (hTd n _).1]
        exact (hTd n _).2
      calc
        _ = ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂Γ.measure u := by
          simpa only [measureReal_def] using!
            (integral_indicator_one (μ := Γ.measure u) hA).symm
        _ ≤ ∫ x, d x ∂Γ.measure u := by
          apply integral_mono_ae ((integrable_const 1).indicator hA) hd
          refine Eventually.of_forall fun x => ?_
          by_cases hx : x ∈ A
          · rw [indicator_of_mem hx]
            exact (hTK n (q.rep u hu x) hx).ge
          · rw [indicator_of_notMem hx]
            exact (hTd n _).1
    have hzero : (Γ.measure u A).toReal ≤ 0 :=
      ge_of_tendsto hweak (Eventually.of_forall hbound)
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hzero ENNReal.toReal_nonneg) |>.resolve_right
        (lt_of_le_of_lt (measure_mono (subset_univ A)) (Γ.finite u hu)).ne
  · rw [not_nonempty_iff_eq_empty.mp hKne, preimage_empty, measure_empty]

theorem EnergyFamily.quasiContinuous_lipschitz_chain
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U) (Γ : EnergyFamily F U)
    (q : RepresentativeFamily Γ) {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    (T : ℝ → ℝ) (hT : ∃ L : ℝ≥0, LipschitzWith L T) (hT0 : T 0 = 0)
    (D : ℝ → ℝ) (hD : Measurable D) (hderiv : ∀ᵐ s : ℝ, HasDerivAt T (D s) s)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => T (q.rep u hu x)) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal = ∫ x in B, (D (q.rep u hu x)) ^ 2 ∂(Γ.measure u) := by
  obtain ⟨L, hTL⟩ := hT
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  let ν : Measure ℝ := (Γ.measure u).map (q.rep u hu)
  have hνac : ν ≪ volume := by
    apply Measure.AbsolutelyContinuous.mk
    intro S hS hS0
    rw [hS.measure_eq_iSup_isCompact ν]
    apply le_antisymm
    · apply iSup_le
      intro K
      apply iSup_le
      intro hKS
      apply iSup_le
      intro hK
      change ((Γ.measure u).map (q.rep u hu)) K ≤ 0
      rw [Measure.map_apply (q.measurable u hu) hK.measurableSet,
        Γ.quasiContinuous_nullity h q hu hK (measure_mono_null hKS hS0)]
    · exact bot_le
  have haederiv : ∀ᵐ x ∂Γ.measure u, HasDerivAt T (D (q.rep u hu x)) (q.rep u hu x) :=
    ae_of_ae_map (q.measurable u hu).aemeasurable (hνac.ae_le hderiv)
  have hDbound : ∀ᵐ x ∂Γ.measure u, |D (q.rep u hu x)| ≤ L := by
    filter_upwards [haederiv] with x hx
    rw [← hx.deriv, ← Real.norm_eq_abs]
    exact norm_deriv_le_of_lipschitz hTL
  obtain ⟨Φ, hΦc, hΦL, hΦ0, hΦlim, hΦderiv⟩ := lipschitz_c1_approximation T hTL hT0
  let wn : ℕ → Lp ℝ 2 m := fun n => (hΦL n).compLp (hΦ0 n) u
  have hwn : ∀ n, wn n ∈ F.domain := fun n =>
    (lipschitz_comp_mem F (hΦL n) (hΦ0 n) hu
      (LipschitzWith.coeFn_compLp (hΦL n) (hΦ0 n) u)).1
  have hwnrep : ∀ n, ⇑(wn n) =ᵐ[m] fun x => Φ n (q.rep u hu x) := by
    intro n
    filter_upwards [LipschitzWith.coeFn_compLp (hΦL n) (hΦ0 n) u,
      q.ae_rep u hu] with x hx hy
    rw [hx]
    change Φ n (u x) = Φ n (q.rep u hu x)
    rw [hy]
  have hwrep : ⇑w =ᵐ[m] fun x => T (u x) := by
    filter_upwards [hwae, q.ae_rep u hu] with x hx hy
    rw [hx, hy]
  have hwnlim : Tendsto wn atTop (𝓝 w) := by
    apply tendsto_Lp_of_tendsto_comp (K := 2 * (L : ℝ))
      (fun n => LipschitzWith.coeFn_compLp (hΦL n) (hΦ0 n) u) hwrep hΦlim
    intro n s
    have hn := (hΦL n).dist_le_mul s 0
    have ht := hTL.dist_le_mul s 0
    simp only [Real.dist_eq, hΦ0 n, hT0, sub_zero] at hn ht
    exact (abs_sub _ _).trans (by linarith)
  let dn : ℕ → X → ℝ := fun n x => deriv (Φ n) (q.rep u hu x)
  let d : X → ℝ := fun x => D (q.rep u hu x)
  have hdmeas : Measurable d := hD.comp (q.measurable u hu)
  have hdnmeas : ∀ n, Measurable (dn n) := fun n =>
    ((hΦc n).continuous_deriv (by norm_num)).measurable.comp (q.measurable u hu)
  have hdnbound : ∀ n x, |dn n x| ≤ L := fun n x => by
    exact norm_deriv_le_of_lipschitz (hΦL n)
  have hdnlim : ∀ᵐ x ∂Γ.measure u, Tendsto (fun n => dn n x) atTop (𝓝 (d x)) := by
    filter_upwards [haederiv] with x hx
    exact hΦderiv _ _ hx
  let en : ℕ → ℝ := fun n => ∫ x, (dn n x - d x) ^ 2 ∂Γ.measure u
  have hebound : ∀ n, ∀ᵐ x ∂Γ.measure u, ‖(dn n x - d x) ^ 2‖ ≤ 4 * (L : ℝ) ^ 2 := by
    intro n
    filter_upwards [hDbound] with x hx
    have hab : |dn n x - d x| ≤ 2 * (L : ℝ) :=
      (abs_sub _ _).trans (by linarith [hdnbound n x])
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc
      _ ≤ (2 * (L : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hab 2
      _ = _ := by ring
  have heint : ∀ n, Integrable (fun x => (dn n x - d x) ^ 2) (Γ.measure u) :=
    fun n => (integrable_const (4 * (L : ℝ) ^ 2)).mono'
      (((hdnmeas n).sub hdmeas).pow_const 2).aestronglyMeasurable (hebound n)
  have henlim : Tendsto en atTop (𝓝 0) := by
    have hzlim : ∀ᵐ x ∂Γ.measure u,
        Tendsto (fun n => (dn n x - d x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hdnlim] with x hx
      simpa only [sub_self, zero_pow two_ne_zero] using! (hx.sub_const (d x)).pow 2
    simpa only [integral_zero] using!
      tendsto_integral_of_dominated_convergence (fun _ : X => 4 * (L : ℝ) ^ 2)
        (fun n => (heint n).1) (integrable_const _) hebound hzlim
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
      F.form (wn p - wn r) (wn p - wn r) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (henlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4)))
    refine ⟨N, ?_⟩
    intro p hp r hr
    have hsubrep : ⇑(wn p - wn r) =ᵐ[m]
        fun x => Φ p (q.rep u hu x) - Φ r (q.rep u hu x) := by
      filter_upwards [Lp.coeFn_sub (wn p) (wn r), hwnrep p, hwnrep r] with x hx hy hz
      simp only [hx, Pi.sub_apply, hy, hz]
    have hsubderiv : ∀ s, deriv (fun t => Φ p t - Φ r t) s =
        deriv (Φ p) s - deriv (Φ r) s := fun s =>
      (((hΦc p).differentiable (by norm_num) s).hasDerivAt.sub
        ((hΦc r).differentiable (by norm_num) s).hasDerivAt).deriv
    have hchain := Γ.quasiContinuous_chain h q hu (fun s => Φ p s - Φ r s)
      ((hΦc p).sub (hΦc r)) ((hΦL p).sub (hΦL r))
      (by simp only [hΦ0 p, hΦ0 r, sub_self]) (F.domain.sub_mem (hwn p) (hwn r))
      hsubrep MeasurableSet.univ
    simp only [Measure.restrict_univ,
      Γ.mass _ (F.domain.sub_mem (hwn p) (hwn r)), hsubderiv] at hchain
    have hle : F.form (wn p - wn r) (wn p - wn r) ≤ 2 * en p + 2 * en r := by
      rw [hchain]
      calc
        _ ≤ ∫ x, 2 * (dn p x - d x) ^ 2 + 2 * (dn r x - d x) ^ 2 ∂Γ.measure u := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
            (((heint p).const_mul 2).add ((heint r).const_mul 2))
          exact Eventually.of_forall fun x => by
            change (dn p x - dn r x) ^ 2 ≤
              2 * (dn p x - d x) ^ 2 + 2 * (dn r x - d x) ^ 2
            nlinarith [sq_nonneg (dn p x + dn r x - 2 * d x)]
        _ = _ := by
          rw [integral_add ((heint p).const_mul 2) ((heint r).const_mul 2),
            integral_const_mul, integral_const_mul]
    linarith [hN p hp, hN r hr]
  have henergy := (F.toClosedForm.mem_domain_of_tendsto_of_formCauchy wn hwn w hwnlim hcauchy).2
  have hmeasure := Γ.measure_tendsto_of_energy hwn hw henergy hB
  have hdbound : ∀ᵐ x ∂Γ.measure u, ‖d x ^ 2‖ ≤ (L : ℝ) ^ 2 := by
    filter_upwards [hDbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hdnbound2 : ∀ n, ∀ᵐ x ∂(Γ.measure u).restrict B, ‖dn n x ^ 2‖ ≤ (L : ℝ) ^ 2 := by
    intro n
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hdnbound n x) 2
  have hintegral : Tendsto (fun n => ∫ x in B, dn n x ^ 2 ∂Γ.measure u) atTop
      (𝓝 (∫ x in B, d x ^ 2 ∂Γ.measure u)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : X => (L : ℝ) ^ 2)
      (fun n => ((hdnmeas n).pow_const 2).aestronglyMeasurable) (integrable_const _)
      hdnbound2
    filter_upwards [ae_restrict_of_ae hdnlim] with x hx
    exact hx.pow 2
  have hchain : ∀ n, (Γ.measure (wn n) B).toReal = ∫ x in B, dn n x ^ 2 ∂Γ.measure u :=
    fun n => Γ.quasiContinuous_chain h q hu (Φ n) (hΦc n) (hΦL n) (hΦ0 n)
      (hwn n) (hwnrep n) hB
  exact tendsto_nhds_unique hmeasure (hintegral.congr fun n => (hchain n).symm)

end DirichletForm.FOTConstruction
