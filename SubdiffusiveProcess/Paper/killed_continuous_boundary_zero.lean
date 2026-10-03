module

public import SubdiffusiveProcess.Lane4.Carriers
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

section aux
open Filter
open scoped Topology Distributions

/-- Fundamental theorem of calculus along a ray leaving the support of a test function. -/
theorem aux_killed_continuous_boundary_zero_line {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (φ : 𝓓(Ω, ℝ)) (e y : SpatialCoordinates d) {L : ℝ} (hL : 0 ≤ L)
    (hy : y + L • e ∉ (Ω : Set (SpatialCoordinates d))) :
    ‖φ y‖ₑ ≤ ∫⁻ t in Ioc 0 L, ‖fderiv ℝ φ (y + t • e) e‖ₑ := by
  have hdiff : Differentiable ℝ (φ : SpatialCoordinates d → ℝ) :=
    φ.contDiff.differentiable (by simp)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (y + s • e))
      (fderiv ℝ φ (y + t • e) e) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => y + s • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add y
    exact (hdiff (y + t • e)).hasFDerivAt.comp_hasDerivAt t hline
  have hcont : Continuous (fun t : ℝ => fderiv ℝ φ (y + t • e) e) :=
    (φ.contDiff.continuous_fderiv_apply (by simp)).comp
      ((continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const)
  have hzero : φ (y + L • e) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (φ.tsupport_subset h))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := L)
    (fun t _ => hderiv t) (hcont.intervalIntegrable 0 L)
  rw [hzero, zero_smul, add_zero, intervalIntegral.integral_of_le hL] at hftc
  calc ‖φ y‖ₑ = ‖∫ t in Ioc 0 L, fderiv ℝ φ (y + t • e) e‖ₑ := by
        rw [hftc, zero_sub, enorm_neg]
    _ ≤ _ := enorm_integral_le_lintegral_enorm _

/-- Tonelli and translation invariance turn the ray estimate into a box estimate. -/
theorem aux_killed_continuous_boundary_zero_smooth_box {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (φ : 𝓓(Ω, ℝ)) (e : SpatialCoordinates d) {L : ℝ}
    (hL : 0 ≤ L) (B S : Set (SpatialCoordinates d)) (hBm : MeasurableSet B)
    (hSm : MeasurableSet S)
    (hB : ∀ y ∈ B, y + L • e ∉ (Ω : Set (SpatialCoordinates d)))
    (hBS : ∀ y ∈ B, ∀ t ∈ Ioc 0 L, y + t • e ∈ (Ω : Set (SpatialCoordinates d)) →
      y + t • e ∈ S) :
    ∫⁻ y in B, ‖φ y‖ₑ ≤ ENNReal.ofReal L * ∫⁻ u in S, ‖fderiv ℝ φ u e‖ₑ := by
  set F : SpatialCoordinates d → ℝ≥0∞ := S.indicator (fun u => ‖fderiv ℝ φ u e‖ₑ) with hF
  have hFm : Measurable F := by
    refine Measurable.indicator ?_ hSm
    exact ((φ.contDiff.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)).measurable.enorm
  have hpt : ∀ y ∈ B, ∀ t ∈ Ioc 0 L, ‖fderiv ℝ φ (y + t • e) e‖ₑ ≤ F (y + t • e) := by
    intro y hy t ht
    by_cases hΩ : y + t • e ∈ (Ω : Set (SpatialCoordinates d))
    · rw [hF, indicator_of_mem (hBS y hy t ht hΩ)]
    · have h0 : fderiv ℝ φ (y + t • e) = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun h => hΩ (φ.tsupport_subset h))
      simp [h0]
  calc ∫⁻ y in B, ‖φ y‖ₑ
      ≤ ∫⁻ y in B, ∫⁻ t in Ioc 0 L, F (y + t • e) := by
        refine setLIntegral_mono' hBm fun y hy => ?_
        refine (aux_killed_continuous_boundary_zero_line φ e y hL (hB y hy)).trans ?_
        exact setLIntegral_mono' measurableSet_Ioc fun t ht => hpt y hy t ht
    _ ≤ ∫⁻ y, ∫⁻ t in Ioc 0 L, F (y + t • e) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in Ioc 0 L, ∫⁻ y, F (y + t • e) := by
        refine lintegral_lintegral_swap ?_
        exact (hFm.comp (measurable_fst.add (measurable_snd.smul measurable_const))).aemeasurable
    _ = ∫⁻ t in Ioc 0 L, ∫⁻ u, F u := by
        congr 1
        funext t
        exact lintegral_add_right_eq_self F (t • e)
    _ = ENNReal.ofReal L * ∫⁻ u in S, ‖fderiv ℝ φ u e‖ₑ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm, hF,
          lintegral_indicator hSm]


/-- On a finite measure, `L²` convergence gives `L¹` convergence of the pointwise error. -/
theorem aux_killed_continuous_boundary_zero_l1_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => ∫⁻ y, ‖g y - f n y‖ₑ ∂μ) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => eLpNorm (⇑(f n) - ⇑g) 2 μ) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' f g).mp h
  have hc : μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  have h3 := ENNReal.Tendsto.mul_const h2 (Or.inr hc)
  rw [zero_mul] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
    (fun n => zero_le) (fun n => ?_)
  calc ∫⁻ y, ‖g y - f n y‖ₑ ∂μ = eLpNorm (⇑g - ⇑(f n)) 1 μ :=
        (eLpNorm_one_eq_lintegral_enorm
          ((Lp.aestronglyMeasurable g).sub (Lp.aestronglyMeasurable (f n)))).symm
    _ ≤ eLpNorm (⇑g - ⇑(f n)) 2 μ *
          μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
          ((Lp.aestronglyMeasurable g).sub (Lp.aestronglyMeasurable (f n)))
    _ = eLpNorm (⇑(f n) - ⇑g) 2 μ *
          μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := by
        rw [eLpNorm_sub_comm]

/-- The coordinate direction `σ e_i` with `|σ| = 1` has the same derivative size as `e_i`. -/
theorem aux_killed_continuous_boundary_zero_enorm_dir {d : ℕ}
    (A : SpatialCoordinates d →L[ℝ] ℝ) (i : Fin d) {σ : ℝ} (hσ : |σ| = 1) :
    ‖A (Pi.single i σ)‖ₑ = ‖A (Pi.single i 1)‖ₑ := by
  have hs : (Pi.single i σ : SpatialCoordinates d) = σ • Pi.single i (1 : ℝ) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [hs, A.map_smul, enorm_smul, Real.enorm_eq_ofReal_abs, hσ, ENNReal.ofReal_one, one_mul]

/-- The box estimate passes from test functions to the killed closure. -/
theorem aux_killed_continuous_boundary_zero_killed_box {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (w : SobolevData Ω) (hw : w ∈ killedSobolevGraph Ω) (i : Fin d) {σ : ℝ} (hσ : |σ| = 1)
    {L : ℝ} (hL : 0 ≤ L) (B S : Set (SpatialCoordinates d))
    (hBΩ : B ⊆ (Ω : Set (SpatialCoordinates d))) (hBm : MeasurableSet B)
    (hSm : MeasurableSet S)
    (hB : ∀ y ∈ B, y + L • (Pi.single i σ : SpatialCoordinates d) ∉
      (Ω : Set (SpatialCoordinates d)))
    (hBS : ∀ y ∈ B, ∀ t ∈ Ioc 0 L,
      y + t • (Pi.single i σ : SpatialCoordinates d) ∈ (Ω : Set (SpatialCoordinates d)) →
        y + t • (Pi.single i σ : SpatialCoordinates d) ∈ S) :
    ∫⁻ y in B, ‖w.1 y‖ₑ ≤
      ENNReal.ofReal L * ∫⁻ u in S, ‖w.2 i u‖ₑ
        ∂(volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  set μΩ := volume.restrict (Ω : Set (SpatialCoordinates d)) with hμΩ
  have hΩm : MeasurableSet (Ω : Set (SpatialCoordinates d)) := Ω.isOpen.measurableSet
  have hcl : w ∈ closure (Set.range (smoothSobolevDataLinear (Ω := Ω))) := by
    have : w ∈ ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))).topologicalClosure :
        Set (SobolevData Ω)) := hw
    rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range] at this
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  choose φ hφ using hu
  have hlim' : Tendsto (fun n => smoothSobolevDataLinear (φ n)) atTop (𝓝 w) := by
    convert hlim using 1
    funext n
    exact hφ n
  have h1 : Tendsto (fun n => testL2 (φ n)) atTop (𝓝 w.1) :=
    (continuous_fst.tendsto w).comp hlim'
  have h2 : Tendsto (fun n => testPartialL2 (φ n) i) atTop (𝓝 (w.2 i)) :=
    (((continuous_apply i).comp continuous_snd).tendsto w).comp hlim'
  have ha := aux_killed_continuous_boundary_zero_l1_tendsto h1
  have hb := aux_killed_continuous_boundary_zero_l1_tendsto h2
  set Y := ∫⁻ u in S, ‖w.2 i u‖ₑ ∂μΩ with hY
  have hBle : volume.restrict B ≤ μΩ := Measure.restrict_mono hBΩ le_rfl
  have hSle : volume.restrict (S ∩ (Ω : Set (SpatialCoordinates d))) ≤ μΩ :=
    Measure.restrict_mono inter_subset_right le_rfl
  have hclaim : ∀ n, ∫⁻ y in B, ‖w.1 y‖ₑ ≤
      ENNReal.ofReal L * (Y + ∫⁻ u, ‖w.2 i u - testPartialL2 (φ n) i u‖ₑ ∂μΩ) +
        ∫⁻ y, ‖w.1 y - testL2 (φ n) y‖ₑ ∂μΩ := by
    intro n
    set T := testL2 (φ n) with hT
    set P := testPartialL2 (φ n) i with hP
    have hTB : ∫⁻ y in B, ‖T y‖ₑ = ∫⁻ y in B, ‖φ n y‖ₑ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_mono hBle (testL2_coeFn (φ n))] with y hy
      rw [hy]
    have hsmooth := aux_killed_continuous_boundary_zero_smooth_box (φ n)
      (Pi.single i σ) hL B (S ∩ (Ω : Set (SpatialCoordinates d))) hBm (hSm.inter hΩm) hB
      (fun y hy t ht hΩ => ⟨hBS y hy t ht hΩ, hΩ⟩)
    have hPS : ∫⁻ u in S ∩ (Ω : Set (SpatialCoordinates d)),
        ‖fderiv ℝ (φ n) u (Pi.single i σ)‖ₑ = ∫⁻ u in S, ‖P u‖ₑ ∂μΩ := by
      rw [hμΩ, Measure.restrict_restrict hSm]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_mono hSle (testPartialL2_coeFn (φ n) i)] with u hu
      rw [hu, aux_killed_continuous_boundary_zero_enorm_dir _ i hσ]
    have hPY : ∫⁻ u in S, ‖P u‖ₑ ∂μΩ ≤ Y + ∫⁻ u, ‖w.2 i u - P u‖ₑ ∂μΩ := by
      calc ∫⁻ u in S, ‖P u‖ₑ ∂μΩ
          ≤ ∫⁻ u in S, (‖w.2 i u‖ₑ + ‖w.2 i u - P u‖ₑ) ∂μΩ := by
            refine lintegral_mono fun u => ?_
            calc ‖P u‖ₑ = ‖w.2 i u - (w.2 i u - P u)‖ₑ := by rw [sub_sub_cancel]
              _ ≤ _ := enorm_sub_le
        _ = Y + ∫⁻ u in S, ‖w.2 i u - P u‖ₑ ∂μΩ :=
            lintegral_add_left' (Lp.aestronglyMeasurable (w.2 i)).restrict.enorm _
        _ ≤ Y + ∫⁻ u, ‖w.2 i u - P u‖ₑ ∂μΩ := by
            gcongr
            exact Measure.restrict_le_self
    calc ∫⁻ y in B, ‖w.1 y‖ₑ
        ≤ ∫⁻ y in B, (‖T y‖ₑ + ‖w.1 y - T y‖ₑ) := by
          refine lintegral_mono fun y => ?_
          calc ‖w.1 y‖ₑ = ‖T y + (w.1 y - T y)‖ₑ := by rw [add_sub_cancel]
            _ ≤ _ := enorm_add_le _ _
      _ = (∫⁻ y in B, ‖T y‖ₑ) + ∫⁻ y in B, ‖w.1 y - T y‖ₑ :=
          lintegral_add_left' ((Lp.aestronglyMeasurable T).mono_measure hBle).enorm _
      _ ≤ ENNReal.ofReal L * (Y + ∫⁻ u, ‖w.2 i u - P u‖ₑ ∂μΩ) +
            ∫⁻ y, ‖w.1 y - T y‖ₑ ∂μΩ := by
          gcongr ?_ + ?_
          · rw [hTB]
            refine hsmooth.trans ?_
            rw [hPS]
            gcongr
          · exact lintegral_mono' hBle le_rfl
  have hlimit : Tendsto (fun n => ENNReal.ofReal L *
      (Y + ∫⁻ u, ‖w.2 i u - testPartialL2 (φ n) i u‖ₑ ∂μΩ) +
        ∫⁻ y, ‖w.1 y - testL2 (φ n) y‖ₑ ∂μΩ) atTop (𝓝 (ENNReal.ofReal L * (Y + 0) + 0)) :=
    (ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hb) (Or.inr ENNReal.ofReal_ne_top)).add ha
  rw [add_zero, add_zero] at hlimit
  exact ge_of_tendsto' hlimit hclaim


/-- Volume of a coordinate box whose `i`th half-width is `a` and other half-widths are `b`. -/
theorem aux_killed_continuous_boundary_zero_box_volume {d : ℕ} (i : Fin d)
    (lo : Fin d → ℝ) (a b : ℝ) :
    volume (univ.pi fun j => Ioo (lo j) (lo j + if j = i then a else b)) =
      ENNReal.ofReal a * ∏ _j ∈ ({i}ᶜ : Finset (Fin d)), ENNReal.ofReal b := by
  rw [Real.volume_pi_Ioo, Fintype.prod_eq_mul_prod_compl i]
  simp only [add_sub_cancel_left]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [if_neg (by simpa using hj)]

end aux

/-- Boundary value of a continuous representative of an H^1_0 function on a cube (paper 579). -/
theorem killed_continuous_boundary_zero :
  ∀ (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (w : SobolevData (centeredCube z r hr)),
    w ∈ killedSobolevGraph (centeredCube z r hr) →
    ∀ V : SpatialCoordinates d → ℝ, Continuous V →
      (w.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V →
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) → V x = 0 := by
  intro d z r hr w hw V hV hVeq x hxc hxo
  by_contra hVx
  have hΩ : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  have hΩopen : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen
  have hr2 : 0 < r / 2 := half_pos hr
  -- `x` lies on the boundary: some coordinate is extremal.
  have hxz : ∀ j, x j - z j ≤ r / 2 ∧ z j - x j ≤ r / 2 := by
    intro j
    have h1 := dist_le_pi_dist x z j
    have h2 : dist x z ≤ r / 2 := hxc
    rw [Real.dist_eq] at h1
    have h := h1.trans h2
    exact ⟨(le_abs_self _).trans h, by linarith [neg_abs_le (x j - z j)]⟩
  obtain ⟨i, hi⟩ : ∃ i, r / 2 ≤ |x i - z i| := by
    by_contra h
    push_neg at h
    exact hxo ((dist_pi_lt_iff hr2).mpr fun j => by rw [Real.dist_eq]; exact h j)
  obtain ⟨σ, hσ, hσx⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * (x i - z i) = r / 2 := by
    rcases (abs_eq hr2.le).mp (le_antisymm (abs_le.mpr ⟨by linarith [(hxz i).2],
        (hxz i).1⟩) hi) with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- Continuity of `V` at `x`.
  set c := |V x| with hc
  have hcpos : 0 < c := abs_pos.mpr hVx
  obtain ⟨ρ, hρ, hρV⟩ := Metric.continuous_iff.mp hV x (c / 2) (by positivity)
  set δ := min (ρ / 2) (r / 2) with hδdef
  have hδ : 0 < δ := lt_min (half_pos hρ) hr2
  have hδρ : δ < ρ := (min_le_left _ _).trans_lt (half_lt_self hρ)
  have hδr : δ ≤ r / 2 := min_le_right _ _
  -- The boxes.
  let wd : ℝ → Fin d → ℝ := fun ε j => if j = i then ε else δ
  let B : ℝ → Set (SpatialCoordinates d) := fun ε =>
    (centeredCube z r hr : Set (SpatialCoordinates d)) ∩
      univ.pi fun j => Ioo (x j - wd ε j) (x j + wd ε j)
  let S : ℝ → Set (SpatialCoordinates d) := fun ε =>
    univ.pi fun j => Ioo (x j - wd (3 * ε) j) (x j - wd (3 * ε) j +
      if j = i then 6 * ε else 2 * δ)
  let μΩ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  let Y : ℝ → ℝ≥0∞ := fun ε => ∫⁻ u in S ε, ‖w.2 i u‖ₑ ∂μΩ
  set K := ∏ _j ∈ ({i}ᶜ : Finset (Fin d)), ENNReal.ofReal δ with hK
  set K' := ∏ _j ∈ ({i}ᶜ : Finset (Fin d)), ENNReal.ofReal (2 * δ) with hK'
  have hK0 : K ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ _ => (ENNReal.ofReal_pos.mpr hδ).ne'
  have hK'top : K' ≠ ⊤ := ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  -- The per-scale estimate.
  have hscale : ∀ ε ∈ Ioo 0 δ, ENNReal.ofReal (c / 2) * K ≤ ENNReal.ofReal 2 * Y ε := by
    intro ε hε
    obtain ⟨hε0, hεδ⟩ := hε
    have hwpos : ∀ j, 0 < wd ε j := fun j => by
      simp only [wd]; split_ifs <;> assumption
    have hwle : ∀ j, wd ε j ≤ δ := fun j => by
      simp only [wd]; split_ifs <;> linarith
    have hBm : MeasurableSet (B ε) :=
      (hΩopen.inter (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)).measurableSet
    have hSm : MeasurableSet (S ε) :=
      (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).measurableSet
    -- Upper bound from the killed box estimate.
    have hupper := aux_killed_continuous_boundary_zero_killed_box w hw i hσabs
      (L := 2 * ε) (by linarith) (B ε) (S ε) inter_subset_left hBm hSm
      (by
        intro y hy hyΩ
        have hyi : x i - ε < y i ∧ y i < x i + ε := by
          have := (mem_univ_pi.mp hy.2) i
          simpa [wd] using this
        rw [hΩ, mem_ball, dist_pi_lt_iff hr2] at hyΩ
        have h := hyΩ i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
          Real.dist_eq] at h
        have key : σ * (y i + 2 * ε * σ - z i) = σ * (y i - x i) + r / 2 + 2 * ε := by
          linear_combination (2 * ε) * hσσ + hσx
        have h1 : |σ * (y i + 2 * ε * σ - z i)| < r / 2 := by
          rw [abs_mul, hσabs, one_mul]; exact h
        have h2 : |σ * (y i - x i)| < ε := by
          rw [abs_mul, hσabs, one_mul, abs_sub_lt_iff]; constructor <;> linarith
        linarith [le_abs_self (σ * (y i + 2 * ε * σ - z i)), neg_abs_le (σ * (y i - x i))])
      (by
        intro y hy t ht _
        obtain ⟨ht0, htL⟩ := ht
        refine mem_univ_pi.mpr fun j => ?_
        have hyj := (mem_univ_pi.mp hy.2) j
        by_cases hj : j = i
        · subst hj
          simp only [wd, if_pos rfl, ↓reduceIte, mem_Ioo] at hyj ⊢
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
          have htσ : |t * σ| = t := by rw [abs_mul, hσabs, mul_one, abs_of_pos ht0]
          constructor
          · linarith [neg_abs_le (t * σ)]
          · linarith [le_abs_self (t * σ)]
        · simp only [wd, if_neg hj, mem_Ioo] at hyj ⊢
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_eq_mul,
            mul_zero, add_zero]
          constructor <;> linarith)
    -- Lower bound from continuity of `V` and a sub-box.
    let p : Fin d → ℝ := fun j => if z j ≤ x j then x j - wd ε j else x j
    have hsub : (univ.pi fun j => Ioo (p j) (p j + if j = i then ε else δ)) ⊆ B ε := by
      intro y hy
      have hy' : ∀ j, p j < y j ∧ y j < p j + wd ε j := fun j => (mem_univ_pi.mp hy) j
      refine ⟨?_, mem_univ_pi.mpr fun j => ?_⟩
      · rw [hΩ, mem_ball, dist_pi_lt_iff hr2]
        intro j
        rw [Real.dist_eq, abs_sub_lt_iff]
        have := hy' j
        have hj1 := hwpos j
        have hj2 := hwle j
        have hj3 := hxz j
        simp only [p] at this
        split_ifs at this <;> constructor <;> linarith
      · have := hy' j
        have hj1 := hwpos j
        simp only [p] at this
        rw [mem_Ioo]
        split_ifs at this <;> constructor <;> linarith
    have hvolB : ENNReal.ofReal ε * K ≤ volume (B ε) := by
      rw [← aux_killed_continuous_boundary_zero_box_volume i p ε δ]
      exact measure_mono hsub
    have hlower : ENNReal.ofReal (c / 2) * volume (B ε) ≤ ∫⁻ y in B ε, ‖w.1 y‖ₑ := by
      rw [← setLIntegral_const]
      refine lintegral_mono_ae ?_
      have hBle : volume.restrict (B ε) ≤ μΩ := Measure.restrict_mono inter_subset_left le_rfl
      filter_upwards [ae_restrict_mem hBm, ae_mono hBle hVeq] with y hy hyV
      rw [hyV, Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      have hdist : dist y x < ρ := by
        refine (dist_pi_lt_iff hρ).mpr fun j => ?_
        have := (mem_univ_pi.mp hy.2) j
        rw [mem_Ioo] at this
        rw [Real.dist_eq, abs_sub_lt_iff]
        constructor <;> linarith [hwle j]
      have := hρV y hdist
      rw [Real.dist_eq] at this
      linarith [abs_sub_abs_le_abs_sub (V x) (V y), abs_sub_comm (V x) (V y)]
    have hchain : ENNReal.ofReal ε * (ENNReal.ofReal (c / 2) * K) ≤
        ENNReal.ofReal ε * (ENNReal.ofReal 2 * Y ε) := by
      calc ENNReal.ofReal ε * (ENNReal.ofReal (c / 2) * K)
          = ENNReal.ofReal (c / 2) * (ENNReal.ofReal ε * K) := by ring
        _ ≤ ENNReal.ofReal (c / 2) * volume (B ε) := by gcongr
        _ ≤ ∫⁻ y in B ε, ‖w.1 y‖ₑ := hlower
        _ ≤ ENNReal.ofReal (2 * ε) * Y ε := hupper
        _ = ENNReal.ofReal ε * (ENNReal.ofReal 2 * Y ε) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; ring
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hε0).ne'
      ENNReal.ofReal_ne_top).mp hchain
  -- The thin boxes have vanishing measure, so the gradient mass in them vanishes.
  have hSvol : ∀ ε, volume (S ε) = ENNReal.ofReal (6 * ε) * K' := fun ε =>
    aux_killed_continuous_boundary_zero_box_volume i _ _ _
  have hSmeas : Filter.Tendsto (μΩ ∘ S) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h6 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (6 * ε) * K')
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h0 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (6 * ε))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        have := ((ENNReal.continuous_ofReal.comp
          ((continuous_const (y := (6 : ℝ))).mul continuous_id)).tendsto
          (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simp only [Function.comp_def, id, mul_zero, ENNReal.ofReal_zero] at this
        simpa only [Pi.mul_apply, Function.id_def, mul_zero, ENNReal.ofReal_zero] using! this
      simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hK'top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h6
      (fun _ => zero_le) fun ε => ?_
    rw [← hSvol]
    exact Measure.restrict_apply_le _ _
  have hfin : ∫⁻ u, ‖w.2 i u‖ₑ ∂μΩ ≠ ⊤ :=
    ((Lp.memLp (w.2 i)).integrable one_le_two).hasFiniteIntegral.ne
  have hY : Filter.Tendsto (fun ε => ENNReal.ofReal 2 * Y ε) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 2)
      (tendsto_setLIntegral_zero hfin hSmeas) (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h
    exact h
  have hle : ENNReal.ofReal (c / 2) * K ≤ 0 :=
    ge_of_tendsto hY (Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) hscale)
  exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hK0).ne'
    (nonpos_iff_eq_zero.mp hle)


end Paper
