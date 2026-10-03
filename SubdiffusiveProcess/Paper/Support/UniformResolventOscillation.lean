module

public import SubdiffusiveProcess.Paper.prop_uniform_resolvent_cutoff_oscillation

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Paper

theorem aux_mfd_prop_uniform_resolvent_oscillation_level_bound {d : ℕ} (hd : 2 ≤ d) (Qtri : Homogenization.TriadicCube d)
    (z : SpatialCoordinates d) (s : ℝ) (hr : 0 < s)
    (hroot : closure (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qtri))
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (Homogenization.openCubeSet Qtri))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Qtri), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))))
    (V Ir : ℝ) (hV : ν.real univ ≤ V) (hIr : 0 ≤ Ir)
    (hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube z
      s hr : Set (SpatialCoordinates d)) f ≤
        ENNReal.ofReal Ir)
    (m : ℕ) :
    eLpNorm (fun x => aux_prop_uniform_resolvent_cutoff_oscillation_E z
        s hr f (m + 1) x -
      aux_prop_uniform_resolvent_cutoff_oscillation_E z
        s hr f m x) 2 ν ≤
      ENNReal.ofReal (Real.sqrt ((K + V) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * s ^ (t - d + 1) * Ir) *
        (Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ m) := by
  have hinc := globalTriadicAverages_memLp_and_increment_bound hd Qtri
    z hr (subset_closure.trans hroot) K t hK ht m ν inferInstance hsupp hgrowth f hf
  dsimp only at hinc
  have hsq := hinc.2.2
  have hα : 0 < t - d + 1 := by linarith
  set C0 : ℝ := (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) with hC0
  have hC0nn : 0 ≤ C0 := by positivity
  have hcoef := aux_prop_uniform_resolvent_cutoff_oscillation_level_coeff (d := d) s t hr m
  have hscale := aux_prop_uniform_resolvent_cutoff_oscillation_level_scale_pow s (t - d + 1) hr m
  set ell : ℝ := s / (2 * (triadicHalf m : ℝ) + 1) with hell
  have hellpos : 0 < ell := by rw [hell]; positivity
  have hVnn : 0 ≤ ν.real univ := measureReal_nonneg
  have hq0 : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  set q : ℝ := Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) with hqdef
  have hq2 : q ^ 2 = (3 : ℝ) ^ (-(t - d + 1)) := Real.sq_sqrt hq0
  set X : ℝ := (K + V) * C0 * s ^ (t - d + 1) * Ir with hX
  have hXnn : 0 ≤ X := by
    have : 0 ≤ K + V := by linarith
    positivity
  apply aux_prop_uniform_resolvent_cutoff_oscillation_ennreal_le_of_sq_le (by positivity)
  refine hsq.trans ?_
  have hsqrtd : 0 ≤ Real.sqrt (d : ℝ) * ell := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hsqrtd (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal ((K + ν.real univ) * (ell / 3) ^ t * ((ell / 3) ^ d * ell ^ d)⁻¹ *
          (Real.sqrt (d : ℝ) * ell) ^ ((d : ℝ) + 1)) *
        aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube z s hr :
          Set (SpatialCoordinates d)) f
      ≤ ENNReal.ofReal ((K + ν.real univ) * (ell / 3) ^ t * ((ell / 3) ^ d * ell ^ d)⁻¹ *
          (Real.sqrt (d : ℝ) * ell) ^ ((d : ℝ) + 1)) * ENNReal.ofReal Ir := by
        gcongr
    _ = ENNReal.ofReal ((K + ν.real univ) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m))
          * Ir) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_assoc (K + ν.real univ), mul_assoc (K + ν.real univ), hell, hcoef, hscale]
    _ ≤ ENNReal.ofReal ((Real.sqrt X * q ^ m) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow, Real.sq_sqrt hXnn, ← pow_mul, mul_comm m 2, pow_mul, hq2, hX]
        have hA : 0 ≤ C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m) := by positivity
        have hB : K + ν.real univ ≤ K + V := by linarith
        calc (K + ν.real univ) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m)) * Ir
            ≤ (K + V) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m)) * Ir := by
              gcongr
          _ = (K + V) * C0 * s ^ (t - d + 1) * Ir * ((3 : ℝ) ^ (-(t - d + 1))) ^ m := by ring

/-- Pairing identity: the Lebesgue pairing with the cell-averaged source equals the `h ν`
pairing with the cell averages. -/

theorem aux_mfd_prop_uniform_resolvent_oscillation_trace_diff {d : ℕ} (hd : 2 ≤ d) (Qtri : Homogenization.TriadicCube d)
    (z : SpatialCoordinates d) (s : ℝ) (hr : 0 < s)
    (hroot : closure (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qtri))
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Qtri), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t))
    (hV : μ (centeredCube z
        s hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal V0)
    (φ : SpatialCoordinates d → ℝ)
    (hφ : MemLp φ 2 (volume.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))))
    (Ir : ℝ) (hIr : 0 ≤ Ir)
    (hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube z
      s hr : Set (SpatialCoordinates d)) φ ≤
        ENNReal.ofReal Ir)
    (n : ℕ) :
    eLpNorm (fun x => φ x - aux_prop_uniform_resolvent_cutoff_oscillation_E z
        s hr φ n x) 2
      (μ.restrict (centeredCube z
        s hr : Set (SpatialCoordinates d))) ≤
      ENNReal.ofReal (Real.sqrt ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * s ^ (t - d + 1) * Ir) *
        (Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ n /
          (1 - Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))))) := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z s hr : Set (SpatialCoordinates d))
    with hQdef
  set ν := μ.restrict Q with hνdef
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  have hsupp : ν (closure (Homogenization.openCubeSet Qtri))ᶜ = 0 := by
    rw [hνdef, Measure.restrict_apply isClosed_closure.measurableSet.compl]
    have hempty : (closure (Homogenization.openCubeSet Qtri))ᶜ ∩ Q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.1 (hroot (subset_closure hx.2))
    rw [hempty, measure_empty]
  have hgrowthν : ∀ x ∈ closure (Homogenization.openCubeSet Qtri), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t) := by
    intro x hx ρ hρ hρ1
    exact (Measure.restrict_apply_le Q _).trans (hgrowth x hx ρ hρ hρ1)
  have hVr : ν.real univ ≤ V0 := by
    rw [measureReal_def, hνdef, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  have hα : 0 < t - d + 1 := by linarith
  have hq0' : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  have hq1' : (3 : ℝ) ^ (-(t - d + 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set q : ℝ := Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [hqdef, Real.sqrt_lt' one_pos, one_pow]
    exact hq1'
  have hstep : ∀ m, n ≤ m →
      eLpNorm (fun x => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ (m + 1) x - aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m x) 2 ν ≤
        ENNReal.ofReal (Real.sqrt ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * s ^ (t - d + 1) * Ir) * q ^ m) :=
    fun m _ => aux_mfd_prop_uniform_resolvent_oscillation_level_bound hd Qtri z s hr hroot Km t hKm ht ν hsupp hgrowthν φ hφ V0 Ir hVr hIr
      hI m
  have hint : IntegrableOn φ Q volume := hφ.integrable one_le_two
  have hleb := aux_prop_uniform_resolvent_cutoff_oscillation_triadic_tendsto_ae hd z hr φ hint
  have hνac : ν ≪ volume := hac
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun m => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m x) atTop (𝓝 (φ x)) := by
    filter_upwards [hνac.ae_le hleb, ae_restrict_mem (centeredCube z s hr).isOpen.measurableSet]
      with x hx hxQ
    exact hx hxQ
  exact aux_prop_uniform_resolvent_cutoff_oscillation_fatou_tail ν (fun m => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m) φ
    (fun m => (aux_prop_uniform_resolvent_cutoff_oscillation_E_measurable z hr φ m).aestronglyMeasurable) hlim n _ q
    (Real.sqrt_nonneg _) hq0 hq1 hstep

/-- `E ≤ A √E` forces `E ≤ A²`. -/

theorem aux_mfd_prop_uniform_resolvent_oscillation_w_bound {d : ℕ} (hd : 2 ≤ d) (Qtri : Homogenization.TriadicCube d)
    (z : SpatialCoordinates d) (s : ℝ) (hr : 0 < s)
    (hroot : closure (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qtri))
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 Kc B : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0) (hKc : 0 ≤ Kc) (hB : 0 ≤ B)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Qtri), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t))
    (hV : μ (centeredCube z
        s hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal V0)
    (a : PositiveCoefficient (centeredCube z
      s hr))
    (w : killedSobolevGraph (centeredCube z
      s hr))
    (hcw1 : ‖(w : SobolevData (centeredCube z
        s hr)).1‖ ^ 2 ≤
      Kc * sobolevCoefficientForm a w.val w.val)
    (hcw2 : globalFractionalSqNorm (3 / 4)
        (Set.indicator ((centeredCube z
          s hr) : Set (SpatialCoordinates d))
          (fun x => (w : SobolevData (centeredCube z
            s hr)).1 x)) ≤
      ENNReal.ofReal (Kc * sobolevCoefficientForm a w.val w.val))
    (h : SpatialCoordinates d → ℝ)
    (hh : AEStronglyMeasurable h (μ.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))))
    (hbound : ∀ᵐ x ∂(μ.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))), |h x| ≤ B)
    (n : ℕ)
    (hEw : sobolevCoefficientForm a w.val w.val =
      (∫ x in (centeredCube z
          s hr : Set (SpatialCoordinates d)),
        h x * (w : SobolevData (centeredCube z
          s hr)).1 x ∂μ) -
      ∫ x, h x * aux_prop_uniform_resolvent_cutoff_oscillation_E z
          s hr
          (fun y => (w : SobolevData (centeredCube z
            s hr)).1 y) n x
        ∂(μ.restrict (centeredCube z
          s hr : Set (SpatialCoordinates d)))) :
    ‖(w : SobolevData (centeredCube z
        s hr)).1‖ ^ 2 ≤
      Kc ^ 2 * V0 * ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) *
          (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) /
        (1 - Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ 2 * B ^ 2 *
        (s / (3 : ℝ) ^ n) ^ (t - d + 1) := by
  haveI : IsFiniteMeasure (μ.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = sobolevCoefficientForm a w.val w.val := ⟨_, rfl⟩
  rw [← hEdef] at hcw1 hcw2 hEw
  have hE0 : 0 ≤ E := by rw [hEdef]; exact sobolevCoefficientForm_nonneg a _
  have hφ2 : MemLp (fun y => (w : SobolevData (centeredCube z
      s hr)).1 y) 2
      (volume.restrict (centeredCube z
        s hr : Set (SpatialCoordinates d))) := Lp.memLp _
  have hφs : StronglyMeasurable (fun y => (w : SobolevData (centeredCube
      z s hr)).1 y) :=
    Lp.stronglyMeasurable _
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ,
      cs = (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ) :=
    ⟨_, rfl⟩
  have hcs0 : 0 ≤ cs := by rw [hcsdef]; positivity
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ,
      C0 = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) := ⟨_, rfl⟩
  have hC00 : 0 ≤ C0 := by rw [hC0def]; positivity
  have hIr0 : 0 ≤ cs * (Kc * E) := by positivity
  have hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube z
      s hr : Set (SpatialCoordinates d))
      (fun y => (w : SobolevData (centeredCube z
        s hr)).1 y) ≤ ENNReal.ofReal (cs * (Kc * E)) := by
    refine (aux_prop_uniform_resolvent_cutoff_oscillation_kernel_compare _ hr _ hφs.measurable).trans ?_
    rw [ENNReal.ofReal_mul hcs0, ← hcsdef]
    gcongr
  have hT := aux_mfd_prop_uniform_resolvent_oscillation_trace_diff hd Qtri z s hr hroot t ht μ hac Km V0 hKm hV0 hgrowth hV _ hφ2
    (cs * (Kc * E)) hIr0 hI n
  rw [← hC0def] at hT
  have hα : 0 < t - d + 1 := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) := ⟨_, rfl⟩
  rw [← hqdef] at hT ⊢
  have hq0' : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  have hq1 : q < 1 := by
    rw [hqdef, Real.sqrt_lt' one_pos, one_pow]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 ≤ q := by rw [hqdef]; exact Real.sqrt_nonneg _
  have h1q : 0 < 1 - q := by linarith
  have hT0 : 0 ≤ Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * (Kc * E))) * q ^ n /
      (1 - q) := by positivity
  have hpair := aux_prop_uniform_resolvent_cutoff_oscillation_pair_diff_bound _ h _ _ B _ hB hT0 hh hbound hφs.aestronglyMeasurable
    (aux_prop_uniform_resolvent_cutoff_oscillation_E_memLp _ hr _ n _) hT
  have hVr : Real.sqrt ((μ.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))).real univ) ≤
      Real.sqrt V0 := by
    apply Real.sqrt_le_sqrt
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = B * Real.sqrt V0 *
      (Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q)) := ⟨_, rfl⟩
  have hEA : E ≤ A * Real.sqrt E := by
    have h1 := hpair.2.2
    rw [← hEw] at h1
    have h3 : Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * (Kc * E))) * q ^ n /
        (1 - q) = Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
        Real.sqrt E := by
      rw [show (Km + V0) * C0 * s ^ (t - d + 1) * (cs * (Kc * E)) =
        ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * E by ring,
        Real.sqrt_mul' _ hE0]
      ring
    rw [h3] at h1
    calc E ≤ B * Real.sqrt ((μ.restrict (centeredCube z
          s hr : Set (SpatialCoordinates d))).real univ) *
          (Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
            Real.sqrt E) := h1
      _ ≤ B * Real.sqrt V0 *
          (Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
            Real.sqrt E) := by gcongr
      _ = A * Real.sqrt E := by rw [hAdef]; ring
  have hEA2 := aux_prop_uniform_resolvent_cutoff_oscillation_sqrt_absorb E A hE0 hEA
  have hKmV : 0 ≤ Km + V0 := by linarith
  have hscale := aux_prop_uniform_resolvent_cutoff_oscillation_level_scale_pow _ (t - d + 1) hr n
  have hq2 : q ^ 2 = (3 : ℝ) ^ (-(t - d + 1)) := by rw [hqdef]; exact Real.sq_sqrt hq0'
  rw [← hC0def, ← hcsdef]
  calc _ ≤ Kc * E := hcw1
    _ ≤ Kc * A ^ 2 := mul_le_mul_of_nonneg_left hEA2 hKc
    _ = Kc ^ 2 * V0 * ((Km + V0) * C0 * cs) / (1 - q) ^ 2 * B ^ 2 *
          (s / (3 : ℝ) ^ n) ^ (t - d + 1) := by
        have hsq1 : Real.sqrt V0 ^ 2 = V0 := Real.sq_sqrt hV0
        have hsq2 : Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) *
            (cs * Kc)) ^ 2 = (Km + V0) * C0 * s ^ (t - d + 1) *
            (cs * Kc) := Real.sq_sqrt (by positivity)
        have hq2n : (q ^ n) ^ 2 = ((3 : ℝ) ^ (-(t - d + 1))) ^ n := by
          rw [← pow_mul, mul_comm n 2, pow_mul, hq2]
        rw [hscale, hAdef, mul_pow, mul_pow, div_pow, mul_pow, hsq1, hsq2, hq2n]
        field_simp


/-- Square-mean oscillation of `vc + ψ` on a ball, for `vc` globally `1/2`-Hölder and `ψ`
supported in `U` with controlled `L²` norm. -/

theorem aux_mfd_prop_uniform_resolvent_oscillation_instance {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon < 1)
    (Qtri : Homogenization.TriadicCube d) (z : SpatialCoordinates d) (s : ℝ) (hr : 0 < s)
    (hroot : closure (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qtri))
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 Kc Kh : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0) (hKc : 0 ≤ Kc) (hKh : 0 ≤ Kh)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Qtri), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ ((d : ℝ) - epsilon)))
    (hV : μ (centeredCube z s hr : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal V0)
    (a : PositiveCoefficient (centeredCube z s hr))
    (hcoer : ∀ v : killedSobolevGraph (centeredCube z s hr),
      ‖(v : SobolevData (centeredCube z s hr)).1‖ ^ 2 ≤ Kc * sobolevCoefficientForm a v.val v.val ∧
      globalFractionalSqNorm (3 / 4)
        (Set.indicator (centeredCube z s hr : Set (SpatialCoordinates d)) (fun x => (v : SobolevData (centeredCube z s hr)).1 x)) ≤
        ENNReal.ofReal (Kc * sobolevCoefficientForm a v.val v.val))
    (hHol : ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 → ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ (centeredCube z s hr : Set (SpatialCoordinates d)), |F0 x| ≤ MF) → ∀ v : killedSobolevGraph (centeredCube z s hr),
        (∀ w : killedSobolevGraph (centeredCube z s hr), sobolevCoefficientForm a v.val w.val =
          ∫ x in (centeredCube z s hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube z s hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube z s hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z s hr : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ (centeredCube z s hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure (centeredCube z s hr : Set (SpatialCoordinates d)), ∀ y ∈ closure (centeredCube z s hr : Set (SpatialCoordinates d)),
            |vc x - vc y| ≤ Kh * MF * dist x y ^ (1 / 2 : ℝ)))
    (u : killedSobolevGraph (centeredCube z s hr)) (h : SpatialCoordinates d → ℝ)
    (hh : AEStronglyMeasurable h (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d)))) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂(μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))), |h x| ≤ B)
    (hfin : ∀ w : killedSobolevGraph (centeredCube z s hr), sobolevCoefficientForm a u.val w.val =
      ∫ x in (centeredCube z s hr : Set (SpatialCoordinates d)), h x * (w : SobolevData (centeredCube z s hr)).1 x ∂μ)
    (u0 : SpatialCoordinates d → ℝ)
    (hzero : ∀ x, u0 x = Set.indicator (centeredCube z s hr : Set (SpatialCoordinates d)) (fun y => (u : SobolevData (centeredCube z s hr)).1 y) x)
    (x : SpatialCoordinates d) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ y in Metric.ball x r,
        (u0 y - (volume.real (Metric.ball x r))⁻¹ * ∫ w in Metric.ball x r, u0 w) ^ 2) ≤
      (aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s Km V0 Kc Kh * B) ^ 2 *
        volume.real (Metric.ball x r) * r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  have hQm : MeasurableSet (centeredCube z s hr : Set (SpatialCoordinates d)) := (centeredCube z s hr).isOpen.measurableSet
  haveI : IsFiniteMeasure (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  have hR0 : 0 < r ^ ((d : ℝ) + 2) := Real.rpow_pos_of_pos hr0 _
  have hR1 : r ^ ((d : ℝ) + 2) ≤ 1 := Real.rpow_le_one hr0.le hr1 (by positivity)
  obtain ⟨n, hn1, hn2⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_level_choice s
    (r ^ ((d : ℝ) + 2)) hr hR0 hR1
  have ht0 : 0 < (d : ℝ) - epsilon := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have htd : (d : ℝ) - 1 < (d : ℝ) - epsilon := by linarith
  have hℓpos : 0 < s / (3 : ℝ) ^ n := by positivity
  have hℓ2 : s / (3 : ℝ) ^ n ≤ 2 := by linarith
  obtain ⟨MF, hMFdef⟩ : ∃ MF : ℝ, MF = B * Km *
      (s / (3 : ℝ) ^ n) ^ ((d : ℝ) - epsilon) /
        (s / (3 : ℝ) ^ n) ^ d := ⟨_, rfl⟩
  have hMF0 : 0 ≤ MF := by rw [hMFdef]; positivity
  have hF0b : ∀ y, |aux_prop_uniform_resolvent_cutoff_oscillation_source z
      s hr (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) h n y| ≤ MF := by
    intro y
    rw [hMFdef]
    exact aux_prop_uniform_resolvent_cutoff_oscillation_source_bound _ hr μ h B hB hbound Km _ hKm ht0 (fun y hy => hgrowth y (hroot hy)) n hℓ2 y
  have hF0m := aux_prop_uniform_resolvent_cutoff_oscillation_source_measurable z hr
    (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) h n
  have hF0L2 : MemLp (aux_prop_uniform_resolvent_cutoff_oscillation_source z
      s hr (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) h n) 2 (volume.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hF0m.aestronglyMeasurable MF
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]; exact hF0b y))
  obtain ⟨v, hv⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_comparison_exists a Kc (fun v => (hcoer v).1) _ hF0L2
  obtain ⟨vc, hvcae, hvc0, hvcHol⟩ := hHol _ hF0m MF hMF0 (fun y _ => hF0b y) v hv
  have hC : 0 ≤ Kh * MF := mul_nonneg hKh hMF0
  have hglob := aux_prop_uniform_resolvent_cutoff_oscillation_holder_global (centeredCube z s hr : Set (SpatialCoordinates d)) (centeredCube z s hr).isOpen vc (Kh * MF) hC hvc0 hvcHol
  have hhint : Integrable h (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) := by
    refine Integrable.mono' (integrable_const B) hh ?_
    filter_upwards [hbound] with y hy
    simpa [Real.norm_eq_abs] using hy
  have hwint : IntegrableOn (fun y => ((u - v : killedSobolevGraph (centeredCube z s hr)) :
      SobolevData (centeredCube z s hr)).1 y) (centeredCube z s hr : Set (SpatialCoordinates d)) volume :=
    (Lp.memLp _).integrable one_le_two
  have hpair := aux_prop_uniform_resolvent_cutoff_oscillation_pairing z hr n (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) h hhint
    _ hwint
  have hEw : sobolevCoefficientForm a (u - v : killedSobolevGraph (centeredCube z s hr)).val
      (u - v : killedSobolevGraph (centeredCube z s hr)).val =
      (∫ y in (centeredCube z s hr : Set (SpatialCoordinates d)), h y * ((u - v : killedSobolevGraph (centeredCube z s hr)) : SobolevData (centeredCube z s hr)).1 y ∂μ) -
      ∫ y, h y * aux_prop_uniform_resolvent_cutoff_oscillation_E z
          s hr
          (fun y => ((u - v : killedSobolevGraph (centeredCube z s hr)) : SobolevData (centeredCube z s hr)).1 y) n y
        ∂(μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) := by
    rw [aux_prop_uniform_resolvent_cutoff_oscillation_form_sub, hfin, hv, hpair]
  have hwb := aux_mfd_prop_uniform_resolvent_oscillation_w_bound hd Qtri z s hr hroot ((d : ℝ) - epsilon) htd μ hac Km V0 Kc B hKm hV0 hKc
    hB hgrowth hV a (u - v) (hcoer (u - v)).1 (hcoer (u - v)).2 h hh hbound n hEw
  have hdecomp := aux_prop_uniform_resolvent_cutoff_oscillation_decomp (centeredCube z s hr) u v vc hvcae hvc0 u0 hzero
  have hW2 := (aux_prop_uniform_resolvent_cutoff_oscillation_L2_norm_sq
    ((u - v : killedSobolevGraph (centeredCube z
      s hr)) : SobolevData (centeredCube
        z s hr)).1).trans_le hwb
  have hcamp := aux_prop_uniform_resolvent_cutoff_oscillation_campanato_assembly (centeredCube z s hr : Set (SpatialCoordinates d)) hQm u0 vc _ vc.continuous (Kh * MF) hC hglob
    hdecomp (Lp.memLp _) _ hW2 x r
  refine hcamp.trans ?_
  have hvol : volume.real (Metric.ball x r) = (2 * r) ^ d := by
    rw [measureReal_def, Real.volume_pi_ball x hr0, Fintype.card_fin,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hvol, hMFdef]
  have hσ : 0 < min s (1 / 3) := lt_min hr (by norm_num)
  have hCw : 0 ≤ Kc ^ 2 * V0 * ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
        (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - epsilon))) *
        (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) /
      (1 - Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) - epsilon - d + 1)))) ^ 2 := by
    have : 0 ≤ Km + V0 := by linarith
    positivity
  exact aux_prop_uniform_resolvent_cutoff_oscillation_final_algebra (d := d) epsilon r _ _ B Km Kh _ hepsilon hepsilon1 hr0 hr1 hσ hCw
    hn1 hn2


/-- Uniform mass of the cube from unit-ball growth, by a fixed finite cover of its closure. -/

theorem aux_mfd_prop_uniform_resolvent_oscillation_cover {d : ℕ}
    (z : SpatialCoordinates d) (s : ℝ) (hr : 0 < s) :
    ∃ V1 : ℝ, 0 ≤ V1 ∧ ∀ (μ : Measure (SpatialCoordinates d)) (Km : ℝ), 0 ≤ Km →
      (∀ x ∈ closure (centeredCube z s hr : Set (SpatialCoordinates d)), μ (Metric.ball x 1) ≤ ENNReal.ofReal Km) →
      μ (centeredCube z s hr : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (V1 * Km) := by
  have hcomp : IsCompact (closure (centeredCube z s hr : Set (SpatialCoordinates d))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (centeredCube_isBounded _ hr).closure
  obtain ⟨T, hTsub, hTfin, hcover⟩ := finite_cover_balls_of_compact hcomp one_pos
  refine ⟨(hTfin.toFinset.card : ℝ), Nat.cast_nonneg _, ?_⟩
  intro μ Km hKm hball
  have hsub : (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆ ⋃ x ∈ hTfin.toFinset, Metric.ball x 1 := by
    intro y hy
    have := hcover (subset_closure hy)
    simp only [Set.mem_iUnion] at this ⊢
    obtain ⟨x, hxT, hyx⟩ := this
    exact ⟨x, hTfin.mem_toFinset.2 hxT, hyx⟩
  calc μ (centeredCube z s hr : Set (SpatialCoordinates d)) ≤ μ (⋃ x ∈ hTfin.toFinset, Metric.ball x 1) := measure_mono hsub
    _ ≤ ∑ x ∈ hTfin.toFinset, μ (Metric.ball x 1) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ hTfin.toFinset, ENNReal.ofReal Km := by
        exact Finset.sum_le_sum (fun x hx => hball x (hTsub (hTfin.mem_toFinset.1 hx)))
    _ = ENNReal.ofReal ((hTfin.toFinset.card : ℝ) * Km) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]


end Paper
