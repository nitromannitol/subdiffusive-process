import SubdiffusiveProcess.Compactness.UniformApproximation
import SubdiffusiveProcess.Probability.HigherMomentConvergence

/-!
# Compactness transfer under a Lipschitz-type scalar comparison

Source: `mfd:lem-prefix-limit`, cell-level compactness composed with the local-normalization
transport (paper 2749--2766). If a family of values in a complete pseudometric space compares to
a totally-bounded (resp. compact-closure) reference family via a fixed Lipschitz-type constant,
it inherits total boundedness (resp. compact closure). Combined with a clamp-truncation argument,
this gives: a fixed scalar function with a moment strictly above `2`, multiplied against an
`L¹`-relatively-compact, `L²`-norm-bounded family, stays `L¹`-relatively compact
(`isCompact_closure_range_smul_of_memLp_higher`) — the tool needed for the reference-scalar factor
`ref` in the local-normalization transport of `mfd:lem-prefix-limit`'s cell-level response
coordinates.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace SubdiffusiveProcess

/-- If `dist (f i) (f j) ≤ M * dist (g i) (g j)` for all `i j` and `M ≥ 0`, total boundedness of
`range g` transfers to `range f`. -/
theorem totallyBounded_range_of_dist_le_mul {X ι : Type*} [PseudoMetricSpace X]
    {f g : ι → X} {M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ i j, dist (f i) (f j) ≤ M * dist (g i) (g j))
    (hg : TotallyBounded (range g)) :
    TotallyBounded (range f) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set ε' : ℝ := ε / (2 * M + 1) with hε'def
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨t, htsub, htfin, hcover⟩ := Metric.finite_approx_of_totallyBounded hg ε' hε'pos
  haveI : Finite (↥t) := htfin.to_subtype
  let F : ↥t → ι := fun y => (htsub y.2).choose
  have hF : ∀ y : ↥t, g (F y) = (y : X) := fun y => (htsub y.2).choose_spec
  have hMlt : ∀ r : ℝ, 0 ≤ r → r < ε' → M * r < ε := by
    intro r hr0 hr
    calc M * r ≤ M * ε' := by
          rcases eq_or_lt_of_le hM with hM0 | hMpos
          · simp [← hM0]
          · exact mul_le_mul_of_nonneg_left hr.le hMpos.le
      _ < ε := by
          rw [hε'def]
          have hlt : M / (2 * M + 1) < 1 := by
            rw [div_lt_one (by positivity)]
            linarith
          calc M * (ε / (2 * M + 1)) = ε * (M / (2 * M + 1)) := by ring
            _ < ε * 1 := mul_lt_mul_of_pos_left hlt hε
            _ = ε := mul_one ε
  refine ⟨range (fun y : ↥t => f (F y)), (Set.finite_range _), ?_⟩
  rintro x ⟨i, rfl⟩
  have hgi : g i ∈ ⋃ y ∈ t, Metric.ball y ε' := hcover (mem_range_self i)
  simp only [mem_iUnion, Metric.mem_ball] at hgi
  obtain ⟨y, hyt, hdy⟩ := hgi
  refine mem_iUnion.mpr ⟨f (F ⟨y, hyt⟩), mem_iUnion.mpr ⟨⟨⟨y, hyt⟩, rfl⟩, ?_⟩⟩
  have hstep := hd i (F ⟨y, hyt⟩)
  rw [hF ⟨y, hyt⟩] at hstep
  calc dist (f i) (f (F ⟨y, hyt⟩)) ≤ M * dist (g i) y := hstep
    _ < ε := hMlt _ dist_nonneg hdy

/-- The compact-closure form of `totallyBounded_range_of_dist_le_mul`, for a complete space. -/
theorem isCompact_closure_range_of_dist_le_mul {X ι : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] {f g : ι → X} {M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ i j, dist (f i) (f j) ≤ M * dist (g i) (g j))
    (hg : IsCompact (closure (range g))) :
    IsCompact (closure (range f)) := by
  apply TotallyBounded.isCompact_of_isClosed _ isClosed_closure
  apply TotallyBounded.closure
  exact totallyBounded_range_of_dist_le_mul hM hd
    (TotallyBounded.subset subset_closure hg.totallyBounded)

theorem aux_clampf_abs_le (M x : ℝ) (hM : 0 ≤ M) : |max (-M) (min M x)| ≤ M := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem aux_clampf_eq_of_le (M x : ℝ) (h : |x| ≤ M) : max (-M) (min M x) = x := by
  have h1 : x ≤ M := (abs_le.mp h).2
  have h2 : -M ≤ x := (abs_le.mp h).1
  rw [min_eq_right h1, max_eq_right h2]

theorem aux_clampf_abs_le_abs (M x : ℝ) (hM : 0 ≤ M) : |max (-M) (min M x)| ≤ |x| := by
  rcases le_or_gt |x| M with h | h
  · rw [aux_clampf_eq_of_le M x h]
  · exact (aux_clampf_abs_le M x hM).trans h.le

theorem aux_clampf_sub_abs_le (M x : ℝ) (hM : 0 ≤ M) : |x - max (-M) (min M x)| ≤ 2 * |x| := by
  rcases le_or_gt |x| M with h | h
  · rw [aux_clampf_eq_of_le M x h]
    simp only [sub_self, abs_zero]
    positivity
  · have h1 : |max (-M) (min M x)| ≤ M := aux_clampf_abs_le M x hM
    have htri : |x - max (-M) (min M x)| ≤ |x| + |max (-M) (min M x)| := by
      rw [sub_eq_add_neg]
      calc |x + -(max (-M) (min M x))| ≤ |x| + |-(max (-M) (min M x))| := abs_add_le _ _
        _ = |x| + |max (-M) (min M x)| := by rw [abs_neg]
    linarith

/-- A fixed scalar function `φ` with a higher (`q > 2`) finite moment, multiplied against an
`L¹`-relatively-compact, `L²`-norm-bounded family `h`, is again `L¹`-relatively compact. Truncate
`φ` at level `M` (the clamp `max(-M)(min M ·)`): the truncated multiplier is bounded, so the
truncated family is compact via `isCompact_closure_range_of_dist_le_mul`; the residual
`φ - clamp_M φ` has `→ 0` vanishing `L²` norm as `M → ∞`
(`tendsto_eLpNorm_of_ae_tendsto_of_higher_bound`, since it is `≡ 0` once `M` exceeds `|φ(ω)|` and
uniformly bounded via the `q`-moment), giving a uniform-in-`K` `L¹` tail bound on the residual
times `h K` via Cauchy-Schwarz against the family's `L²` bound `B`. -/
theorem isCompact_closure_range_smul_of_memLp_higher
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (φ : Ω → ℝ) {q : ℝ≥0∞} (hq2 : (2 : ℝ≥0∞) < q) (hqtop : q ≠ ⊤) (hφq : MemLp φ q μ)
    (h : ℕ → Ω → ℝ) (hmem1 : ∀ K, MemLp (h K) 1 μ) (hmem2 : ∀ K, MemLp (h K) 2 μ)
    (B : ℝ) (hB0 : 0 ≤ B) (hBbd : ∀ K, eLpNorm (h K) 2 μ ≤ ENNReal.ofReal B)
    (hmemφ1 : ∀ K, MemLp (fun ω => φ ω * h K ω) 1 μ)
    (hcompact1 : IsCompact (closure (Set.range (fun K => (hmem1 K).toLp (h K))))) :
    IsCompact (closure (Set.range (fun K => (hmemφ1 K).toLp (fun ω => φ ω * h K ω)))) := by
  set φt : ℕ → Ω → ℝ := fun M ω => max (-(M : ℝ)) (min (M : ℝ) (φ ω)) with hφtdef
  have hφtcont : ∀ M : ℕ, Continuous (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := fun M =>
    continuous_const.max (continuous_const.min continuous_id)
  have hφtaesm : ∀ M, AEStronglyMeasurable (φt M) μ := fun M =>
    (hφtcont M).comp_aestronglyMeasurable hφq.1
  have hφtle : ∀ M : ℕ, ∀ ω, |φt M ω| ≤ |φ ω| := fun M ω =>
    aux_clampf_abs_le_abs (M : ℝ) (φ ω) (Nat.cast_nonneg M)
  have hφtleM : ∀ M : ℕ, ∀ ω, |φt M ω| ≤ (M : ℝ) := fun M ω =>
    aux_clampf_abs_le (M : ℝ) (φ ω) (Nat.cast_nonneg M)
  have hφtmemq : ∀ M, MemLp (φt M) q μ :=
    fun M => hφq.mono (hφtaesm M) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hφtle M ω)
  have hmemφtK1 : ∀ M K, MemLp (fun ω => φt M ω * h K ω) 1 μ := fun M K =>
    ((hmem1 K).const_mul (M : ℝ)).mono ((hφtaesm M).mul (hmem1 K).1) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) M)]
      exact mul_le_mul_of_nonneg_right (hφtleM M ω) (abs_nonneg _))
  -- Step 1: for fixed M, the clamp-multiplied family is compact (M-Lipschitz transfer from h).
  have hcompactM : ∀ M : ℕ, IsCompact (closure (Set.range
      (fun K => (hmemφtK1 M K).toLp (fun ω => φt M ω * h K ω)))) := by
    intro M
    apply isCompact_closure_range_of_dist_le_mul (Nat.cast_nonneg (α := ℝ) M) ?_ hcompact1
    intro K J
    rw [Lp.dist_edist, Lp.dist_edist, Lp.edist_toLp_toLp, Lp.edist_toLp_toLp]
    have hbound : eLpNorm (fun ω => φt M ω * h K ω - φt M ω * h J ω) 1 μ ≤
        (M : ℝ≥0∞) * eLpNorm (fun ω => h K ω - h J ω) 1 μ := by
      have heq : (fun ω => φt M ω * h K ω - φt M ω * h J ω) =
          (fun ω => φt M ω * (h K ω - h J ω)) := by funext ω; ring
      rw [heq]
      calc eLpNorm (fun ω => φt M ω * (h K ω - h J ω)) 1 μ ≤
          eLpNorm (fun ω => (M : ℝ) * (h K ω - h J ω)) 1 μ := by
            apply eLpNorm_mono_ae
            filter_upwards with ω
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
              abs_of_nonneg (Nat.cast_nonneg (α := ℝ) M)]
            exact mul_le_mul_of_nonneg_right (hφtleM M ω) (abs_nonneg _)
        _ = (M : ℝ≥0∞) * eLpNorm (fun ω => h K ω - h J ω) 1 μ := by
            have heq2 : (fun ω => (M : ℝ) * (h K ω - h J ω)) =
                (M : ℝ) • (fun ω => h K ω - h J ω) := rfl
            rw [heq2, eLpNorm_const_smul]
            congr 1
            rw [Real.enorm_eq_ofReal (Nat.cast_nonneg (α := ℝ) M), ENNReal.ofReal_natCast]
    have hfin1 : eLpNorm (fun ω => h K ω - h J ω) 1 μ ≠ ⊤ :=
      (((hmem1 K).sub (hmem1 J)).eLpNorm_lt_top).ne
    calc (eLpNorm (fun ω => φt M ω * h K ω - φt M ω * h J ω) 1 μ).toReal ≤
        ((M : ℝ≥0∞) * eLpNorm (fun ω => h K ω - h J ω) 1 μ).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M) hfin1) hbound
      _ = (M : ℝ) * (eLpNorm (fun ω => h K ω - h J ω) 1 μ).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  -- Step 2: the residual (φ - φt M) has vanishing L² norm as M → ∞, hence a uniform (in K) L¹
  -- tail bound on the residual times h K, via Cauchy-Schwarz against the L² bound B.
  haveI hHT : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by
    have hcancel : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 2 * (2 : ℝ≥0∞)⁻¹ := by ring
      _ = 1 := hcancel
      _ = (1 : ℝ≥0∞)⁻¹ := inv_one.symm⟩
  have hq1 : (1 : ℝ≥0∞) ≤ q := le_trans (by norm_num) hq2.le
  have hresmemq : ∀ M, MemLp (fun ω => φ ω - φt M ω) q μ := fun M => hφq.sub (hφtmemq M)
  have hresaesm : ∀ M, AEStronglyMeasurable (fun ω => φ ω - φt M ω) μ :=
    fun M => (hresmemq M).1
  have hresbound : ∀ M : ℕ, eLpNorm (fun ω => φ ω - φt M ω) q μ ≤
      (2 : ℝ≥0∞) * eLpNorm φ q μ := by
    intro M
    have htri : eLpNorm (fun ω => φ ω - φt M ω) q μ ≤
        eLpNorm φ q μ + eLpNorm (φt M) q μ := by
      have heq : (fun ω => φ ω - φt M ω) = φ - φt M := rfl
      rw [heq]
      exact (eLpNorm_sub_le hφq.1 (hφtaesm M) hq1).trans_eq rfl
    have hφtle2 : eLpNorm (φt M) q μ ≤ eLpNorm φ q μ :=
      eLpNorm_mono_ae (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hφtle M ω)
    calc eLpNorm (fun ω => φ ω - φt M ω) q μ ≤ eLpNorm φ q μ + eLpNorm (φt M) q μ := htri
      _ ≤ eLpNorm φ q μ + eLpNorm φ q μ := by gcongr
      _ = 2 * eLpNorm φ q μ := by ring
  have hreslim : ∀ᵐ ω ∂μ,
      Tendsto (fun M : ℕ => (fun ω => φ ω - φt M ω) ω) atTop (𝓝 ((0 : Ω → ℝ) ω)) := by
    refine ae_of_all _ fun ω => ?_
    have hev : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop] (fun M => φ ω - φt M ω) := by
      obtain ⟨N, hN⟩ := exists_nat_ge |φ ω|
      filter_upwards [eventually_ge_atTop N] with M hM
      have hle : |φ ω| ≤ (M : ℝ) := hN.trans (Nat.cast_le.mpr hM)
      simp only [hφtdef, aux_clampf_eq_of_le M (φ ω) hle, sub_self]
    simpa using Tendsto.congr' hev tendsto_const_nhds
  have hresK : MemLp (0 : Ω → ℝ) q μ ∧
      Tendsto (fun M : ℕ => eLpNorm (fun ω => φ ω - φt M ω) 2 μ) atTop (𝓝 0) := by
    have := tendsto_eLpNorm_of_ae_tendsto_of_higher_bound (μ := μ) (f := fun M ω => φ ω - φt M ω)
      (g := (0 : Ω → ℝ)) (p := 2) (q := q) (by norm_num) hq2 hqtop
      (K := 2 * eLpNorm φ q μ) (by
        refine ENNReal.mul_ne_top (by norm_num) hφq.eLpNorm_lt_top.ne)
      hresaesm aestronglyMeasurable_zero hresbound hreslim
    simpa only [sub_zero] using this
  have hresmem2 : ∀ M, MemLp (fun ω => φ ω - φt M ω) 2 μ :=
    fun M => (hresmemq M).mono_exponent hq2.le
  set errM : ℕ → ℝ := fun M => (eLpNorm (fun ω => φ ω - φt M ω) 2 μ).toReal * B
    with herrMdef
  have herrtend : Tendsto errM atTop (𝓝 0) := by
    have hreal : Tendsto (fun M : ℕ => (eLpNorm (fun ω => φ ω - φt M ω) 2 μ).toReal)
        atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by norm_num)).comp hresK.2
      simpa using this
    simpa [herrMdef] using hreal.mul_const B
  have hferr : ∀ M K, dist ((hmemφ1 K).toLp (fun ω => φ ω * h K ω))
      ((hmemφtK1 M K).toLp (fun ω => φt M ω * h K ω)) ≤ errM M := by
    intro M K
    rw [Lp.dist_edist, Lp.edist_toLp_toLp]
    have heq : (fun ω => φ ω * h K ω) - (fun ω => φt M ω * h K ω) =
        (fun ω => (φ ω - φt M ω) * h K ω) := by
      funext ω; simp only [Pi.sub_apply]; ring
    rw [heq]
    have hHol : eLpNorm (fun ω => (φ ω - φt M ω) * h K ω) 1 μ ≤
        eLpNorm (fun ω => φ ω - φt M ω) 2 μ * eLpNorm (h K) 2 μ := by
      have hsmul : (fun ω => (φ ω - φt M ω) * h K ω) =
          (fun ω => φ ω - φt M ω) • h K := rfl
      rw [hsmul]
      exact eLpNorm_smul_le_mul_eLpNorm (E := ℝ) (p := 2) (q := 2) (r := 1)
        (hmem2 K).1 (hresaesm M)
    have hstep : eLpNorm (fun ω => (φ ω - φt M ω) * h K ω) 1 μ ≤
        eLpNorm (fun ω => φ ω - φt M ω) 2 μ * ENNReal.ofReal B :=
      hHol.trans (by gcongr; exact hBbd K)
    calc (eLpNorm (fun ω => (φ ω - φt M ω) * h K ω) 1 μ).toReal ≤
        (eLpNorm (fun ω => φ ω - φt M ω) 2 μ * ENNReal.ofReal B).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (hresmem2 M).eLpNorm_lt_top.ne
            ENNReal.ofReal_ne_top) hstep
      _ = errM M := by rw [herrMdef, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0]
  exact isCompact_closure_range_of_approximating_compact_ranges
    (f := fun K => (hmemφ1 K).toLp (fun ω => φ ω * h K ω))
    (g := fun M K => (hmemφtK1 M K).toLp (fun ω => φt M ω * h K ω))
    (err := errM) hcompactM herrtend hferr

end SubdiffusiveProcess
