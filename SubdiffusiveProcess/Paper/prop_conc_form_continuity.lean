module

public import SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity
public import SubdiffusiveProcess.Paper.lem_cutoffs

@[expose] public section

/-! Extracted local form data for the relative concentration proof.
This module proves the stated deterministic implications; it does not construct random bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set Topology TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity Homogenization SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Part 2 of `SubdiffusiveProcess.Paper.prop_conc_form_continuity` (split for the heartbeat budget): Arzelà–Ascoli
extraction of a uniformly convergent subsequence of the continuous representatives `vc`, and
vanishing of the limit on the frontier of the cube. -/
theorem aux_prop_conc_form_continuity_Gf_continuous_subseq {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K) (MF : ℝ) (hMF : 0 ≤ MF)
    (vc : ℕ → SpatialCoordinates d → ℝ) (hvcc : ∀ N, Continuous (vc N))
    (hvc0 : ∀ N, ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), vc N x = 0)
    (hvchol : ∀ N, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        |vc N x - vc N y| ≤ (K * MF) * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (1 / 2 : ℝ)) :
    ∃ (σ : ℕ → ℕ) (_ : StrictMono σ) (g : SpatialCoordinates d → ℝ)
      (_ : ContinuousOn g (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) (B : ℝ),
      0 ≤ B ∧
      TendstoUniformlyOn (fun n => vc (σ n)) g atTop
        (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (∀ N, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), |vc N x| ≤ B) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = 0) := by
  -- a boundary corner of the cube
  set y0 : SpatialCoordinates d := fun i => z i + r / 2 with hy0
  have hy0c : y0 ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [aux_lem_cutoffs_holder_mem_closure_cube]
    intro i
    simp only [hy0, add_sub_cancel_left]
    rw [abs_of_pos (half_pos hr)]
  have hy0Q : y0 ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro h
    change y0 ∈ Metric.ball z (r / 2) at h
    rw [Metric.mem_ball] at h
    have h0 := dist_le_pi_dist y0 z ⟨0, by omega⟩
    simp only [hy0, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hr)] at h0
    exact (not_lt_of_ge h0) h
  have hdiam : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      Real.sqrt (∑ j : Fin d, (x j - y0 j) ^ 2) ≤ Real.sqrt d * r := by
    intro x hx
    refine (aux_lem_cutoffs_holder_edist_le_dist x y0).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine (dist_pi_le_iff hr.le).mpr fun i => ?_
    rw [aux_lem_cutoffs_holder_mem_closure_cube] at hx hy0c
    rw [Real.dist_eq]
    have h1 := hx i
    have h2 := hy0c i
    calc |x i - y0 i| = |(x i - z i) - (y0 i - z i)| := by ring_nf
      _ ≤ |x i - z i| + |y0 i - z i| := abs_sub _ _
      _ ≤ r / 2 + r / 2 := add_le_add h1 h2
      _ = r := by ring
  set B : ℝ := (K * MF) * (Real.sqrt d * r) ^ (1 / 2 : ℝ) with hB
  have hbdd : ∀ N, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      |vc N x| ≤ B := by
    intro N x hx
    have h := hvchol N x hx y0 hy0c
    rw [hvc0 N y0 hy0Q, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (hdiam x hx) (by norm_num)
  have hcpt : IsCompact (closure (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [_root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_closure_cube]; exact (closedCube z r hr).isCompact
  obtain ⟨σ, hσ, g, hgc, hgu⟩ := aux_lem_cutoffs_subseq_uniform _ hcpt vc
    (fun N => (hvcc N).continuousOn) (by norm_num : (0 : ℝ) < 1 / 2)
    (mul_nonneg hK hMF) hbdd hvchol
  -- the limit vanishes on the frontier
  have hg0 : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = 0 := by
    intro x hx
    have hxc : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      frontier_subset_closure hx
    have hxQ : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      rw [(centeredCube z r hr).isOpen.frontier_eq] at hx
      exact hx.2
    have hpt := hgu.tendsto_at hxc
    simp only [hvc0 _ x hxQ] at hpt
    exact tendsto_nhds_unique hpt tendsto_const_nhds
  exact ⟨σ, hσ, g, hgc, B, by rw [hB]; positivity, hgu, hbdd, hg0⟩

open Classical in
/-- Part 3 of `SubdiffusiveProcess.Paper.prop_conc_form_continuity` (split for the heartbeat budget): the actual
`GN (σ n) f` (whose continuous representatives are `vc (σ n)`, by `hvcae`) converges in `L²` to
the `L²` class `Ulp` of the uniform limit `U` of `vc ∘ σ`, using the uniform convergence `hgu`
transported through the `if`-extension `hU` and the finite-measure `Lp` norm bound. -/
theorem aux_prop_conc_form_continuity_Gf_continuous_Ltwo {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (σ : ℕ → ℕ) (g : SpatialCoordinates d → ℝ)
    (vc : ℕ → SpatialCoordinates d → ℝ)
    (hgu : TendstoUniformlyOn (fun n => vc (σ n)) g atTop
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (U : SpatialCoordinates d → ℝ)
    (hU : ∀ x, U x = if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) then g x else 0)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (f : DomainL2 (centeredCube z r hr))
    (hvcae : ∀ N, ((GN N f : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc N)
    (Ulp : DomainL2 (centeredCube z r hr))
    (hUlpae : (Ulp : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) :
    Tendsto (fun n => GN (σ n) f) atTop (𝓝 Ulp) := by
  have finiteCubeMeasure : IsFiniteMeasure (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [isFiniteMeasure_restrict, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  set c : ℝ := ((measureUnivNNReal (volume.restrict
    (centeredCube z r hr : Set (SpatialCoordinates d)))) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  rw [Metric.tendstoUniformlyOn_iff] at hgu
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (2 * (c + 1)) := by positivity
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp (hgu _ hε')
  refine ⟨n0, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hb : ∀ᵐ y ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      ‖(GN (σ n) f - Ulp : DomainL2 (centeredCube z r hr)) y‖ ≤ ε / (2 * (c + 1)) := by
    filter_upwards [Lp.coeFn_sub (GN (σ n) f) Ulp, hvcae (σ n), hUlpae,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y h1 h2 h3 hyQ
    rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]
    simp only [hU, ite_eq_left hyQ]
    have := hn0 n hn y (subset_closure hyQ)
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  calc ‖GN (σ n) f - Ulp‖ ≤ c * (ε / (2 * (c + 1))) := Lp.norm_le_of_ae_bound hε'.le hb
    _ < ε := by
        have : c * (ε / (2 * (c + 1))) = ε * (c / (2 * (c + 1))) := by ring
        rw [this]
        have hlt : c / (2 * (c + 1)) < 1 := by
          rw [div_lt_one (by positivity)]; linarith only [hc0]
        exact (mul_lt_mul_of_pos_left hlt hε).trans_eq (mul_one ε)

/-- **Continuity of the limit inverse on smooth sources.**  Uniform `C^{1/2}` bounds on the
killed responses (from the `lem_as_regularity` Dirichlet estimate, uniform in the cutoff),
Arzelà–Ascoli, and the `L²` identification of the limit. Assembled from
`SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity` and `SubdiffusiveProcess.Paper.aux_prop_conc_form_continuity_Gf_continuous_subseq` (split for the
heartbeat budget: the combined proof exceeds the default heartbeat limit as one declaration). -/
theorem prop_conc_form_continuity (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) (K : ℝ) (hK : 0 ≤ K)
    (hD : ∀ N, _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_DirProp z r hr (a N) K)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GN n f =
      (responseSolution (killedResponseSpace hP) (a n)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hG : Tendsto GN atTop (𝓝 G))
    (f : DomainL2 (centeredCube z r hr))
    (hf : ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (f : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((G f : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0 := by
  classical
  obtain ⟨fc, hfs, hfc, _hfsub, hfae⟩ := hf
  obtain ⟨MF0, hMF0⟩ := hfs.continuous.bounded_above_of_compact_support hfc
  set MF : ℝ := max MF0 0 with hMFdef
  have hMF : 0 ≤ MF := le_max_right _ _
  have hfb : ∀ x, |fc x| ≤ MF := fun x =>
    (by simpa only [Real.norm_eq_abs] using hMF0 x : |fc x| ≤ MF0).trans (le_max_left _ _)
  have hvc := _root_.SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity hd z r hr hP a K hK hD GN hGN f fc hfs hfc hfae
    MF hMF hfb
  choose vc hvcc hvcae hvc0 hvchol using hvc
  obtain ⟨σ, hσ, g, hgc, B, hB0, hgu, hbdd, hg0⟩ :=
    _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_continuity_Gf_continuous_subseq hd z r hr K hK MF hMF vc hvcc hvc0 hvchol
  set U : SpatialCoordinates d → ℝ :=
    fun x => if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) then g x else 0 with hU
  have hUc : Continuous U := by
    refine continuous_if ?_ hgc continuous_const.continuousOn
    intro x hx
    exact hg0 x hx
  have hU0 : ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0 := by
    intro x hx; simp only [hU, ite_eq_right hx]
  refine ⟨U, hUc, ?_, hU0⟩
  -- `L²` identification
  have finiteCubeMeasure : IsFiniteMeasure (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [isFiniteMeasure_restrict, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hgb : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), |g x| ≤ B := by
    intro x hx
    have hpt := hgu.tendsto_at hx
    exact le_of_tendsto' ((continuous_abs.tendsto _).comp hpt) (fun n => hbdd (σ n) x hx)
  have hUb : ∀ x, |U x| ≤ B := by
    intro x
    by_cases hxQ : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
    · simp only [hU, ite_eq_left hxQ]; exact hgb x (subset_closure hxQ)
    · simp only [hU, ite_eq_right hxQ, abs_zero]
      exact hB0
  have hUmem : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hUc.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hUb x)
  set Ulp : DomainL2 (centeredCube z r hr) := hUmem.toLp U with hUlp
  have hGf : Tendsto (fun n => GN (σ n) f) atTop (𝓝 (G f)) :=
    (((ContinuousLinearMap.apply ℝ _ f).continuous.tendsto G).comp hG).comp hσ.tendsto_atTop
  have hUl : Tendsto (fun n => GN (σ n) f) atTop (𝓝 Ulp) :=
    _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_continuity_Gf_continuous_Ltwo z r hr σ g vc hgu U (congrFun hU) GN f hvcae
      Ulp hUmem.coeFn_toLp
  have heq : G f = Ulp := tendsto_nhds_unique hGf hUl
  rw [heq]
  exact hUmem.coeFn_toLp

end SubdiffusiveProcess.Paper
