module

public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Tactic

@[expose] public section

/-! Smooth compactly supported sources are dense in L2 of an open finite-measure set.
The support lies inside the open set; this does not assert density in a form norm. -/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal Topology ContDiff Manifold

namespace SubdiffusiveProcess.SmoothSources

/-- Multiplication by a cutoff between zero and one does not enlarge the discarded magnitude. -/
theorem norm_sub_mul_le_norm (c v : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ‖v - c * v‖ ≤ ‖v‖ := by
  have h1c : (0 : ℝ) ≤ 1 - c := by linarith only [h1]
  calc
    ‖v - c * v‖ = ‖(1 - c) * v‖ := by
      congr 1
      ring
    _ = ‖(1 - c : ℝ)‖ * ‖v‖ := norm_mul (1 - c) v
    _ ≤ 1 * ‖v‖ := by
      gcongr
      rw [Real.norm_eq_abs, abs_of_nonneg h1c]
      linarith only [h0]
    _ = ‖v‖ := by rw [one_mul]

/-- A smooth L2 function can be cut off inside an open finite-measure set with arbitrarily small L2 error. -/
theorem exists_contDiff_tsupport_subset_eLpNorm_sub_le {d : ℕ}
    {U : Set (Fin d → ℝ)} (hUopen : IsOpen U) (hUfinite : volume U ≠ ⊤)
    {g : (Fin d → ℝ) → ℝ} (hgL2 : MemLp g 2 (volume.restrict U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : (Fin d → ℝ) → ℝ, MemLp φ 2 (volume.restrict U) ∧
      eLpNorm (g - φ) 2 (volume.restrict U) ≤ ENNReal.ofReal ε ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U := by
    obtain ⟨δ, hδpos, hδ⟩ :=
      hgL2.eLpNorm_indicator_le (p := (2 : ENNReal)) (by norm_num)
        ENNReal.ofNat_ne_top (ENNReal.ofReal_pos.mpr hε)
    obtain ⟨K, hKU, hK_compact, hK_closed, hμK⟩ :=
      hUopen.measurableSet.exists_isCompact_isClosed_diff_lt (μ := volume)
        hUfinite hδpos.ne'
    rcases exists_compact_closed_between hK_compact hUopen hKU with
      ⟨L, hL_compact, hL_closed, hKL, hLU⟩
    rcases exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, Fin d → ℝ)) hK_closed hKL with
      ⟨η, hη_one, hη_zero, hη_range⟩
    let φ : (Fin d → ℝ) → ℝ := fun x => η x * g x
    have hη_cont : ContDiff ℝ (⊤ : ℕ∞) η := η.contMDiff.contDiff
    have hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ := by
      change ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * g x)
      exact hη_cont.mul hg_cont
    have hφ_support : Function.support φ ⊆ L := by
      intro x hx
      by_contra hxL
      have hz : η x = 0 := hη_zero x hxL
      exact hx (by simp only [φ, hz, zero_mul])
    have hφ_compact : HasCompactSupport φ :=
      HasCompactSupport.of_support_subset_isCompact hL_compact hφ_support
    have hφ_tsupport : tsupport φ ⊆ U := by
      have hφ_tsupport_L : tsupport φ ⊆ L := by
        simpa only [tsupport] using closure_minimal hφ_support hL_closed
      exact hφ_tsupport_L.trans hLU
    have hφL2 : MemLp φ 2 (volume.restrict U) :=
      hφ_cont.continuous.memLp_of_hasCompactSupport hφ_compact
    refine ⟨φ, hφL2, ?_, hφ_cont, hφ_compact, hφ_tsupport⟩
    have hμsmall : volume.restrict U (U \ K) ≤ δ := by
      rw [Measure.restrict_apply (hUopen.measurableSet.diff hK_closed.measurableSet)]
      simpa only [Set.inter_eq_self_of_subset_left (Set.diff_subset : U \ K ⊆ U)] using hμK.le
    have hindicator := hδ (U \ K) (hUopen.measurableSet.diff hK_closed.measurableSet) hμsmall
    calc
      eLpNorm (g - φ) 2 (volume.restrict U)
          ≤ eLpNorm ((U \ K).indicator g) 2 (volume.restrict U) := by
            refine eLpNorm_mono_ae (hgL2.sub hφL2).aestronglyMeasurable ?_
            have hmem : ∀ᵐ x ∂ volume.restrict U, x ∈ U :=
              ae_restrict_mem hUopen.measurableSet
            filter_upwards [hmem] with x hxU
            by_cases hxK : x ∈ K
            · have hφx : φ x = g x := by
                have hηx : η x = 1 := hη_one.self_of_nhdsSet x hxK
                simp only [φ, hηx, one_mul]
              change ‖g x - φ x‖ ≤ _
              rw [hφx, sub_self, norm_zero]
              exact norm_nonneg _
            · have hxDiff : x ∈ U \ K := ⟨hxU, hxK⟩
              rw [Set.indicator_of_mem hxDiff]
              exact norm_sub_mul_le_norm (η x) (g x) (hη_range x).1 (hη_range x).2
      _ ≤ ENNReal.ofReal ε := hindicator

/-- Smooth support-preserving cutoff approximation implies density of smooth sources. -/
theorem dense_smooth_tsupport_subset {d : ℕ}
    {U : Set (Fin d → ℝ)} (_hUopen : IsOpen U) (_hUfinite : volume U ≠ ⊤)
    (hcut : ∀ {g : (Fin d → ℝ) → ℝ}, MemLp g 2 (volume.restrict U) → ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ {ε : ℝ}, 0 < ε → ∃ φ : (Fin d → ℝ) → ℝ, MemLp φ 2 (volume.restrict U) ∧
        eLpNorm (g - φ) 2 (volume.restrict U) ≤ ENNReal.ofReal ε ∧
        ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U) :
    Dense {f : Lp ℝ 2 (volume.restrict U) | ∃ fc : (Fin d → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧ tsupport fc ⊆ U ∧
        (f : (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict U] fc} := by
  haveI exponentAtLeastOne : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  haveI finiteOnCompacts : IsFiniteMeasureOnCompacts (volume.restrict U) := inferInstance
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := by positivity
  have hdense := MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (E := Fin d → ℝ) (F := ℝ) (μ := volume.restrict U) (p := (2 : ENNReal))
    ENNReal.ofNat_ne_top
  rw [Metric.dense_iff] at hdense
  obtain ⟨g_lp, hg_ball, g, hg_ae, hg_compact, hg_cont⟩ := hdense f (ε / 2) hε2
  rw [Metric.mem_ball] at hg_ball
  have hfg_lt : dist f g_lp < ε / 2 := by
    rw [dist_comm]
    exact hg_ball
  have hgL2 : MemLp g 2 (volume.restrict U) := (MeasureTheory.Lp.memLp g_lp).ae_eq hg_ae
  obtain ⟨φ, hφL2, hφ_err, hφ_cont, hφ_compact, hφ_tsupport⟩ := hcut hgL2 hg_cont hε2
  refine ⟨hφL2.toLp φ, ?_, ?_⟩
  · exact ⟨φ, hφ_cont, hφ_compact, hφ_tsupport, hφL2.coeFn_toLp⟩
  · have hdist_gφ : dist g_lp (hφL2.toLp φ) ≤ ε / 2 := by
      rw [MeasureTheory.Lp.dist_def]
      have hcongr :
          eLpNorm ((↑↑g_lp : (Fin d → ℝ) → ℝ) - (↑↑(hφL2.toLp φ) : (Fin d → ℝ) → ℝ))
              2 (volume.restrict U) =
            eLpNorm (g - φ) 2 (volume.restrict U) := by
        apply MeasureTheory.eLpNorm_congr_ae
        filter_upwards [hg_ae, hφL2.coeFn_toLp] with x hx1 hx2
        simp only [Pi.sub_apply, hx1, hx2]
      rw [hcongr]
      exact ENNReal.toReal_le_of_le_ofReal hε2.le hφ_err
    calc
      dist (hφL2.toLp φ) f = dist f (hφL2.toLp φ) := dist_comm _ _
      _ ≤ dist f g_lp + dist g_lp (hφL2.toLp φ) := dist_triangle _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add hfg_lt.le hdist_gφ
      _ = ε := by ring

/-- Smooth sources supported inside an open finite-measure set are dense in its L2 space. -/
theorem dense_smooth_compact_support {d : ℕ} {U : Set (Fin d → ℝ)}
    (hUopen : IsOpen U) (hUfinite : volume U ≠ ⊤) :
    Dense {f : Lp ℝ 2 (volume.restrict U) | ∃ fc : (Fin d → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧ tsupport fc ⊆ U ∧
        (f : (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict U] fc} :=
  dense_smooth_tsupport_subset hUopen hUfinite
    (fun {_g} hg hc {_eps} hε => exists_contDiff_tsupport_subset_eLpNorm_sub_le hUopen hUfinite hg hc hε)

end SubdiffusiveProcess.SmoothSources
