import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Paper

/-- An almost-everywhere monotone, almost-everywhere nonnegative real sequence
with uniformly bounded `L^P` norms (`1 ≤ P < ∞`, probability law) converges in
`L^P` to an almost-everywhere strongly measurable limit.  The limit is the
pointwise supremum; it lies in `L^P` by Fatou, and it dominates the sequence,
which gives uniform integrability. -/
theorem aux_prefix_field_mono_Lp_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v : ℕ → Ω → ℝ) (P : ℝ≥0∞) (hP : 1 ≤ P) (hPtop : P ≠ ∞)
    (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hnn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ v n x)
    (hmono : ∀ᵐ x ∂μ, Monotone (fun n => v n x))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hbound : ∀ n, eLpNorm (v n) P μ ≤ C) :
    ∃ g : Ω → ℝ, AEStronglyMeasurable g μ ∧
      Tendsto (fun n => eLpNorm (v n - g) P μ) atTop (𝓝 0) := by
  -- Step 1: the pointwise supremum is finite almost everywhere.
  let G : Ω → ℝ≥0∞ := fun x => ⨆ n, ENNReal.ofReal (v n x)
  have hGint : ∫⁻ x, G x ∂μ ≤ C := by
    have hsup : ∫⁻ x, G x ∂μ = ⨆ n, ∫⁻ x, ENNReal.ofReal (v n x) ∂μ :=
      lintegral_iSup' (fun n => (hv n).aemeasurable.ennreal_ofReal)
        (hmono.mono fun x hx n n' hnn' => ENNReal.ofReal_le_ofReal (hx hnn'))
    rw [hsup]
    refine iSup_le fun n => ?_
    calc
      ∫⁻ x, ENNReal.ofReal (v n x) ∂μ ≤ ∫⁻ x, ‖v n x‖ₑ ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ = eLpNorm (v n) 1 μ := (eLpNorm_one_eq_lintegral_enorm).symm
      _ ≤ eLpNorm (v n) P μ := eLpNorm_le_eLpNorm_of_exponent_le hP (hv n)
      _ ≤ C := hbound n
  have hGmeas : AEMeasurable G μ :=
    AEMeasurable.iSup fun n => (hv n).aemeasurable.ennreal_ofReal
  have hGfin : ∀ᵐ x ∂μ, G x < ∞ :=
    ae_lt_top' hGmeas (ne_top_of_le_ne_top hC hGint)
  have hbdd : ∀ᵐ x ∂μ, BddAbove (Set.range fun n => v n x) := by
    filter_upwards [hGfin] with x hx
    refine ⟨(G x).toReal, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hx.ne).1
      (le_iSup (fun n => ENNReal.ofReal (v n x)) n)
  -- Step 2: the real supremum is the almost-everywhere limit.
  let g : Ω → ℝ := fun x => ⨆ n, v n x
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (g x)) := by
    filter_upwards [hmono, hbdd] with x hx hb
    exact tendsto_atTop_ciSup hx hb
  have hgmeas : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hv hlim
  -- Step 3: the limit is in `L^P` (Fatou).
  have hgC : eLpNorm g P μ ≤ C :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound) hv hlim
  have hgLp : MemLp g P μ := ⟨hgmeas, lt_of_le_of_lt hgC (lt_top_iff_ne_top.2 hC)⟩
  -- Step 4: domination by the limit gives uniform integrability.
  have hdom : ∀ᵐ x ∂μ, ∀ n, ‖v n x‖ ≤ ‖g x‖ := by
    filter_upwards [hnn, hbdd] with x hx hb n
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hx n),
      abs_of_nonneg ((hx n).trans (le_ciSup hb n))]
    exact le_ciSup hb n
  have hui : UnifIntegrable v P μ := by
    intro ε hε
    obtain ⟨δ, hδ, hδs⟩ := hgLp.eLpNorm_indicator_le hP hPtop hε
    refine ⟨δ, hδ, fun n s hs hμs => le_trans (eLpNorm_mono_ae ?_) (hδs s hs hμs)⟩
    filter_upwards [hdom] with x hx
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]
      exact hx n
    · simp [Set.indicator_of_notMem hxs]
  exact ⟨g, hgmeas, tendsto_Lp_finite_of_tendsto_ae hP hPtop hv hgLp hui hlim⟩


/-- Cauchy form of `aux_prefix_field_mono_Lp_tendsto` at a real exponent `p ≥ 1`. -/
theorem aux_prefix_field_mono_Lp_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v : ℕ → Ω → ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hnn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ v n x)
    (hmono : ∀ᵐ x ∂μ, Monotone (fun n => v n x))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ n, eLpNorm (v n) (ENNReal.ofReal p) μ ≤ C)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' →
      eLpNorm (fun x => v n x - v n' x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal eps := by
  have hP : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  obtain ⟨g, hg, htend⟩ := aux_prefix_field_mono_Lp_tendsto μ v (ENNReal.ofReal p)
    hP ENNReal.ofReal_ne_top hv hnn hmono C hC hbound
  have hhalf : (0 : ℝ≥0∞) < ENNReal.ofReal (eps / 2) :=
    ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.mp htend) _ hhalf)
  refine ⟨n0, fun n n' hn hn' => ?_⟩
  have hsplit : (fun x => v n x - v n' x) = (v n - g) - (v n' - g) := by
    funext x; simp only [Pi.sub_apply]; ring
  rw [hsplit]
  calc
    eLpNorm ((v n - g) - (v n' - g)) (ENNReal.ofReal p) μ ≤
        eLpNorm (v n - g) (ENNReal.ofReal p) μ +
          eLpNorm (v n' - g) (ENNReal.ofReal p) μ :=
      eLpNorm_sub_le ((hv n).sub hg) ((hv n').sub hg) hP
    _ ≤ ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) :=
      add_le_add (hn0 n hn) (hn0 n' hn')
    _ = ENNReal.ofReal eps := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring


end Paper
