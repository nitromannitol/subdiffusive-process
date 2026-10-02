import SubdiffusiveProcess.PartProcess.CoreClosure
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess

/-- Compact continuous approximation can be localized to any open full-measure set. -/
theorem exists_supportedCc_approx {d : ℕ} {m : Measure (Fin d → ℝ)}
    (hm : IsLocallyFiniteMeasure m) (V : Set (Fin d → ℝ)) (hV : IsOpen V)
    (hfull : m Vᶜ = 0) (f : (Fin d → ℝ) → ℝ) (hf : MemLp f 2 m)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ g : (Fin d → ℝ) → ℝ, HasCompactSupport g ∧ tsupport g ⊆ V ∧
      eLpNorm (f - g) 2 m ≤ ε ∧ Continuous g ∧ MemLp g 2 m := by
  letI := hm
  suffices H : ∃ g : (Fin d → ℝ) → ℝ, eLpNorm (f - g) 2 m ≤ ε ∧
      Continuous g ∧ MemLp g 2 m ∧ HasCompactSupport g ∧ tsupport g ⊆ V by
    obtain ⟨g, hg, hc, hL, hK, hVg⟩ := H
    exact ⟨g, hK, hVg, hg, hc, hL⟩
  apply hf.induction_dense (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) _ _ _ _ hε
  rotate_left
  · rintro f g ⟨hf, hfL, hfK, hfs⟩ ⟨hg, hgL, hgK, hgs⟩
    exact ⟨hf.add hg, hfL.add hgL, hfK.add hgK,
      (tsupport_add f g).trans (union_subset hfs hgs)⟩
  · rintro f ⟨_, hf, _, _⟩
    exact hf.aestronglyMeasurable
  intro c t ht htμ ε hε
  obtain ⟨δ, hδpos, hδ⟩ := exists_Lp_half ℝ m 2 hε
  obtain ⟨η, hηpos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set (Fin d → ℝ), m s ≤ η →
        eLpNorm (s.indicator (fun _ => c)) 2 m ≤ δ :=
    exists_eLpNorm_indicator_le (by norm_num) c hδpos.ne'
  have hηpos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 hηpos
  have htV : (t ∩ V).indicator (fun _ => c) =ᵐ[m] t.indicator (fun _ => c) := by
    have hmem : ∀ᵐ x ∂m, x ∈ V := by
      rw [ae_iff]
      exact hfull
    filter_upwards [hmem] with x hx
    by_cases hxt : x ∈ t <;> simp [Set.indicator_apply, hxt, hx]
  obtain ⟨s, hst, hsK, hsC, hms⟩ :=
    (ht.inter hV.measurableSet).exists_isCompact_isClosed_diff_lt
      ((measure_mono inter_subset_left).trans_lt htμ).ne hηpos'.ne'
  have hsμ : m s < ⊤ := (measure_mono (hst.trans inter_subset_left)).trans_lt htμ
  have I1 : eLpNorm (s.indicator (fun _ => c) - t.indicator (fun _ => c)) 2 m ≤ δ := by
    rw [eLpNorm_congr_ae (EventuallyEq.rfl.sub htV.symm)]
    rw [← eLpNorm_neg, neg_sub, ← indicator_diff hst]
    exact hη _ hms.le
  obtain ⟨L, hLK, hsL⟩ := exists_compact_superset hsK
  obtain ⟨W, hWo, hsW, hWV⟩ := hsK.exists_isOpen_closure_subset
    (hV.mem_nhdsSet.2 (hst.trans inter_subset_right))
  let O := W ∩ interior L
  have hOo : IsOpen O := hWo.inter isOpen_interior
  have hsO : s ⊆ O := subset_inter hsW hsL
  obtain ⟨g, hgc, I2, _, hgs, hgL⟩ :=
    exists_continuous_eLpNorm_sub_le_of_closed (p := 2) (by norm_num)
      hsC hOo hsO hsμ.ne c hδpos.ne'
  have hK : HasCompactSupport g :=
    HasCompactSupport.intro hLK (fun x hx => by
      rw [← Function.notMem_support]
      exact fun h => hx (interior_subset (hgs h).2))
  have htsV : tsupport g ⊆ V := by
    exact (closure_mono hgs).trans
      ((closure_mono inter_subset_left).trans hWV)
  have I3 : eLpNorm (g - t.indicator (fun _ => c)) 2 m ≤ ε := by
    convert (hδ _ _
      (hgL.aestronglyMeasurable.sub
        (aestronglyMeasurable_const.indicator hsC.measurableSet))
      ((aestronglyMeasurable_const.indicator hsC.measurableSet).sub
        (aestronglyMeasurable_const.indicator ht)) I2 I1).le using 2
    simp only [sub_add_sub_cancel]
  exact ⟨g, I3, hgc, hgL, hK, htsV⟩

/-- Soft thresholding a uniform core approximation controls its support. -/
theorem exists_localCore_uniform {d : ℕ} {m : Measure (Fin d → ℝ)}
    (E : _root_.DirichletForm m) (V : Set (Fin d → ℝ))
    (C : Set (Lp ℝ 2 m)) (hC : DirichletForm.IsCoreOn E.toClosedForm V C)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfV : tsupport f ⊆ V) (U : Set (Fin d → ℝ)) (hfU : tsupport f ⊆ U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : Lp ℝ 2 m, E.toClosedForm.MemCoreOn U u ∧
      ∃ g : (Fin d → ℝ) → ℝ, Continuous g ∧ HasCompactSupport g ∧
        tsupport g ⊆ tsupport f ∧ ⇑u =ᵐ[m] g ∧ ∀ x, |g x - f x| < ε := by
  obtain ⟨w, hwC, g, hg, hgK, _, hwg, herr⟩ :=
    hC.denseUniform f hf hfc hfV (ε / 4) (by positivity)
  let Γ : ℝ → ℝ := fun t => max (t - ε / 2) 0 + min (t + ε / 2) 0
  have hΓ : LipschitzWith 2 Γ := by
    have hp : LipschitzWith 1 (fun t : ℝ => max (t - ε / 2) 0) := by
      simpa using (LipschitzWith.id.sub (LipschitzWith.const (ε / 2))).max
        (LipschitzWith.const 0)
    have hn : LipschitzWith 1 (fun t : ℝ => min (t + ε / 2) 0) := by
      simpa using (LipschitzWith.id.add (LipschitzWith.const (ε / 2))).min
        (LipschitzWith.const 0)
    convert hp.add hn using 1 <;> norm_num
  have hΓzero : ∀ t, |t| ≤ ε / 2 → Γ t = 0 := by
    intro t ht
    obtain ⟨hl, hr⟩ := abs_le.1 ht
    dsimp [Γ]
    rw [max_eq_right (by linarith), min_eq_right (by linarith)]
    exact add_zero 0
  have hΓ0 : Γ 0 = 0 := hΓzero 0 (by simp only [abs_zero]; positivity)
  have hΓerr : ∀ t, |Γ t - t| ≤ ε / 2 := by
    intro t
    dsimp [Γ]
    simp only [max_def, min_def]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  let z : Lp ℝ 2 m := hΓ.compLp hΓ0 w
  have hzw : ⇑z =ᵐ[m] fun x => Γ (w x) := LipschitzWith.coeFn_compLp hΓ hΓ0 w
  have hzE : z ∈ E.domain :=
    (DirichletForm.lipschitz_comp_mem E hΓ hΓ0 (hC.memCoreOn w hwC).1 hzw).1
  have hzg : ⇑z =ᵐ[m] Γ ∘ g := hzw.trans (hwg.fun_comp Γ)
  have hsupport : Function.support (Γ ∘ g) ⊆ tsupport f := by
    intro x hx
    by_contra hnot
    have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hnot
    have hsmall := herr x
    rw [hfx, sub_zero] at hsmall
    have hle : |g x| ≤ ε / 2 := by linarith
    exact hx (hΓzero _ hle)
  have hts : tsupport (Γ ∘ g) ⊆ tsupport f := closure_minimal hsupport isClosed_closure
  have hcompact : HasCompactSupport (Γ ∘ g) :=
    IsCompact.of_isClosed_subset hfc isClosed_closure hts
  have hcont : Continuous (Γ ∘ g) := hΓ.continuous.comp hg
  refine ⟨z, ⟨hzE, Γ ∘ g, hcont, hcompact, hts.trans hfU, hzg⟩,
    Γ ∘ g, hcont, hcompact, hts, hzg, ?_⟩
  intro x
  have hb := abs_add_le (Γ (g x) - g x) (g x - f x)
  have he := hΓerr (g x)
  have ha := herr x
  simp only [Function.comp_apply]
  have hs : Γ (g x) - f x = (Γ (g x) - g x) + (g x - f x) := by ring
  rw [hs]
  linarith

end SubdiffusiveProcess.PartProcess
