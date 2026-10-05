module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

/-!
# `L^q`-relative compactness transports down to `L^p` on a probability measure

This module establishes what is *not* the Rademacher counterexample: given a family that is
already relatively compact in `L^q` (not merely bounded), the natural inclusion `L^q ↪ L^p`
for `p ≤ q` on a probability measure is `1`-Lipschitz, so the SAME family, reinterpreted at
the lower exponent `p`, is again relatively compact. This module does not claim boundedness
alone implies precompactness.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

noncomputable section

/-- The image of a relatively compact sequence under a continuous map is relatively compact. -/
theorem lp_compact_image {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (f : ℕ → X) (hf : IsCompact (closure (Set.range f)))
    (F : X → Y) (hF : Continuous F) :
    IsCompact (closure (Set.range (fun n => F (f n)))) := by
  have hIm : IsCompact (F '' closure (Set.range f)) := hf.image hF
  have hsub : closure (Set.range (fun n => F (f n))) ⊆ F '' closure (Set.range f) := by
    apply closure_minimal
    · rintro y ⟨n, rfl⟩
      exact ⟨f n, subset_closure ⟨n, rfl⟩, rfl⟩
    · exact hIm.isClosed
  exact IsCompact.of_isClosed_subset hIm isClosed_closure hsub

/-- A finite (`Fintype`-indexed) tuple of relatively compact sequences is itself relatively
compact in the product, and any continuous function of the tuple stays relatively compact.
This is the general tool behind both a fixed finite linear combination of relatively compact
real sequences (`ι` indexes the terms) and a finite-dimensional continuous function of
jointly-compact matrix entries (`ι := Fin d × Fin d`). -/
theorem isCompact_closure_range_finset_apply {ι X Y : Type*} [Fintype ι]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    (f : ι → ℕ → X) (hf : ∀ i, IsCompact (closure (Set.range (f i))))
    (F : (ι → X) → Y) (hF : Continuous F) :
    IsCompact (closure (Set.range (fun K => F (fun i => f i K)))) := by
  set g : ℕ → (ι → X) := fun K i => f i K with hgdef
  have hgcompact : IsCompact (closure (Set.range g)) := by
    have hsub : closure (Set.range g) ⊆ Set.pi Set.univ (fun i => closure (Set.range (f i))) := by
      apply closure_minimal
      · rintro x ⟨K, rfl⟩
        intro i _
        exact subset_closure ⟨K, rfl⟩
      · exact isClosed_set_pi (fun i _ => isClosed_closure)
    exact IsCompact.of_isClosed_subset (isCompact_univ_pi hf) isClosed_closure hsub
  exact lp_compact_image g hgcompact F hF

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- On a probability measure, `L^q`-relative compactness (`p ≤ q`) transports down to
`L^p`-relative compactness of the same family: the natural inclusion `Lq ↪ Lp` is
`1`-Lipschitz by `eLpNorm_le_eLpNorm_of_exponent_le` (no `measure_univ` correction factor
needed, since it equals `1`), and continuous images of compact sets stay compact. -/
theorem isCompact_closure_range_mono_exponent [IsProbabilityMeasure μ]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q)
    {f : ℕ → α → ℝ} (hq : ∀ n, MemLp (f n) q μ)
    (hcompact : IsCompact (closure (Set.range (fun n => (hq n).toLp (f n))))) :
    IsCompact (closure (Set.range (fun n => ((hq n).mono_exponent hpq).toLp (f n)))) := by
  set ι : Lp ℝ q μ → Lp ℝ p μ := fun g =>
    ((Lp.memLp g).mono_exponent hpq).toLp (g : α → ℝ) with hιdef
  have hLip : LipschitzWith 1 ι := by
    refine LipschitzWith.of_edist_le fun g1 g2 => ?_
    rw [hιdef]
    simp only
    rw [Lp.edist_toLp_toLp, Lp.edist_def]
    exact eLpNorm_le_eLpNorm_of_exponent_le hpq
  have hrep : (fun n => ((hq n).mono_exponent hpq).toLp (f n)) =
      ι ∘ (fun n => (hq n).toLp (f n)) := by
    funext n
    show ((hq n).mono_exponent hpq).toLp (f n) = ι ((hq n).toLp (f n))
    rw [hιdef]
    exact (MemLp.toLp_congr ((Lp.memLp ((hq n).toLp (f n))).mono_exponent hpq)
      ((hq n).mono_exponent hpq) (hq n).coeFn_toLp).symm
  rw [hrep]
  exact lp_compact_image _ hcompact ι hLip.continuous

/-- A fixed linear combination of three already-`L¹`-relatively-compact real families is
again relatively compact, transported across an a.e. identity for the target function `F`
(the shape a polarization identity produces: one term at coefficient `1` or `2`, or a
`+`/`-` combination of two or three response values). -/
theorem isCompact_closure_range_combo3 (c1 c2 c3 : ℝ)
    {F G1 G2 G3 : ℕ → α → ℝ}
    (hmem1 : ∀ K, MemLp (G1 K) 1 μ) (hmem2 : ∀ K, MemLp (G2 K) 1 μ) (hmem3 : ∀ K, MemLp (G3 K) 1 μ)
    (hc1 : IsCompact (closure (Set.range (fun K => (hmem1 K).toLp (G1 K)))))
    (hc2 : IsCompact (closure (Set.range (fun K => (hmem2 K).toLp (G2 K)))))
    (hc3 : IsCompact (closure (Set.range (fun K => (hmem3 K).toLp (G3 K)))))
    (heq : ∀ K, F K =ᵐ[μ] (fun omega => c1 * G1 K omega + (c2 * G2 K omega + c3 * G3 K omega))) :
    ∃ hmemF : ∀ K, MemLp (F K) 1 μ,
      IsCompact (closure (Set.range (fun K => (hmemF K).toLp (F K)))) := by
  have hmemF : ∀ K, MemLp (F K) 1 μ := fun K =>
    (((hmem1 K).const_smul c1).add ((hmem2 K).const_smul c2 |>.add ((hmem3 K).const_smul c3))).ae_eq
      (heq K).symm
  refine ⟨hmemF, ?_⟩
  set f1 : ℕ → Lp ℝ 1 μ := fun K => (hmem1 K).toLp (G1 K) with hf1def
  set f2 : ℕ → Lp ℝ 1 μ := fun K => (hmem2 K).toLp (G2 K) with hf2def
  set f3 : ℕ → Lp ℝ 1 μ := fun K => (hmem3 K).toLp (G3 K) with hf3def
  have hz1 : IsCompact (closure (Set.range (fun K => c2 • f2 K + c3 • f3 K))) :=
    lp_compact_image (fun K => (f2 K, f3 K))
      (by
        have hprod : IsCompact (closure (Set.range f2) ×ˢ closure (Set.range f3)) := hc2.prod hc3
        have hsub : closure (Set.range (fun K => (f2 K, f3 K))) ⊆
            closure (Set.range f2) ×ˢ closure (Set.range f3) := by
          apply closure_minimal
          · rintro x ⟨K, rfl⟩
            exact ⟨subset_closure ⟨K, rfl⟩, subset_closure ⟨K, rfl⟩⟩
          · exact hprod.isClosed
        exact IsCompact.of_isClosed_subset hprod isClosed_closure hsub)
      (fun p => c2 • p.1 + c3 • p.2)
      (((continuous_const_smul c2).comp continuous_fst).add ((continuous_const_smul c3).comp continuous_snd))
  have hz2 : IsCompact (closure (Set.range (fun K => c1 • f1 K + (c2 • f2 K + c3 • f3 K)))) :=
    lp_compact_image (fun K => (f1 K, c2 • f2 K + c3 • f3 K))
      (by
        have hprod : IsCompact
            (closure (Set.range f1) ×ˢ closure (Set.range (fun K => c2 • f2 K + c3 • f3 K))) :=
          hc1.prod hz1
        have hsub : closure (Set.range (fun K => (f1 K, c2 • f2 K + c3 • f3 K))) ⊆
            closure (Set.range f1) ×ˢ closure (Set.range (fun K => c2 • f2 K + c3 • f3 K)) := by
          apply closure_minimal
          · rintro x ⟨K, rfl⟩
            exact ⟨subset_closure ⟨K, rfl⟩, subset_closure ⟨K, rfl⟩⟩
          · exact hprod.isClosed
        exact IsCompact.of_isClosed_subset hprod isClosed_closure hsub)
      (fun p => c1 • p.1 + p.2)
      ((continuous_const_smul c1).comp continuous_fst |>.add continuous_snd)
  have hrep : (fun K => (hmemF K).toLp (F K)) = (fun K => c1 • f1 K + (c2 • f2 K + c3 • f3 K)) := by
    funext K
    apply Lp.ext
    have e1 : ⇑(f1 K) =ᵐ[μ] G1 K := (hmem1 K).coeFn_toLp
    have e2 : ⇑(f2 K) =ᵐ[μ] G2 K := (hmem2 K).coeFn_toLp
    have e3 : ⇑(f3 K) =ᵐ[μ] G3 K := (hmem3 K).coeFn_toLp
    have el : ⇑(c1 • f1 K + (c2 • f2 K + c3 • f3 K)) =ᵐ[μ]
        (fun omega => c1 * (f1 K omega) + (c2 * (f2 K omega) + c3 * (f3 K omega))) := by
      filter_upwards [Lp.coeFn_add (c1 • f1 K) (c2 • f2 K + c3 • f3 K),
        Lp.coeFn_add (c2 • f2 K) (c3 • f3 K), Lp.coeFn_smul c1 (f1 K),
        Lp.coeFn_smul c2 (f2 K), Lp.coeFn_smul c3 (f3 K)] with omega h1 h2 h3 h4 h5
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 h5
      rw [h1, h3, h2, h4, h5]
    have er : (fun omega => c1 * (f1 K omega) + (c2 * (f2 K omega) + c3 * (f3 K omega))) =ᵐ[μ]
        (fun omega => c1 * G1 K omega + (c2 * G2 K omega + c3 * G3 K omega)) := by
      filter_upwards [e1, e2, e3] with omega h1 h2 h3
      rw [h1, h2, h3]
    have hF := (hmemF K).coeFn_toLp
    exact hF.trans ((heq K).trans (el.trans er).symm)
  rw [hrep]
  exact hz2

end
