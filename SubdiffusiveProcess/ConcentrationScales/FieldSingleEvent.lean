module

public import SubdiffusiveProcess.ConcentrationScales.FieldMoments

@[expose] public section

/-!
# The single exceedance event of `p.concentration.for.scales.exp.field`

For `k ∈ ℤ`, `j, h ∈ ℕ` and a level `t`, the event that
`ess sup_{x ∈ cube (k+h+j)} ∏_{i=k-j}^{k+j} exp|X_i(x)| > exp t`
is (up to a null set) contained in an event `E` which is measurable for `σ(X_i : |i-k| ≤ j)` and has probability at most
`3^{d(h+2j)} · 2^{2j+1} · exp(-λ t + (2j+1) λ²δ²/4)`.
-/

namespace SubdiffusiveProcess.ConcentrationScales

open MeasureTheory ProbabilityTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

section Single

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Deterministic cover step: if every index cell of the cover has small product of cell suprema, the
essential supremum over the centered cube is small. -/
theorem essSup_prod_exp_le (n : ℤ) (m : ℕ) (I : Finset ℤ) (hnI : ∀ i ∈ I, n ≤ i)
    (x : ℤ → Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (t : ℝ)
    (hbox : ∀ u ∈ idxBox d m,
      ∏ i ∈ I, essSup (fun y => ENNReal.ofReal (Real.exp (lam * |x i y|)))
        (volume.restrict (cell d i (parentIdx d n i u))) ≤ ENNReal.ofReal (Real.exp (lam * t))) :
    essSup (fun y => ENNReal.ofReal (∏ i ∈ I, Real.exp |x i y|)) (volume.restrict (cube d (n + m))) ≤
      ENNReal.ofReal (Real.exp t) := by
  refine essSup_le_of_ae_le _ ?_
  refine ae_restrict_of_ae_restrict_of_subset (cube_subset_iUnion_cell d n m) ?_
  rw [ae_restrict_biUnion_finset_iff]
  intro u hu
  have hi : ∀ i ∈ I, ∀ᵐ y ∂(volume.restrict (cell d n u)),
      ENNReal.ofReal (Real.exp (lam * |x i y|)) ≤
        essSup (fun y => ENNReal.ofReal (Real.exp (lam * |x i y|)))
          (volume.restrict (cell d i (parentIdx d n i u))) := fun i hi =>
    ae_restrict_of_ae_restrict_of_subset (cell_subset_parent (hnI i hi) u)
      (ENNReal.ae_le_essSup _)
  have hall := (Filter.eventually_all_finset I).mpr hi
  filter_upwards [hall] with y hy
  have h1 : ∏ i ∈ I, ENNReal.ofReal (Real.exp (lam * |x i y|)) ≤ ENNReal.ofReal (Real.exp (lam * t)) :=
    (Finset.prod_le_prod hy).trans (hbox u hu)
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg _), ← Real.exp_sum] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h1
  have h3 : ∑ i ∈ I, lam * |x i y| ≤ lam * t := Real.exp_le_exp.mp h2
  rw [← Finset.mul_sum] at h3
  have h4 : ∑ i ∈ I, |x i y| ≤ t := le_of_mul_le_mul_left h3 hlam
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_sum]
  exact Real.exp_le_exp.mpr h4


theorem sum_bound_eq (d h j : ℕ) (lam δ t : ℝ) :
    (((3 ^ (h + 2 * j)) ^ d : ℕ) : ℝ≥0∞) *
        ((ENNReal.ofReal (Real.exp (lam * t)))⁻¹ *
          (ENNReal.ofReal (Real.exp (lam ^ 2 * δ ^ 2 / 4)) * 2) ^ (2 * j + 1)) =
      ENNReal.ofReal (Real.exp (d * (h + 2 * j) * Real.log 3 +
        (2 * j + 1) * (Real.log 2 + lam ^ 2 * δ ^ 2 / 4) - lam * t)) := by
  have h1 : (ENNReal.ofReal (Real.exp (lam * t)))⁻¹ = ENNReal.ofReal (Real.exp (-(lam * t))) := by
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), Real.exp_neg]
  have h2 : ENNReal.ofReal (Real.exp (lam ^ 2 * δ ^ 2 / 4)) * 2 =
      ENNReal.ofReal (Real.exp (lam ^ 2 * δ ^ 2 / 4) * 2) := by
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
    simp
  have h3 : ((((3 ^ (h + 2 * j)) ^ d : ℕ) : ℝ≥0∞)) =
      ENNReal.ofReal ((((3 ^ (h + 2 * j)) ^ d : ℕ) : ℝ)) := (ENNReal.ofReal_natCast _).symm
  rw [h1, h2, h3, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hA : ((((3 ^ (h + 2 * j)) ^ d : ℕ) : ℝ)) = Real.exp (d * (h + 2 * j) * Real.log 3) := by
    have : (d : ℝ) * (h + 2 * j) * Real.log 3 = (((h + 2 * j) * d : ℕ) : ℝ) * Real.log 3 := by
      push_cast; ring
    rw [this, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    push_cast
    ring
  have hB : (Real.exp (lam ^ 2 * δ ^ 2 / 4) * 2) ^ (2 * j + 1) =
      Real.exp ((2 * j + 1) * (Real.log 2 + lam ^ 2 * δ ^ 2 / 4)) := by
    have : ((2 : ℝ) * j + 1) * (Real.log 2 + lam ^ 2 * δ ^ 2 / 4) =
        ((2 * j + 1 : ℕ) : ℝ) * (Real.log 2 + lam ^ 2 * δ ^ 2 / 4) := by push_cast; ring
    rw [this, Real.exp_nat_mul, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm]
  rw [hA, hB, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem exists_local_event {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℤ → Ω → Vec d → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hXm : ∀ i, Measurable fun p : Ω × Vec d => X i p.1 p.2) (hind : iIndepFun X μ)
    (hstat : ∀ (i : ℤ) (z : Vec d), (∀ a : Fin d, ∃ n : ℤ, z a = (3 : ℝ) ^ i * n) →
      μ.map (fun ω x => X i ω (x + z)) = μ.map (X i))
    (hΓ : ∀ i, ∫⁻ ω, essSup (fun x => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X i ω x|) ^ 2)))
      (volume.restrict (cube d i)) ∂μ ≤ 2)
    (k : ℤ) (j h : ℕ) (t lam : ℝ) (hlam : 0 < lam) :
    ∃ E : Set Ω,
      MeasurableSet[⨆ i ∈ Set.Icc (k - (j : ℤ)) (k + (j : ℤ)),
        MeasurableSpace.comap (X i) inferInstance] E ∧
      (∀ᵐ ω ∂μ, ENNReal.ofReal (Real.exp t) <
          essSup (fun x => ENNReal.ofReal (∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |X i ω x|))
            (volume.restrict (cube d (k + h + j))) → ω ∈ E) ∧
      μ E ≤ ENNReal.ofReal (Real.exp (d * (h + 2 * j) * Real.log 3 +
        (2 * j + 1) * (Real.log 2 + lam ^ 2 * δ ^ 2 / 4) - lam * t)) := by
  classical
  set n : ℤ := k - j with hn
  set m : ℕ := h + 2 * j with hm
  set I : Finset ℤ := Finset.Icc (k - j) (k + j) with hI
  have hnI : ∀ i ∈ I, n ≤ i := fun i hi => (Finset.mem_Icc.mp hi).1
  have hcube : cube d (k + h + j) = cube d (n + m) := by
    congr 1
    simp only [hn, hm]
    push_cast
    ring
  have hXmeas : ∀ i, Measurable (X i) := fun i => measurable_field_of_uncurry (hXm i)
  have hrep : ∀ (u : Fin d → ℤ) (i : ℤ), ∃ ρ : (Vec d → ℝ) → ℝ≥0∞, Measurable ρ ∧
      ∀ᵐ ω ∂μ, essSup (fun y => ENNReal.ofReal (Real.exp (lam * |X i ω y|)))
        (volume.restrict (cell d i (parentIdx d n i u))) = ρ (X i ω) := fun u i =>
    exists_measurable_functional_ae_eq_essSup (μ := μ)
      (ν := volume.restrict (cell d i (parentIdx d n i u))) (Y := X i) (hXm i)
      (G := fun s => ENNReal.ofReal (Real.exp (lam * |s|))) (by fun_prop)
  choose ρ hρm hρae using hrep
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam * t)) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  set B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam ^ 2 * δ ^ 2 / 4)) * 2 with hB
  refine ⟨⋃ u ∈ idxBox d m, {ω | c < ∏ i ∈ I, ρ u i (X i ω)}, ?_, ?_, ?_⟩
  · have hcomap : ∀ i, Measurable[MeasurableSpace.comap (X i) inferInstance] (X i) :=
      fun i => comap_measurable (X i)
    have hfi : ∀ u i, i ∈ Set.Icc (k - (j : ℤ)) (k + (j : ℤ)) →
        Measurable[⨆ i ∈ Set.Icc (k - (j : ℤ)) (k + (j : ℤ)),
          MeasurableSpace.comap (X i) inferInstance] (fun ω => ρ u i (X i ω)) := by
      intro u i hi
      have h1 : Measurable[MeasurableSpace.comap (X i) inferInstance] (fun ω => ρ u i (X i ω)) :=
        (hρm u i).comp (hcomap i)
      exact h1.mono (le_iSup₂ (f := fun i (_ : i ∈ Set.Icc (k - (j : ℤ)) (k + (j : ℤ))) =>
        MeasurableSpace.comap (X i) inferInstance) i hi) le_rfl
    refine Finset.measurableSet_biUnion _ fun u _ => ?_
    refine measurableSet_lt measurable_const ?_
    exact Finset.measurable_prod I fun i hi => hfi u i (by simpa [hI] using hi)
  · have hall : ∀ᵐ ω ∂μ, ∀ u ∈ idxBox d m, ∀ i ∈ I,
        essSup (fun y => ENNReal.ofReal (Real.exp (lam * |X i ω y|)))
          (volume.restrict (cell d i (parentIdx d n i u))) = ρ u i (X i ω) :=
      (Filter.eventually_all_finset (idxBox d m)).mpr fun u _ =>
        (Filter.eventually_all_finset I).mpr fun i _ => hρae u i
    filter_upwards [hall] with ω hω hlt
    by_contra hE
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hE
    have hbox : ∀ u ∈ idxBox d m,
        ∏ i ∈ I, essSup (fun y => ENNReal.ofReal (Real.exp (lam * |X i ω y|)))
          (volume.restrict (cell d i (parentIdx d n i u))) ≤ ENNReal.ofReal (Real.exp (lam * t)) := by
      intro u hu
      rw [Finset.prod_congr rfl (hω u hu)]
      exact hE u hu
    have := essSup_prod_exp_le (d := d) n m I hnI (fun i => X i ω) hlam t hbox
    rw [hcube] at hlt
    exact absurd hlt (not_lt.mpr this)
  · calc μ (⋃ u ∈ idxBox d m, {ω | c < ∏ i ∈ I, ρ u i (X i ω)})
        ≤ ∑ u ∈ idxBox d m, μ {ω | c < ∏ i ∈ I, ρ u i (X i ω)} := measure_biUnion_finset_le _ _
      _ ≤ ∑ u ∈ idxBox d m, c⁻¹ * B ^ I.card := by
          refine Finset.sum_le_sum fun u _ => ?_
          refine measure_lt_prod_le hXmeas hind I (ρ u) (hρm u) B ?_ hc0 hctop
          intro i hi
          have hstat' := hstat i (cellShift d i (parentIdx d n i u))
            (fun a => ⟨parentIdx d n i u a, by simp [cellShift]⟩)
          calc ∫⁻ ω, ρ u i (X i ω) ∂μ
              = ∫⁻ ω, essSup (fun y => ENNReal.ofReal (Real.exp (lam * |X i ω y|)))
                (volume.restrict (cell d i (parentIdx d n i u))) ∂μ :=
                (lintegral_congr_ae (hρae u i)).symm
            _ ≤ B := lintegral_essSup_exp_cell_le hδ (hXm i) i _ hstat' (hΓ i) lam
      _ = ENNReal.ofReal (Real.exp (d * (h + 2 * j) * Real.log 3 +
            (2 * j + 1) * (Real.log 2 + lam ^ 2 * δ ^ 2 / 4) - lam * t)) := by
          rw [Finset.sum_const, card_idxBox, nsmul_eq_mul]
          have hcard : I.card = 2 * j + 1 := by
            simp only [hI, Int.card_Icc]
            omega
          rw [hcard, hm]
          exact sum_bound_eq d h j lam δ t

/-- The single exceedance event with the optimal Chernoff parameter `λ = 2t / ((2j+1) δ²)`. -/
theorem exists_local_event_gaussian {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℤ → Ω → Vec d → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hXm : ∀ i, Measurable fun p : Ω × Vec d => X i p.1 p.2) (hind : iIndepFun X μ)
    (hstat : ∀ (i : ℤ) (z : Vec d), (∀ a : Fin d, ∃ n : ℤ, z a = (3 : ℝ) ^ i * n) →
      μ.map (fun ω x => X i ω (x + z)) = μ.map (X i))
    (hΓ : ∀ i, ∫⁻ ω, essSup (fun x => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X i ω x|) ^ 2)))
      (volume.restrict (cube d i)) ∂μ ≤ 2)
    (k : ℤ) (j h : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ E : Set Ω,
      MeasurableSet[⨆ i ∈ Set.Icc (k - (j : ℤ)) (k + (j : ℤ)),
        MeasurableSpace.comap (X i) inferInstance] E ∧
      (∀ᵐ ω ∂μ, ENNReal.ofReal (Real.exp t) <
          essSup (fun x => ENNReal.ofReal (∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |X i ω x|))
            (volume.restrict (cube d (k + h + j))) → ω ∈ E) ∧
      μ E ≤ ENNReal.ofReal (Real.exp (d * (h + 2 * j) * Real.log 3 + (2 * j + 1) * Real.log 2 -
        t ^ 2 / ((2 * j + 1) * δ ^ 2))) := by
  have hj : (0 : ℝ) < 2 * j + 1 := by positivity
  have hlam : 0 < 2 * t / ((2 * j + 1) * δ ^ 2) := by positivity
  obtain ⟨E, hE1, hE2, hE3⟩ :=
    exists_local_event hδ hXm hind hstat hΓ k j h t _ hlam
  refine ⟨E, hE1, hE2, hE3.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_eq ?_)))⟩
  field_simp
  ring

end Single

end

end SubdiffusiveProcess.ConcentrationScales
