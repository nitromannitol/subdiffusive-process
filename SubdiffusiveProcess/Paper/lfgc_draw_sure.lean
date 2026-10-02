import SubdiffusiveProcess.Paper.lfgc_layer_tail
import SubdiffusiveProcess.Paper.primitive_scores_finite

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# The drift score is finite at every centre on one full-measure event

The drift formula of `primitive_scores` at `(k, z)` is bounded by the finite first three
terms and by the gradient majorant series at `(k + 1, z')` for the integer point `z'` nearest
to `z` (the cube of side `3^k` about `z` lies in the cube of side `3^{k+1}` about `z'`).
Hence finiteness of countably many majorant series (every cutoff, level and integer centre),
which holds almost surely, makes every drift score finite at every real centre.
-/

open MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ}

theorem aux_lfgc_draw_sure_translatedCube_subset_succ (k : ℕ) (z z' : Vec d) (hz : ∀ i, |z i - z' i| ≤ 1 / 2) :
    translatedCube d (k : ℤ) z ⊆ translatedCube d ((k + 1 : ℕ) : ℤ) z' := by
  intro x hx
  rw [Paper.aux_psf_mem_translatedCube_iff] at hx ⊢
  intro i
  have h1 := hx i
  have h2 := hz i
  rw [zpow_natCast] at h1 ⊢
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h4 : |x i - z' i| ≤ |x i - z i| + |z i - z' i| := by
    have := abs_add_le (x i - z i) (z i - z' i)
    rwa [sub_add_sub_cancel] at this
  rw [pow_succ]
  linarith

/-- Termwise bound of the gradient tail by the majorant at the next level. -/
theorem aux_lfgc_draw_sure_dterm4_term_le (k : ℕ) (z z' : Vec d) (hz : ∀ i, |z i - z' i| ≤ 1 / 2)
    (g : PotentialSample d) (j : ℕ) :
    (if k ≤ j then
        ENNReal.ofReal ((3 : ℝ) ^ k) *
          sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k : ℤ) z,
            w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g j) x)|}
      else 0) ≤
      (if j = k then ENNReal.ofReal (Paper.aux_psf_maxObs k (k + 1) z' g) else 0) +
        Paper.aux_psf_Dmaj4 (k + 1) z' j g := by
  by_cases hkj : k ≤ j
  · rw [if_pos hkj]
    have hb : sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k : ℤ) z,
        w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g j) x)|} ≤
        ENNReal.ofReal (((3 : ℝ) ^ j)⁻¹ * Paper.aux_psf_maxObs j (k + 1) z' g) := by
      refine Paper.aux_psf_normOn_le_of_le k z _ _ ?_
      intro x hx
      have hnn : (0 : ℝ) ≤ Homogenization.euclideanNorm (shellGradient (g j) x) :=
        Real.sqrt_nonneg _
      rw [abs_of_nonneg hnn]
      exact Paper.aux_psf_grad_le_maxObs j (k + 1) z' x g (aux_lfgc_draw_sure_translatedCube_subset_succ k z z' hz hx)
    have hc : (0 : ℝ) ≤ (3 : ℝ) ^ k := by positivity
    have hm := Paper.aux_psf_maxObs_nonneg j (k + 1) z' g
    have hstep : ENNReal.ofReal ((3 : ℝ) ^ k) *
        sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k : ℤ) z,
          w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g j) x)|} ≤
        ENNReal.ofReal ((3 : ℝ) ^ k * (((3 : ℝ) ^ j)⁻¹ * Paper.aux_psf_maxObs j (k + 1) z' g)) := by
      rw [ENNReal.ofReal_mul hc]
      gcongr
    refine hstep.trans ?_
    rcases eq_or_lt_of_le hkj with hjk | hjk
    · subst hjk
      rw [if_pos rfl]
      refine le_trans (le_of_eq ?_) le_self_add
      congr 1
      field_simp
    · rw [if_neg (Nat.ne_of_gt hjk), zero_add]
      unfold Paper.aux_psf_Dmaj4
      rw [if_pos (Nat.succ_le_of_lt hjk)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hj0 : (0 : ℝ) ≤ ((3 : ℝ) ^ j)⁻¹ := by positivity
      rw [pow_succ]
      nlinarith [mul_nonneg hj0 hm]
  · rw [if_neg hkj]
    exact zero_le _

theorem aux_lfgc_draw_sure_dterm4_le (k : ℕ) (z z' : Vec d) (hz : ∀ i, |z i - z' i| ≤ 1 / 2)
    (g : PotentialSample d) :
    (∑' j : ℕ, if k ≤ j then
        ENNReal.ofReal ((3 : ℝ) ^ k) *
          sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k : ℤ) z,
            w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g j) x)|}
      else 0) ≤
      ENNReal.ofReal (Paper.aux_psf_maxObs k (k + 1) z' g) +
        ∑' j : ℕ, Paper.aux_psf_Dmaj4 (k + 1) z' j g := by
  calc _ ≤ ∑' j : ℕ, ((if j = k then ENNReal.ofReal (Paper.aux_psf_maxObs k (k + 1) z' g)
          else 0) + Paper.aux_psf_Dmaj4 (k + 1) z' j g) :=
        ENNReal.tsum_le_tsum (aux_lfgc_draw_sure_dterm4_term_le k z z' hz g)
    _ = _ := by rw [ENNReal.tsum_add, tsum_ite_eq]

/-- The drift formula is finite once the next-level majorant series at a nearby point is. -/
theorem aux_lfgc_draw_sure_dsc_ne_top_of_near (M : GMCModel d) (s : ℝ) (hs0 : 0 < s) (k : ℕ) (z z' : Vec d)
    (hz : ∀ i, |z i - z' i| ≤ 1 / 2) (g : PotentialSample d)
    (hfin : (∑' j : ℕ, Paper.aux_psf_Dmaj4 (k + 1) z' j g) ≠ ⊤) :
    (sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d (j:ℤ) \ cube d ((j:ℤ) - 1) ∧
          v = ENNReal.ofReal ((3:ℝ) ^ (-(s / 2) * ((k:ℝ) - (l:ℝ)))) *
            (min (Paper.aux_psf_Jval M l g x) 1) ^ (1/2 : ℝ)} +
        sSup {v : ℝ≥0∞ | ∃ j : ℕ, j ≤ k ∧
          v = ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * ((k:ℝ) - (j:ℝ)))) *
            sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
              w = ENNReal.ofReal |shellBlock k j g x|}} +
        ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * (k:ℝ))) *
          sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
            w = ENNReal.ofReal |g 0 x|} +
        ∑' j : ℕ, if k ≤ j then
          ENNReal.ofReal ((3:ℝ) ^ k) *
            sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
              w = ENNReal.ofReal
                |Homogenization.euclideanNorm (shellGradient (g j) x)|}
        else 0) ≠ ⊤ := by
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (Paper.aux_psf_Dterm1_le_one M s hs0 k z g)
  · exact ne_top_of_le_ne_top (Paper.aux_psf_Dmaj2_ne_top s k z g)
      (Paper.aux_psf_Dterm2_le s k z g)
  · exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (Paper.aux_psf_Dterm3_le s k z g)
  · exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hfin⟩)
      (aux_lfgc_draw_sure_dterm4_le k z z' hz g)

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Almost surely every next-level majorant series at an integer centre is finite. -/
theorem lfgc_draw_sure (M : GMCModel d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N k : ℕ) (z' : Fin d → ℤ),
      (∑' j : ℕ, Paper.aux_psf_Dmaj4 (k + 1) (fun i => (z' i : ℝ)) j (aux_lfgc_layer_tail_canonEta N omega)) ≠ ⊤ := by
  rw [ae_all_iff]
  intro N
  rw [ae_all_iff]
  intro k
  rw [ae_all_iff]
  intro z'
  have h := Paper.aux_psf_Dmaj4_tsum_ae M (k + 1) (fun i => (z' i : ℝ))
  rw [← aux_lfgc_layer_tail_map_canonEta M N] at h
  exact ae_of_ae_map (aux_lfgc_layer_tail_measurable_canonEta N).aemeasurable h

end Paper
