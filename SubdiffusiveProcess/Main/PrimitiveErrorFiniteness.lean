module

public import SubdiffusiveProcess.Main.PrimitiveScores
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CutoffEllipticity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.AccumulatedErrorMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

@[expose] public section

/-! This file establishes a.e. finiteness of the complete `primitiveErrorScore`, for a fixed
`(k, z)`. Three of its four summands (the matched-response term, the shell-block term, and the
shell-zero term) are surely finite (for every `omega`, not merely a.e.): the first by a finite
range and the algebraic cap `min _ 1 ≤ 1`, the other two by compactness of `translatedCube`
together with the continuity of `shellBlock`/`omega 0`. Only the fourth (gradient-tail) summand
needs genuine probability content, bridged from the frozen GMC library's real-valued
gradient-tail summability (`ae_summable_translatedCube_gradient_tail`,
`SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge`) into the `ℝ≥0∞`-valued `primitiveNormOn`
formulation used by `SubdiffusiveProcess.Main.PrimitiveScores`.

It does NOT establish the `hFiniteScoreGuard`-shaped statement consumed by `lem_goodext` (that
needs this fixed-`(k,z)` fact quantified over all `(N, U, D, code, j)` via a countable a.e.
intersection, plus transport through `eta`). -/
open Set SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace SubdiffusiveProcess

/-- On a nonempty set with a bounded-above nonnegative test function, the extended-valued
`primitiveNormOn` sup agrees with the real-valued sup cast through `ENNReal.ofReal`. -/
theorem aux_bridge_primitiveNormOn_eq_ofReal_vectorSupNormOn {d : ℕ}
    (S : Set (Vec d)) (g : Vec d → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hne : S.Nonempty) (hbdd : BddAbove {r : ℝ | ∃ x ∈ S, r = g x}) :
    primitiveNormOn S g = ENNReal.ofReal (sSup {r : ℝ | ∃ x ∈ S, r = g x}) := by
  set T : Set ℝ := {r : ℝ | ∃ x ∈ S, r = g x} with hT
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨g x, x, hx, rfl⟩
  have gc : GaloisConnection Real.toNNReal ((↑) : ℝ≥0 → ℝ) :=
    fun r p => Real.toNNReal_le_iff_le_coe
  have hmono : Monotone Real.toNNReal := fun a b h => Real.toNNReal_mono h
  have hbddN : BddAbove (Real.toNNReal '' T) := hmono.map_bddAbove hbdd
  have hkey : Real.toNNReal (sSup T) = sSup (Real.toNNReal '' T) :=
    gc.l_csSup' hTne hbdd
  have hofReal : primitiveNormOn S g
      = sSup ((fun r => (ENNReal.ofReal r)) '' T) := by
    unfold primitiveNormOn
    congr 1
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g x, ⟨x, hx, rfl⟩, by rw [abs_of_nonneg (hg x)]⟩
    · rintro ⟨r, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by rw [abs_of_nonneg (hg x)]⟩
  rw [hofReal]
  have heq : ((fun r => ENNReal.ofReal r) '' T)
      = ((↑) : ℝ≥0 → ℝ≥0∞) '' (Real.toNNReal '' T) := by
    rw [Set.image_image]; rfl
  rw [heq, sSup_image, ← ENNReal.coe_sSup hbddN, ← hkey]
  rfl

/-- The gradient-tail term of `primitiveErrorScore` is a.e. finite: the frozen GMC library
already proves the underlying real gradient-sup-norm tail is a.e. summable
(`ae_summable_translatedCube_gradient_tail`), so this is a bridging consequence, not a new
analytic estimate. -/
theorem ae_primitiveErrorScore_gradientTail_ne_top {d : ℕ} [NeZero d]
    (M : GMCModel d) (k : ℕ) (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑' j : ℕ, if k ≤ j then
        ENNReal.ofReal ((3 : ℝ) ^ k) *
          primitiveNormOn (translatedCube d (k : ℤ) z)
            (fun x => euclideanNorm (shellGradient (omega j) x))
        else 0) ≠ ⊤ := by
  filter_upwards [ae_summable_translatedCube_gradient_tail M k z] with omega hsum
  set F : ℕ → ℝ := fun j => if k ≤ j then
      (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z) (shellGradient (omega j))
    else 0 with hF
  have hFnn : ∀ j, 0 ≤ F j := by
    intro j
    dsimp only [F]
    split_ifs with h
    · exact mul_nonneg (by positivity)
        (vectorSupNormOn_shellGradient_nonneg j k h z omega)
    · exact le_refl 0
  have hcoeEq : (fun j => ((F j).toNNReal : ℝ)) = F :=
    funext fun j => (Real.coe_toNNReal' (F j)).trans (max_eq_left (hFnn j))
  have hSummableNN : Summable (fun j => (F j).toNNReal) := by
    apply NNReal.summable_coe.mp
    rw [hcoeEq]
    exact hsum
  have hterm_eq : (fun j : ℕ => if k ≤ j then
      ENNReal.ofReal ((3 : ℝ) ^ k) *
        primitiveNormOn (translatedCube d (k : ℤ) z)
          (fun x => euclideanNorm (shellGradient (omega j) x))
      else 0) = (fun j => ((F j).toNNReal : ℝ≥0∞)) := by
    funext j
    dsimp only [F]
    split_ifs with h
    · have hne : (translatedCube d (k : ℤ) z).Nonempty := ⟨z + 0, 0, zero_mem_cube d (k : ℤ), rfl⟩
      have hsub : translatedCube d (k : ℤ) z ⊆ (fun x => z + x) '' closure (cube d (k : ℤ)) :=
        Set.image_mono subset_closure
      have hcompact : IsCompact ((fun x => z + x) '' closure (cube d (k : ℤ))) :=
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.isCompact_closure_cube d (k : ℤ)).image
          (continuous_const.add continuous_id)
      have hcontOnJ : Continuous (fun x => euclideanNorm (shellGradient (omega j) x)) :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.comp
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellGradient (omega j))
      have hbig : BddAbove ((fun x => euclideanNorm (shellGradient (omega j) x)) ''
          ((fun x => z + x) '' closure (cube d (k : ℤ)))) :=
        (hcompact.image hcontOnJ).bddAbove
      have hbdd : BddAbove {r : ℝ | ∃ x ∈ translatedCube d (k : ℤ) z,
          r = euclideanNorm (shellGradient (omega j) x)} := by
        apply hbig.mono
        rintro r ⟨x, hx, rfl⟩
        exact ⟨x, hsub hx, rfl⟩
      rw [aux_bridge_primitiveNormOn_eq_ofReal_vectorSupNormOn
          (translatedCube d (k : ℤ) z) (fun x => euclideanNorm (shellGradient (omega j) x))
          (fun x => euclideanNorm_nonneg _) hne hbdd,
        ← ENNReal.ofReal_mul (by positivity)]
      rfl
    · simp
  rw [hterm_eq, ENNReal.tsum_coe_ne_top_iff_summable]
  exact hSummableNN

/-- On any translated cube, `primitiveNormOn` of a continuous test function is finite, for
every sample (not merely a.e.): the cube sits inside a compact set, and a continuous function's
image on a compact set is bounded. -/
theorem aux_primitiveNormOn_translatedCube_ne_top_of_continuous {d : ℕ} (k : ℤ) (z : Vec d)
    (f : Vec d → ℝ) (hf : Continuous f) :
    primitiveNormOn (translatedCube d k z) f ≠ ⊤ := by
  have hne : (translatedCube d k z).Nonempty := ⟨z + 0, 0, zero_mem_cube d k, rfl⟩
  have hsub : translatedCube d k z ⊆ (fun x => z + x) '' closure (cube d k) :=
    Set.image_mono subset_closure
  have hcompact : IsCompact ((fun x => z + x) '' closure (cube d k)) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.isCompact_closure_cube d k).image
      (continuous_const.add continuous_id)
  have hcont : Continuous (fun x => |f x|) := hf.abs
  have hbig : BddAbove ((fun x => |f x|) '' ((fun x => z + x) '' closure (cube d k))) :=
    (hcompact.image hcont).bddAbove
  have hbdd : BddAbove {r : ℝ | ∃ x ∈ translatedCube d k z, r = |f x|} := by
    apply hbig.mono
    rintro r ⟨x, hx, rfl⟩
    exact ⟨x, hsub hx, rfl⟩
  have hg : ∀ x, (0 : ℝ) ≤ |f x| := fun x => abs_nonneg _
  rw [show primitiveNormOn (translatedCube d k z) f
      = primitiveNormOn (translatedCube d k z) (fun x => |f x|) by
    unfold primitiveNormOn; congr 1; ext v; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [abs_abs]⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [abs_abs]⟩,
    aux_bridge_primitiveNormOn_eq_ofReal_vectorSupNormOn (translatedCube d k z)
      (fun x => |f x|) hg hne hbdd]
  exact ENNReal.ofReal_ne_top

/-- The matched-response summand of `primitiveErrorScore` is surely finite: its second factor is
capped at `1` by `min _ 1`, and its first factor ranges over a finite set of exponents (indexed
by `l ≤ k`). -/
theorem aux_primitiveErrorScore_term1_ne_top {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ) (omega : PotentialSample d) (k : ℕ) (z : Vec d) :
    (sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
        (min (primitiveResponseDefect M omega l x) 1) ^ (1 / 2 : ℝ)}) ≠ ⊤ := by
  have hle : (sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
        (min (primitiveResponseDefect M omega l x) 1) ^ (1 / 2 : ℝ)})
      ≤ ∑ l ∈ Finset.range (k + 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) := by
    apply sSup_le
    rintro v ⟨j, l, hjk, hlk, hlj, x, hgrid, hcube, rfl⟩
    have h1 : (min (primitiveResponseDefect M omega l x) 1) ^ (1 / 2 : ℝ) ≤ 1 :=
      ENNReal.rpow_le_one (min_le_right _ _) (by norm_num)
    calc ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
          (min (primitiveResponseDefect M omega l x) 1) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) * 1 := by gcongr
      _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) := mul_one _
      _ ≤ ∑ l' ∈ Finset.range (k + 1),
            ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l' : ℝ)))) :=
          Finset.single_le_sum (f := fun l' : ℕ =>
              ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l' : ℝ)))))
            (fun i _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hlk))
  have hfin : (∑ l ∈ Finset.range (k + 1),
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))))) ≠ ⊤ :=
    (ENNReal.sum_ne_top.mpr fun l _ => ENNReal.ofReal_ne_top)
  exact ne_top_of_le_ne_top hfin hle

/-- The shell-block summand of `primitiveErrorScore` is surely finite: a finite (`j ≤ k`) max of
`primitiveNormOn`-of-a-continuous-function terms, each finite by
`aux_primitiveNormOn_translatedCube_ne_top_of_continuous`. -/
theorem aux_primitiveErrorScore_term2_ne_top {d : ℕ} [NeZero d]
    (s : ℝ) (omega : PotentialSample d) (k : ℕ) (z : Vec d) :
    (sSup {v : ℝ≥0∞ | ∃ j : ℕ, j ≤ k ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
        primitiveNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)}) ≠ ⊤ := by
  have hle : (sSup {v : ℝ≥0∞ | ∃ j : ℕ, j ≤ k ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
        primitiveNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)})
      ≤ ∑ j ∈ Finset.range (k + 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
            primitiveNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega) := by
    apply sSup_le
    rintro v ⟨j, hjk, rfl⟩
    exact Finset.single_le_sum (f := fun j' : ℕ =>
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j' : ℝ)))) *
          primitiveNormOn (translatedCube d (k : ℤ) z) (shellBlock k j' omega))
      (fun i _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hjk))
  have hfin : (∑ j ∈ Finset.range (k + 1),
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
        primitiveNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro j _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (aux_primitiveNormOn_translatedCube_ne_top_of_continuous (k : ℤ) z (shellBlock k j omega)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellBlock k j omega))
  exact ne_top_of_le_ne_top hfin hle

/-- The shell-zero summand of `primitiveErrorScore` is surely finite: `omega 0` is continuous
(every `PotentialField` coordinate is `C¹`), so `aux_primitiveNormOn_translatedCube_ne_top_of_continuous`
applies directly. -/
theorem aux_primitiveErrorScore_term3_ne_top {d : ℕ} [NeZero d]
    (s : ℝ) (omega : PotentialSample d) (k : ℕ) (z : Vec d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
      primitiveNormOn (translatedCube d (k : ℤ) z) (omega 0) ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (aux_primitiveNormOn_translatedCube_ne_top_of_continuous (k : ℤ) z (omega 0)
      (_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one (omega 0)).continuous)

/-- The complete `primitiveErrorScore` is a.e. finite, for a fixed `(k, z)`: three of its four
summands are surely finite (`aux_primitiveErrorScore_term1_ne_top`,
`aux_primitiveErrorScore_term2_ne_top`, `aux_primitiveErrorScore_term3_ne_top`), and the fourth
is a.e. finite by `ae_primitiveErrorScore_gradientTail_ne_top`. -/
theorem ae_primitiveErrorScore_ne_top {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ) (k : ℕ) (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, primitiveErrorScore M s omega k z ≠ ⊤ := by
  filter_upwards [ae_primitiveErrorScore_gradientTail_ne_top M k z] with omega hterm4
  unfold primitiveErrorScore
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨aux_primitiveErrorScore_term1_ne_top M s omega k z,
     aux_primitiveErrorScore_term2_ne_top s omega k z⟩,
    aux_primitiveErrorScore_term3_ne_top s omega k z⟩, hterm4⟩

end SubdiffusiveProcess
