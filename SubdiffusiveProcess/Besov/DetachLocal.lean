module

public import SubdiffusiveProcess.Besov.DetachTheta
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.OscillationPoincare

@[expose] public section

/-!
# Local multiscale Poincaré on an overlap cube (detach inequality)

For an overlap cube `S*` of the centre `S` (side `3^{S.scale+1}`, centre `cubeCenter S`) contained in the
domain of an `H¹` function `u`, the translate `x ↦ u (x + c_S)` is an `H¹` function on the origin-centred
triadic cube of scale `S.scale + 1`, and the Book's multiscale Poincaré estimate applies to it.
-/

open MeasureTheory
open Homogenization

namespace SubdiffusiveProcess.Besov.Detach

noncomputable section

theorem cubeSet_overlap_eq_translate {d : ℕ} (S : TriadicCube d) :
    ScalarOverlap.cubeSet S =
      translateSet (cubeCenter S) (cubeSet (originCube d (S.scale + 1))) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  have h3 : (3 : ℝ) ^ (S.scale + 1) = (3 : ℝ) ^ S.scale * 3 := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [ScalarOverlap.cubeSet, Homogenization.cubeSet, Set.mem_setOf_eq,
    Homogenization.cubeCenter, Homogenization.cubeScaleFactor, originCube,
    Pi.sub_apply, Pi.zero_apply, Int.cast_zero, h3]
  constructor
  · intro h i
    have hi := h i
    constructor <;> linarith
  · intro h i
    have hi := h i
    constructor <;> linarith

theorem openCubeSet_overlap_eq_translate {d : ℕ} (S : TriadicCube d) :
    ScalarOverlap.openCubeSet S =
      translateSet (cubeCenter S) (openCubeSet (originCube d (S.scale + 1))) := by
  ext x
  rw [Homogenization.mem_translateSet_iff_sub_mem]
  have hpow : (3 : ℝ) ^ (S.scale + 1) = (3 : ℝ) ^ S.scale * 3 := by
    rw [zpow_add_one₀ (show (3 : ℝ) ≠ 0 by norm_num)]
  simp only [Homogenization.ScalarOverlap.openCubeSet, Homogenization.openCubeSet, Set.mem_setOf_eq,
    Pi.sub_apply, Homogenization.cubeCenter, Homogenization.cubeScaleFactor, Homogenization.originCube,
    Pi.zero_apply, Int.cast_zero, zero_sub, hpow]
  constructor
  · intro h i
    have := h i
    constructor <;> nlinarith [this.1, this.2]
  · intro h i
    have := h i
    constructor <;> nlinarith [this.1, this.2]

theorem overlap_oscillation_eq {d : ℕ} (S : TriadicCube d) (u : Vec d → ℝ) :
    cubeBesovOverlapOscillation S 2 u =
      cubeBesovOscillation (originCube d (S.scale + 1)) 2 (fun x => u (x + cubeCenter S)) := by
  set c := cubeCenter S with hc
  set Q' := originCube d (S.scale + 1) with hQ'
  have hvol : ScalarOverlap.cubeVolume S = cubeVolume Q' := by
    unfold ScalarOverlap.cubeVolume ScalarOverlap.scaleFactor cubeVolume cubeScaleFactor
    simp only [hQ', originCube]
    rw [zpow_add_one₀ (by norm_num : (3:ℝ) ≠ 0)]
    ring
  have hme : MeasurableEmbedding (fun x : Vec d => x + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  have hmp : MeasurePreserving (fun x : Vec d => x + c) volume volume :=
    measurePreserving_add_right volume c
  have hB : ScalarOverlap.normalizedCubeMeasure S =
      Measure.map (fun x : Vec d => x + c) (normalizedCubeMeasure Q') := by
    unfold ScalarOverlap.normalizedCubeMeasure ScalarOverlap.cubeMeasure normalizedCubeMeasure cubeMeasure
    rw [Measure.map_smul _ (hme.measurable.aemeasurable), (hmp.restrict_image_emb hme (cubeSet Q')).map_eq,
      image_addRight_eq_translateSet, ← cubeSet_overlap_eq_translate, hvol]
  have hA : ScalarOverlap.cubeAverage S u = cubeAverage Q' (fun x => u (x + c)) := by
    rw [ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure, hB, hme.integral_map]
  unfold cubeBesovOverlapOscillation cubeBesovOscillation ScalarOverlap.cubeLpNorm cubeLpNorm
    cubeFluctuation
  rw [hB, hme.eLpNorm_map_measure, hA]
  rfl

theorem exists_translated_h1 {d : ℕ} {V : Set (Vec d)} (hV : IsOpen V) (u : H1Function V)
    (S : TriadicCube d) (hS : ScalarOverlap.openCubeSet S ⊆ V) :
    ∃ v : H1Function (openCubeSet (originCube d (S.scale + 1))),
      (∀ x, v.toFun x = u.toFun (x + cubeCenter S)) ∧
        (∀ x, v.grad x = u.grad (x + cubeCenter S)) := by
  let W : Set (Vec d) := translateSet (cubeCenter S) (openCubeSet (originCube d (S.scale + 1)))
  have hW_eq : W = ScalarOverlap.openCubeSet S := (openCubeSet_overlap_eq_translate S).symm
  have hWopen : IsOpen W := by rw [hW_eq]; exact ScalarOverlap.isOpen_openCubeSet S
  have hWV : W ⊆ V := by rw [hW_eq]; exact hS
  refine ⟨H1Function.untranslate (cubeCenter S) (u.restrict hWopen hWV), ?_, ?_⟩
  · intro x
    rw [H1Function.untranslate_toFun]
    rfl
  · intro x
    rw [H1Function.untranslate_grad]
    rfl

theorem overlap_local_poincare {d : ℕ} [NeZero d] {V : Set (Vec d)} (hV : IsOpen V)
    (u : H1Function V) (S : TriadicCube d) (hS : ScalarOverlap.openCubeSet S ⊆ V) :
    cubeBesovOverlapOscillation S 2 u.toFun ≤
      SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.oscillationMultiscalePoincareConstant d *
        ∑ i : Fin d, cubeBesovCircNorm (originCube d (S.scale + 1)) 1 2 1
          (fun x => u.grad (x + cubeCenter S) i) := by
  obtain ⟨v, hv, hg⟩ := exists_translated_h1 hV u S hS
  have h := SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm (originCube d (S.scale + 1)) v
  have hleft : cubeBesovOscillation (originCube d (S.scale + 1)) 2 (fun x => v.toFun x)
      = cubeBesovOscillation (originCube d (S.scale + 1)) 2 (fun x => u.toFun (x + cubeCenter S)) :=
    congrArg (cubeBesovOscillation (originCube d (S.scale + 1)) 2) (funext fun x => hv x)
  have hright : (∑ i : Fin d, cubeBesovCircNorm (originCube d (S.scale + 1)) 1 2 1 (fun x => v.grad x i))
      = (∑ i : Fin d, cubeBesovCircNorm (originCube d (S.scale + 1)) 1 2 1 (fun x => u.grad (x + cubeCenter S) i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (cubeBesovCircNorm (originCube d (S.scale + 1)) 1 2 1) (funext fun x => congrFun (hg x) i)
  rw [hleft, hright] at h
  rw [overlap_oscillation_eq S u.toFun]
  exact h

theorem cubeBesovCircPartialNorm_eq {d : ℕ} (Q : TriadicCube d) (g : Vec d → ℝ) (N : ℕ) :
    cubeBesovCircPartialNorm Q 1 2 1 (N + 1) g =
      ∑ k ∈ Finset.range (N + 2), (cubeScaleFactor Q / (3 : ℝ) ^ k) * Real.sqrt (theta Q k g) := by
  have hN : N + 1 + 1 = N + 2 := by omega
  have hA : ∀ j : ℕ, cubeBesovCircDepthAverage Q 2 g j = theta Q j g := fun j => by
    unfold cubeBesovCircDepthAverage theta
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  unfold cubeBesovCircPartialNorm cubeBesovCircPartialSeminorm
  rw [hN, ENNReal.toReal_one, div_one, Real.rpow_one]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold cubeBesovCircDepthSeminorm cubeBesovCircDepthWeight
  rw [hA j]
  simp only [ENNReal.toReal_ofNat, Real.sqrt_eq_rpow, Real.rpow_one]

theorem cubeBesovCircNorm_le {d : ℕ} (Q : TriadicCube d) (g : Vec d → ℝ) (B : ℝ)
    (hB : ∀ N : ℕ,
      ∑ k ∈ Finset.range (N + 2), (cubeScaleFactor Q / (3 : ℝ) ^ k) * Real.sqrt (theta Q k g) ≤ B) :
    cubeBesovCircNorm Q 1 2 1 g ≤ B := by
  unfold cubeBesovCircNorm cubeBesovCircNormValueSet
  apply csSup_le (Set.range_nonempty _)
  intro b hb
  obtain ⟨N, rfl⟩ := hb
  simp only [cubeBesovCircNormEntry, if_neg (by norm_num : (1 : ENNReal) ≠ ⊤)]
  rw [cubeBesovCircPartialNorm_eq]
  exact hB N

end

end SubdiffusiveProcess.Besov.Detach
