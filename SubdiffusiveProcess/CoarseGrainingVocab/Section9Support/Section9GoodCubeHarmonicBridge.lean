import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeHarmonicContraction
import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.Compose
import SubdiffusiveProcess.Frozen.Section6.CutoffHolderBoundedMultiplier




set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (translatedCube IsMiddleHalfSubcube oscillationOn
  IsWeaklyHarmonicOn)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass (eqOn_of_ae_eq_of_continuousOn)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-! ## Sup-norm geometry of the concentric window -/

theorem mem_cubeSet_iff {Q : Cube d} {x : Vec d} :
    x ∈ cubeSet Q ↔ ∀ i, |x i - Q.1 i| < Q.2 / 2 :=
  mem_centeredAxisCube

/-- Membership in a cube, read through the sup norm of `Vec d`. -/
theorem norm_sub_le_of_mem_cubeSet {Q : Cube d} (hQ : 0 ≤ Q.2) {x : Vec d}
    (hx : x ∈ cubeSet Q) : ‖x - Q.1‖ ≤ Q.2 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using le_of_lt (mem_cubeSet_iff.mp hx i)

/-- The centre of a positive-side cube lies in it. -/
theorem centre_mem_cubeSet {Q : Cube d} (hQ : 0 < Q.2) : Q.1 ∈ cubeSet Q :=
  mem_cubeSet_iff.mpr fun _ => by simpa using by linarith

/-- A shifted inclusion of cubes in sup-norm form. -/
theorem cubeSet_subset_cubeSet_of_dist {Q R : Cube d}
    (h : ∀ i, |Q.1 i - R.1 i| + Q.2 / 2 ≤ R.2 / 2) :
    cubeSet Q ⊆ cubeSet R := by
  intro x hx
  refine mem_cubeSet_iff.mpr fun i => ?_
  have hxi := mem_cubeSet_iff.mp hx i
  have habs : |x i - R.1 i| ≤ |x i - Q.1 i| + |Q.1 i - R.1 i| := by
    have hrw : x i - R.1 i = (x i - Q.1 i) + (Q.1 i - R.1 i) := by ring
    rw [hrw]
    exact abs_add_le _ _
  linarith [h i]

/-- The closure of a cube, in sup-norm form. -/
theorem closure_cubeSet_subset_of_dist {Q R : Cube d}
    (h : ∀ i, |Q.1 i - R.1 i| + Q.2 / 2 < R.2 / 2) :
    closure (cubeSet Q) ⊆ cubeSet R := by
  have hclosed : IsClosed (⋂ i : Fin d, {z : Vec d | |z i - Q.1 i| ≤ Q.2 / 2}) :=
    isClosed_iInter fun i =>
      isClosed_le (((continuous_apply i).sub continuous_const).abs) continuous_const
  have hsub : cubeSet Q ⊆ ⋂ i : Fin d, {z : Vec d | |z i - Q.1 i| ≤ Q.2 / 2} := fun z hz =>
    Set.mem_iInter.mpr fun i => le_of_lt (mem_cubeSet_iff.mp hz i)
  refine (closure_minimal hsub hclosed).trans fun z hz => mem_cubeSet_iff.mpr fun i => ?_
  have hzi := Set.mem_iInter.mp hz i
  simp only [Set.mem_setOf_eq] at hzi
  have habs : |z i - R.1 i| ≤ |z i - Q.1 i| + |Q.1 i - R.1 i| := by
    have hrw : z i - R.1 i = (z i - Q.1 i) + (Q.1 i - R.1 i) := by ring
    rw [hrw]
    exact abs_add_le _ _
  linarith [h i]

/-! ## `oscillationOn` against `oscillation` -/

/-- Every difference on a window is bounded by the window's `oscillation`, once
that is finite. -/
theorem abs_sub_le_toReal_oscillation {U : Set (Vec d)} {h : Vec d → ℝ}
    (hfin : oscillation U h ≠ ⊤) {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    |h x - h y| ≤ (oscillation U h).toReal := by
  have hle : ENNReal.ofReal |h x - h y| ≤ oscillation U h := by
    refine le_trans ?_ (le_iSup₂ (f := fun x (_ : x ∈ U) =>
      ⨆ y, ⨆ (_ : y ∈ U), ENNReal.ofReal |h x - h y|) x hx)
    exact le_iSup₂ (f := fun y (_ : y ∈ U) => ENNReal.ofReal |h x - h y|) y hy
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle

/-- The `ENNReal` oscillation is dominated by the real one whenever the latter
is an upper bound for the differences. -/
theorem oscillation_le_ofReal_of_bound {U : Set (Vec d)} {h : Vec d → ℝ} {r : ℝ}
    (hr : ∀ x ∈ U, ∀ y ∈ U, |h x - h y| ≤ r) :
    oscillation U h ≤ ENNReal.ofReal r := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
  exact ENNReal.ofReal_le_ofReal (hr x hx y hy)

/-- The real oscillation of a window on which every difference is bounded. -/
theorem oscillationOn_le_of_bound {U : Set (Vec d)} {h : Vec d → ℝ} {r : ℝ}
    (hne : U.Nonempty) (hr : ∀ x ∈ U, ∀ y ∈ U, |h x - h y| ≤ r) :
    oscillationOn U h ≤ r := by
  obtain ⟨x0, hx0⟩ := hne
  refine Real.sSup_le ?_ (le_trans (abs_nonneg (h x0 - h x0)) (hr x0 hx0 x0 hx0))
  rintro s ⟨x, hx, y, hy, rfl⟩
  exact hr x hx y hy

/-- The real oscillation of a nonempty window is nonnegative. -/
theorem oscillationOn_nonneg_of_bddAbove {U : Set (Vec d)} {h : Vec d → ℝ} {r : ℝ}
    (hne : U.Nonempty) (hr : ∀ x ∈ U, ∀ y ∈ U, |h x - h y| ≤ r) :
    0 ≤ oscillationOn U h := by
  obtain ⟨x, hx⟩ := hne
  refine le_csSup ⟨r, ?_⟩ ⟨x, hx, x, hx, by simp⟩
  rintro s ⟨u, hu, v, hv, rfl⟩
  exact hr u hu v hv


/-- The real oscillation does not see a change of the function off the window. -/
theorem oscillationOn_congr {U : Set (Vec d)} {f g : Vec d → ℝ} (heq : Set.EqOn f g U) :
    oscillationOn U f = oscillationOn U g := by
  unfold oscillationOn
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, by rw [heq hx, heq hy]⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, by rw [heq hx, heq hy]⟩

/-- A single difference is below the real oscillation, once the differences are
bounded. -/
theorem abs_sub_le_oscillationOn {U : Set (Vec d)} {h : Vec d → ℝ} {r : ℝ}
    (hr : ∀ x ∈ U, ∀ y ∈ U, |h x - h y| ≤ r) {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    |h x - h y| ≤ oscillationOn U h := by
  refine le_csSup ⟨r, ?_⟩ ⟨x, hx, y, hy, rfl⟩
  rintro s ⟨u, hu, v, hv, rfl⟩
  exact hr u hu v hv

/-! ## The concentric window of P378-F3 -/

section Window

variable {p : Cube d × Cube d} {m : ℤ} {j2 : ℕ}

/-- The window on which the Section 6 anchor is run: the cube of scale `m-1`
concentric with the **inner** cube of the pair. -/
theorem translatedCube_pred_eq (p : Cube d × Cube d) (m : ℤ) :
    translatedCube d (m - 1) p.1.1 = cubeSet (p.1.1, (3 : ℝ) ^ (m - 1)) :=
  translatedCube_eq_cubeSet _ _

/-- The inner side of an admissible pair, in triadic form. -/
theorem inner_side_eq (houter : p.2.2 = (3 : ℝ) ^ m)
    (hinner : p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2) :
    p.1.2 = (3 : ℝ) ^ (m - (j2 : ℤ)) := by
  rw [hinner, houter, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  ring

/-- The inner centre is strictly inside the middle half of the outer cube. -/
theorem abs_inner_centre_sub_lt (hip : 0 < p.1.2)
    (hhalf : cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2)) (i : Fin d) :
    |p.1.1 i - p.2.1 i| < p.2.2 / 4 := by
  have hmem := hhalf (centre_mem_cubeSet hip)
  have := (mem_centeredAxisCube (x := p.2.1) (z := p.1.1) (L := p.2.2 / 2)).mp hmem i
  linarith

/-- **The window sits compactly inside the outer cube.**  This is what makes
`WeakHarmonic a (cubeSet p.2) h` hand over an `H¹` solution on all of it. -/
theorem closure_window_subset (hip : 0 < p.1.2) (houter : p.2.2 = (3 : ℝ) ^ m)
    (hhalf : cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2)) :
    closure (translatedCube d (m - 1) p.1.1) ⊆ cubeSet p.2 := by
  rw [translatedCube_pred_eq]
  refine closure_cubeSet_subset_of_dist fun i => ?_
  have hd := abs_inner_centre_sub_lt hip hhalf i
  have h3 : (3 : ℝ) ^ (m - 1) = (3 : ℝ) ^ m / 3 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hpos : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  simp only [h3, houter] at *
  linarith

/-- The inner cube lies in the window. -/
theorem inner_subset_window (hj2 : 1 ≤ j2) (houter : p.2.2 = (3 : ℝ) ^ m)
    (hinner : p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2) :
    cubeSet p.1 ⊆ translatedCube d (m - 1) p.1.1 := by
  rw [translatedCube_pred_eq]
  refine cubeSet_subset_cubeSet_of_dist fun i => ?_
  have hle : (3 : ℝ) ^ (m - (j2 : ℤ)) ≤ (3 : ℝ) ^ (m - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [inner_side_eq houter hinner]
  simp only [sub_self, abs_zero]
  linarith

/-- The anchor's outer readout window lies in the window. -/
theorem ball_subset_window (m : ℤ) (p : Cube d × Cube d) :
    {x : Vec d | ‖x - p.1.1‖ ≤ 3 * (3 : ℝ) ^ (m - 1) / 8} ⊆
      translatedCube d (m - 1) p.1.1 := by
  rw [translatedCube_pred_eq]
  intro x hx
  refine mem_cubeSet_iff.mpr fun i => ?_
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (m - 1) := zpow_pos (by norm_num) _
  have hxi : |x i - p.1.1 i| ≤ 3 * (3 : ℝ) ^ (m - 1) / 8 := by
    have := norm_le_pi_norm (x - p.1.1) i
    rw [Real.norm_eq_abs, Pi.sub_apply] at this
    exact le_trans this hx
  simp only
  linarith

/-- **The inner cube is a middle-half subcube of the window at relative depth
`j₂ - 1`.**  The sup-norm side condition `3^{m-j₂}/2 ≤ 3^{m-1}/4` is exactly
where `j₂ ≥ 2` is used. -/
theorem isMiddleHalfSubcube_window (hj2 : 2 ≤ j2) (hip : 0 < p.1.2)
    (houter : p.2.2 = (3 : ℝ) ^ m)
    (hinner : p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2) :
    IsMiddleHalfSubcube (m - 1) p.1.1 (j2 - 1) (cubeSet p.1) := by
  have hside := inner_side_eq houter hinner
  refine ⟨p.1.1, ?_, ?_⟩
  · rw [translatedCube_eq_cubeSet]
    have hidx : (m - 1) - ((j2 - 1 : ℕ) : ℤ) = m - (j2 : ℤ) := by
      have : ((j2 - 1 : ℕ) : ℤ) = (j2 : ℤ) - 1 := by omega
      rw [this]; ring
    rw [hidx, ← hside]
  · intro x hx
    have hnorm := norm_sub_le_of_mem_cubeSet hip.le hx
    have hle : (3 : ℝ) ^ (m - (j2 : ℤ)) ≤ (3 : ℝ) ^ (m - 2) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (3 : ℝ) ^ (m - 2) = (3 : ℝ) ^ (m - 1) / 3 := by
      rw [show m - 2 = (m - 1) - 1 by ring, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [hside] at hnorm
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (m - 1) := zpow_pos (by norm_num) _
    rw [h2] at hle
    linarith

end Window






theorem oscillation_le_of_windowContraction
    {a : Vec d → ℝ} {eps0 K : ℝ} {p : Cube d × Cube d} {m : ℤ} {j2 : ℕ}
    (hj2 : 2 ≤ j2) (hip : 0 < p.1.2)
    (houter : p.2.2 = (3 : ℝ) ^ m)
    (hinner : p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2)
    (hhalf : cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2))
    (hK0 : 0 ≤ K) (hKeps : K ≤ eps0) (heps0 : 0 < eps0)
    (hanchor : ∀ u : H1Function (translatedCube d (m - 1) p.1.1),
      IsWeaklyHarmonicOn a (translatedCube d (m - 1) p.1.1) u →
      ∃ hRep : Vec d → ℝ,
        ContinuousOn hRep (translatedCube d (m - 1) p.1.1) ∧
        hRep =ᵐ[volume.restrict (translatedCube d (m - 1) p.1.1)] u.toFun ∧
        oscillationOn (cubeSet p.1) hRep ≤ K *
          oscillationOn {x : Vec d | ‖x - p.1.1‖ ≤ 3 * (3 : ℝ) ^ (m - 1) / 8} hRep)
    {h : Vec d → ℝ} (hharm : WeakHarmonic a (cubeSet p.2) h) :
    oscillation (cubeSet p.1) h ≤ ENNReal.ofReal eps0 * oscillation (cubeSet p.2) h := by
  by_cases htop : oscillation (cubeSet p.2) h = ⊤
  · have hne : ENNReal.ofReal eps0 ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact heps0
    rw [htop, ENNReal.mul_top hne]
    exact le_top
  set W : Set (Vec d) := translatedCube d (m - 1) p.1.1 with hWdef
  have hWeq : W = cubeSet (p.1.1, (3 : ℝ) ^ (m - 1)) := translatedCube_pred_eq p m
  have hWopen : IsOpen W := by rw [hWeq]; exact isOpen_centeredAxisCube _ _
  have hWsub : closure W ⊆ cubeSet p.2 := closure_window_subset hip houter hhalf
  have hWbdd : Bornology.IsBounded W := by rw [hWeq]; exact isBounded_centeredAxisCube _ _
  have hWsub' : W ⊆ cubeSet p.2 := subset_closure.trans hWsub
  set ball : Set (Vec d) := {x : Vec d | ‖x - p.1.1‖ ≤ 3 * (3 : ℝ) ^ (m - 1) / 8} with hballdef
  have hinnerW : cubeSet p.1 ⊆ W := inner_subset_window (le_trans one_le_two hj2) houter hinner
  have hballW : ball ⊆ W := ball_subset_window m p
  set S : ℝ := (oscillation (cubeSet p.2) h).toReal with hS
  have hbound : ∀ x ∈ cubeSet p.2, ∀ y ∈ cubeSet p.2, |h x - h y| ≤ S :=
    fun x hx y hy => abs_sub_le_toReal_oscillation htop hx hy
  obtain ⟨u, hu_ae, hu_id⟩ := hharm.2 W hWopen hWbdd.isCompact_closure hWsub
  have hu_wh : IsWeaklyHarmonicOn a W u := by
    intro phi
    simpa only [vecDot_smul_left] using hu_id phi
  obtain ⟨hRep, hRepC, hRep_ae, hosc⟩ := hanchor u hu_wh
  have hae : ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ W → hRep x = h x := by
    rw [← ae_restrict_iff' hWopen.measurableSet]
    filter_upwards [hRep_ae, hu_ae] with x h1 h2
    rw [h1, h2]
  have heqOn : Set.EqOn hRep h W :=
    eqOn_of_ae_eq_of_continuousOn hWopen hRepC (hharm.1.mono hWsub') hae
  rw [oscillationOn_congr (heqOn.mono hinnerW),
    oscillationOn_congr (heqOn.mono hballW)] at hosc
  have hballne : ball.Nonempty := by
    refine ⟨p.1.1, ?_⟩
    have : (0 : ℝ) < (3 : ℝ) ^ (m - 1) := zpow_pos (by norm_num) _
    simp only [hballdef, Set.mem_setOf_eq, sub_self, norm_zero]
    linarith
  have hballbd : ∀ x ∈ ball, ∀ y ∈ ball, |h x - h y| ≤ S := fun x hx y hy =>
    hbound x (hWsub' (hballW hx)) y (hWsub' (hballW hy))
  have hballS : oscillationOn ball h ≤ S := oscillationOn_le_of_bound hballne hballbd
  have hball0 : 0 ≤ oscillationOn ball h :=
    oscillationOn_nonneg_of_bddAbove hballne hballbd
  have hfinal : ∀ x ∈ cubeSet p.1, ∀ y ∈ cubeSet p.1, |h x - h y| ≤ eps0 * S := by
    intro x hx y hy
    have h1 : |h x - h y| ≤ oscillationOn (cubeSet p.1) h :=
      abs_sub_le_oscillationOn (r := S)
        (fun uu hu vv hv => hbound uu (hWsub' (hinnerW hu)) vv (hWsub' (hinnerW hv))) hx hy
    have h2 : K * oscillationOn ball h ≤ eps0 * S := by nlinarith
    linarith [hosc]
  refine le_trans (oscillation_le_ofReal_of_bound hfinal) ?_
  rw [ENNReal.ofReal_mul heps0.le, hS, ENNReal.ofReal_toReal htop]






theorem exists_pair_harmonicOscillation_of_frozen (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ eps0 : ℝ, 0 < eps0 → ∃ j2 : ℕ, 2 ≤ j2 ∧
        ∀ M : GMCModel d, M.delta ≤ c → ∀ (L : ℕ) (m : ℤ) (p : Cube d × Cube d),
          0 < p.1.2 → p.2.2 = (3 : ℝ) ^ m →
          p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2 →
          cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2) →
          ∃ bad : Set (PotentialSample d),
            M.P.toMeasure bad ≤ ENNReal.ofReal
              (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ bad, ∀ h : Vec d → ℝ,
              WeakHarmonic (aCutoff M L omega) (cubeSet p.2) h →
                oscillation (cubeSet p.1) h ≤
                  ENNReal.ofReal eps0 * oscillation (cubeSet p.2) h := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hmain⟩ :=
    SubdiffusiveProcess.Frozen.Section6.cutoff_holder_bounded_multiplier d
  refine ⟨c, C, hc, hC, ?_⟩
  intro eps0 heps0
  obtain ⟨j, hj2, hjle⟩ := exists_depth_of_contraction C c eps0 hc heps0
  refine ⟨j + 1, by omega, ?_⟩
  intro M hdelta L m p hip houter hinner hhalf
  have hmid : IsMiddleHalfSubcube (m - 1) p.1.1 (j + 1 - 1) (cubeSet p.1) :=
    isMiddleHalfSubcube_window (by omega) hip houter hinner
  obtain ⟨bad, _, hbadmu, hbadmain⟩ :=
    hmain M hdelta L (m - 1) p.1.1 (j + 1 - 1) (by omega) (cubeSet p.1) hmid
  refine ⟨bad, hbadmu, ?_⟩
  intro omega hom h hharm
  refine oscillation_le_of_windowContraction (j2 := j + 1)
    (K := C * (3 : ℝ) ^ (-c * ((j + 1 - 1 : ℕ) : ℝ))) (by omega) hip houter hinner hhalf
    (by positivity) (by simpa using hjle) heps0 ?_ hharm
  intro u hu
  obtain ⟨hRep, hRepC, hRepAe, hRepOsc, -⟩ :=
    hbadmain omega hom (fun _ => (1 : ℝ)) continuousOn_const (fun _ _ => one_pos)
      ⟨1, one_pos, fun x _ => by simpa using hepsStar.le⟩ u (by simpa using hu)
  exact ⟨hRep, hRepC, hRepAe, hRepOsc⟩

/-- **The full `LocalHarmonicOscillation` clause on a finite family of
admissible pairs, from the PROVED Section 6 anchor.**  The bad event is the
finite union of the anchor's per-pair events, so its probability carries the
factor `card Pfam`.

This is the deterministic content of the good cube's harmonic display,
complete.  Two structural gaps remain before it can be read as
`GoodCubeHarmonicContractionEvent`, and both are about the *shape* of the event
rather than about the estimate.

1. *Constant ordering.*  The factor `card Pfam` depends on the depth pair
   `(j₁, j₂)` and on `d`, and `card Pfam` is only known after the reference
   template is given, whereas `GoodCubeHarmonicContractionEvent` (and
   `GoodCubeReducedPackage`) fix the tail constant `C₀` **before** quantifying
   over `j₁` and over the template.  The frozen block itself does not have this
   problem: there `C`, `j₁` and `j₂` sit in one existential group and `grid0`,
   `Pfam0` come after it.
2. *Coefficient-locality.*  Clause 7a asks for a bad predicate on
   `nativeBox n 1 0 → ℝ`, i.e. an event determined by the restriction of
   `aCutoff M n ω` to the native box; the Section 6 anchor returns an event
   measurable for the full shell field `⨆ i, comap (ω ↦ ω i)`, with no
   spatial localisation in its statement. -/
theorem exists_localHarmonicOscillation_of_frozen (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ eps0 : ℝ, 0 < eps0 → ∃ j2 : ℕ, 2 ≤ j2 ∧
        ∀ M : GMCModel d, M.delta ≤ c → ∀ (L : ℕ) (m : ℤ)
          (Pfam : Finset (Cube d × Cube d)),
          (∀ p ∈ Pfam, 0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ m ∧
            p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2 ∧
            cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2)) →
          ∃ bad : Set (PotentialSample d),
            M.P.toMeasure bad ≤ ENNReal.ofReal ((Pfam.card : ℝ) *
              (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)))) ∧
            ∀ omega ∉ bad,
              LocalHarmonicOscillation (aCutoff M L omega) eps0
                (Pfam : Set (Cube d × Cube d)) := by
  obtain ⟨c, C, hc, hC, hmain⟩ := exists_pair_harmonicOscillation_of_frozen d
  refine ⟨c, C, hc, hC, ?_⟩
  intro eps0 heps0
  obtain ⟨j2, hj2, hpair⟩ := hmain eps0 heps0
  refine ⟨j2, hj2, ?_⟩
  intro M hdelta L m Pfam hPfam
  set X : ℝ := C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) with hX
  have hX0 : 0 ≤ X := by positivity
  have hchoice : ∀ p ∈ Pfam, ∃ bad : Set (PotentialSample d),
      M.P.toMeasure bad ≤ ENNReal.ofReal X ∧
      ∀ omega ∉ bad, ∀ h : Vec d → ℝ,
        WeakHarmonic (aCutoff M L omega) (cubeSet p.2) h →
          oscillation (cubeSet p.1) h ≤
            ENNReal.ofReal eps0 * oscillation (cubeSet p.2) h := by
    intro p hp
    obtain ⟨hip, houter, hinner, hhalf⟩ := hPfam p hp
    exact hpair M hdelta L m p hip houter hinner hhalf
  choose! badOf hbadmu hbadmain using hchoice
  refine ⟨⋃ p ∈ Pfam, badOf p, ?_, ?_⟩
  · refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun p hp => hbadmu p hp)) ?_
    have hcard : (0 : ℝ) ≤ (Pfam.card : ℝ) := by positivity
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul hcard,
      ENNReal.ofReal_natCast]
  · intro omega hom
    refine ⟨fun p hp h hharm => ?_⟩
    refine hbadmain p hp omega (fun hmem => hom ?_) h hharm
    exact Set.mem_biUnion hp hmem

/-- **The harmonic display on an admissible reference geometry.**  Every
`IsLocalCubeGeometry` of inner depth `j₂` supplies exactly the hypotheses of
`exists_localHarmonicOscillation_of_frozen` at the outer scale `m = n - j₁`, so
the contraction holds off an event whose probability is the frozen layer-zero
size times a factor `K` depending only on the template.

The `K` is quantified **after** the geometry.  That is the whole distance
between this theorem and `GoodCubeHarmonicContractionEvent`, apart from the
coefficient-locality of the event; see the docstring of
`exists_localHarmonicOscillation_of_frozen`. -/
theorem exists_localHarmonicOscillation_of_isLocalCubeGeometry (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ eps0 : ℝ, 0 < eps0 → ∃ j2 : ℕ, 2 ≤ j2 ∧
        ∀ M : GMCModel d, M.delta ≤ c →
          ∀ (L n j1 : ℕ) (grid : Finset (Vec d)) (y : Vec d)
            (Pfam : Set (Cube d × Cube d)) (Qfam Afam : Set (Cube d)),
            IsLocalCubeGeometry grid j1 j2 (y, (3 : ℝ) ^ n) Pfam Qfam Afam →
            ∃ (K : ℝ) (bad : Set (PotentialSample d)), 0 < K ∧
              M.P.toMeasure bad ≤ ENNReal.ofReal (K *
                (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)))) ∧
              ∀ omega ∉ bad,
                LocalHarmonicOscillation (aCutoff M L omega) eps0 Pfam := by
  obtain ⟨c, C, hc, hC, hmain⟩ := exists_localHarmonicOscillation_of_frozen d
  refine ⟨c, C, hc, hC, ?_⟩
  intro eps0 heps0
  obtain ⟨j2, hj2, hfam⟩ := hmain eps0 heps0
  refine ⟨j2, hj2, ?_⟩
  intro M hdelta L n j1 grid y Pfam Qfam Afam hgeom
  classical
  set F : Finset (Cube d × Cube d) := hgeom.finite_P.toFinset with hF
  have hFcoe : (F : Set (Cube d × Cube d)) = Pfam := by
    rw [hF, Set.Finite.coe_toFinset]
  have hhyp : ∀ p ∈ F, 0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ)) ∧
      p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2 ∧
      cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2) := by
    intro p hp
    have hpP : p ∈ Pfam := by rw [← hFcoe]; exact hp
    refine ⟨hgeom.side_pos p.1 (hgeom.pair_mem p hpP).1, ?_,
      hgeom.pair_inner_side p hpP, hgeom.pair_middle_half p hpP⟩
    rw [hgeom.pair_outer_side p hpP]
    show (3 : ℝ) ^ (-(j1 : ℤ)) * (3 : ℝ) ^ n = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ))
    rw [show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast 3 n).symm,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  obtain ⟨bad, hbadmu, hbadmain⟩ :=
    hfam M hdelta L ((n : ℤ) - (j1 : ℤ)) F hhyp
  refine ⟨(F.card : ℝ) + 1, bad, by positivity, ?_, ?_⟩
  · refine hbadmu.trans (ENNReal.ofReal_le_ofReal ?_)
    have hX : (0 : ℝ) ≤ C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) := by
      positivity
    nlinarith
  · intro omega hom
    have h := hbadmain omega hom
    rw [hFcoe] at h
    exact h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
