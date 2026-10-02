import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput




set_option autoImplicit false

open Set Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-! ## Cubes as sup-norm balls -/

theorem mem_centeredAxisCube {x z : Vec d} {L : ℝ} :
    z ∈ centeredAxisCube x L ↔ ∀ i, |z i - x i| < L / 2 := by
  constructor
  · intro h i
    have hi := h i (Set.mem_univ i)
    simp only [Set.mem_Ioo] at hi
    rw [abs_lt]
    constructor <;> linarith [hi.1, hi.2]
  · intro h i _
    have hi := h i
    rw [abs_lt] at hi
    simp only [Set.mem_Ioo]
    constructor <;> linarith [hi.1, hi.2]

theorem centeredAxisCube_mono {x : Vec d} {L L' : ℝ} (h : L ≤ L') :
    centeredAxisCube x L ⊆ centeredAxisCube x L' := by
  intro z hz
  rw [mem_centeredAxisCube] at hz ⊢
  intro i
  exact lt_of_lt_of_le (hz i) (by linarith)

theorem closure_centeredAxisCube_subset {x : Vec d} {L L' : ℝ} (h : L < L') :
    closure (centeredAxisCube x L) ⊆ centeredAxisCube x L' := by
  have hclosed : IsClosed (⋂ i : Fin d, {z : Vec d | |z i - x i| ≤ L / 2}) := by
    refine isClosed_iInter fun i => ?_
    exact isClosed_le (((continuous_apply i).sub continuous_const).abs) continuous_const
  have hsub : centeredAxisCube x L ⊆ ⋂ i : Fin d, {z : Vec d | |z i - x i| ≤ L / 2} := by
    intro z hz
    rw [mem_centeredAxisCube] at hz
    exact Set.mem_iInter.mpr fun i => le_of_lt (hz i)
  refine (closure_minimal hsub hclosed).trans ?_
  intro z hz
  rw [mem_centeredAxisCube]
  intro i
  have := Set.mem_iInter.mp hz i
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- A cube sits inside a nearby larger cube. -/
theorem centeredAxisCube_subset_of_dist {x1 x2 : Vec d} {L1 L2 r : ℝ}
    (hd : ∀ i, |x1 i - x2 i| ≤ r) (h : r + L1 / 2 ≤ L2 / 2) :
    centeredAxisCube x1 L1 ⊆ centeredAxisCube x2 L2 := by
  intro z hz
  rw [mem_centeredAxisCube] at hz ⊢
  intro i
  have h1 := hz i
  have h2 : |z i - x2 i| ≤ |z i - x1 i| + |x1 i - x2 i| := by
    calc |z i - x2 i| = |(z i - x1 i) + (x1 i - x2 i)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have h3 := hd i
  linarith

/-- The closure of a cube sits inside a nearby strictly larger cube. -/
theorem closure_centeredAxisCube_subset_of_dist {x1 x2 : Vec d} {L1 L2 r : ℝ}
    (hd : ∀ i, |x1 i - x2 i| ≤ r) (h : r + L1 / 2 < L2 / 2) :
    closure (centeredAxisCube x1 L1) ⊆ centeredAxisCube x2 L2 :=
  (closure_centeredAxisCube_subset (by linarith : L1 < L2 - 2 * r)).trans
    (centeredAxisCube_subset_of_dist hd (by linarith))

/-! ## The finite offset family -/



def scaleOffsets (y : Vec d) (m : ℤ) (M : ℕ) : Finset (Vec d) :=
  Finset.image (fun w : Fin d → Fin M =>
    (fun i => y i / (3 : ℝ) ^ m + (w i : ℝ) / (M : ℝ))) Finset.univ

theorem mem_scaleOffsets {y : Vec d} {m : ℤ} {M : ℕ} (w : Fin d → Fin M) :
    (fun i => y i / (3 : ℝ) ^ m + (w i : ℝ) / (M : ℝ)) ∈ scaleOffsets y m M :=
  Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩

/-- A lattice point of step `t = c * (3 ^ m / M)` through `y` carries a grid cube
of side `3 ^ m`, for every grid containing the scale-`m` offsets. -/
theorem isGridCube_scaleOffsets {y : Vec d} {t : ℝ} {m : ℤ} {M c : ℕ} (hM : 0 < M)
    {grid : Finset (Vec d)} (hsub : scaleOffsets y m M ⊆ grid)
    (ht : t = (c : ℝ) * ((3 : ℝ) ^ m / (M : ℝ))) (N : Fin d → ℤ) :
    IsGridCube grid (fun i => y i + t * (N i : ℝ)) ((3 : ℝ) ^ m) := by
  have hMz : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hpow : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  set N' : Fin d → ℤ := fun i => (c : ℤ) * N i with hN'
  refine ⟨(fun i => y i / (3 : ℝ) ^ m + (((N' i % (M : ℤ)).toNat : ℕ) : ℝ) / (M : ℝ)),
    ?_, m, (fun i => N' i / (M : ℤ)), rfl, ?_⟩
  · refine hsub (mem_scaleOffsets (y := y) (m := m) (M := M)
      (fun i => ⟨(N' i % (M : ℤ)).toNat, ?_⟩))
    have h0 : 0 ≤ N' i % (M : ℤ) := Int.emod_nonneg _ (by omega)
    have h1 : N' i % (M : ℤ) < (M : ℤ) := Int.emod_lt_of_pos _ hMz
    omega
  · funext i
    have h0 : 0 ≤ N' i % (M : ℤ) := Int.emod_nonneg _ (by omega)
    have hcast : (((N' i % (M : ℤ)).toNat : ℕ) : ℝ) = ((N' i % (M : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)
    have hdiv : (M : ℤ) * (N' i / (M : ℤ)) + N' i % (M : ℤ) = N' i :=
      Int.mul_ediv_add_emod _ _
    have hR : ((N' i % (M : ℤ) : ℤ) : ℝ) + (M : ℝ) * ((N' i / (M : ℤ) : ℤ) : ℝ)
        = (c : ℝ) * (N i : ℝ) := by
      have h4 : ((N' i : ℤ) : ℝ)
          = (M : ℝ) * ((N' i / (M : ℤ) : ℤ) : ℝ) + ((N' i % (M : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hdiv.symm
      have h3 : ((N' i : ℤ) : ℝ) = (c : ℝ) * ((N i : ℤ) : ℝ) := by
        rw [hN']; push_cast; ring
      rw [← h3, h4]; ring
    have hsplit : (3 : ℝ) ^ m * (y i / (3 : ℝ) ^ m
          + (((N' i % (M : ℤ)).toNat : ℕ) : ℝ) / (M : ℝ)
          + ((N' i / (M : ℤ) : ℤ) : ℝ))
        = y i + ((3 : ℝ) ^ m / (M : ℝ)) * ((((N' i % (M : ℤ)).toNat : ℕ) : ℝ)
          + (M : ℝ) * ((N' i / (M : ℤ) : ℤ) : ℝ)) := by
      field_simp
      ring
    simp only []
    rw [hsplit, hcast, hR, ht]
    ring

/-! ## Index sets -/

/-- Integer indices bounded by `K` in every coordinate. -/
def boxIdx (d K : ℕ) : Set (Fin d → ℤ) := {N | ∀ i, |N i| ≤ (K : ℤ)}

theorem finite_boxIdx (d K : ℕ) : (boxIdx d K).Finite := by
  have hEq : boxIdx d K = Set.pi Set.univ (fun _ : Fin d => Set.Icc (-(K : ℤ)) (K : ℤ)) := by
    ext N
    simp only [boxIdx, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc,
      forall_const, abs_le]
  rw [hEq]
  exact Set.Finite.pi fun _ => Set.finite_Icc _ _

/-- The centre of the lattice cube with index `N` and step `t`. -/
def latticeCentre (y : Vec d) (t : ℝ) (N : Fin d → ℤ) : Vec d :=
  fun i => y i + t * (N i : ℝ)

/-- The index of a lattice cube of step `t` whose centre is nearest to `x`. -/
def nearestIdx (y : Vec d) (t : ℝ) (x : Vec d) : Fin d → ℤ :=
  fun i => round ((x i - y i) / t)

theorem nearestIdx_close {y : Vec d} {t : ℝ} (ht : 0 < t) (x : Vec d) (i : Fin d) :
    |x i - latticeCentre y t (nearestIdx y t x) i| ≤ t / 2 := by
  have hround : |(x i - y i) / t - round ((x i - y i) / t)| ≤ 1 / 2 :=
    abs_sub_round _
  have hx : x i - latticeCentre y t (nearestIdx y t x) i
      = t * ((x i - y i) / t - (round ((x i - y i) / t) : ℝ)) := by
    unfold latticeCentre nearestIdx
    field_simp
    ring
  rw [hx, abs_mul, abs_of_pos ht]
  calc t * |(x i - y i) / t - (round ((x i - y i) / t) : ℝ)| ≤ t * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left hround (le_of_lt ht)
    _ = t / 2 := by ring

theorem isGridCube_centre {y : Vec d} {m : ℤ} {M : ℕ} (hM : 0 < M)
    {grid : Finset (Vec d)} (hsub : scaleOffsets y m M ⊆ grid) :
    IsGridCube grid y ((3 : ℝ) ^ m) := by
  have h := isGridCube_scaleOffsets (y := y) (t := 0) (m := m) (M := M) (c := 0)
    hM hsub (by norm_num) (fun _ => 0)
  simpa using h

/-- At the origin the offsets do not depend on the scale. -/
theorem scaleOffsets_zero (m m' : ℤ) (M : ℕ) :
    scaleOffsets (0 : Vec d) m M = scaleOffsets (0 : Vec d) m' M := by
  unfold scaleOffsets
  congr 1
  funext w
  funext i
  simp

/-- **Closure of an offset family under triadic descent.**

Under the scaled reading of `IsGridCube` a triadic dilation by `3` divides the
offset of a cube by `3`, so a family of offsets is stable under dilation exactly
when every offset is `3 * g'` modulo the integer lattice for some offset `g'` of
the family.  This is what makes the version 2 reference template transportable
to every scale (`Section9GoodCubeReferenceAffine`). -/
def TriadicOffsets (grid : Finset (Vec d)) : Prop :=
  ∀ g ∈ grid, ∃ g' ∈ grid, ∃ v : Fin d → ℤ, ∀ i, (3 : ℝ) * g' i = g i + (v i : ℝ)

/-- Iterating triadic descent. -/
theorem TriadicOffsets.pow {grid : Finset (Vec d)} (h : TriadicOffsets grid) (n : ℕ) :
    ∀ g ∈ grid, ∃ g' ∈ grid, ∃ v : Fin d → ℤ,
      ∀ i, (3 : ℝ) ^ n * g' i = g i + (v i : ℝ) := by
  induction n with
  | zero =>
    intro g hg
    exact ⟨g, hg, fun _ => 0, fun i => by simp⟩
  | succ n ih =>
    intro g hg
    obtain ⟨g1, hg1, v1, hv1⟩ := ih g hg
    obtain ⟨g2, hg2, v2, hv2⟩ := h g1 hg1
    refine ⟨g2, hg2, fun i => v1 i + (3 : ℤ) ^ n * v2 i, fun i => ?_⟩
    have hstep : (3 : ℝ) ^ (n + 1) * g2 i = (3 : ℝ) ^ n * ((3 : ℝ) * g2 i) := by ring
    rw [hstep, hv2 i, mul_add, hv1 i]
    push_cast
    ring

/-- Triadic descent inside `Fin 8`: `3 * (3 * w) = w` modulo `8`. -/
private theorem triadic_fin8 (w : Fin 8) :
    3 * (((3 * w : Fin 8) : ℕ) : ℤ)
      = ((w : ℕ) : ℤ)
        + 8 * ((3 * (((3 * w : Fin 8) : ℕ) : ℤ) - ((w : ℕ) : ℤ)) / 8) := by
  revert w
  decide

/-- The eight equal subdivisions of the side, at the origin, are closed under
triadic descent: `8` is prime to `3`. -/
theorem triadicOffsets_scaleOffsets_zero (d : ℕ) (m : ℤ) :
    TriadicOffsets (scaleOffsets (0 : Vec d) m 8) := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hg
  refine ⟨_, mem_scaleOffsets (y := (0 : Vec d)) (m := m) (M := 8)
      (fun i => 3 * w i),
    (fun i => (3 * (((3 * w i : Fin 8) : ℕ) : ℤ) - ((w i : ℕ) : ℤ)) / 8), fun i => ?_⟩
  have h := triadic_fin8 (w i)
  have hR : (3 : ℝ) * ((((3 * w i : Fin 8) : ℕ) : ℝ))
      = (((w i : ℕ) : ℝ))
        + 8 * (((3 * (((3 * w i : Fin 8) : ℕ) : ℤ) - ((w i : ℕ) : ℤ)) / 8 : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Pi.zero_apply, zero_div, zero_add]
  rw [show (((8 : ℕ)) : ℝ) = 8 by norm_num]
  field_simp
  linarith [hR]

theorem idx_le_of_abs_le {N : ℤ} {K : ℕ} (h : |(N : ℝ)| ≤ (K : ℝ)) : |N| ≤ (K : ℤ) := by
  rw [← Int.cast_abs] at h
  exact_mod_cast h

/-! ## The inward-shifted index used for the `A`-cubes -/

/-- The lattice index nearest to `T` after an inward shift of four units. -/
def innerIdx (T : ℝ) : ℤ := if 0 ≤ T then ⌊max 0 (T - 4)⌋ else -⌊max 0 (-T - 4)⌋

private theorem innerIdx_aux {T : ℝ} (hT : 0 ≤ T) :
    T - 5 ≤ (⌊max 0 (T - 4)⌋ : ℝ) ∧ (⌊max 0 (T - 4)⌋ : ℝ) ≤ T ∧
      0 ≤ (⌊max 0 (T - 4)⌋ : ℝ) ∧ (⌊max 0 (T - 4)⌋ : ℝ) ≤ max 0 (T - 4) := by
  have hm0 : (0 : ℝ) ≤ max 0 (T - 4) := le_max_left _ _
  have hmT : max 0 (T - 4) ≤ T := max_le hT (by linarith)
  have hfl_le : (⌊max 0 (T - 4)⌋ : ℝ) ≤ max 0 (T - 4) := Int.floor_le _
  have hfl_gt : max 0 (T - 4) - 1 < (⌊max 0 (T - 4)⌋ : ℝ) := Int.sub_one_lt_floor _
  have hfl_nonneg : (0 : ℝ) ≤ (⌊max 0 (T - 4)⌋ : ℝ) := by
    have : (0 : ℤ) ≤ ⌊max 0 (T - 4)⌋ := Int.le_floor.mpr (by exact_mod_cast hm0)
    exact_mod_cast this
  have hge : T - 4 ≤ max 0 (T - 4) := le_max_right _ _
  refine ⟨by linarith, le_trans hfl_le hmT, hfl_nonneg, hfl_le⟩

theorem innerIdx_dist (T : ℝ) : |(innerIdx T : ℝ) - T| ≤ 5 := by
  unfold innerIdx
  by_cases h : 0 ≤ T
  · rw [if_pos h]
    obtain ⟨h1, h2, _, _⟩ := innerIdx_aux h
    rw [abs_le]; constructor <;> linarith
  · rw [if_neg h]
    have hT : (0 : ℝ) ≤ -T := by linarith [not_le.mp h]
    obtain ⟨h1, h2, _, _⟩ := innerIdx_aux hT
    push_cast
    rw [abs_le]; constructor <;> linarith

theorem innerIdx_abs (T : ℝ) : |(innerIdx T : ℝ)| ≤ max 0 (|T| - 4) := by
  unfold innerIdx
  by_cases h : 0 ≤ T
  · rw [if_pos h, abs_of_nonneg h]
    obtain ⟨_, _, h3, h4⟩ := innerIdx_aux h
    rw [abs_of_nonneg h3]
    exact h4
  · rw [if_neg h]
    have hT : (0 : ℝ) ≤ -T := by linarith [not_le.mp h]
    have habs : |T| = -T := abs_of_neg (not_le.mp h)
    obtain ⟨_, _, h3, h4⟩ := innerIdx_aux hT
    rw [habs]
    push_cast
    rw [abs_neg, abs_of_nonneg h3]
    exact h4

/-! ## The construction -/

private theorem localCubeGeometry_nearest (y : Vec d) {A B s a tP : ℝ} {K : ℕ}
    (htPpos : 0 < tP) (htPdef : tP = a / 2) (hsa : s = A * B * a)
    (hKR : (K : ℝ) * 3 = A * B) (hAB27 : 27 ≤ A * B) :
    ∀ x : Vec d, (∀ i, |x i - y i| < s / 8) →
      (∀ i, |(nearestIdx y tP x i : ℤ)| ≤ (K : ℤ)) ∧
        (∀ i, |x i - (y i + tP * ((nearestIdx y tP x i : ℤ) : ℝ))| ≤ tP / 2) := by
  intro x hx
  have hclose : ∀ i, |x i - (y i + tP * ((nearestIdx y tP x i : ℤ) : ℝ))| ≤ tP / 2 := by
    intro i
    have h := nearestIdx_close (y := y) (t := tP) htPpos x i
    exact h
  refine ⟨fun i => ?_, hclose⟩
  have h1 := hclose i
  have h2 : tP * |((nearestIdx y tP x i : ℤ) : ℝ)| ≤ s / 8 + tP / 2 := by
    have h4 : |tP * ((nearestIdx y tP x i : ℤ) : ℝ)| - |x i - y i|
        ≤ |tP * ((nearestIdx y tP x i : ℤ) : ℝ) - (x i - y i)| :=
      abs_sub_abs_le_abs_sub _ _
    have h5 : |tP * ((nearestIdx y tP x i : ℤ) : ℝ) - (x i - y i)| ≤ tP / 2 := by
      rw [abs_sub_comm]
      calc |x i - y i - tP * ((nearestIdx y tP x i : ℤ) : ℝ)|
          = |x i - (y i + tP * ((nearestIdx y tP x i : ℤ) : ℝ))| := by ring_nf
        _ ≤ tP / 2 := h1
    rw [abs_mul, abs_of_pos htPpos] at h4
    linarith [hx i]
  refine idx_le_of_abs_le ?_
  have hsa2 : s = A * B * (2 * tP) := by rw [hsa, htPdef]; ring
  rw [hsa2] at h2
  have hkey : tP * |((nearestIdx y tP x i : ℤ) : ℝ)| ≤ tP * (A * B / 4 + 1 / 2) := by
    linarith [h2]
  have hX : |((nearestIdx y tP x i : ℤ) : ℝ)| ≤ A * B / 4 + 1 / 2 :=
    le_of_mul_le_mul_left hkey htPpos
  have hAB : (27 : ℝ) ≤ A * B := hAB27
  have hKval : (K : ℝ) = A * B / 3 := by linarith [hKR]
  rw [hKval]
  linarith

private theorem localCubeGeometry_inner (y : Vec d) {A B s a u : ℝ}
    {Ac : (Fin d → ℤ) → Cube d} {AI : Set (Fin d → ℤ)}
    (hupos : 0 < u) (hudef : u = a / 486) (hsa : s = A * B * a)
    (hAB27 : 27 ≤ A * B) (hapos : 0 < a)
    (hAIdef : AI = {N | ∀ i, u * |(N i : ℝ)| + (a / 243) / 2 ≤ s / 8})
    (hmemAc : ∀ (N : Fin d → ℤ) (z : Vec d),
      z ∈ cubeSet (Ac N) ↔ ∀ i, |z i - (y i + u * (N i : ℝ))| < (a / 243) / 2) :
    ∀ x : Vec d, (∀ i, |x i - y i| < s / 8) →
      ∃ N ∈ AI, cubeSet (Ac N) ⊆ centeredAxisCube x (a / 8) := by
  intro x hx
  refine ⟨fun i => innerIdx ((x i - y i) / u), ?_, ?_⟩
  · rw [hAIdef]
    intro i
    have hT : u * |((x i - y i) / u)| = |x i - y i| := by
      rw [abs_div, abs_of_pos hupos]
      field_simp
    have h1 := innerIdx_abs ((x i - y i) / u)
    have husmall : u ≤ s / 8 := by
      have h27 : (27 : ℝ) * a ≤ A * B * a := mul_le_mul_of_nonneg_right hAB27 hapos.le
      rw [hudef, hsa]
      linarith
    have hu243 : (a / 243) / 2 = u := by rw [hudef]; ring
    rw [hu243]
    rcases max_cases (0 : ℝ) (|((x i - y i) / u)| - 4) with ⟨he, hle⟩ | ⟨he, hlt⟩
    · rw [he] at h1
      have h2 : |((innerIdx ((x i - y i) / u) : ℤ) : ℝ)| = 0 :=
        le_antisymm h1 (abs_nonneg _)
      rw [h2]
      linarith
    · rw [he] at h1
      have h2 : u * |((innerIdx ((x i - y i) / u) : ℤ) : ℝ)|
          ≤ u * (|((x i - y i) / u)| - 4) := by
        exact mul_le_mul_of_nonneg_left h1 (le_of_lt hupos)
      have h3 : u * (|((x i - y i) / u)| - 4) = |x i - y i| - 4 * u := by
        rw [mul_sub, hT]; ring
      rw [h3] at h2
      linarith [hx i]
  · intro z hz
    rw [hmemAc] at hz
    rw [mem_centeredAxisCube]
    intro i
    have hd := innerIdx_dist ((x i - y i) / u)
    have hT : u * ((x i - y i) / u) = x i - y i := by field_simp
    have h1 : |u * ((innerIdx ((x i - y i) / u) : ℤ) : ℝ) - (x i - y i)| ≤ 5 * u := by
      have : u * ((innerIdx ((x i - y i) / u) : ℤ) : ℝ) - (x i - y i)
          = u * (((innerIdx ((x i - y i) / u) : ℤ) : ℝ) - ((x i - y i) / u)) := by
        rw [mul_sub, hT]
      rw [this, abs_mul, abs_of_pos hupos]
      nlinarith [hd, abs_nonneg (((innerIdx ((x i - y i) / u) : ℤ) : ℝ) - ((x i - y i) / u))]
    have h2 := hz i
    have hu243 : (a / 243) / 2 = u := by rw [hudef]; ring
    rw [hu243] at h2
    have h3 : |z i - x i| ≤ |z i - (y i + u * ((innerIdx ((x i - y i) / u) : ℤ) : ℝ))|
        + |u * ((innerIdx ((x i - y i) / u) : ℤ) : ℝ) - (x i - y i)| := by
      have := abs_add_le (z i - (y i + u * ((innerIdx ((x i - y i) / u) : ℤ) : ℝ)))
        (u * ((innerIdx ((x i - y i) / u) : ℤ) : ℝ) - (x i - y i))
      calc |z i - x i|
          = |(z i - (y i + u * ((innerIdx ((x i - y i) / u) : ℤ) : ℝ)))
              + (u * ((innerIdx ((x i - y i) / u) : ℤ) : ℝ) - (x i - y i))| := by ring_nf
        _ ≤ _ := this
    have hfin : (6 : ℝ) * u ≤ a / 16 := by rw [hudef]; linarith [hapos]
    linarith

private theorem localCubeGeometry_chain (y : Vec d) {A B s a tP : ℝ} {j1 j2 K : ℕ}
    {Bp Bb Ac : (Fin d → ℤ) → Cube d} {PI AI : Set (Fin d → ℤ)}
    (hAdef : A = (3 : ℝ) ^ j1) (hBdef : B = (3 : ℝ) ^ j2)
    (hApos : 0 < A) (hBpos : 0 < B) (hapos : 0 < a)
    (htPdef : tP = a / 2) (hsa : s = A * B * a)
    (hPIdef : PI = boxIdx d K)
    (hmemBp : ∀ (N : Fin d → ℤ) (z : Vec d),
      z ∈ cubeSet (Bp N) ↔ ∀ i, |z i - (y i + tP * (N i : ℝ))| < a / 2)
    (hmemV : ∀ z : Vec d,
      z ∈ middleQuarter ((y, s) : Cube d) ↔ ∀ i, |z i - y i| < s / 8)
    (hnearP : ∀ x : Vec d, (∀ i, |x i - y i| < s / 8) →
      (∀ i, |(nearestIdx y tP x i : ℤ)| ≤ (K : ℤ)) ∧
        (∀ i, |x i - (y i + tP * ((nearestIdx y tP x i : ℤ) : ℝ))| ≤ tP / 2))
    (hAnear : ∀ x : Vec d, (∀ i, |x i - y i| < s / 8) →
      ∃ N ∈ AI, cubeSet (Ac N) ⊆ centeredAxisCube x (a / 8))
    (hAquarter : ∀ N ∈ AI, ∀ z : Vec d, z ∈ cubeSet (Ac N) → ∀ c, |z c - y c| < s / 8) :
    ∀ x ∈ middleQuarter ((y, s) : Cube d), ∀ y' ∈ middleQuarter ((y, s) : Cube d),
      ∃ (k : ℕ) (ch : ℕ → Cube d),
        (∀ i ≤ k, ∃ p ∈ (fun N => (Bp N, Bb N)) '' PI, ch i = p.1) ∧
        x ∈ cubeSet (ch 0) ∧ y' ∈ cubeSet (ch k) ∧
        ∀ i < k, ∃ Q ∈ Ac '' AI,
          cubeSet Q ⊆ cubeSet (ch i) ∩ cubeSet (ch (i + 1)) ∩ middleQuarter ((y, s) : Cube d) := by
  intro x hx y' hy'
  rw [hmemV] at hx hy'
  obtain ⟨kk, hkk⟩ : ∃ k : ℕ, k = 4 * 3 ^ (j1 + j2) := ⟨_, rfl⟩
  have hkkpos : 0 < kk := by rw [hkk]; positivity
  have hkkR : (kk : ℝ) = 4 * (A * B) := by
    rw [hkk, hAdef, hBdef, ← pow_add]; push_cast; ring
  have hkkne : (kk : ℝ) ≠ 0 := by
    rw [hkkR]; positivity
  obtain ⟨pt, hptdef⟩ : ∃ f : ℕ → Vec d,
      f = fun (i : ℕ) (c : Fin d) => x c + ((i : ℝ) / (kk : ℝ)) * (y' c - x c) := ⟨_, rfl⟩
  have hptV : ∀ i, i ≤ kk → ∀ c, |pt i c - y c| < s / 8 := by
    intro i hi c
    have hθ0 : (0 : ℝ) ≤ (i : ℝ) / (kk : ℝ) := by positivity
    have hθ1 : (i : ℝ) / (kk : ℝ) ≤ 1 := by
      rw [div_le_one (by rw [hkkR]; positivity)]
      exact_mod_cast hi
    have hxc := hx c
    have hyc := hy' c
    have hM1 : |x c - y c| ≤ max |x c - y c| |y' c - y c| := le_max_left _ _
    have hM2 : |y' c - y c| ≤ max |x c - y c| |y' c - y c| := le_max_right _ _
    have hMlt : max |x c - y c| |y' c - y c| < s / 8 := max_lt hxc hyc
    have hxl := abs_le.mp hM1
    have hyl := abs_le.mp hM2
    have hth : (0 : ℝ) ≤ 1 - (i : ℝ) / (kk : ℝ) := by linarith
    rw [hptdef]
    simp only
    rw [abs_lt]
    constructor
    · nlinarith [mul_nonneg hth (by linarith [hxl.1] :
          (0 : ℝ) ≤ (x c - y c) + max |x c - y c| |y' c - y c|),
        mul_nonneg hθ0 (by linarith [hyl.1] :
          (0 : ℝ) ≤ (y' c - y c) + max |x c - y c| |y' c - y c|)]
    · nlinarith [mul_nonneg hth (by linarith [hxl.2] :
          (0 : ℝ) ≤ max |x c - y c| |y' c - y c| - (x c - y c)),
        mul_nonneg hθ0 (by linarith [hyl.2] :
          (0 : ℝ) ≤ max |x c - y c| |y' c - y c| - (y' c - y c))]
  have hpt0 : pt 0 = x := by
    rw [hptdef]; funext c; simp
  have hptk : pt kk = y' := by
    rw [hptdef]; funext c
    simp only
    rw [div_self hkkne]
    ring
  have hstep : ∀ i, ∀ c, |pt i c - pt (i + 1) c| ≤ a / 16 := by
    intro i c
    have hd : pt i c - pt (i + 1) c = -((1 : ℝ) / (kk : ℝ)) * (y' c - x c) := by
      rw [hptdef]
      simp only
      push_cast
      field_simp
      ring
    have hyx : |y' c - x c| ≤ s / 4 := by
      have h1 := hx c
      have h2 := hy' c
      rw [abs_le]
      rw [abs_lt] at h1 h2
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rw [hd, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < (1:ℝ)/(kk:ℝ))]
    rw [hkkR]
    have hABpos : (0 : ℝ) < A * B := mul_pos hApos hBpos
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith [hsa, hapos, hABpos, abs_nonneg (y' c - x c)]
  refine ⟨kk, fun i => Bp (nearestIdx y tP (pt i)), ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨(Bp (nearestIdx y tP (pt i)), Bb (nearestIdx y tP (pt i))),
      ⟨nearestIdx y tP (pt i), by
        rw [hPIdef]; exact (hnearP (pt i) (hptV i hi)).1, rfl⟩, rfl⟩
  · show x ∈ cubeSet (Bp (nearestIdx y tP (pt 0)))
    rw [hpt0, hmemBp]
    intro i
    have h := (hnearP x hx).2 i
    have htPq : tP / 2 < a / 2 := by rw [htPdef]; linarith [hapos]
    linarith
  · show y' ∈ cubeSet (Bp (nearestIdx y tP (pt kk)))
    rw [hptk, hmemBp]
    intro i
    have h := (hnearP y' hy').2 i
    have htPq : tP / 2 < a / 2 := by rw [htPdef]; linarith [hapos]
    linarith
  · intro i hi
    obtain ⟨N0, hN0, hsub⟩ := hAnear (pt i) (hptV i (le_of_lt hi))
    refine ⟨Ac N0, ⟨N0, hN0, rfl⟩, ?_⟩
    intro z hz
    have hzball := hsub hz
    rw [mem_centeredAxisCube] at hzball
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hmemBp]
      intro c
      have h1 := hzball c
      have h2 := (hnearP (pt i) (hptV i (le_of_lt hi))).2 c
      have htPq : tP / 2 = a / 4 := by rw [htPdef]; ring
      have h3 : |z c - (y c + tP * ((nearestIdx y tP (pt i) c : ℤ) : ℝ))|
          ≤ |z c - pt i c| + |pt i c - (y c + tP * ((nearestIdx y tP (pt i) c : ℤ) : ℝ))| := by
        calc |z c - (y c + tP * ((nearestIdx y tP (pt i) c : ℤ) : ℝ))|
            = |(z c - pt i c) + (pt i c - (y c + tP * ((nearestIdx y tP (pt i) c : ℤ) : ℝ)))| := by
              ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
    · rw [hmemBp]
      intro c
      have h1 := hzball c
      have h2 := (hnearP (pt (i + 1)) (hptV (i + 1) hi)).2 c
      have htPq : tP / 2 = a / 4 := by rw [htPdef]; ring
      have h4 := hstep i c
      have h3 : |z c - (y c + tP * ((nearestIdx y tP (pt (i+1)) c : ℤ) : ℝ))|
          ≤ |z c - pt i c| + |pt i c - pt (i+1) c|
            + |pt (i+1) c - (y c + tP * ((nearestIdx y tP (pt (i+1)) c : ℤ) : ℝ))| := by
        calc |z c - (y c + tP * ((nearestIdx y tP (pt (i+1)) c : ℤ) : ℝ))|
            = |((z c - pt i c) + (pt i c - pt (i+1) c))
                + (pt (i+1) c - (y c + tP * ((nearestIdx y tP (pt (i+1)) c : ℤ) : ℝ)))| := by
              ring_nf
          _ ≤ |(z c - pt i c) + (pt i c - pt (i+1) c)|
                + |pt (i+1) c - (y c + tP * ((nearestIdx y tP (pt (i+1)) c : ℤ) : ℝ))| :=
              abs_add_le _ _
          _ ≤ _ := by
              have := abs_add_le (z c - pt i c) (pt i c - pt (i+1) c)
              linarith
      linarith
    · rw [hmemV]
      exact hAquarter N0 hN0 z hz

private theorem exists_localCubeGeometryScales (n j1 j2 : ℕ)
    (hj1 : 2 ≤ j1) (hj2 : 1 ≤ j2) :
    ∃ A B s a u tP tQ : ℝ,
      A = (3 : ℝ) ^ j1 ∧
      B = (3 : ℝ) ^ j2 ∧
      s = (3 : ℝ) ^ n ∧
      0 < A ∧
      0 < B ∧
      0 < s ∧
      9 ≤ A ∧
      3 ≤ B ∧
      27 ≤ A * B ∧
      a = s / (A * B) ∧
      0 < a ∧
      s = A * B * a ∧
      u = a / 486 ∧
      0 < u ∧
      tP = a / 2 ∧
      0 < tP ∧
      tQ = B * a / 8 ∧
      0 < tQ ∧
      (3 : ℝ) ^ (-(j1 : ℤ)) = 1 / A ∧
      (3 : ℝ) ^ (-(j2 : ℤ)) = 1 / B ∧
      s = (3 : ℝ) ^ (n : ℤ) ∧
      a = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ) - (j2 : ℤ)) ∧
      B * a = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ)) ∧
      a / 243 = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ) - (j2 : ℤ) - 5) := by
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (3 : ℝ) ^ j1 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = (3 : ℝ) ^ j2 := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (3 : ℝ) ^ n := ⟨_, rfl⟩
  have hApos : (0 : ℝ) < A := by rw [hAdef]; positivity
  have hBpos : (0 : ℝ) < B := by rw [hBdef]; positivity
  have hspos : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hA9 : (9 : ℝ) ≤ A := by
    rw [hAdef]
    calc (9 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
      _ ≤ (3 : ℝ) ^ j1 := pow_le_pow_right₀ (by norm_num) hj1
  have hB3 : (3 : ℝ) ≤ B := by
    rw [hBdef]
    calc (3 : ℝ) = (3 : ℝ) ^ 1 := by norm_num
      _ ≤ (3 : ℝ) ^ j2 := pow_le_pow_right₀ (by norm_num) hj2
  have hAB27 : (27 : ℝ) ≤ A * B := by nlinarith [hA9, hB3, hApos, hBpos]
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = s / (A * B) := ⟨_, rfl⟩
  have hapos : (0 : ℝ) < a := by rw [hadef]; positivity
  have hsa : s = A * B * a := by rw [hadef]; field_simp
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = a / 486 := ⟨_, rfl⟩
  have hupos : (0 : ℝ) < u := by rw [hudef]; positivity
  obtain ⟨tP, htPdef⟩ : ∃ t : ℝ, t = a / 2 := ⟨_, rfl⟩
  have htPpos : (0 : ℝ) < tP := by rw [htPdef]; positivity
  obtain ⟨tQ, htQdef⟩ : ∃ t : ℝ, t = B * a / 8 := ⟨_, rfl⟩
  have htQpos : (0 : ℝ) < tQ := by rw [htQdef]; positivity
  -- inverse powers, for the two side clauses
  have hAinv : (3 : ℝ) ^ (-(j1 : ℤ)) = 1 / A := by
    rw [hAdef, zpow_neg, ← zpow_natCast (3 : ℝ) j1]; simp
  have hBinv : (3 : ℝ) ^ (-(j2 : ℤ)) = 1 / B := by
    rw [hBdef, zpow_neg, ← zpow_natCast (3 : ℝ) j2]; simp
  -- sides as integer powers of three
  have hsz : s = (3 : ℝ) ^ ((n : ℤ)) := by rw [hsdef, zpow_natCast]
  have haz : a = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ) - (j2 : ℤ)) := by
    rw [hadef, hsz, hAdef, hBdef, ← zpow_natCast (3 : ℝ) j1, ← zpow_natCast (3 : ℝ) j2,
      ← zpow_add₀ h3ne, ← zpow_sub₀ h3ne]
    ring_nf
  have hBaz : B * a = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ)) := by
    rw [haz, hBdef, ← zpow_natCast (3 : ℝ) j2, ← zpow_add₀ h3ne]
    ring_nf
  have hAz : a / 243 = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ) - (j2 : ℤ) - 5) := by
    have h5 : (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ) - (j2 : ℤ) - 5)
        = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ) - (j2 : ℤ)) / (3 : ℝ) ^ (5 : ℤ) :=
      zpow_sub₀ h3ne _ _
    rw [h5, ← haz]
    norm_num
  exact ⟨A, B, s, a, u, tP, tQ, hAdef, hBdef, hsdef, hApos, hBpos, hspos,
    hA9, hB3, hAB27, hadef, hapos, hsa, hudef, hupos, htPdef, htPpos, htQdef,
    htQpos, hAinv, hBinv, hsz, haz, hBaz, hAz⟩



theorem exists_isLocalCubeGeometry (y : Vec d) (n j1 j2 : ℕ)
    (hj1 : 2 ≤ j1) (hj2 : 1 ≤ j2) :
    ∃ (grid : Finset (Vec d)) (Pfam : Set (Cube d × Cube d)) (Qfam Afam : Set (Cube d)),
      IsLocalCubeGeometry grid j1 j2 (y, (3 : ℝ) ^ n) Pfam Qfam Afam ∧
      (∀ Q ∈ Qfam, Q.2 ≤ (3 : ℝ) ^ n) ∧ (y = 0 → TriadicOffsets grid) := by
  classical
  obtain ⟨A, B, s, a, u, tP, tQ, hAdef, hBdef, hsdef, hApos, hBpos, hspos,
    hA9, hB3, hAB27, hadef, hapos, hsa, hudef, hupos, htPdef, htPpos, htQdef,
    htQpos, hAinv, hBinv, hsz, haz, hBaz, hAz⟩ := exists_localCubeGeometryScales n j1 j2 hj1 hj2
  -- the offset grid: the eight equal subdivisions of the side, at each of the
  -- four scales `s`, `B * a`, `a`, `a / 243` of the construction
  obtain ⟨mU, hmU⟩ : ∃ m : ℤ, m = (n : ℤ) := ⟨_, rfl⟩
  obtain ⟨mB, hmB⟩ : ∃ m : ℤ, m = (n : ℤ) - (j1 : ℤ) := ⟨_, rfl⟩
  obtain ⟨ma, hma⟩ : ∃ m : ℤ, m = (n : ℤ) - (j1 : ℤ) - (j2 : ℤ) := ⟨_, rfl⟩
  obtain ⟨mA, hmA⟩ : ∃ m : ℤ, m = (n : ℤ) - (j1 : ℤ) - (j2 : ℤ) - 5 := ⟨_, rfl⟩
  have h3mU : (3 : ℝ) ^ mU = s := by rw [hmU, ← hsz]
  have h3mB : (3 : ℝ) ^ mB = B * a := by rw [hmB, ← hBaz]
  have h3ma : (3 : ℝ) ^ ma = a := by rw [hma, ← haz]
  have h3mA : (3 : ℝ) ^ mA = a / 243 := by rw [hmA, ← hAz]
  obtain ⟨grid, hgriddef⟩ : ∃ g : Finset (Vec d),
      g = ((scaleOffsets y mU 8 ∪ scaleOffsets y mB 8) ∪ scaleOffsets y ma 8)
        ∪ scaleOffsets y mA 8 := ⟨_, rfl⟩
  have hsubU : scaleOffsets y mU 8 ⊆ grid := by
    rw [hgriddef]
    exact (Finset.subset_union_left.trans Finset.subset_union_left).trans
      Finset.subset_union_left
  have hsubB : scaleOffsets y mB 8 ⊆ grid := by
    rw [hgriddef]
    exact (Finset.subset_union_right.trans Finset.subset_union_left).trans
      Finset.subset_union_left
  have hsuba : scaleOffsets y ma 8 ⊆ grid := by
    rw [hgriddef]
    exact Finset.subset_union_right.trans Finset.subset_union_left
  have hsubA : scaleOffsets y mA 8 ⊆ grid := by
    rw [hgriddef]
    exact Finset.subset_union_right
  -- index bounds
  obtain ⟨J', hJ'⟩ : ∃ J', j1 + j2 = J' + 1 := ⟨j1 + j2 - 1, by omega⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = 3 ^ J' := ⟨_, rfl⟩
  have hKR : (K : ℝ) * 3 = A * B := by
    rw [hKdef, hAdef, hBdef, ← pow_add, hJ']
    push_cast; ring
  have hKpos : (0 : ℝ) < (K : ℝ) := by nlinarith only [hKR, mul_pos hApos hBpos]
  obtain ⟨KA, hKAdef⟩ : ∃ K : ℕ, K = 61 * 3 ^ (j1 + j2) := ⟨_, rfl⟩
  have hKAR : (KA : ℝ) = 61 * (A * B) := by
    rw [hKAdef, hAdef, hBdef, ← pow_add]; push_cast; ring
  -- the three cube families
  obtain ⟨Bp, hBpdef⟩ : ∃ f : (Fin d → ℤ) → Cube d,
      f = fun N => (latticeCentre y tP N, a) := ⟨_, rfl⟩
  obtain ⟨Bb, hBbdef⟩ : ∃ f : (Fin d → ℤ) → Cube d,
      f = fun N => (latticeCentre y tQ (nearestIdx y tQ (latticeCentre y tP N)),
        B * a) := ⟨_, rfl⟩
  have hBbdist : ∀ (N : Fin d → ℤ) (i : Fin d),
      |latticeCentre y tP N i
          - latticeCentre y tQ (nearestIdx y tQ (latticeCentre y tP N)) i| ≤ tQ / 2 :=
    fun N i => nearestIdx_close (y := y) (t := tQ) htQpos (latticeCentre y tP N) i
  obtain ⟨Ac, hAcdef⟩ : ∃ f : (Fin d → ℤ) → Cube d,
      f = fun N => (latticeCentre y u N, a / 243) := ⟨_, rfl⟩
  obtain ⟨PI, hPIdef⟩ : ∃ S : Set (Fin d → ℤ), S = boxIdx d K := ⟨_, rfl⟩
  obtain ⟨AI, hAIdef⟩ : ∃ S : Set (Fin d → ℤ),
      S = {N | ∀ i, u * |(N i : ℝ)| + (a / 243) / 2 ≤ s / 8} := ⟨_, rfl⟩
  have hPI_finite : PI.Finite := by rw [hPIdef]; exact finite_boxIdx d K
  have hAI_finite : AI.Finite := by
    refine Set.Finite.subset (finite_boxIdx d KA) ?_
    intro N hN i
    rw [hAIdef] at hN
    have h1 := hN i
    have h2 : u * |(N i : ℝ)| ≤ s / 8 := by
      have hp : (0 : ℝ) < (a / 243) / 2 := by positivity
      linarith only [h1, hp]
    refine idx_le_of_abs_le ?_
    rw [hKAR]
    rw [hudef] at h2
    nlinarith only [h2, hsa, hapos, hAB27, abs_nonneg ((N i : ℝ)), mul_pos (mul_pos hApos hBpos) hapos]
  -- membership characterisation of the cubes
  have hmemBp : ∀ (N : Fin d → ℤ) (z : Vec d),
      z ∈ cubeSet (Bp N) ↔ ∀ i, |z i - (y i + tP * (N i : ℝ))| < a / 2 := by
    intro N z; rw [hBpdef]; exact mem_centeredAxisCube
  have hmemAc : ∀ (N : Fin d → ℤ) (z : Vec d),
      z ∈ cubeSet (Ac N) ↔ ∀ i, |z i - (y i + u * (N i : ℝ))| < (a / 243) / 2 := by
    intro N z; rw [hAcdef]; exact mem_centeredAxisCube
  have hmemV : ∀ z : Vec d,
      z ∈ middleQuarter ((y, s) : Cube d) ↔ ∀ i, |z i - y i| < s / 8 := by
    intro z
    show z ∈ centeredAxisCube y (s / 4) ↔ _
    rw [mem_centeredAxisCube]
    constructor <;> intro h i <;> [skip; skip] <;> · have := h i; linarith only [this]
  -- the nearest paired cube of a point of the middle quarter
  have hnearP := localCubeGeometry_nearest y htPpos htPdef hsa hKR hAB27
  have hAquarter : ∀ N ∈ AI, ∀ z : Vec d, z ∈ cubeSet (Ac N) → ∀ c, |z c - y c| < s / 8 := by
    intro N hN z hz c
    rw [hmemAc] at hz
    have h1 := hz c
    have h2 := (hAIdef ▸ hN :
      N ∈ {N : Fin d → ℤ | ∀ i, u * |(N i : ℝ)| + (a / 243) / 2 ≤ s / 8}) c
    have h3 : |z c - y c| ≤ |z c - (y c + u * (N c : ℝ))| + |u * (N c : ℝ)| := by
      calc |z c - y c| = |(z c - (y c + u * (N c : ℝ))) + u * (N c : ℝ)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_mul, abs_of_pos hupos] at h3
    have hu243 : (a / 243) / 2 = u := by rw [hudef]; ring
    rw [hu243] at h2
    linarith only [h1, h2, h3, hu243]
  -- an `A`-cube inside a small neighbourhood of any point of the middle quarter
  have hAnear := localCubeGeometry_inner y hupos hudef hsa hAB27 hapos hAIdef hmemAc
  -- the geometry
  rw [← hsdef]
  refine ⟨grid, (fun N => (Bp N, Bb N)) '' PI,
    insert ((y, s) : Cube d) ((Bp '' PI) ∪ (Bb '' PI) ∪ (Ac '' AI)), Ac '' AI,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (((hPI_finite.image Bp).union (hPI_finite.image Bb)).union
      (hAI_finite.image Ac)).insert _
  · exact hPI_finite.image _
  · exact Set.mem_insert _ _
  · rintro Q (rfl | ((⟨N, _, rfl⟩ | ⟨N, _, rfl⟩) | ⟨N, _, rfl⟩))
    · exact hspos
    · rw [hBpdef]; exact hapos
    · rw [hBbdef]; positivity
    · rw [hAcdef]; positivity
  · rintro Q (rfl | ((⟨N, _, rfl⟩ | ⟨N, _, rfl⟩) | ⟨N, _, rfl⟩))
    · show IsGridCube grid y s
      rw [← h3mU]
      exact isGridCube_centre (by norm_num) hsubU
    · rw [hBpdef]
      show IsGridCube grid (fun i => y i + tP * (N i : ℝ)) a
      rw [← h3ma]
      refine isGridCube_scaleOffsets (c := 4) (by norm_num) hsuba ?_ N
      rw [h3ma, htPdef]; push_cast; ring
    · rw [hBbdef]
      show IsGridCube grid
        (fun i => y i + tQ * ((nearestIdx y tQ (latticeCentre y tP N) i : ℤ) : ℝ))
        (B * a)
      rw [← h3mB]
      refine isGridCube_scaleOffsets (c := 1) (by norm_num) hsubB ?_
        (nearestIdx y tQ (latticeCentre y tP N))
      rw [h3mB, htQdef]; push_cast; ring
    · rw [hAcdef]
      show IsGridCube grid (fun i => y i + u * (N i : ℝ)) (a / 243)
      rw [← h3mA]
      refine isGridCube_scaleOffsets (c := 4) (by norm_num) hsubA ?_ N
      rw [h3mA, hudef]; push_cast; ring
  · rintro p ⟨N, hN, rfl⟩
    exact ⟨Set.mem_insert_of_mem _ (Or.inl (Or.inl ⟨N, hN, rfl⟩)),
      Set.mem_insert_of_mem _ (Or.inl (Or.inr ⟨N, hN, rfl⟩))⟩
  · rintro p ⟨N, hN, rfl⟩
    show closure (cubeSet (Bp N)) ⊆ cubeSet (Bb N)
    rw [hBpdef, hBbdef]
    refine closure_centeredAxisCube_subset_of_dist (r := tQ / 2) (hBbdist N) ?_
    rw [htQdef]
    nlinarith only [hB3, hapos]
  · rintro p ⟨N, hN, rfl⟩
    show cubeSet (Bp N) ⊆ centeredAxisCube (Bb N).1 ((Bb N).2 / 2)
    rw [hBpdef, hBbdef]
    refine centeredAxisCube_subset_of_dist (r := tQ / 2) (hBbdist N) ?_
    rw [htQdef]
    nlinarith only [hB3, hapos]
  · rintro p ⟨N, hN, rfl⟩
    show cubeSet (Bb N) ⊆ centeredAxisCube ((y, s) : Cube d).1 (((y, s) : Cube d).2 / 2)
    have hNi : ∀ i, |(N i : ℝ)| ≤ (K : ℝ) := by
      intro i
      have := (hPIdef ▸ hN : N ∈ boxIdx d K) i
      have h' : ((|N i| : ℤ) : ℝ) ≤ ((K : ℤ) : ℝ) := by exact_mod_cast this
      rw [Int.cast_abs] at h'
      exact_mod_cast h'
    have hKval : (K : ℝ) = A * B / 3 := by linarith only [hKR]
    have h6 : tP * (K : ℝ) = s / 6 := by rw [htPdef, hKval, hsa]; ring
    have hd : ∀ i, |latticeCentre y tQ (nearestIdx y tQ (latticeCentre y tP N)) i - y i|
        ≤ tQ / 2 + s / 6 := by
      intro i
      have h2 := hBbdist N i
      have h3 : |latticeCentre y tP N i - y i| = tP * |(N i : ℝ)| := by
        show |y i + tP * (N i : ℝ) - y i| = tP * |(N i : ℝ)|
        rw [show y i + tP * (N i : ℝ) - y i = tP * (N i : ℝ) by ring, abs_mul,
          abs_of_pos htPpos]
      have h5 : tP * |(N i : ℝ)| ≤ tP * (K : ℝ) :=
        mul_le_mul_of_nonneg_left (hNi i) (le_of_lt htPpos)
      have h4 : |latticeCentre y tQ (nearestIdx y tQ (latticeCentre y tP N)) i - y i|
          ≤ |latticeCentre y tQ (nearestIdx y tQ (latticeCentre y tP N)) i
              - latticeCentre y tP N i| + |latticeCentre y tP N i - y i| := by
        calc |latticeCentre y tQ (nearestIdx y tQ (latticeCentre y tP N)) i - y i|
            = |(latticeCentre y tQ (nearestIdx y tQ (latticeCentre y tP N)) i
                - latticeCentre y tP N i) + (latticeCentre y tP N i - y i)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      rw [abs_sub_comm] at h2
      linarith only [h2, h3, h4, h5, h6]
    rw [hBbdef]
    refine centeredAxisCube_subset_of_dist (r := tQ / 2 + s / 6) hd ?_
    have hBa : (0 : ℝ) < B * a := mul_pos hBpos hapos
    rw [htQdef, hsa]
    nlinarith only [hBa, mul_nonneg (sub_nonneg.mpr hA9) hBa.le]
  · rintro p ⟨N, hN, rfl⟩
    show (Bb N).2 = (3 : ℝ) ^ (-(j1 : ℤ)) * ((y, s) : Cube d).2
    rw [hBbdef, hAinv]
    show B * a = 1 / A * s
    rw [hsa]; field_simp
  · rintro p ⟨N, hN, rfl⟩
    show (Bp N).2 = (3 : ℝ) ^ (-(j2 : ℤ)) * (Bb N).2
    rw [hBpdef, hBbdef, hBinv]
    show a = 1 / B * (B * a)
    field_simp
  · intro x hx
    rw [hmemV] at hx
    obtain ⟨hidx, hdist⟩ := hnearP x hx
    have hp : ((Bp (nearestIdx y tP x), Bb (nearestIdx y tP x)) : Cube d × Cube d)
        ∈ (fun N => (Bp N, Bb N)) '' PI := ⟨nearestIdx y tP x, by rw [hPIdef]; exact hidx, rfl⟩
    have hx' : x ∈ cubeSet (Bp (nearestIdx y tP x)) := by
      rw [hmemBp]
      intro i
      have hdi : |x i - (y i + tP * ((nearestIdx y tP x i : ℤ) : ℝ))| ≤ tP / 2 := hdist i
      have htp : tP / 2 < a / 2 := by rw [htPdef]; linarith only [hapos]
      linarith only [hdi, htp]
    exact Set.mem_biUnion hp hx'
  · exact fun Q hQ => Set.mem_insert_of_mem _ (Or.inr hQ)
  · rintro Q ⟨N, hN, rfl⟩
    intro z hz
    rw [hmemV]
    exact hAquarter N hN z hz
  · exact localCubeGeometry_chain y hAdef hBdef hApos hBpos hapos htPdef hsa
      hPIdef hmemBp hmemV hnearP hAnear hAquarter
  · -- every family cube is at most as wide as the parent
    rintro Q (rfl | ((⟨N, _, rfl⟩ | ⟨N, _, rfl⟩) | ⟨N, _, rfl⟩))
    · exact le_rfl
    · rw [hBpdef]
      show a ≤ s
      nlinarith only [hsa, hAB27, hapos]
    · rw [hBbdef]
      show B * a ≤ s
      nlinarith only [hsa, hA9, mul_pos hBpos hapos]
    · rw [hAcdef]
      show a / 243 ≤ s
      nlinarith only [hsa, hAB27, hapos]
  · -- at the origin the offset family is closed under triadic descent
    rintro rfl
    rw [hgriddef, scaleOffsets_zero mB mU, scaleOffsets_zero ma mU,
      scaleOffsets_zero mA mU]
    simp only [Finset.union_self]
    exact triadicOffsets_scaleOffsets_zero d mU

/-! ## The smallness clause and the assembled deterministic fragment -/



theorem exists_smallness_depth (C eta : ℝ) (hC : 0 < C) (heta : 0 < eta) :
    ∃ j1 : ℕ, 2 ≤ j1 ∧ C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (2 * C / eta) h3
  have h3p : (0 : ℝ) < (3 : ℝ) ^ (j : ℕ) := pow_pos (by norm_num) j
  have key : (2 : ℝ) * C < eta * (3 : ℝ) ^ (j : ℕ) := by
    rw [div_lt_iff₀ heta] at hj
    linarith
  set j1 := max j 2 with hj1def
  have h2j1 : 2 ≤ j1 := le_max_right _ _
  have h0 : (0 : ℝ) ≤ (j1 : ℝ) := by positivity
  have hexp : -(3 * (j1 : ℝ) / 2) ≤ -((j1 : ℝ)) := by linarith
  have hpow : (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ ((3 : ℝ) ^ (j1 : ℕ))⁻¹ := by
    have h1 := Real.rpow_le_rpow_of_exponent_le (le_of_lt h3) hexp
    have h2 : (3 : ℝ) ^ (-(j1 : ℝ)) = ((3 : ℝ) ^ (j1 : ℕ))⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
    rwa [h2] at h1
  have key1 : (2 : ℝ) * C < eta * (3 : ℝ) ^ (j1 : ℕ) := by
    have hle : (3 : ℝ) ^ (j : ℕ) ≤ (3 : ℝ) ^ (j1 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (le_max_left j 2)
    nlinarith
  have hfin : C * ((3 : ℝ) ^ (j1 : ℕ))⁻¹ ≤ eta / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hp : (0 : ℝ) < (3 : ℝ) ^ (j1 : ℕ) := pow_pos (by norm_num) j1
    rw [inv_eq_one_div, mul_comm C, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div,
      div_le_iff₀ hp]
    nlinarith
  refine ⟨j1, h2j1, ?_⟩
  calc C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2))
      ≤ C * ((3 : ℝ) ^ (j1 : ℕ))⁻¹ := mul_le_mul_of_nonneg_left hpow hC.le
    _ ≤ eta / 2 := hfin

/-- **The assembled deterministic fragment of the anchor.**  Clauses 5 and 6 of
`SubdiffusiveProcess.Frozen.Section9.weighted_good_cube_events` hold jointly for the depths
`(j₁, 1)` produced here, for every constant `C` the probabilistic and analytic
parts may supply: the smallness of `C·3^{-3j₁/2}` forces `j₁` large, and the
geometry exists for every `j₁ ≥ 2`, so the two clauses do not compete. -/
theorem exists_depth_geometry_of_constant (d : ℕ) (C eta : ℝ) (hC : 0 < C)
    (heta : 0 < eta) :
    ∃ j1 j2 : ℕ, 2 ≤ j1 ∧ 1 ≤ j2 ∧
      C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
      ∀ (n : ℕ) (z : SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.Lattice d),
        ∃ (grid : Finset (Vec d)) (Pfam : Set (Cube d × Cube d))
          (Qfam Afam : Set (Cube d)),
          IsLocalCubeGeometry grid j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
            Pfam Qfam Afam := by
  obtain ⟨j1, hj1, hsmall⟩ := exists_smallness_depth C eta hC heta
  refine ⟨j1, 1, hj1, le_rfl, hsmall, fun n z => ?_⟩
  obtain ⟨grid, Pfam, Qfam, Afam, hgeo, -, -⟩ :=
    exists_isLocalCubeGeometry (goodCubeCentre n z) n j1 1 hj1 le_rfl
  exact ⟨grid, Pfam, Qfam, Afam, hgeo⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
