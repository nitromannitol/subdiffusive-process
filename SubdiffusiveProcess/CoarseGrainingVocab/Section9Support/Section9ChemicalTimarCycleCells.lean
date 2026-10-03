module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarSeparation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-! ## Unit cube cells -/

/-- The unit cube cell with lower corner `a`: the `2^d` sites `∏ᵢ {aᵢ, aᵢ + 1}`. -/
def unitCubeCell (a : Lattice d) : Set (Lattice d) := {x | ∀ i, x i = a i ∨ x i = a i + 1}

theorem mem_unitCubeCell_iff {a x : Lattice d} :
    x ∈ unitCubeCell a ↔ ∀ i, x i = a i ∨ x i = a i + 1 := Iff.rfl

/-- Every unit cube cell is a `1`-step clique. -/
theorem latticeDist_le_one_of_mem_unitCubeCell {a x y : Lattice d}
    (hx : x ∈ unitCubeCell a) (hy : y ∈ unitCubeCell a) : latticeDist x y ≤ 1 := by
  refine latticeDist_le_iff.mpr fun i => ?_
  have h1 := hx i
  have h2 := hy i
  omega

/-- Two `1`-step adjacent sites lie in a common unit cube cell: the corner `min x y`. -/
theorem exists_unitCubeCell_of_latticeDist_le_one {x y : Lattice d}
    (h : latticeDist x y ≤ 1) : ∃ a : Lattice d, x ∈ unitCubeCell a ∧ y ∈ unitCubeCell a := by
  refine ⟨fun i => min (x i) (y i), fun i => ?_, fun i => ?_⟩
  · have := latticeDist_le_iff.mp h i
    show x i = min (x i) (y i) ∨ x i = min (x i) (y i) + 1
    omega
  · have := latticeDist_le_iff.mp h i
    show y i = min (x i) (y i) ∨ y i = min (x i) (y i) + 1
    omega



theorem latticeDist_le_one_iff_exists_unitCubeCell {x y : Lattice d} :
    latticeDist x y ≤ 1 ↔ ∃ a : Lattice d, x ∈ unitCubeCell a ∧ y ∈ unitCubeCell a :=
  ⟨exists_unitCubeCell_of_latticeDist_le_one,
    fun ⟨_, hx, hy⟩ => latticeDist_le_one_of_mem_unitCubeCell hx hy⟩

/-! ## The step map -/

/-- One `ℓ^∞` step from `x` towards `t`: every coordinate moves by one towards its target. -/
def latticeStepToward (t x : Lattice d) : Lattice d :=
  fun i => x i + (if x i < t i then 1 else if t i < x i then -1 else 0)

/-- The step map moves by a single `1`-step. -/
theorem latticeDist_latticeStepToward_le_one (t x : Lattice d) :
    latticeDist x (latticeStepToward t x) ≤ 1 := by
  refine latticeDist_le_iff.mpr fun i => ?_
  simp only [latticeStepToward]
  split_ifs <;> omega

/-- The step map decreases the distance to its target by one. -/
theorem latticeDist_latticeStepToward_le_pred {t x : Lattice d} {m : ℕ}
    (h : latticeDist x t ≤ m) : latticeDist (latticeStepToward t x) t ≤ m - 1 := by
  refine latticeDist_le_iff.mpr fun i => ?_
  have := latticeDist_le_iff.mp h i
  simp only [latticeStepToward]
  split_ifs <;> omega

/-- **The step map is nonexpansive**, hence carries `1`-step paths to `1`-step paths. -/
theorem latticeDist_latticeStepToward_le (t x y : Lattice d) :
    latticeDist (latticeStepToward t x) (latticeStepToward t y) ≤ latticeDist x y := by
  refine latticeDist_le_iff.mpr fun i => ?_
  have := coord_le_latticeDist x y i
  simp only [latticeStepToward]
  split_ifs <;> omega

/-! ## The descent onto the inner boundary -/

/-- A site of `K` adjacent to a site off `K` lies on the inner boundary of `K`. -/
theorem mem_innerBoundary_of_dist {K : Set (Lattice d)} {x u : Lattice d}
    (hx : x ∈ K) (hu : u ∉ K) (h : latticeDist x u ≤ 1) : x ∈ innerBoundary K :=
  ⟨hx, u, hu, by rwa [latticeDist_comm]⟩

/-- **The visible boundary is a `1`-step retract of the component it bounds.**  Every site of
`K` is joined, by a `1`-step path *inside* `K`, to a site of `innerBoundary K`: walk straight
towards any site off `K` until the next step would leave `K`. -/
theorem exists_mem_innerBoundary_jStepReachableIn {K : Set (Lattice d)} {t : Lattice d}
    (ht : t ∉ K) : ∀ (n : ℕ) (x : Lattice d), x ∈ K → latticeDist x t ≤ n →
      ∃ y ∈ innerBoundary K, JStepReachableIn 1 K x y := by
  intro n
  induction n with
  | zero =>
    intro x hx hn
    exact ⟨x, mem_innerBoundary_of_dist hx ht (by omega),
      jStepReachableIn_of_dist hx hx (by simp)⟩
  | succ n ih =>
    intro x hx hn
    by_cases h' : latticeStepToward t x ∈ K
    · have hdist : latticeDist (latticeStepToward t x) t ≤ n := by
        simpa using latticeDist_latticeStepToward_le_pred (t := t) (x := x) hn
      obtain ⟨y, hy, hpath⟩ := ih (latticeStepToward t x) h' hdist
      exact ⟨y, hy,
        (jStepReachableIn_of_dist hx h' (latticeDist_latticeStepToward_le_one t x)).trans hpath⟩
    · exact ⟨x, mem_innerBoundary_of_dist hx h' (latticeDist_latticeStepToward_le_one t x),
        jStepReachableIn_of_dist hx hx (by simp)⟩

/-- The descent, in the form used downstream. -/
theorem exists_mem_innerBoundary_jStepReachableIn_of_mem {K : Set (Lattice d)} {x t : Lattice d}
    (hx : x ∈ K) (ht : t ∉ K) : ∃ y ∈ innerBoundary K, JStepReachableIn 1 K x y :=
  exists_mem_innerBoundary_jStepReachableIn ht (latticeDist x t) x hx le_rfl

/-- The inner boundary of a nonempty set with nonempty complement is nonempty. -/
theorem innerBoundary_nonempty {K : Set (Lattice d)} (hK : K.Nonempty) (hKc : Kᶜ.Nonempty) :
    (innerBoundary K).Nonempty := by
  obtain ⟨x, hx⟩ := hK
  obtain ⟨t, ht⟩ := hKc
  obtain ⟨y, hy, -⟩ := exists_mem_innerBoundary_jStepReachableIn_of_mem hx ht
  exact ⟨y, hy⟩

/-- The visible boundary of a set, seen from a site off it, is nonempty. -/
theorem visibleBoundary_nonempty {S : Set (Lattice d)} {c : Lattice d} (hS : S.Nonempty)
    (hc : c ∉ S) : (visibleBoundary S c).Nonempty := by
  rw [visibleBoundary_eq_innerBoundary]
  refine innerBoundary_nonempty ⟨c, self_mem_jStepComponent hc⟩ ?_
  obtain ⟨s, hs⟩ := hS
  exact ⟨s, fun hmem => (jStepComponent_subset hmem) hs⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
