module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

variable {d : ℕ}

/-- The lattice `ℤ^d` used in the Section 9 percolation construction. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- The canonical embedding of a lattice site into physical space. -/
def latticeToVec (z : Lattice d) : Fin d → ℝ :=
  fun i => (z i : ℝ)

/-- The `ℕ`-valued `\ell^\infty` distance on `ℤ^d`. -/
def latticeDist (x y : Lattice d) : ℕ :=
  Finset.univ.sup fun i => (x i - y i).natAbs

/-- Every coordinate difference is bounded by the lattice distance. -/
theorem coord_le_latticeDist (x y : Lattice d) (i : Fin d) :
    (x i - y i).natAbs ≤ latticeDist x y :=
  Finset.le_sup (f := fun i => (x i - y i).natAbs) (Finset.mem_univ i)

/-- Coordinatewise characterization of a lattice-distance bound. -/
theorem latticeDist_le_iff {x y : Lattice d} {r : ℕ} :
    latticeDist x y ≤ r ↔ ∀ i, (x i - y i).natAbs ≤ r :=
  ⟨fun h i => (coord_le_latticeDist x y i).trans h,
    fun h => Finset.sup_le fun i _ => h i⟩

@[simp]
theorem latticeDist_self (x : Lattice d) : latticeDist x x = 0 :=
  Nat.le_zero.mp (Finset.sup_le fun i _ => by simp)

theorem latticeDist_comm (x y : Lattice d) : latticeDist x y = latticeDist y x :=
  Finset.sup_congr rfl fun i _ => by rw [← Int.natAbs_neg, neg_sub]

theorem latticeDist_triangle (x y z : Lattice d) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  refine Finset.sup_le fun i _ => ?_
  have hsplit : x i - z i = (x i - y i) + (y i - z i) :=
    (sub_add_sub_cancel (x i) (y i) (z i)).symm
  calc
    (x i - z i).natAbs ≤ (x i - y i).natAbs + (y i - z i).natAbs := by
      rw [hsplit]
      exact Int.natAbs_add_le _ _
    _ ≤ latticeDist x y + latticeDist y z :=
      Nat.add_le_add (coord_le_latticeDist x y i) (coord_le_latticeDist y z i)



def IsJStepPath (J : ℕ) (x : ℕ → Lattice d) (N : ℕ) : Prop :=
  ∀ i, i < N → latticeDist (x i) (x (i + 1)) ≤ J

theorem IsJStepPath.mono {J N M : ℕ} {x : ℕ → Lattice d}
    (h : IsJStepPath J x N) (hMN : M ≤ N) : IsJStepPath J x M :=
  fun i hi => h i (hi.trans_le hMN)

theorem IsJStepPath.shift {J N : ℕ} {x : ℕ → Lattice d}
    (h : IsJStepPath J x N) (a M : ℕ) (hle : a + M ≤ N) :
    IsJStepPath J (fun i => x (a + i)) M := by
  intro i hi
  have hlt : a + i < N := by omega
  simpa only [Nat.add_assoc] using h (a + i) hlt

/-- Along a `J`-step path, distance from a fixed center can increase by at
most `J` in one step. -/
theorem IsJStepPath.latticeDist_succ_le {J N : ℕ} {x : ℕ → Lattice d}
    (h : IsJStepPath J x N) (z : Lattice d) {i : ℕ} (hi : i < N) :
    latticeDist z (x (i + 1)) ≤ latticeDist z (x i) + J :=
  (latticeDist_triangle z (x i) (x (i + 1))).trans
    (Nat.add_le_add_left (h i hi) _)

/-- The closed `\ell^\infty` lattice ball used below. -/
def InLatticeBall (z v : Lattice d) (r : ℕ) : Prop :=
  latticeDist z v ≤ r

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
