import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ExitTime




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

variable {Omega : Type*} {d : ℕ}



structure GoodCubeEvents (Omega : Type*) (d : ℕ) where
  /-- The paper's local good event `G(U)` for the cube indexed by `(n, z)`. -/
  localGood : ℕ → Vec d → Set Omega
  

  longBad : ℕ → ℕ → Vec d → Set Omega

/-- The event on which `translatedCube d (n : ℤ) z` is good. -/
def GoodCubeEvents.goodEvent (E : GoodCubeEvents Omega d) (n : ℕ) (z : Vec d) :
    Set Omega :=
  E.localGood n z ∩ ⋂ j : {j : ℕ // 1 ≤ j}, (E.longBad j n z)ᶜ

/-- The paper's good-cube predicate: the local event occurs and no bad event at an offset
`j ≥ 1` occurs. -/
def IsGoodCube (E : GoodCubeEvents Omega d) (omega : Omega) (n : ℕ) (z : Vec d) : Prop :=
  omega ∈ E.localGood n z ∧ ∀ j : ℕ, 1 ≤ j → omega ∉ E.longBad j n z

theorem isGoodCube_iff (E : GoodCubeEvents Omega d) (omega : Omega) (n : ℕ) (z : Vec d) :
    IsGoodCube E omega n z ↔
      omega ∈ E.localGood n z ∧ ∀ j : ℕ, 1 ≤ j → omega ∉ E.longBad j n z :=
  Iff.rfl

theorem mem_goodEvent_iff (E : GoodCubeEvents Omega d) (omega : Omega) (n : ℕ)
    (z : Vec d) : omega ∈ E.goodEvent n z ↔ IsGoodCube E omega n z := by
  simp only [GoodCubeEvents.goodEvent, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, IsGoodCube]
  constructor
  · rintro ⟨hlocal, hbad⟩
    exact ⟨hlocal, fun j hj ↦ hbad ⟨j, hj⟩⟩
  · rintro ⟨hlocal, hbad⟩
    exact ⟨hlocal, fun j ↦ hbad j j.property⟩

/-- A good cube satisfies its local event. -/
theorem IsGoodCube.localGood {E : GoodCubeEvents Omega d} {omega : Omega} {n : ℕ}
    {z : Vec d} (h : IsGoodCube E omega n z) : omega ∈ E.localGood n z :=
  h.1



theorem IsGoodCube.notMem_longBad {E : GoodCubeEvents Omega d} {omega : Omega} {n j : ℕ}
    {z : Vec d} (h : IsGoodCube E omega n z) (hj : 1 ≤ j) : omega ∉ E.longBad j n z :=
  h.2 j hj



theorem IsGoodCube.mk {E : GoodCubeEvents Omega d} {omega : Omega} {n : ℕ} {z : Vec d}
    (hlocal : omega ∈ E.localGood n z)
    (hbad : ∀ j : ℕ, 1 ≤ j → omega ∉ E.longBad j n z) :
    IsGoodCube E omega n z :=
  ⟨hlocal, hbad⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
