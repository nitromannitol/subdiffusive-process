module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarCycleCoboundary
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarCycleSplit

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-- A function constant across every admissible step of a set is constant along its paths. -/
theorem eq_of_jStepReachableIn_of_forall_adj {S : Set (Lattice d)} {α : Type*}
    {g : Lattice d → α} (hadj : ∀ x ∈ S, ∀ y ∈ S, latticeDist x y ≤ 1 → g x = g y)
    {u w : Lattice d} (h : JStepReachableIn 1 S u w) : g u = g w :=
  jStepReachableIn_induction (P := fun z => g u = g z) h rfl
    (fun x hx y hy hP hxy => hP.trans (hadj x hx y hy hxy))

/-- **`[Timár, Lemma 2]`, symmetric form, proved.**  If `ℤ^d` is split into two `1`-step
connected pieces, the inner boundary of either piece is `1`-step connected. -/
theorem jStepReachableIn_innerBoundary {K : Set (Lattice d)}
    (hKconn : ∀ u ∈ K, ∀ v ∈ K, JStepReachableIn 1 K u v)
    (hTconn : ∀ u ∈ Kᶜ, ∀ v ∈ Kᶜ, JStepReachableIn 1 Kᶜ u v)
    {u₀ v : Lattice d} (hu₀ : u₀ ∈ innerBoundary K) (hv : v ∈ innerBoundary K) :
    JStepReachableIn 1 (innerBoundary K) u₀ v := by
  classical
  by_contra hcon
  set B : Set (Lattice d) := innerBoundary K with hBdef
  set B₁ : Set (Lattice d) := {x | x ∈ B ∧ JStepReachableIn 1 B u₀ x} with hB1def
  have hB1B : B₁ ⊆ B := fun w hw => hw.1
  have hBK : B ⊆ K := fun w hw => hw.1
  have hu₀B1 : u₀ ∈ B₁ := ⟨hu₀, jStepReachableIn_self_iff.mpr hu₀⟩
  have hvB1 : v ∉ B₁ := fun h => hcon h.2
  -- a boundary site adjacent to `B₁` is in `B₁`
  have hext : ∀ w ∈ B, ∀ p ∈ B₁, latticeDist p w ≤ 1 → w ∈ B₁ := fun w hw p hp hpw =>
    ⟨hw, hp.2.trans (jStepReachableIn_of_dist (hB1B hp) hw hpw)⟩
  -- the cut cochain and the indicator of `Kᶜ`
  obtain ⟨ω, hωdef⟩ : ∃ ω : Lattice d → Lattice d → ZMod 2, ∀ a b : Lattice d,
      ω a b = if (a ∈ B₁ ∧ b ∈ Kᶜ) ∨ (b ∈ B₁ ∧ a ∈ Kᶜ) then 1 else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨χ, hχdef⟩ : ∃ χ : Lattice d → ZMod 2, ∀ a : Lattice d,
      χ a = if a ∈ Kᶜ then 1 else 0 := ⟨_, fun _ => rfl⟩
  have hω0 : ∀ a b : Lattice d, ¬((a ∈ B₁ ∧ b ∈ Kᶜ) ∨ (b ∈ B₁ ∧ a ∈ Kᶜ)) → ω a b = 0 :=
    fun a b h => by rw [hωdef]; exact if_neg h
  have hω1 : ∀ a b : Lattice d, ((a ∈ B₁ ∧ b ∈ Kᶜ) ∨ (b ∈ B₁ ∧ a ∈ Kᶜ)) → ω a b = 1 :=
    fun a b h => by rw [hωdef]; exact if_pos h
  have hB1K : ∀ a : Lattice d, a ∈ B₁ → a ∉ Kᶜ := fun a ha hc => hc (hBK (hB1B ha))
  have hωK : ∀ a b : Lattice d, a ∈ K → b ∈ K → ω a b = 0 := by
    intro a b ha hb
    refine hω0 a b ?_
    rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact h hb
    · exact h ha
  have hωT : ∀ a b : Lattice d, a ∈ Kᶜ → b ∈ Kᶜ → ω a b = 0 := by
    intro a b ha hb
    refine hω0 a b ?_
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hB1K a h ha
    · exact hB1K b h hb
  -- on sites of `B₁ ∪ Kᶜ` the cochain is the coboundary of the indicator of `Kᶜ`
  have hpair : ∀ a b : Lattice d, (a ∈ B₁ ∨ a ∈ Kᶜ) → (b ∈ B₁ ∨ b ∈ Kᶜ) →
      ω a b = χ a + χ b := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [hωK a b (hBK (hB1B ha)) (hBK (hB1B hb)), hχdef, hχdef,
        if_neg (hB1K a ha), if_neg (hB1K b hb), add_zero]
    · rw [hω1 a b (Or.inl ⟨ha, hb⟩), hχdef, hχdef, if_neg (hB1K a ha), if_pos hb, zero_add]
    · rw [hω1 a b (Or.inr ⟨hb, ha⟩), hχdef, hχdef, if_pos ha, if_neg (hB1K b hb), add_zero]
    · rw [hωT a b ha hb, hχdef, hχdef, if_pos ha, if_pos hb]
      decide
  -- the cut cochain is a cell cocycle
  have hcocycle : IsCellCocycle ω := by
    intro x y z hxy hyz hxz
    by_cases hT : x ∈ Kᶜ ∨ y ∈ Kᶜ ∨ z ∈ Kᶜ
    · by_cases hb : x ∈ B₁ ∨ y ∈ B₁ ∨ z ∈ B₁
      · obtain ⟨t, ht, hxt, hyt, hzt⟩ : ∃ t : Lattice d, t ∈ Kᶜ ∧ latticeDist x t ≤ 1 ∧
            latticeDist y t ≤ 1 ∧ latticeDist z t ≤ 1 := by
          rcases hT with h | h | h
          · exact ⟨x, h, by simp, by rwa [latticeDist_comm], by rwa [latticeDist_comm]⟩
          · exact ⟨y, h, hxy, by simp, by rwa [latticeDist_comm]⟩
          · exact ⟨z, h, hxz, hyz, by simp⟩
        obtain ⟨p, hp, hpx, hpy, hpz⟩ : ∃ p : Lattice d, p ∈ B₁ ∧ latticeDist p x ≤ 1 ∧
            latticeDist p y ≤ 1 ∧ latticeDist p z ≤ 1 := by
          rcases hb with h | h | h
          · exact ⟨x, h, by simp, hxy, hxz⟩
          · exact ⟨y, h, by rwa [latticeDist_comm], by simp, hyz⟩
          · exact ⟨z, h, by rwa [latticeDist_comm], by rwa [latticeDist_comm], by simp⟩
        have hmem : ∀ w : Lattice d, latticeDist w t ≤ 1 → latticeDist p w ≤ 1 →
            (w ∈ B₁ ∨ w ∈ Kᶜ) := by
          intro w hwt hpw
          by_cases hwK : w ∈ K
          · exact Or.inl (hext w ⟨hwK, t, ht, by rwa [latticeDist_comm]⟩ p hp hpw)
          · exact Or.inr hwK
        rw [hpair x y (hmem x hxt hpx) (hmem y hyt hpy),
          hpair y z (hmem y hyt hpy) (hmem z hzt hpz),
          hpair z x (hmem z hzt hpz) (hmem x hxt hpx)]
        have k : ∀ a b c : ZMod 2, a + b + (b + c) + (c + a) = 0 := by decide
        exact k _ _ _
      · push_neg at hb
        obtain ⟨hbx, hby, hbz⟩ := hb
        rw [hω0 x y (by rintro (⟨h, -⟩ | ⟨h, -⟩); exacts [hbx h, hby h]),
          hω0 y z (by rintro (⟨h, -⟩ | ⟨h, -⟩); exacts [hby h, hbz h]),
          hω0 z x (by rintro (⟨h, -⟩ | ⟨h, -⟩); exacts [hbz h, hbx h])]
        decide
    · push_neg at hT
      obtain ⟨hTx, hTy, hTz⟩ := hT
      rw [hωK x y (not_not.mp hTx) (not_not.mp hTy), hωK y z (not_not.mp hTy) (not_not.mp hTz),
        hωK z x (not_not.mp hTz) (not_not.mp hTx)]
      decide
  -- the potential, and the contradiction
  obtain ⟨g, hg⟩ := exists_potential_of_isCellCocycle hcocycle
  have hgsplit : ∀ a b : ZMod 2, (0 : ZMod 2) = a + b → a = b := by decide
  have hgK : ∀ a ∈ K, ∀ b ∈ K, g a = g b := by
    intro a ha b hb
    refine eq_of_jStepReachableIn_of_forall_adj (fun p hp q hq hpq => ?_) (hKconn a ha b hb)
    exact hgsplit _ _ (by rw [← hωK p q hp hq, hg p q hpq])
  have hgT : ∀ a ∈ Kᶜ, ∀ b ∈ Kᶜ, g a = g b := by
    intro a ha b hb
    refine eq_of_jStepReachableIn_of_forall_adj (fun p hp q hq hpq => ?_) (hTconn a ha b hb)
    exact hgsplit _ _ (by rw [← hωT p q hp hq, hg p q hpq])
  have hu₀K : u₀ ∈ K := hu₀.1
  have hvK : v ∈ K := hv.1
  obtain ⟨t₀, ht₀, ht₀u⟩ := hu₀.2
  obtain ⟨t₁, ht₁, ht₁v⟩ := hv.2
  have e1 : (1 : ZMod 2) = g u₀ + g t₀ := by
    rw [← hω1 u₀ t₀ (Or.inl ⟨hu₀B1, ht₀⟩)]
    exact hg u₀ t₀ (by rwa [latticeDist_comm])
  have e2 : (0 : ZMod 2) = g v + g t₁ := by
    refine Eq.trans ?_ (hg v t₁ (by rwa [latticeDist_comm]))
    refine (hω0 v t₁ ?_).symm
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hvB1 h
    · exact ht₁ (hBK (hB1B h))
  rw [hgK v hvK u₀ hu₀K, hgT t₁ ht₁ t₀ ht₀] at e2
  rw [← e2] at e1
  exact absurd e1 (by decide)

/-- **`[Timár, Lemma 2]`, symmetric form** — `SplitBoundaryConnectivity d` holds for every `d`. -/
theorem splitBoundaryConnectivity (d : ℕ) : SplitBoundaryConnectivity d :=
  fun _ _ _ hKconn hTconn _ hu _ hv => jStepReachableIn_innerBoundary hKconn hTconn hu hv

/-- **The corrected `[Timár, Lemma 2]` is a theorem, in every dimension.**  The outer boundary of
a finite `1`-step connected set of `ℤ^d`, seen from one component of the complement, is `1`-step
connected.

(The *recorded* form `TimarBoundaryConnectivity`, without the visibility condition, is false in
every dimension `d ≥ 1`: `not_timarBoundaryConnectivity`, P-347.) -/
theorem timarBoundaryComponentConnectivity (d : ℕ) : TimarBoundaryComponentConnectivity d :=
  timarBoundaryComponentConnectivity_of_splitBoundaryConnectivity (splitBoundaryConnectivity d)

/-- The corrected `[Timár, Lemma 2]` in the `innerBoundary` form of P-352: the inner boundary of
a component of the complement of a finite `1`-step connected set is `1`-step connected. -/
theorem jStepReachableIn_innerBoundary_jStepComponent {S : Set (Lattice d)} (hSne : S.Nonempty)
    (hSconn : ∀ u ∈ S, ∀ v ∈ S, JStepReachableIn 1 S u v) (c : Lattice d) :
    ∀ u ∈ innerBoundary (jStepComponent 1 Sᶜ c), ∀ v ∈ innerBoundary (jStepComponent 1 Sᶜ c),
      JStepReachableIn 1 (innerBoundary (jStepComponent 1 Sᶜ c)) u v :=
  fun _ hu _ hv =>
    jStepReachableIn_innerBoundary
      (fun _ ha _ hb => jStepReachableIn_within_jStepComponent ha hb)
      (jStepReachableIn_compl_jStepComponent hSne hSconn) hu hv

/-- **The recorded statement of P-345, rescued.**  For a finite `1`-step connected set whose
complement is `1`-step connected, the *whole* outer boundary is `1`-step connected — the case in
which `TimarBoundaryConnectivity` is not refuted. -/
theorem jStepReachableIn_outerBoundary_of_compl_connected {S : Set (Lattice d)} (hfin : S.Finite)
    (hne : S.Nonempty) (hSconn : ∀ u ∈ S, ∀ v ∈ S, JStepReachableIn 1 S u v) {c : Lattice d}
    (hc : c ∉ S) (hcompl : ∀ u ∈ Sᶜ, ∀ v ∈ Sᶜ, JStepReachableIn 1 Sᶜ u v) :
    ∀ u ∈ outerBoundary S, ∀ v ∈ outerBoundary S,
      JStepReachableIn 1 (outerBoundary S) u v :=
  outerBoundary_connected_of_timarBoundaryComponentConnectivity
    (timarBoundaryComponentConnectivity d) S hfin hne hSconn hc hcompl

/-! ## `[DRS]` condition S1 without externals -/

variable {Ω : Type*}

/-- **The recorded external of `[DRS]` condition S1 is a theorem** for `2 ≤ d` and `1 ≤ J`.

`2 ≤ d` is necessary and not an artefact: `DimensionOne.not_timarBoundaryInput_one` refutes
`TimarBoundaryInput` on the line. -/
theorem timarBoundaryInput_of_two_le (hd : 2 ≤ d) {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ}
    (hJ : 1 ≤ J) (ω : Ω) (z : Lattice d) (L : ℕ) : TimarBoundaryInput E Cbox J ω z L :=
  timarBoundaryInput_of_timarBoundaryComponentConnectivity hd
    (timarBoundaryComponentConnectivity d) hJ ω z L

/-- **`[DRS]` condition S1 at scale `L`, from clause (ii) alone.**  For `2 ≤ d` and `1 ≤ J` the
bad-component diameter bound gives the good connectivity in the double ball with no further
input. -/
theorem goodConnectedInDoubleBall_of_badComponentDiameterBound_of_two_le (hd : 2 ≤ d)
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} (hJ : 1 ≤ J) {ω : Ω} {z : Lattice d} {C q : ℝ}
    {h L : ℕ} (hbad : BadComponentDiameterBound E Cbox J ω z C q h)
    (hsmall : C * (1 + h + q⁻¹ * Real.log (2 + (2 * L : ℝ))) ^ 2 ≤ (L : ℝ) / 100) :
    GoodConnectedInDoubleBall E Cbox ω z L :=
  goodConnectedInDoubleBall_of_timarBoundaryComponentConnectivity hd
    (timarBoundaryComponentConnectivity d) hJ hbad hsmall



theorem goodConnectedInDoubleBallAt_of_badComponentDiameterBound_of_two_le (hd : 2 ≤ d)
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} (hJ : 1 ≤ J) {ω : Ω} {z : Lattice d} {C q : ℝ}
    {h L : ℕ} {D : ℝ} (hD : (L : ℝ) / 20 ≤ D)
    (hbad : BadComponentDiameterBound E Cbox J ω z C q h)
    (hsmall : C * (1 + h + q⁻¹ * Real.log (2 + (2 * L : ℝ))) ^ 2 ≤ (L : ℝ) / 100) :
    GoodConnectedInDoubleBallAt E Cbox ω z L D :=
  goodConnectedInDoubleBallAt_of_timarBoundaryComponentConnectivity hd
    (timarBoundaryComponentConnectivity d) hJ ω z L hD
    (fun v hv hvbad a ha b hb i =>
      ((hbad (2 * L : ℝ) (by positivity) v hv hvbad) a ha b hb i).trans hsmall)

/-- The `L / 20` instance, which is the diameter threshold of `D_L(z)`. -/
theorem goodConnectedInDoubleBallAt_twentieth_of_badComponentDiameterBound_of_two_le
    (hd : 2 ≤ d) {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} (hJ : 1 ≤ J) {ω : Ω}
    {z : Lattice d} {C q : ℝ} {h L : ℕ}
    (hbad : BadComponentDiameterBound E Cbox J ω z C q h)
    (hsmall : C * (1 + h + q⁻¹ * Real.log (2 + (2 * L : ℝ))) ^ 2 ≤ (L : ℝ) / 100) :
    GoodConnectedInDoubleBallAt E Cbox ω z L ((L : ℝ) / 20) :=
  goodConnectedInDoubleBallAt_of_badComponentDiameterBound_of_two_le hd hJ le_rfl hbad hsmall

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
