import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalBadChain
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarComponent




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-! ## A greedy separated subset of a finite set of naturals -/

/-- A function on `ℕ` that is strictly increasing below `k` grows at least as fast as its
argument: `f i + (j - i) ≤ f j` for `i ≤ j < k`.  This is the numerical content of "the
increasing enumeration of a set of naturals dominates the identity". -/
private theorem add_sub_le_of_lt_of_lt {k : ℕ} {f : ℕ → ℕ}
    (hf : ∀ a b : ℕ, a < b → b < k → f a < f b) :
    ∀ j, j < k → ∀ i, i ≤ j → f i + (j - i) ≤ f j := by
  intro j
  induction j with
  | zero =>
    intro _ i hi
    have : i = 0 := Nat.le_zero.mp hi
    subst this
    simp
  | succ n ih =>
    intro hn i hi
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · have hin : i ≤ n := Nat.lt_succ_iff.mp hlt
      have hnk : n < k := Nat.lt_of_succ_lt hn
      have h1 : f i + (n - i) ≤ f n := ih hnk i hin
      have h2 : f n < f (n + 1) := hf n (n + 1) (Nat.lt_succ_self n) hn
      omega
    · have : i = n + 1 := le_antisymm hi hge
      subst this
      simp

/-- **Greedy separation.**  A finite set of naturals with at least `m * (s + 1)` elements has a
subset of exactly `m` elements any two of which differ by more than `s`.

The witness is the image of `0, s+1, 2(s+1), …, (m-1)(s+1)` under the increasing enumeration
`Finset.orderEmbOfFin` of `S`. -/
theorem exists_separated_subset (s m : ℕ) (S : Finset ℕ) (h : m * (s + 1) ≤ S.card) :
    ∃ T : Finset ℕ, T ⊆ S ∧ T.card = m ∧
      ∀ a ∈ T, ∀ b ∈ T, a < b → a + s < b := by
  classical
  -- the increasing enumeration of `S`, extended by `0` off `Fin S.card`
  set emb : Fin S.card ↪o ℕ := S.orderEmbOfFin rfl with hemb
  set f : ℕ → ℕ := fun n => if hn : n < S.card then emb ⟨n, hn⟩ else 0 with hfdef
  have hf : ∀ a b : ℕ, a < b → b < S.card → f a < f b := by
    intro a b hab hb
    have ha : a < S.card := lt_trans hab hb
    simp only [hfdef, dif_pos ha, dif_pos hb]
    exact emb.strictMono (show (⟨a, ha⟩ : Fin S.card) < ⟨b, hb⟩ from hab)
  have hfmem : ∀ n, n < S.card → f n ∈ S := by
    intro n hn
    simp only [hfdef, dif_pos hn, hemb]
    exact S.orderEmbOfFin_mem rfl _
  -- the selected indices lie inside the enumeration range
  have hidx : ∀ i : Fin m, (i : ℕ) * (s + 1) < S.card := by
    intro i
    have hi : (i : ℕ) + 1 ≤ m := i.2
    calc (i : ℕ) * (s + 1) < ((i : ℕ) + 1) * (s + 1) := by
          exact (Nat.mul_lt_mul_right (Nat.succ_pos s)).mpr (Nat.lt_succ_self _)
      _ ≤ m * (s + 1) := Nat.mul_le_mul_right _ hi
      _ ≤ S.card := h
  set g : Fin m → ℕ := fun i => f ((i : ℕ) * (s + 1)) with hgdef
  -- the key separation estimate for two selected indices
  have hsep : ∀ i j : Fin m, (i : ℕ) < (j : ℕ) → g i + s < g j := by
    intro i j hij
    have hlt : (i : ℕ) * (s + 1) < (j : ℕ) * (s + 1) :=
      (Nat.mul_lt_mul_right (Nat.succ_pos s)).mpr hij
    have hkey := add_sub_le_of_lt_of_lt hf ((j : ℕ) * (s + 1)) (hidx j)
      ((i : ℕ) * (s + 1)) hlt.le
    have hgap : (s + 1) ≤ (j : ℕ) * (s + 1) - (i : ℕ) * (s + 1) := by
      have : ((i : ℕ) + 1) * (s + 1) ≤ (j : ℕ) * (s + 1) :=
        Nat.mul_le_mul_right _ hij
      have hexp : ((i : ℕ) + 1) * (s + 1) = (i : ℕ) * (s + 1) + (s + 1) := by ring
      omega
    simp only [hgdef]
    omega
  have hgmono : StrictMono g := by
    intro i j hij
    have := hsep i j hij
    omega
  refine ⟨Finset.image g Finset.univ, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hfmem _ (hidx i)
  · rw [Finset.card_image_of_injective _ hgmono.injective, Finset.card_univ,
      Fintype.card_fin]
  · intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    have hij : (i : ℕ) < (j : ℕ) := by
      by_contra hcon
      have : (j : ℕ) ≤ (i : ℕ) := Nat.le_of_not_lt hcon
      rcases lt_or_eq_of_le this with hlt | heq
      · exact absurd (hsep j i hlt) (by omega)
      · exact absurd (congrArg g (Fin.ext heq.symm)) (by omega)
    exact hsep i j hij

/-! ## The `ℓ^∞` geodesic is parametrised by arclength -/

/-- **Geodesic spreading.**  Along the `ℓ^∞` geodesic from `v` to `w`, two points at times
`k ≤ k'` with `k' ≤ latticeDist v w` are at lattice distance at least `k' - k`.

Since `latticeDist_latticeGeodesic_succ` gives distance at most `1` per step, the geodesic moves
at exactly unit speed until it arrives, so times in disjoint bands give well-separated sites. -/
theorem sub_le_latticeDist_latticeGeodesic {v w : Lattice d} {k k' : ℕ}
    (hk : k ≤ k') (hk' : k' ≤ latticeDist v w) :
    k' - k ≤ latticeDist (latticeGeodesic v w k) (latticeGeodesic v w k') := by
  rcases Nat.eq_zero_or_pos (latticeDist v w) with hzero | hpos
  · have : k' = 0 := Nat.le_zero.mp (hzero ▸ hk')
    subst this
    have : k = 0 := Nat.le_zero.mp hk
    subst this
    simp
  · -- the sup defining `latticeDist v w` is attained
    have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
      rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin d)) with hemp | hne
      · exfalso
        rw [latticeDist, hemp] at hpos
        simp at hpos
      · exact hne
    obtain ⟨i₀, -, hi₀⟩ :=
      Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d)) hne
        (fun i => (v i - w i).natAbs)
    have hattain : (v i₀ - w i₀).natAbs = latticeDist v w := hi₀.symm
    -- at that coordinate the geodesic really does move `k'` steps
    have hcoord : ((latticeGeodesic v w k i₀ - latticeGeodesic v w k' i₀).natAbs) = k' - k := by
      simp only [latticeGeodesic]
      have h1 : (k' : ℤ) ≤ (latticeDist v w : ℤ) := by exact_mod_cast hk'
      have h2 : (k : ℤ) ≤ (k' : ℤ) := by exact_mod_cast hk
      have h3 : ((v i₀ - w i₀).natAbs : ℤ) = (latticeDist v w : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hattain
      rw [Int.natAbs_eq_iff]
      omega
    calc k' - k = (latticeGeodesic v w k i₀ - latticeGeodesic v w k' i₀).natAbs := hcoord.symm
      _ ≤ latticeDist (latticeGeodesic v w k) (latticeGeodesic v w k') :=
          coord_le_latticeDist _ _ i₀

/-! ## A crude entropy bound for binomial coefficients -/

/-- `m ^ m ≤ m ! * exp m`, obtained by keeping the `k = m` term of the exponential series. -/
private theorem pow_self_le_factorial_mul_exp (m : ℕ) :
    ((m : ℝ)) ^ m ≤ (m.factorial : ℝ) * Real.exp (m : ℝ) := by
  have hnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hterm : ((m : ℝ)) ^ m / (m.factorial : ℝ) ≤ Real.exp (m : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hnonneg (m + 1))
    refine Finset.single_le_sum (f := fun i => ((m : ℝ)) ^ i / (i.factorial : ℝ)) ?_ ?_
    · intro i _
      positivity
    · exact Finset.self_mem_range_succ m
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by
    exact_mod_cast m.factorial_pos
  rw [div_le_iff₀ hfac] at hterm
  calc ((m : ℝ)) ^ m ≤ Real.exp (m : ℝ) * (m.factorial : ℝ) := hterm
    _ = (m.factorial : ℝ) * Real.exp (m : ℝ) := by ring

/-- **Entropy of a band choice.**  The crude bound `C(n, m) ≤ (3 n / m) ^ m`, valid for every
`n` and every `m ≥ 1`.

The proof combines `Nat.choose_le_pow_div` (`C(n,m) ≤ n ^ m / m !`) with
`m ^ m ≤ m ! * exp m` and `exp 1 < 3`; the constant `3` is not optimal (the sharp value is
`e ≈ 2.718`), but it is what the band-counting bounds of Section 9 consume. -/
theorem choose_le_pow_div (n m : ℕ) (hm : 1 ≤ m) :
    ((n.choose m : ℕ) : ℝ) ≤ (3 * (n : ℝ) / (m : ℝ)) ^ m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- step 1: the standard bound `C(n,m) ≤ n ^ m / m !`
  have h1 : ((n.choose m : ℕ) : ℝ) ≤ (n : ℝ) ^ m / (m.factorial : ℝ) :=
    Nat.choose_le_pow_div m n
  -- step 2: `exp m ≤ 3 ^ m`
  have hexp : Real.exp (m : ℝ) ≤ (3 : ℝ) ^ m := by
    rw [← Real.exp_one_pow]
    refine pow_le_pow_left₀ (Real.exp_nonneg 1) ?_ m
    have h9 := Real.exp_one_lt_d9
    norm_num at h9
    linarith
  -- step 3: `1 / m ! ≤ 3 ^ m / m ^ m`
  have h2 : (n : ℝ) ^ m / (m.factorial : ℝ) ≤ (n : ℝ) ^ m * ((3 : ℝ) ^ m / (m : ℝ) ^ m) := by
    have hkey : ((m : ℝ)) ^ m ≤ (m.factorial : ℝ) * (3 : ℝ) ^ m :=
      le_trans (pow_self_le_factorial_mul_exp m)
        (by
          have : (0 : ℝ) ≤ (m.factorial : ℝ) := hfac.le
          exact mul_le_mul_of_nonneg_left hexp this)
    have hmm : (0 : ℝ) < (m : ℝ) ^ m := pow_pos hmpos m
    have hinv : 1 / (m.factorial : ℝ) ≤ (3 : ℝ) ^ m / (m : ℝ) ^ m := by
      rw [div_le_div_iff₀ hfac hmm]
      linarith [hkey]
    have hnpow : (0 : ℝ) ≤ (n : ℝ) ^ m := pow_nonneg hnn m
    calc (n : ℝ) ^ m / (m.factorial : ℝ) = (n : ℝ) ^ m * (1 / (m.factorial : ℝ)) := by
          ring
      _ ≤ (n : ℝ) ^ m * ((3 : ℝ) ^ m / (m : ℝ) ^ m) := by
          exact mul_le_mul_of_nonneg_left hinv hnpow
  -- step 4: rewrite the right-hand side
  have h3 : (3 * (n : ℝ) / (m : ℝ)) ^ m = (n : ℝ) ^ m * ((3 : ℝ) ^ m / (m : ℝ) ^ m) := by
    rw [div_pow, mul_pow]
    ring
  rw [h3]
  linarith [h1, h2]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
