import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.IntervalPacking

/-!
# Encoding separated interval configurations by their union

The Appendix-B union bound counts packed configurations by subsets of the
three-scale index window.  This is valid because pairwise distance-two
centered intervals are exactly the connected components of their union.  The
injectivity statement below makes that source sentence explicit.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

/-- An interval from one separated partition which meets an interval from a
second separated partition of the same union is contained in the latter. -/
private theorem centeredIntInterval_subset_of_mem_biUnion_eq
    {K L : Finset ℤ} {r R : ℤ → ℕ}
    (hsepL : ∀ a ∈ L, ∀ b ∈ L, a ≠ b →
      centeredIntIntervalsSeparated a (R a) b (R b))
    (hunion : K.biUnion (fun k ↦ centeredIntInterval k (r k)) =
      L.biUnion (fun k ↦ centeredIntInterval k (R k)))
    {a b : ℤ} (ha : a ∈ K) (hb : b ∈ L)
    (hoverlap : ∃ x, x ∈ centeredIntInterval a (r a) ∧
      x ∈ centeredIntInterval b (R b)) :
    centeredIntInterval a (r a) ⊆ centeredIntInterval b (R b) := by
  have hleft : b - (R b : ℤ) ≤ a - (r a : ℤ) := by
    by_contra hnot
    have hlt : a - (r a : ℤ) < b - (R b : ℤ) := by omega
    let x : ℤ := b - (R b : ℤ) - 1
    obtain ⟨y, hya, hyb⟩ := hoverlap
    have hxA : x ∈ centeredIntInterval a (r a) := by
      simp only [centeredIntInterval, Finset.mem_Icc] at hya hyb ⊢
      dsimp [x]
      omega
    have hxUnionK : x ∈ K.biUnion (fun k ↦ centeredIntInterval k (r k)) :=
      Finset.mem_biUnion.mpr ⟨a, ha, hxA⟩
    have hxUnionL : x ∈ L.biUnion (fun k ↦ centeredIntInterval k (R k)) := by
      rw [← hunion]
      exact hxUnionK
    obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hxUnionL
    have hcb : c ≠ b := by
      intro heq
      subst c
      simp only [centeredIntInterval, Finset.mem_Icc] at hxc
      dsimp [x] at hxc
      omega
    have hxSep : x ∈ separatedIntInterval b (R b) := by
      simp only [separatedIntInterval, Finset.mem_Icc]
      dsimp [x]
      omega
    exact Finset.disjoint_left.mp (hsepL c hc b hb hcb).1 hxc hxSep
  have hright : a + (r a : ℤ) ≤ b + (R b : ℤ) := by
    by_contra hnot
    have hlt : b + (R b : ℤ) < a + (r a : ℤ) := by omega
    let x : ℤ := b + (R b : ℤ) + 1
    obtain ⟨y, hya, hyb⟩ := hoverlap
    have hxA : x ∈ centeredIntInterval a (r a) := by
      simp only [centeredIntInterval, Finset.mem_Icc] at hya hyb ⊢
      dsimp [x]
      omega
    have hxUnionK : x ∈ K.biUnion (fun k ↦ centeredIntInterval k (r k)) :=
      Finset.mem_biUnion.mpr ⟨a, ha, hxA⟩
    have hxUnionL : x ∈ L.biUnion (fun k ↦ centeredIntInterval k (R k)) := by
      rw [← hunion]
      exact hxUnionK
    obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hxUnionL
    have hcb : c ≠ b := by
      intro heq
      subst c
      simp only [centeredIntInterval, Finset.mem_Icc] at hxc
      dsimp [x] at hxc
      omega
    have hxSep : x ∈ separatedIntInterval b (R b) := by
      simp only [separatedIntInterval, Finset.mem_Icc]
      dsimp [x]
      omega
    exact Finset.disjoint_left.mp (hsepL c hc b hb hcb).1 hxc hxSep
  intro x hx
  simp only [centeredIntInterval, Finset.mem_Icc] at hx ⊢
  exact ⟨hleft.trans hx.1, hx.2.trans hright⟩

/-- Pairwise separated centered-interval configurations are determined by
their union, including both their centres and their radii. -/
theorem centeredIntInterval_configuration_injective
    (K L : Finset ℤ) (r R : ℤ → ℕ)
    (hsepK : ∀ a ∈ K, ∀ b ∈ K, a ≠ b →
      centeredIntIntervalsSeparated a (r a) b (r b))
    (hsepL : ∀ a ∈ L, ∀ b ∈ L, a ≠ b →
      centeredIntIntervalsSeparated a (R a) b (R b))
    (hunion : K.biUnion (fun k ↦ centeredIntInterval k (r k)) =
      L.biUnion (fun k ↦ centeredIntInterval k (R k))) :
    K = L ∧ ∀ k ∈ K, r k = R k := by
  have hmatch : ∀ a ∈ K, ∃ b ∈ L, a = b ∧ r a = R b := by
    intro a ha
    have haUnionK : a ∈ K.biUnion (fun k ↦ centeredIntInterval k (r k)) :=
      Finset.mem_biUnion.mpr ⟨a, ha, center_mem_centeredIntInterval a (r a)⟩
    have haUnionL : a ∈ L.biUnion (fun k ↦ centeredIntInterval k (R k)) := by
      rw [← hunion]
      exact haUnionK
    obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp haUnionL
    have hoverlap : ∃ x, x ∈ centeredIntInterval a (r a) ∧
        x ∈ centeredIntInterval b (R b) :=
      ⟨a, center_mem_centeredIntInterval a (r a), hab⟩
    have hsubAB := centeredIntInterval_subset_of_mem_biUnion_eq
      hsepL hunion ha hb hoverlap
    have hsubBA := centeredIntInterval_subset_of_mem_biUnion_eq
      hsepK hunion.symm hb ha ⟨a, hab, center_mem_centeredIntInterval a (r a)⟩
    have hleftAB := hsubAB (show a - (r a : ℤ) ∈ centeredIntInterval a (r a) by
      simp only [centeredIntInterval, Finset.mem_Icc]
      omega)
    have hleftBA := hsubBA (show b - (R b : ℤ) ∈ centeredIntInterval b (R b) by
      simp only [centeredIntInterval, Finset.mem_Icc]
      omega)
    have hrightAB := hsubAB (show a + (r a : ℤ) ∈ centeredIntInterval a (r a) by
      simp only [centeredIntInterval, Finset.mem_Icc]
      omega)
    have hrightBA := hsubBA (show b + (R b : ℤ) ∈ centeredIntInterval b (R b) by
      simp only [centeredIntInterval, Finset.mem_Icc]
      omega)
    simp only [centeredIntInterval, Finset.mem_Icc] at hleftAB hleftBA hrightAB hrightBA
    have habCenter : a = b := by omega
    have hradiusInt : (r a : ℤ) = (R b : ℤ) := by omega
    exact ⟨b, hb, habCenter, by exact_mod_cast hradiusInt⟩
  have hKL : K ⊆ L := by
    intro a ha
    obtain ⟨b, hb, hab, _⟩ := hmatch a ha
    simpa only [hab] using hb
  have hLK : L ⊆ K := by
    intro b hb
    have hbUnionL : b ∈ L.biUnion (fun k ↦ centeredIntInterval k (R k)) :=
      Finset.mem_biUnion.mpr ⟨b, hb, center_mem_centeredIntInterval b (R b)⟩
    have hbUnionK : b ∈ K.biUnion (fun k ↦ centeredIntInterval k (r k)) := by
      rw [hunion]
      exact hbUnionL
    obtain ⟨a, ha, hba⟩ := Finset.mem_biUnion.mp hbUnionK
    have hoverlap : ∃ x, x ∈ centeredIntInterval b (R b) ∧
        x ∈ centeredIntInterval a (r a) :=
      ⟨b, center_mem_centeredIntInterval b (R b), hba⟩
    have hsubBA := centeredIntInterval_subset_of_mem_biUnion_eq
      hsepK hunion.symm hb ha hoverlap
    have hsubAB := centeredIntInterval_subset_of_mem_biUnion_eq
      hsepL hunion ha hb ⟨b, hba, center_mem_centeredIntInterval b (R b)⟩
    have hleftBA := hsubBA (show b - (R b : ℤ) ∈ centeredIntInterval b (R b) by
      simp only [centeredIntInterval, Finset.mem_Icc]
      omega)
    have hleftAB := hsubAB (show a - (r a : ℤ) ∈ centeredIntInterval a (r a) by
      simp only [centeredIntInterval, Finset.mem_Icc]
      omega)
    have hrightBA := hsubBA (show b + (R b : ℤ) ∈ centeredIntInterval b (R b) by
      simp only [centeredIntInterval, Finset.mem_Icc]
      omega)
    have hrightAB := hsubAB (show a + (r a : ℤ) ∈ centeredIntInterval a (r a) by
      simp only [centeredIntInterval, Finset.mem_Icc]
      omega)
    simp only [centeredIntInterval, Finset.mem_Icc] at hleftBA hleftAB hrightBA hrightAB
    have hcenter : b = a := by omega
    simpa only [hcenter] using ha
  have hEq : K = L := Finset.Subset.antisymm hKL hLK
  refine ⟨hEq, ?_⟩
  intro k hk
  obtain ⟨b, _hb, hkb, hr⟩ := hmatch k hk
  simpa only [hkb] using hr

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
