module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTruncation
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

theorem iIndep_pairs {ι Ω : Type*} [mΩ : MeasurableSpace Ω] (mu : Measure Ω)
    (m : ι → Bool → MeasurableSpace Ω) (hle : ∀ i b, m i b ≤ mΩ)
    (hrows : iIndep (fun i => ⨆ b, m i b) mu)
    (hcols : ∀ i, iIndep (m i) mu) : iIndep (fun p : ι × Bool => m p.1 p.2) mu := by
  let mX : ∀ (i : ι) (b : Bool), MeasurableSpace Ω := m
  have hm : ∀ i b, @Measurable Ω Ω mΩ (mX i b) id := fun i b _ hs => hle i b _ hs
  have hid (n : MeasurableSpace Ω) : n.comap (fun x : Ω => x) = n := MeasurableSpace.comap_id
  have hi : @iIndepFun Ω ι mΩ (fun _ => Bool → Ω)
      (fun i => @MeasurableSpace.pi Bool (fun _ => Ω) (mX i)) (fun _ ω _ => ω) mu := by
    rw [iIndepFun_iff_iIndep]
    simpa only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def, hid] using hrows
  have hj : ∀ i, @iIndepFun Ω Bool mΩ (fun _ => Ω) (mX i) (fun _ => id) mu := by
    intro i
    rw [iIndepFun_iff_iIndep]
    simpa only [MeasurableSpace.comap_id] using hcols i
  have h := @iIndepFun_uncurry' ι Ω mΩ mu Bool (fun _ _ => Ω) mX
    (fun _ _ => id) hm hi hj
  rw [iIndepFun_iff_iIndep] at h
  simpa only [MeasurableSpace.comap_id] using h

theorem iIndep_bool_of_indep {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (m : Bool → MeasurableSpace Ω)
    (h : Indep (m false) (m true) mu) : iIndep m mu := by
  rw [iIndep_iff]
  intro s f hf
  fin_cases s
  · simp
  · change mu (⋂ i ∈ ({true} : Finset Bool), f i) = ∏ i ∈ ({true} : Finset Bool), mu (f i)
    simp
  · change mu (⋂ i ∈ ({false} : Finset Bool), f i) = ∏ i ∈ ({false} : Finset Bool), mu (f i)
    simp
  · have hi := (Indep_iff _ _ _).mp h (f false) (f true)
      (hf false (by simp)) (hf true (by simp))
    have hinter : (⋂ i : Bool, f i) = f false ∩ f true := by
      ext ω
      constructor
      · intro hω
        exact ⟨Set.mem_iInter.mp hω false, Set.mem_iInter.mp hω true⟩
      · rintro ⟨hfalse, htrue⟩
        exact Set.mem_iInter.mpr (fun b => by cases b <;> assumption)
    simpa [hinter, Set.inter_comm, mul_comm] using hi


theorem indep_columns {ι Ω : Type*} [mΩ : MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (m : ι → Bool → MeasurableSpace Ω)
    (hle : ∀ i b, m i b ≤ mΩ) (hrows : iIndep (fun i => ⨆ b, m i b) mu)
    (hcols : ∀ i, Indep (m i false) (m i true) mu) :
    Indep (⨆ i, m i false) (⨆ i, m i true) mu := by
  have hpair := iIndep_pairs mu m hle hrows
    (fun i => iIndep_bool_of_indep mu (m i) (hcols i))
  have hdisj : Disjoint {p : ι × Bool | p.2 = false} {p : ι × Bool | p.2 = true} :=
    Set.disjoint_left.mpr (fun _ hp hq => Bool.false_ne_true (hp.symm.trans hq))
  have heq (b : Bool) : (⨆ p ∈ {p : ι × Bool | p.2 = b}, m p.1 p.2) = ⨆ i, m i b := by
    apply le_antisymm
    · refine iSup_le fun p => iSup_le fun hp => ?_
      change p.2 = b at hp
      rw [hp]
      exact le_iSup (fun i => m i b) p.1
    · exact iSup_le fun i => le_iSup_of_le (i, b) (le_iSup_of_le rfl le_rfl)
  have h := indep_iSup_of_disjoint (fun p : ι × Bool => hle p.1 p.2) hpair hdisj
  rwa [heq false, heq true] at h



theorem indep_event_truncations {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω)
    (S T : Set (Lattice d)) (n : ℕ) (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hsp : ∀ j < n, Indep (eventFieldSigma (E j) S) (eventFieldSigma (E j) T) mu) :
    Indep (⨆ j ∈ Finset.range n, eventFieldSigma (E j) S)
      (⨆ j ∈ Finset.range n, eventFieldSigma (E j) T) mu := by
  let m (j : Fin n) (b : Bool) := eventFieldSigma (E j) (if b then T else S)
  have hfull (j : ℕ) : eventFieldSigma (E j) Set.univ ≤ mΩ :=
    MeasurableSpace.generateFrom_le (fun _ ⟨z, _, hz⟩ => hz ▸ hE j z)
  have hrow (j : Fin n) : (⨆ b, m j b) ≤ eventFieldSigma (E j) Set.univ :=
    iSup_le (fun b => eventFieldSigma_mono (E j) (Set.subset_univ _))
  have hrows : iIndep (fun j => ⨆ b, m j b) mu := by
    rw [iIndep_iff]
    intro s f hf
    have hsc' := iIndep.precomp (g := fun j : Fin n => j.val) Fin.val_injective hsc
    exact hsc'.meas_biInter (fun j hj => hrow j _ (hf j hj))
  have h := indep_columns mu m
    (fun j b => (eventFieldSigma_mono (E j) (Set.subset_univ _)).trans (hfull j))
    hrows (fun j => hsp j j.isLt)
  have heq (U : Set (Lattice d)) : (⨆ j : Fin n, eventFieldSigma (E j) U) =
      ⨆ j ∈ Finset.range n, eventFieldSigma (E j) U := by
    apply le_antisymm
    · exact iSup_le (fun j => le_iSup_of_le j.val
        (le_iSup_of_le (Finset.mem_range.mpr j.isLt) le_rfl))
    · exact iSup_le (fun j => iSup_le (fun hj =>
        le_iSup_of_le (⟨j, Finset.mem_range.mp hj⟩ : Fin n) le_rfl))
  simpa only [m, Bool.false_eq_true, ↓reduceIte, heq] using h



theorem indep_event_truncations_of_separated_balls {d j0 r Cdep : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (E : ℕ → Lattice d → Set Ω) (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    {x y : Lattice d} (hxy : 2 * r + Cdep * 3 ^ j0 < latticeDist x y) :
    Indep
      (⨆ j ∈ Finset.range (j0 + 1), eventFieldSigma (E j) (latticeBallFinset x r : Set _))
      (⨆ j ∈ Finset.range (j0 + 1), eventFieldSigma (E j) (latticeBallFinset y r : Set _))
      mu := by
  -- The scale at level `j` is dominated by the scale at level `j0` when `j ≤ j0`.
  have hpow : ∀ j ≤ j0, Cdep * 3 ^ j ≤ Cdep * 3 ^ j0 := fun j hj =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hj)
  -- Hence the two balls are separated at every scale `j < j0 + 1`.
  have hsep : ∀ j < j0 + 1, 2 * r + Cdep * 3 ^ j < latticeDist x y := by
    intro j hj
    have hle : Cdep * 3 ^ j ≤ Cdep * 3 ^ j0 := hpow j (Nat.lt_succ_iff.mp hj)
    have h1 : 2 * r + Cdep * 3 ^ j ≤ 2 * r + Cdep * 3 ^ j0 :=
      Nat.add_le_add_iff_left.mpr hle
    exact lt_of_le_of_lt h1 hxy
  -- Pointwise independence of the event fields on the two balls at each scale.
  have key : ∀ j < j0 + 1,
      Indep (eventFieldSigma (E j) (latticeBallFinset x r : Set _))
        (eventFieldSigma (E j) (latticeBallFinset y r : Set _)) mu := by
    intro j hj
    refine hr j (latticeBallFinset x r) (latticeBallFinset y r) ?_
    intro u hu v hv
    exact latticeDist_separated_balls (hsep j hj)
      ((mem_latticeBallFinset_iff).mp hu) ((mem_latticeBallFinset_iff).mp hv)
  -- Lift the per-scale independence to the truncated (union over scales) fields.
  exact indep_event_truncations mu E _ _ (j0 + 1) hE hsc key



theorem exists_independent_local_truncations {d j0 r Cdep : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (E : ℕ → Lattice d → Set Ω) (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    {x y : Lattice d} (hxy : 2 * r + Cdep * 3 ^ j0 < latticeDist x y)
    {A B : Set Ω}
    (hA : MeasurableSet[⨆ j, eventFieldSigma (E j) (latticeBallFinset x r : Set _)] A)
    (hB : MeasurableSet[⨆ j, eventFieldSigma (E j) (latticeBallFinset y r : Set _)] B) :
    ∃ A' B', mu (A \ A') + mu (A' \ A) + (mu (B \ B') + mu (B' \ B)) ≤
      (∑' j : ℕ, ∑ z ∈ latticeBallFinset x r, mu (E (j + j0 + 1) z)) +
      (∑' j : ℕ, ∑ z ∈ latticeBallFinset y r, mu (E (j + j0 + 1) z)) ∧
      mu (A' ∩ B') = mu A' * mu B' := by
  obtain ⟨A', hA', heA⟩ := exists_event_truncation_measure mu E (latticeBallFinset x r) j0 hE hA
  obtain ⟨B', hB', heB⟩ := exists_event_truncation_measure mu E (latticeBallFinset y r) j0 hE hB
  have hi := indep_event_truncations_of_separated_balls mu E hE hsc hr hxy
  exact ⟨A', B', add_le_add heA heB, (Indep_iff _ _ _).mp hi A' B' hA' hB'⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
