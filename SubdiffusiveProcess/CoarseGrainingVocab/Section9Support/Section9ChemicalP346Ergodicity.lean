module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalLocalIndependence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalZeroOneCylinder

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

theorem eventFieldSigma_translate {d : ℕ} {Ω : Type*} (E : Lattice d → Set Ω)
    (S : Set (Lattice d)) (a : Lattice d) :
    eventFieldSigma (fun z => E (z + a)) S =
      eventFieldSigma E ((fun z => z + a) '' S) := by
  unfold eventFieldSigma
  apply congrArg MeasurableSpace.generateFrom
  ext A
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z + a, mem_image_of_mem _ hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, hw, rfl⟩


theorem finiteFieldSigma_le_truncation {d : ℕ} {Ω : Type*} (E : ℕ → Lattice d → Set Ω)
    (F : Finset (ℕ × Lattice d)) (S : Set (Lattice d)) (n : ℕ)
    (hF : ∀ p ∈ F, p.1 < n ∧ p.2 ∈ S) :
    finiteFieldSigma E F ≤ ⨆ j ∈ Finset.range n, eventFieldSigma (E j) S := by
  unfold finiteFieldSigma
  refine iSup_le fun p => iSup_le fun hp => ?_
  exact le_iSup_of_le p.1 (le_iSup_of_le (Finset.mem_range.mpr (hF p hp).1)
    (eventFieldSigma_mono (E p.1) (Set.singleton_subset_iff.mpr (hF p hp).2)))


theorem coord_natAbs_le_finite_radius {d : ℕ} (F : Finset (ℕ × Lattice d))
    {p : ℕ × Lattice d} (hp : p ∈ F) (i : Fin d) :
    (p.2 i).natAbs ≤ F.sup (fun t => latticeDist 0 t.2) := by
  have h1 : ((0 : Lattice d) i - p.2 i).natAbs ≤ latticeDist 0 p.2 :=
    coord_le_latticeDist 0 p.2 i
  have h2 : ((0 : Lattice d) i - p.2 i).natAbs = (p.2 i).natAbs := by
    simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
  calc (p.2 i).natAbs = ((0 : Lattice d) i - p.2 i).natAbs := h2.symm
    _ ≤ latticeDist 0 p.2 := h1
    _ ≤ F.sup (fun t => latticeDist 0 t.2) :=
      Finset.le_sup (f := fun t : ℕ × Lattice d => latticeDist 0 t.2) hp


theorem latticeDist_translate_gt_of_coordinate_bound {d r R : ℕ} (i : Fin d) {u v : Lattice d}
    (hu : (u i).natAbs ≤ r) (hv : (v i).natAbs ≤ r) :
    R < latticeDist u (v + (fun _ : Fin d => ((2*r+R+1 : ℕ) : ℤ))) := by
  have h := coord_le_latticeDist u
    (v + (fun _ : Fin d => ((2*r+R+1 : ℕ) : ℤ))) i
  simp only [Pi.add_apply] at h
  omega


theorem scale_lt_finite_cutoff {d : ℕ} (F : Finset (ℕ × Lattice d))
    {p : ℕ × Lattice d} (hp : p ∈ F) : p.1 < F.sup Prod.fst + 1 := by
  have h : p.1 ≤ F.sup Prod.fst := Finset.le_sup hp
  omega


theorem indep_of_subsigmas {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    {m n M N : MeasurableSpace Ω} (h : Indep M N mu) (hm : m ≤ M) (hn : n ≤ N) :
    Indep m n mu := by
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  exact h s t (hm s hs) (hn t ht)


theorem finiteFieldSigma_translate_le_truncation {d : ℕ} {Ω : Type*}
    (E : ℕ → Lattice d → Set Ω) (F : Finset (ℕ × Lattice d)) (S : Set (Lattice d))
    (n : ℕ) (hF : ∀ p ∈ F, p.1 < n ∧ p.2 ∈ S) (a : Lattice d) :
    finiteFieldSigma (fun j z => E j (z + a)) F ≤
      ⨆ j ∈ Finset.range n, eventFieldSigma (E j) ((fun z => z + a) '' S) := by
  have h := finiteFieldSigma_le_truncation (fun j z => E j (z+a)) F S n hF
  simp only [eventFieldSigma_translate] at h
  exact h


theorem indep_eventFieldSigma_translate {d R : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (E : Lattice d → Set Ω) (h : FiniteRangeIndependentEvents mu R E)
    (S : Set (Lattice d)) (a : Lattice d)
    (hsep : ∀ u ∈ S, ∀ v ∈ S, R < latticeDist u (v + a)) :
    Indep (eventFieldSigma E S) (eventFieldSigma E ((fun z => z + a) '' S)) mu := by
  apply h S ((fun z => z + a) '' S)
  intro u hu v hv
  obtain ⟨z, hz, rfl⟩ := hv
  exact hsep u hu z hz




theorem shiftedFiniteFieldIndependence_of_eventIndependence {d Cdep : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (E : ℕ → Lattice d → Set Ω) (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E) :
    ShiftedFiniteFieldIndependence mu E := by
  intro F
  set n : ℕ := F.sup Prod.fst + 1 with hn
  set r : ℕ := F.sup (fun t => latticeDist 0 t.2) with hrr
  set R : ℕ := Cdep * 3 ^ n with hR
  refine ⟨fun _ => ((2 * r + R + 1 : ℕ) : ℤ), ?_⟩
  have hF : ∀ p ∈ F, p.1 < n ∧ p.2 ∈ Prod.snd '' (F : Set (ℕ × Lattice d)) := by
    intro p hp
    have h1' : p.1 < F.sup Prod.fst + 1 := scale_lt_finite_cutoff F hp
    rw [← hn] at h1'
    exact ⟨h1', ⟨p, hp, rfl⟩⟩
  have h1 : finiteFieldSigma E F ≤
      ⨆ j ∈ Finset.range n, eventFieldSigma (E j) (Prod.snd '' (F : Set (ℕ × Lattice d))) :=
    finiteFieldSigma_le_truncation E F (Prod.snd '' (F : Set (ℕ × Lattice d))) n hF
  have h2 : finiteFieldSigma (fun j z => E j (z + fun _ => ((2 * r + R + 1 : ℕ) : ℤ))) F ≤
      ⨆ j ∈ Finset.range n, eventFieldSigma (E j)
        ((fun z => z + fun _ => ((2 * r + R + 1 : ℕ) : ℤ)) '' (Prod.snd '' (F : Set (ℕ × Lattice d)))) :=
    finiteFieldSigma_translate_le_truncation E F (Prod.snd '' (F : Set (ℕ × Lattice d))) n hF
      (fun _ => ((2 * r + R + 1 : ℕ) : ℤ))
  have hsp : ∀ j < n, Indep (eventFieldSigma (E j) (Prod.snd '' (F : Set (ℕ × Lattice d))))
      (eventFieldSigma (E j)
        ((fun z => z + fun _ => ((2 * r + R + 1 : ℕ) : ℤ)) '' (Prod.snd '' (F : Set (ℕ × Lattice d))))) mu := by
    intro j hj
    have hRj : Cdep * 3 ^ j ≤ R := by
      rw [hR]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    refine indep_eventFieldSigma_translate mu (E j) (hr j) (Prod.snd '' (F : Set (ℕ × Lattice d)))
      (fun _ => ((2 * r + R + 1 : ℕ) : ℤ)) ?_
    intro u hu v hv
    obtain ⟨p, hp, rfl⟩ := hu
    obtain ⟨q, hq, rfl⟩ := hv
    have hu' : (p.2 ⟨0, hd⟩).natAbs ≤ r := by
      have hc := coord_natAbs_le_finite_radius F hp ⟨0, hd⟩
      rw [← hrr] at hc
      exact hc
    have hv' : (q.2 ⟨0, hd⟩).natAbs ≤ r := by
      have hc := coord_natAbs_le_finite_radius F hq ⟨0, hd⟩
      rw [← hrr] at hc
      exact hc
    have hsep : R < latticeDist p.2 (q.2 + fun _ => ((2 * r + R + 1 : ℕ) : ℤ)) :=
      latticeDist_translate_gt_of_coordinate_bound ⟨0, hd⟩ hu' hv'
    exact Nat.lt_of_le_of_lt hRj hsep
  exact indep_of_subsigmas mu
    (indep_event_truncations mu E (Prod.snd '' (F : Set (ℕ × Lattice d)))
      ((fun z => z + fun _ => ((2 * r + R + 1 : ℕ) : ℤ)) '' (Prod.snd '' (F : Set (ℕ × Lattice d)))) n hE hsc hsp)
    h1 h2



theorem drsConditionP1_of_eventIndependence {d Cdep : ℕ} (hd : 0 < d) {Ω : Type*}
    [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (E : ℕ → Lattice d → Set Ω) (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hlaw : TranslationInvariantEventLaw mu E) : DRSConditionP1 mu E := by
  have h1 : ShiftedFiniteFieldIndependence mu E :=
    shiftedFiniteFieldIndependence_of_eventIndependence hd mu E hlaw.1 hsc hr
  have h2 : CylinderShiftIndependence mu E :=
    cylinderShiftIndependence_of_shiftedFiniteFieldIndependence hlaw.1 h1
  exact drsConditionP1_of_cylinderShiftIndependence hlaw h2


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
