import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalForcing
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDistance
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePathSelection
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangeLatticeBallSeparation
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationConnectivity




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*}

/-! ## Clause (i): the crossing density -/



def AnnulusGoodSite (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (z : Lattice d) (l : ℕ) (v : Lattice d) : Prop :=
  IsPercolationGoodSite E Cbox ω v ∧
    latticeBallSet v Cbox ⊆
      latticeBallSet z (3 * l / 4 : ℝ) \ latticeBallSet z (l / 4 : ℝ)



def CrossingGoodCount (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (ω : Ω)
    (z : Lattice d) (l N : ℕ) : Prop :=
  ∀ path : List (Lattice d), IsJStepListPath J path →
    (∃ v ∈ path, InLatticeBallReal z v (l / 3 : ℝ)) →
    (∃ v ∈ path, ¬ InLatticeBallReal z v (2 * l / 3 : ℝ)) →
    ∃ S : Finset (Lattice d),
      (∀ v ∈ S, v ∈ path) ∧ (∀ v ∈ S, AnnulusGoodSite E Cbox ω z l v) ∧ N ≤ S.card

/-- The blocking relation of the greedy selection: two centres block each other
when their `Cbox`-boxes can meet. -/
private def BoxBlocks (Cbox : ℕ) (v w : Lattice d) : Prop :=
  latticeDist v w ≤ 2 * Cbox

private theorem boxBlocks_refl (Cbox : ℕ) : Reflexive (BoxBlocks (d := d) Cbox) := by
  intro v
  simp [BoxBlocks]

private theorem boxBlocks_symm (Cbox : ℕ) : Symmetric (BoxBlocks (d := d) Cbox) := by
  intro v w h
  simpa [BoxBlocks, latticeDist_comm v w] using h

/-- Centres that do not block each other carry disjoint `Cbox`-boxes. -/
theorem disjoint_latticeBallSet_of_not_boxBlocks {Cbox : ℕ} {v w : Lattice d}
    (h : ¬ BoxBlocks Cbox v w) :
    Disjoint (latticeBallSet v (Cbox : ℝ)) (latticeBallSet w (Cbox : ℝ)) := by
  have hlt : 2 * Cbox < latticeDist v w := Nat.lt_of_not_ge h
  have hex : ∃ i ∈ (Finset.univ : Finset (Fin d)), 2 * Cbox < (v i - w i).natAbs := by
    rw [latticeDist] at hlt
    exact Finset.lt_sup_iff.mp hlt
  obtain ⟨i, -, hi⟩ := hex
  refine latticeBallSet_disjoint_of_exists_two_mul_lt ⟨i, ?_⟩
  have hz : (|v i - w i| : ℤ) = (((v i - w i).natAbs : ℕ) : ℤ) :=
    (Int.natCast_natAbs _).symm
  rw [hz]
  exact_mod_cast hi

/-- **Clause (i) of `FiniteRangePercolationGeometry`, from `[ASD, Lemma B.1(2)]`.**

The greedy selection keeps a `1 / (4 Cbox + 1) ^ d` fraction of the annulus-good
vertices of the crossing, in chronological order, with pairwise disjoint boxes. -/
theorem crossingClause_of_crossingGoodCount
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {ω : Ω} {z : Lattice d} {l N : ℕ}
    {c : ℝ} (hc : c * l * ((2 * (2 * Cbox) + 1) ^ d : ℕ) ≤ (N : ℝ))
    (hcount : CrossingGoodCount E Cbox J ω z l N) :
    ∀ path : List (Lattice d), IsJStepListPath J path →
      (∃ v ∈ path, InLatticeBallReal z v (l / 3 : ℝ)) →
      (∃ v ∈ path, ¬ InLatticeBallReal z v (2 * l / 3 : ℝ)) →
      ∃ chosen : List (Lattice d),
        chosen.Sublist path ∧ c * l ≤ chosen.length ∧
          (∀ v ∈ chosen,
            IsPercolationGoodSite E Cbox ω v ∧
              latticeBallSet v Cbox ⊆
                latticeBallSet z (3 * l / 4 : ℝ) \ latticeBallSet z (l / 4 : ℝ)) ∧
          chosen.Pairwise fun v w ↦
            Disjoint (latticeBallSet v Cbox) (latticeBallSet w Cbox) := by
  classical
  intro path hpath hstart hexit
  obtain ⟨S, hSpath, hSgood, hSN⟩ := hcount path hpath hstart hexit
  set q : List (Lattice d) := path.dedup with hq
  set good : Set (Lattice d) := {v | AnnulusGoodSite E Cbox ω z l v} with hgood
  have hqnodup : q.Nodup := List.nodup_dedup path
  have hqsub : q.Sublist path := List.dedup_sublist path
  -- the count survives loop erasure
  have hSsub : S ⊆ (q.filter fun x ↦ decide (x ∈ good)).toFinset := by
    intro v hv
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨by rw [hq, List.mem_dedup]; exact hSpath v hv, hSgood v hv⟩
  have hN : N ≤ (q.filter fun x ↦ decide (x ∈ good)).length := by
    have hnodup : (q.filter fun x ↦ decide (x ∈ good)).Nodup := hqnodup.filter _
    calc N ≤ S.card := hSN
      _ ≤ (q.filter fun x ↦ decide (x ∈ good)).toFinset.card := Finset.card_le_card hSsub
      _ = (q.filter fun x ↦ decide (x ∈ good)).length :=
          List.toFinset_card_of_nodup hnodup
  -- the fibres of the blocking relation are bounded by a ball count
  have hbounded : ∀ y ∈ q.toFinset.filter (· ∈ good),
      ((q.toFinset.filter (· ∈ good)).filter (BoxBlocks Cbox y)).card ≤
        (2 * (2 * Cbox) + 1) ^ d := by
    intro y _
    have hsub : (q.toFinset.filter (· ∈ good)).filter (BoxBlocks Cbox y) ⊆
        latticeBallFinset y (2 * Cbox) := by
      intro x hx
      have hxb : BoxBlocks Cbox y x := (Finset.mem_filter.mp hx).2
      exact mem_latticeBallFinset_iff.mpr hxb
    calc ((q.toFinset.filter (· ∈ good)).filter (BoxBlocks Cbox y)).card
        ≤ (latticeBallFinset y (2 * Cbox)).card := Finset.card_le_card hsub
      _ = (2 * (2 * Cbox) + 1) ^ d := card_latticeBallFinset y (2 * Cbox)
  obtain ⟨chosen, hsublist, hpairwise, hcard, hchosenGood⟩ :=
    exists_chronological_pairwise_not_blocks_of_count q hqnodup good
      (BoxBlocks Cbox) ((2 * (2 * Cbox) + 1) ^ d) N
      (boxBlocks_refl Cbox) (boxBlocks_symm Cbox) hN hbounded
  refine ⟨chosen, hsublist.trans hqsub, ?_, ?_, ?_⟩
  · have hcardR : (N : ℝ) ≤ (chosen.length : ℝ) * ((2 * (2 * Cbox) + 1) ^ d : ℕ) := by
      exact_mod_cast hcard
    have hDpos : (0 : ℝ) < ((2 * (2 * Cbox) + 1) ^ d : ℕ) := by positivity
    nlinarith
  · intro v hv
    exact hchosenGood v hv
  · refine hpairwise.imp ?_
    intro v w hvw
    exact disjoint_latticeBallSet_of_not_boxBlocks hvw

/-! ## Clause (ii): the bad-component diameter -/



def badComponentFailureEvent (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ)
    (z : Lattice d) (s R : ℝ) : Set Ω :=
  {ω | ∃ v : Lattice d, InLatticeBallReal z v s ∧
      ¬ IsPercolationGoodSite E Cbox ω v ∧
      ¬ HasLatticeDiameterAtMost
          (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox ω u} v) R}

/-- Clause (ii) of `FiniteRangePercolationGeometry`, isolated at one centre. -/
def BadComponentDiameterBound (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (ω : Ω)
    (z : Lattice d) (C q : ℝ) (h : ℕ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ v : Lattice d,
    InLatticeBallReal z v s → ¬ IsPercolationGoodSite E Cbox ω v →
    HasLatticeDiameterAtMost
      (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox ω u} v)
      (C * (1 + h + q⁻¹ * Real.log (2 + s)) ^ 2)

/-- **Clause (ii) from the integer-radius union bound.**

The manuscript's union bound in `[ASD, Lemma B.1(3)]` runs over integer radii.
Rounding a real `s` up to `⌈s⌉₊ ≤ s + 1` enlarges `log (2 + s)` by at most
`log 2 ≤ q⁻¹`-times the same quantity, so the clause holds at every real `s` with
the constant multiplied by `4`. -/
theorem badComponentDiameterBound_of_natRadius
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {ω : Ω} {z : Lattice d} {C q : ℝ}
    {h : ℕ} (hC : 0 ≤ C) (hq : 0 < q)
    (hnat : ∀ m : ℕ, ω ∉ badComponentFailureEvent E Cbox J z m
      (C * (1 + h + q⁻¹ * Real.log (2 + m)) ^ 2)) :
    BadComponentDiameterBound E Cbox J ω z (4 * C) q h := by
  intro s hs v hv hbad
  set m : ℕ := ⌈s⌉₊ with hm
  have hsm : s ≤ (m : ℝ) := Nat.le_ceil s
  have hms : (m : ℝ) ≤ s + 1 := by
    have := Nat.ceil_le_floor_add_one s
    have hfl : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs
    have : (m : ℝ) ≤ (⌊s⌋₊ : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hvm : InLatticeBallReal z v (m : ℝ) := inLatticeBallReal_mono hsm hv
  have hno := hnat m
  simp only [badComponentFailureEvent, Set.mem_setOf_eq, not_exists, not_and, not_not] at hno
  have hdiam := hno v hvm hbad
  refine fun a ha b hb i => (hdiam a ha b hb i).trans ?_
  -- the constant comparison
  have hlogs : Real.log 2 ≤ Real.log (2 + s) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogm : Real.log (2 + m) ≤ Real.log 2 + Real.log (2 + s) := by
    have hle : (2 : ℝ) + m ≤ 2 * (2 + s) := by linarith
    calc Real.log (2 + m) ≤ Real.log (2 * (2 + s)) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log 2 + Real.log (2 + s) := Real.log_mul (by norm_num) (by linarith)
  have hqinv : 0 < q⁻¹ := inv_pos.mpr hq
  set A : ℝ := 1 + h + q⁻¹ * Real.log (2 + s) with hA
  have hA1 : 1 ≤ A := by
    have : 0 ≤ q⁻¹ * Real.log (2 + s) := by
      have : 0 ≤ Real.log (2 + s) := le_trans (Real.log_nonneg (by norm_num)) hlogs
      positivity
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    linarith
  have hB : 1 + h + q⁻¹ * Real.log (2 + m) ≤ 2 * A := by
    have hstep : q⁻¹ * Real.log (2 + m) ≤ q⁻¹ * (Real.log 2 + Real.log (2 + s)) :=
      mul_le_mul_of_nonneg_left hlogm hqinv.le
    have hlog2 : q⁻¹ * Real.log 2 ≤ q⁻¹ * Real.log (2 + s) :=
      mul_le_mul_of_nonneg_left hlogs hqinv.le
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    simp only [hA]
    nlinarith
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hlogmnn : 0 ≤ Real.log (2 + (m : ℝ)) := Real.log_nonneg (by linarith)
  have hBnn : 0 ≤ 1 + (h : ℝ) + q⁻¹ * Real.log (2 + m) := by
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    have := mul_nonneg hqinv.le hlogmnn
    linarith
  have hsq : (1 + (h : ℝ) + q⁻¹ * Real.log (2 + m)) ^ 2 ≤ (2 * A) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * A - (1 + (h : ℝ) + q⁻¹ * Real.log (2 + m)))
      (by linarith : (0 : ℝ) ≤ 2 * A + (1 + (h : ℝ) + q⁻¹ * Real.log (2 + m)))]
  calc C * (1 + (h : ℝ) + q⁻¹ * Real.log (2 + m)) ^ 2 ≤ C * (2 * A) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hC
    _ = 4 * C * A ^ 2 := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
