module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDClauses
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalSeed

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## M3's combinatorial half: the level entropy -/



theorem card_separatedPairs_latticeBall_le_exp_sqrtTwoScheduleEntropy
    (R M k : ℕ) (x : Lattice d)
    (hM : ((2 * M + 1 : ℕ) : ℝ) ≤ 3 * sqrtTwoRatio k) :
    (((separatedPairs R (latticeBallFinset x M)).card : ℕ) : ℝ) ≤
      Real.exp (sqrtTwoScheduleEntropy ((3 : ℝ) ^ (2 * d)) d k) := by
  have hCpos : (0 : ℝ) < (3 : ℝ) ^ (2 * d) := by positivity
  have hrho : (0 : ℝ) < sqrtTwoRatio k := sqrtTwoRatio_pos k
  have hcount : (separatedPairs R (latticeBallFinset x M)).card ≤ ((2 * M + 1) ^ d) ^ 2 := by
    have := card_separatedPairs_le R (latticeBallFinset x M)
    rwa [card_latticeBallFinset x M] at this
  have hcountR : (((separatedPairs R (latticeBallFinset x M)).card : ℕ) : ℝ) ≤
      (((2 * M + 1 : ℕ) : ℝ) ^ d) ^ 2 := by
    have : (((separatedPairs R (latticeBallFinset x M)).card : ℕ) : ℝ) ≤
        ((((2 * M + 1) ^ d) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcount
    simpa using this
  have hstep : (((2 * M + 1 : ℕ) : ℝ) ^ d) ^ 2 ≤ ((3 : ℝ) * sqrtTwoRatio k ^ 1) ^ (2 * d) := by
    have hbase : (0 : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) := by positivity
    have hpow : (((2 * M + 1 : ℕ) : ℝ)) ^ (2 * d) ≤ (3 * sqrtTwoRatio k) ^ (2 * d) :=
      pow_le_pow_left₀ hbase hM (2 * d)
    calc (((2 * M + 1 : ℕ) : ℝ) ^ d) ^ 2 = ((2 * M + 1 : ℕ) : ℝ) ^ (2 * d) := by
          rw [← pow_mul]; ring_nf
      _ ≤ (3 * sqrtTwoRatio k) ^ (2 * d) := hpow
      _ = ((3 : ℝ) * sqrtTwoRatio k ^ 1) ^ (2 * d) := by rw [pow_one]
  refine hcountR.trans (hstep.trans (le_of_eq ?_))
  rw [sqrtTwoScheduleEntropy_eq_log hCpos, Real.exp_log (by positivity), pow_one, mul_pow]

/-! ## P1 and P2 -/

/-- The shift of a multiscale indicator configuration by a lattice vector. -/
def configShift (a : Lattice d) (f : ℕ × Lattice d → ℝ) : ℕ × Lattice d → ℝ :=
  fun p => f (p.1, p.2 + a)



def DRSConditionP1 [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) : Prop :=
  TranslationInvariantEventLaw mu E ∧
    ∀ A : Set (ℕ × Lattice d → ℝ), MeasurableSet A →
      (∀ a : Lattice d, configShift a ⁻¹' A = A) →
      Measure.map (eventFieldConfiguration E) mu A = 0 ∨
        Measure.map (eventFieldConfiguration E) mu A = 1



theorem drsConditionP2 [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (law : ℝ → Measure (ℕ × Lattice d → ℝ))
    (hconst : ∀ u : ℝ, law u = Measure.map (eventFieldConfiguration E) mu) :
    ∀ u v : ℝ, law u = law v := fun u v => by rw [hconst u, hconst v]



def DRSConditionP3 [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cdep : ℕ) (cP : ℝ) : Prop :=
  ∀ (L R : ℕ), 1 ≤ L → 1 ≤ R →
    ∀ (A B : Set Ω) (x1 x2 : Lattice d),
      R * L ≤ latticeDist x1 x2 →
      MeasurableSet[⨆ j, eventFieldSigma (E j)
        (latticeBallFinset x1 (10 * L) : Set (Lattice d))] A →
      MeasurableSet[⨆ j, eventFieldSigma (E j)
        (latticeBallFinset x2 (10 * L) : Set (Lattice d))] B →
      ∃ (j0 : ℕ) (A' B' : Set Ω),
        100 * (Cdep * 3 ^ j0) ≤ R * L ∧
        MeasurableSet[⨆ j ∈ Finset.range (j0 + 1), eventFieldSigma (E j)
          (latticeBallFinset x1 (10 * L) : Set (Lattice d))] A' ∧
        MeasurableSet[⨆ j ∈ Finset.range (j0 + 1), eventFieldSigma (E j)
          (latticeBallFinset x2 (10 * L) : Set (Lattice d))] B' ∧
        mu (A' \ A) + mu (A \ A') + mu (B' \ B) + mu (B \ B') ≤
          ENNReal.ofReal (Real.exp (-(cP * ((R * L : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))) ∧
        mu (A' ∩ B') = mu A' * mu B'



def highLevelInfluence (E : ℕ → Lattice d → Set Ω) (Cbox j0 : ℕ)
    (z : Lattice d) : Set Ω :=
  ⋃ j : ℕ, influenceFailure (E (j + j0 + 1)) (Cbox * 3 ^ (j + j0 + 1)) z

/-- **The truncation tail.**  The same union bound as the bad-site estimate, run
from level `j₀ + 1` on. -/
theorem measure_highLevelInfluence_le_tsum [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cbox j0 : ℕ) (z : Lattice d) (p : ℕ → ℝ≥0∞)
    (hp : ∀ j u, mu (E j u) ≤ p j) :
    mu (highLevelInfluence E Cbox j0 z) ≤
      ∑' j : ℕ, (((2 * (Cbox * 3 ^ (j + j0 + 1)) + 1) ^ d : ℕ) : ℝ≥0∞) *
        p (j + j0 + 1) := by
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
  have h := measure_influenceFailure_le (μ := mu) (E (j + j0 + 1))
    (Cbox * 3 ^ (j + j0 + 1)) z (p (j + j0 + 1)) (hp (j + j0 + 1))
  rwa [nsmul_eq_mul] at h

/-! ## S1: connectivity in the double ball, from `[Timár]` -/



def GoodConnectedInDoubleBall (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (z : Lattice d) (L : ℕ) : Prop :=
  ∀ v w : Lattice d, InLatticeBallReal z v L → InLatticeBallReal z w L →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 10) v →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 10) w →
    JStepReachableIn 1
      {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} v w



def GoodConnectedInDoubleBallAt (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (z : Lattice d) (L : ℕ) (D : ℝ) : Prop :=
  ∀ v w : Lattice d, InLatticeBallReal z v L → InLatticeBallReal z w L →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω D v →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω D w →
    JStepReachableIn 1
      {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} v w

/-- `GoodConnectedInDoubleBall` is the case `D = L / 10`. -/
theorem goodConnectedInDoubleBall_iff_at (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (ω : Ω) (z : Lattice d) (L : ℕ) :
    GoodConnectedInDoubleBall E Cbox ω z L ↔
      GoodConnectedInDoubleBallAt E Cbox ω z L ((L : ℝ) / 10) := Iff.rfl



def TimarBoundaryInput (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (ω : Ω)
    (z : Lattice d) (L : ℕ) : Prop :=
  (∀ v : Lattice d, InLatticeBallReal z v (2 * L : ℝ) →
      ¬ IsPercolationGoodSite E Cbox ω v →
      HasLatticeDiameterAtMost
        (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox ω u} v) ((L : ℝ) / 100)) →
    GoodConnectedInDoubleBall E Cbox ω z L

/-- **The deterministic half of S1.**  Clause (ii) at the centre `z`, once its
right-hand side is below `L / 100` at the radius `2 L`, feeds `[Timár, Lemma 2]`
and delivers S1 at scale `L`. -/
theorem goodConnectedInDoubleBall_of_badComponentDiameterBound
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {ω : Ω} {z : Lattice d} {C q : ℝ}
    {h L : ℕ}
    (hbad : BadComponentDiameterBound E Cbox J ω z C q h)
    (hsmall : C * (1 + h + q⁻¹ * Real.log (2 + (2 * L : ℝ))) ^ 2 ≤ (L : ℝ) / 100)
    (htimar : TimarBoundaryInput E Cbox J ω z L) :
    GoodConnectedInDoubleBall E Cbox ω z L := by
  refine htimar fun v hv hvbad => ?_
  have hL : (0 : ℝ) ≤ 2 * L := by positivity
  exact fun a ha b hb i => ((hbad (2 * L : ℝ) hL v hv hvbad) a ha b hb i).trans hsmall

/-! ## S2: the density of the infinite good component -/

/-- A site lies in the infinite good component. -/
def InInfiniteGoodComponent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (v : Lattice d) : Prop :=
  IsPercolationGoodSite E Cbox ω v ∧
    ¬ (jStepComponent 1 {u | IsPercolationGoodSite E Cbox ω u} v).Finite

/-- The event that `v` is good but its good component is finite. -/
def goodFiniteComponentEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (v : Lattice d) : Set Ω :=
  {ω | IsPercolationGoodSite E Cbox ω v ∧
    (jStepComponent 1 {u | IsPercolationGoodSite E Cbox ω u} v).Finite}



theorem not_inInfiniteGoodComponent_subset (E : ℕ → Lattice d → Set Ω)
    (Cbox : ℕ) (v : Lattice d) :
    {ω : Ω | ¬ InInfiniteGoodComponent E Cbox ω v} ⊆
      percolationBadSite E Cbox v ∪ goodFiniteComponentEvent E Cbox v := by
  intro ω hω
  by_cases hgood : IsPercolationGoodSite E Cbox ω v
  · refine Or.inr ⟨hgood, ?_⟩
    by_contra hfin
    exact hω ⟨hgood, hfin⟩
  · exact Or.inl hgood



def DRSConditionS2 [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) : Prop :=
  ENNReal.ofReal (4 / 5) ≤
    mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}

/-- **S2 from the two bad-site bounds.**  If being bad and being good with a
finite component each have probability at most `b`, and `2 b ≤ 1/5`, then S2
holds. -/
theorem drsConditionS2_of_bounds [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {b : ℝ≥0∞}
    (hmeas : MeasurableSet {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)})
    (hbad : mu (percolationBadSite E Cbox (fun _ => 0)) ≤ b)
    (hfin : mu (goodFiniteComponentEvent E Cbox (fun _ => 0)) ≤ b)
    (hb : 2 * b ≤ ENNReal.ofReal (1 / 5)) :
    DRSConditionS2 mu E Cbox := by
  have hcompl : mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}ᶜ ≤ 2 * b := by
    refine (measure_mono (not_inInfiniteGoodComponent_subset E Cbox _)).trans ?_
    refine (measure_union_le _ _).trans ?_
    have := add_le_add hbad hfin
    simpa [two_mul] using this
  have hle : mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}ᶜ ≤
      ENNReal.ofReal (1 / 5) := hcompl.trans hb
  have hprob : mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)} +
      mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}ᶜ = 1 := by
    rw [measure_add_measure_compl hmeas, measure_univ]
  have hsplit : ENNReal.ofReal (4 / 5) + ENNReal.ofReal (1 / 5) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  by_contra hcon
  simp only [DRSConditionS2, not_le] at hcon
  have : mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)} +
      mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}ᶜ <
      ENNReal.ofReal (4 / 5) + ENNReal.ofReal (1 / 5) :=
    ENNReal.add_lt_add_of_lt_of_le (by finiteness) hcon hle
  rw [hprob, hsplit] at this
  exact lt_irrefl _ this

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
