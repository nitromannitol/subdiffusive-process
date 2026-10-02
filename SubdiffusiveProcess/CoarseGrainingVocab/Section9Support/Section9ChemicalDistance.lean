import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.EventIndependence




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}



def IsShortGoodPath (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (bound : ℝ) (v w : Lattice d) : Prop :=
  ∃ path : List (Lattice d),
    path.head? = some v ∧ path.getLast? = some w ∧
      (path.length : ℝ) ≤ bound ∧ IsJStepListPath 1 path ∧
        ∀ u ∈ path, IsPercolationGoodSite E Cbox ω u

/-- Enlarging the length budget weakens `IsShortGoodPath`. -/
theorem IsShortGoodPath.mono {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω}
    {bound bound' : ℝ} {v w : Lattice d} (hb : bound ≤ bound')
    (h : IsShortGoodPath E Cbox ω bound v w) :
    IsShortGoodPath E Cbox ω bound' v w := by
  obtain ⟨path, hhead, hlast, hlen, hstep, hgood⟩ := h
  exact ⟨path, hhead, hlast, hlen.trans hb, hstep, hgood⟩



def chemicalDistanceFailureEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) (L : ℕ) : Set Ω :=
  {ω | ∃ v w : Lattice d,
      InLatticeBallReal z v L ∧ InLatticeBallReal z w L ∧
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) v ∧
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) w ∧
      ¬ IsShortGoodPath E Cbox ω (Clen * L) v w}

/-- Enlarging a real ball radius weakens membership. -/
theorem inLatticeBallReal_mono {z v : Lattice d} {R S : ℝ} (hRS : R ≤ S)
    (hv : InLatticeBallReal z v R) : InLatticeBallReal z v S :=
  fun i => (hv i).trans hRS

/-- Lowering the required diameter weakens `InGoodComponentOfDiameterAtLeast`. -/
theorem inGoodComponentOfDiameterAtLeast_mono {E : ℕ → Lattice d → Set Ω}
    {Cbox J : ℕ} {ω : Ω} {R S : ℝ} {v : Lattice d} (hSR : S ≤ R)
    (hv : InGoodComponentOfDiameterAtLeast E Cbox J ω R v) :
    InGoodComponentOfDiameterAtLeast E Cbox J ω S v := by
  obtain ⟨hgood, u, w, hu, hw, hdist⟩ := hv
  exact ⟨hgood, u, w, hu, hw, hSR.trans hdist⟩



theorem isShortGoodPath_of_not_mem_chemicalDistanceFailureEvent
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {z : Lattice d} {ω : Ω}
    {l L : ℕ} (hClen : 0 ≤ Clen) (hlL : l ≤ L) (hL2l : (L : ℝ) ≤ 2 * l)
    (hnot : ω ∉ chemicalDistanceFailureEvent E Cbox Clen z L)
    {v w : Lattice d}
    (hv : InLatticeBallReal z v l) (hw : InLatticeBallReal z w l)
    (hvc : InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) v)
    (hwc : InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) w) :
    IsShortGoodPath E Cbox ω (2 * Clen * l) v w := by
  by_contra hpath
  refine hnot ⟨v, w, ?_, ?_, ?_, ?_, ?_⟩
  · exact inLatticeBallReal_mono (by exact_mod_cast hlL) hv
  · exact inLatticeBallReal_mono (by exact_mod_cast hlL) hw
  · exact inGoodComponentOfDiameterAtLeast_mono (by linarith) hvc
  · exact inGoodComponentOfDiameterAtLeast_mono (by linarith) hwc
  · intro hshort
    exact hpath (hshort.mono (by nlinarith))

/-- The set of dyadic heights above which no chemical-distance failure occurs at
the centre `z`. -/
def chemicalDistanceHeightSet (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) (ω : Ω) : Set ℕ :=
  {h | ∀ n : ℕ, h ≤ n → ω ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)}



def chemicalDistanceHeight (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) (ω : Ω) : ℕ :=
  sInf (chemicalDistanceHeightSet E Cbox Clen z ω) + 1

theorem one_le_chemicalDistanceHeight (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) (ω : Ω) :
    1 ≤ chemicalDistanceHeight E Cbox Clen z ω :=
  Nat.le_add_left 1 _

/-- Above the height there is no failure, provided some threshold works at all. -/
theorem not_mem_chemicalDistanceFailureEvent_of_chemicalDistanceHeight_le
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {z : Lattice d} {ω : Ω}
    (hne : (chemicalDistanceHeightSet E Cbox Clen z ω).Nonempty) {n : ℕ}
    (hn : chemicalDistanceHeight E Cbox Clen z ω ≤ n) :
    ω ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n) :=
  Nat.sInf_mem hne n (le_trans (Nat.le_succ _) hn)

/-- The tail inclusion behind `P[H₂(z) > h] ≤ C e^{-c q h}`. -/
theorem chemicalDistanceHeight_gt_subset (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) (h : ℕ) :
    {ω | h + 1 < chemicalDistanceHeight E Cbox Clen z ω} ⊆
      ⋃ n ∈ {n : ℕ | h ≤ n}, chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n) := by
  intro ω hω
  simp only [mem_setOf_eq, chemicalDistanceHeight, add_lt_add_iff_right] at hω
  have hnot : h ∉ chemicalDistanceHeightSet E Cbox Clen z ω := fun hmem =>
    absurd (Nat.sInf_le hmem) (not_le.mpr hω)
  simp only [chemicalDistanceHeightSet, mem_setOf_eq, not_forall, not_not] at hnot
  obtain ⟨n, hhn, hmem⟩ := hnot
  exact mem_biUnion hhn hmem

/-- **The dyadic passage.**  If no chemical-distance failure occurs at any dyadic
radius `2 ^ n` with `n ≥ h`, then clause (iii) of
`FiniteRangePercolationGeometry` holds at every radius `l ≥ exp (Cexp * h)`, with
length constant `2 * Clen`. -/
theorem isShortGoodPath_of_dyadic_threshold
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen Cexp : ℝ} {z : Lattice d} {ω : Ω}
    {h : ℕ} (hClen : 0 ≤ Clen) (hCexp : Real.log 2 ≤ Cexp)
    (hheight : ∀ n : ℕ, h ≤ n →
      ω ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n))
    {l : ℕ} (hl : Real.exp (Cexp * h) ≤ l)
    {v w : Lattice d}
    (hv : InLatticeBallReal z v l) (hw : InLatticeBallReal z w l)
    (hvc : InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) v)
    (hwc : InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) w) :
    IsShortGoodPath E Cbox ω (2 * Clen * l) v w := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : ((2 : ℝ) ^ h) ≤ (l : ℝ) := by
    have hmono : Real.exp (Real.log 2 * h) ≤ Real.exp (Cexp * h) :=
      Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) h])
    have hval : Real.exp (Real.log 2 * h) = (2 : ℝ) ^ h := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    linarith [hval ▸ hmono]
  have hpowNat : 2 ^ h ≤ l := by exact_mod_cast hpow
  have hlpos : 0 < l := lt_of_lt_of_le Nat.one_le_two_pow hpowNat
  set n := Nat.log 2 l with hn
  have hhn : h ≤ n := (Nat.le_log_iff_pow_le (by norm_num) hlpos.ne').mpr hpowNat
  have hlt : l < 2 ^ (n + 1) := Nat.lt_pow_succ_log_self (by norm_num) l
  have hle : 2 ^ n ≤ l := Nat.pow_log_le_self 2 hlpos.ne'
  refine isShortGoodPath_of_not_mem_chemicalDistanceFailureEvent hClen
    (le_of_lt hlt) ?_ (hheight (n + 1) (hhn.trans (Nat.le_succ n))) hv hw hvc hwc
  have h2 : ((2 : ℝ) ^ n) ≤ (l : ℝ) := by exact_mod_cast hle
  have hrw : (((2 : ℕ) ^ (n + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ n := by push_cast; ring
  rw [hrw]
  linarith

/-- **Clause (iii) of `FiniteRangePercolationGeometry`, from the dyadic
thresholds.**  With one constant `C` dominating both `log 2` (for the dyadic
passage) and `2 * Clen` (for the length budget), absence of chemical-distance
failures above the dyadic height `component` gives the third clause verbatim. -/
theorem goodPathClause_of_dyadic_threshold
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen C : ℝ} {z : Lattice d} {ω : Ω}
    {component : ℕ} (hClen : 0 ≤ Clen) (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C)
    (hheight : ∀ n : ℕ, component ≤ n →
      ω ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) :
    ∀ l : ℕ, Real.exp (C * component) ≤ l →
      ∀ v w : Lattice d,
      InLatticeBallReal z v l → InLatticeBallReal z w l →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) v →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) w →
      ∃ path : List (Lattice d),
        path.head? = some v ∧ path.getLast? = some w ∧
          (path.length : ℝ) ≤ C * l ∧ IsJStepListPath 1 path ∧
            ∀ u ∈ path, IsPercolationGoodSite E Cbox ω u := by
  intro l hl v w hv hw hvc hwc
  have hshort :=
    isShortGoodPath_of_dyadic_threshold (Cexp := C) hClen hC1 hheight hl hv hw hvc hwc
  have hbound : 2 * Clen * (l : ℝ) ≤ C * l :=
    mul_le_mul_of_nonneg_right hC2 (Nat.cast_nonneg l)
  exact hshort.mono hbound



def UniformChemicalDistanceBound (d Cdep : ℕ) (Cprob cprob : ℝ) : Prop :=
  ∃ q0 Cbox : ℕ, ∃ c Cfail Clen : ℝ,
    0 < c ∧ 0 < Cfail ∧ 0 ≤ Clen ∧
    ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
      [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
      (q0 : ℝ) ≤ q →
      (∀ j z, mu (E j z) ≤
        ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
      IndependentEventScales mu E →
      MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
      TranslationInvariantEventLaw mu E →
      ∀ (z : Lattice d) (L : ℕ), 1 ≤ L →
        mu (chemicalDistanceFailureEvent E Cbox Clen z L) ≤
          ENNReal.ofReal (Cfail * Real.exp (-c * q * Real.log L ^ 2))



theorem finiteRangePercolationGeometry_of_chemicalDistanceThresholds
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {Clen c C q : ℝ}
    {crossing component : Lattice d → Ω → ℕ}
    (hc : 0 < c) (hClen : 0 ≤ Clen) (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C)
    (hcross : ∀ (ω : Ω) (z : Lattice d), ∀ l : ℕ, crossing z ω ≤ l →
      ∀ path : List (Lattice d), IsJStepListPath J path →
      (∃ v ∈ path, InLatticeBallReal z v (l / 3 : ℝ)) →
      (∃ v ∈ path, ¬InLatticeBallReal z v (2 * l / 3 : ℝ)) →
      ∃ chosen : List (Lattice d),
        chosen.Sublist path ∧ c * l ≤ chosen.length ∧
          (∀ v ∈ chosen,
            IsPercolationGoodSite E Cbox ω v ∧
              latticeBallSet v Cbox ⊆
                latticeBallSet z (3 * l / 4 : ℝ) \ latticeBallSet z (l / 4 : ℝ)) ∧
          chosen.Pairwise fun v w ↦
            Disjoint (latticeBallSet v Cbox) (latticeBallSet w Cbox))
    (hbad : ∀ (ω : Ω) (z : Lattice d), ∀ s : ℝ, 0 ≤ s → ∀ v : Lattice d,
      InLatticeBallReal z v s → ¬IsPercolationGoodSite E Cbox ω v →
      HasLatticeDiameterAtMost
        (jStepComponent J {u | ¬IsPercolationGoodSite E Cbox ω u} v)
        (C * (1 + component z ω + q⁻¹ * Real.log (2 + s)) ^ 2))
    (hheight : ∀ (ω : Ω) (z : Lattice d) (n : ℕ), component z ω ≤ n →
      ω ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) :
    FiniteRangePercolationGeometry E Cbox J c C q crossing component :=
  ⟨hc, fun ω z =>
    ⟨hcross ω z, hbad ω z,
      goodPathClause_of_dyadic_threshold hClen hC1 hC2 (hheight ω z)⟩⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
