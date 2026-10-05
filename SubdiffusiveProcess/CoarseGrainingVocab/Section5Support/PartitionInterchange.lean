module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteSlopeSelection
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# The countable-partition interchange

`DiscreteSlopeSelection.lean` produces a **countably valued** selection: a
measurable index `n : Omega -> Nat` and a sample-free family `D` such that the
slopes of the sample `omega` are `D (n omega)`.  The fibers `{n = m}` are
therefore a countable measurable partition of the sample space on each piece of
which the selected data is one *deterministic* member of the family.

Step 3 of the strict-decay proof (paper label `p.homogenized.coefficient.strict.decay`) consumes exactly
that: it freezes the slopes, uses the independence of the inner coefficient from
the outer layer piece by piece, and reassembles.  The reassembly is the
interchange of the Bochner integral with the countable partition, which is
`MeasureTheory.hasSum_integral_iUnion` on the fibers.

* `hasSum_setIntegral_fiber` -- the partition identity
  `E[f] = sum_m E[1_{n = m} f]`, as a `HasSum`;
* **`integral_le_of_setIntegral_fiber_le`** -- the comparison the induction
  performs: if the fibrewise integrals are ordered, so are the integrals;
* `setIntegral_fiber_congr` -- replacing the selected data by its deterministic
  value on a fiber;
* `setIntegral_mul_eq_integral_indicator_mul` -- the fibrewise product written as
  a product of the indicator with the second factor, which is the shape the
  independence factorization consumes.

Nothing here is specific to the GMC: the statements are about an arbitrary
measure space and an arbitrary measurable `Nat`-valued index.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The fibers of a measurable index are measurable. -/
theorem measurableSet_index_fiber {n : Ω → ℕ} (hn : Measurable n) (m : ℕ) :
    MeasurableSet {ω | n ω = m} :=
  hn (measurableSet_singleton m)

/-- **The countable partition identity.**  The fibers of a measurable
`Nat`-valued index partition the space, so the integral of an integrable
function is the sum of its integrals over the fibers. -/
theorem hasSum_setIntegral_fiber {f : Ω → ℝ} {n : Ω → ℕ} (hn : Measurable n)
    (hf : Integrable f P) :
    HasSum (fun m : ℕ => ∫ ω in {ω | n ω = m}, f ω ∂P) (∫ ω, f ω ∂P) := by
  have hm : ∀ m : ℕ, MeasurableSet {ω : Ω | n ω = m} := measurableSet_index_fiber hn
  have hd : Pairwise (Function.onFun Disjoint fun m : ℕ => {ω : Ω | n ω = m}) := by
    intro a b hab
    refine Set.disjoint_left.2 fun ω ha hb => ?_
    exact hab ((show n ω = a from ha).symm.trans (show n ω = b from hb))
  have huniv : (⋃ m : ℕ, {ω : Ω | n ω = m}) = Set.univ := by
    ext ω
    simp
  have h := hasSum_integral_iUnion (f := f) (μ := P) hm hd
    (by rw [huniv]; exact hf.integrableOn)
  rw [huniv, Measure.restrict_univ] at h
  exact h

/-- **The countable-partition interchange.**  Two integrable functions whose
integrals over every fiber of a measurable index are ordered have ordered
integrals. -/
theorem integral_le_of_setIntegral_fiber_le {f g : Ω → ℝ} {n : Ω → ℕ}
    (hn : Measurable n) (hf : Integrable f P) (hg : Integrable g P)
    (h : ∀ m : ℕ, ∫ ω in {ω | n ω = m}, f ω ∂P ≤ ∫ ω in {ω | n ω = m}, g ω ∂P) :
    ∫ ω, f ω ∂P ≤ ∫ ω, g ω ∂P :=
  hasSum_le h (hasSum_setIntegral_fiber hn hf) (hasSum_setIntegral_fiber hn hg)

/-- On a fiber the selected data is deterministic, so the integrand may be
replaced by its value. -/
theorem setIntegral_fiber_congr {f g : Ω → ℝ} {n : Ω → ℕ} (hn : Measurable n)
    (m : ℕ) (h : ∀ ω, n ω = m → f ω = g ω) :
    ∫ ω in {ω | n ω = m}, f ω ∂P = ∫ ω in {ω | n ω = m}, g ω ∂P :=
  setIntegral_congr_fun (measurableSet_index_fiber hn m) fun ω hω => h ω hω

/-- The fibrewise integral of a product is the integral of the indicator of the
fiber against the second factor. -/
theorem setIntegral_mul_eq_integral_indicator_mul {X Y : Ω → ℝ} {s : Set Ω}
    (hs : MeasurableSet s) :
    ∫ ω in s, X ω * Y ω ∂P = ∫ ω, s.indicator X ω * Y ω ∂P := by
  rw [← integral_indicator hs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]

omit [MeasurableSpace Ω] in
/-- The indicator of a fiber against a function measurable for a
sub-sigma-algebra is again measurable for it. -/
theorem measurable_indicator_fiber_mul {m₀ : MeasurableSpace Ω} {n : Ω → ℕ}
    {X : Ω → ℝ} (hn : Measurable[m₀] n) (hX : Measurable[m₀] X) (k : ℕ) :
    Measurable[m₀] (Set.indicator {ω | n ω = k} X) :=
  hX.indicator (hn (measurableSet_singleton k))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
