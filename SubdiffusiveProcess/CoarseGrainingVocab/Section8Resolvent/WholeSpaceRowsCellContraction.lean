module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsLocalL2
public import SubdiffusiveProcess.Section8.WholeSpaceDivergenceResolventSolution
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayExterior

@[expose] public section

/-!
# The cell contraction for the whole-space carrier

`s.fixed.coefficient` and `mfd:sec-speed` reads

> If `t⁻¹ u − ∇·(a_L ∇u) = 0` on the centered enlargement of a cell `Q`,
> The local `L²` resolvent lemma, applied there, gives
> `‖u‖²_{L²(Q)} + t ‖a^{1/2}∇u‖²_{L²(Q)} ≤ eta ‖u‖²_{L²(Q̂)}`.

This file transports `localL2_resolvent_translatedCube_contraction` from an
`H¹` function on the enlargement to the carrier
`WholeSpaceDivergenceResolventSolution a t f`, whose only local information is
the certificate `locally_weak_solution`.  The hypothesis "the equation is
homogeneous on `Q̂`" is read as "`f` vanishes on `Q̂`", which is how the paper
uses it (cells outside the source family `𝒞`).

The mass-only corollary
`wholeSpaceSolution_cell_mass_contraction` is exactly the one-step contraction
hypothesis `hstep` of the established decay engine
`H1Function.integral_sq_exterior_le_of_graph_cells`
(`WholeSpaceDecaySolver.lean`), so with it the exterior row is reduced to the
*geometric* content of the whole-space resolvent partition lemma
(`s.fixed.coefficient` and `mfd:sec-speed`): a locally finite triadic partition
whose cells satisfy `t (size Q)⁻² Lam(Q̂) ≤ C⁻¹ eta` off the source and whose
graph has bounded sphere growth.

## References

* `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open _root_.SubdiffusiveProcess.Section8
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- **The cell contraction for the carrier.**

If the datum `f` vanishes on the centred threefold enlargement `Q̂` of the cube
`Q = z + □_n` and the coefficient is bounded by `Lam` there, then

```
∫_Q u² + t ∫_Q a |∇u|² ≤ 4096 d Lam t 3^{-2n} ∫_{Q̂} u² .
```

Source: `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem wholeSpaceSolution_cell_contraction
    {a : Vec d → ℝ} {t : ℝ} {f : Vec d → ℝ} {lam Lam : ℝ} {n : ℤ} {z : Vec d}
    (ht : 0 < t)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) z)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hLam : 0 ≤ Lam)
    (haLe : ∀ x ∈ translatedCube d (n + 1) z, a x ≤ Lam)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) z, f x = 0) :
    (∫ x in translatedCube d n z, u.toFun x ^ 2 ∂volume) +
        t * ∫ x in translatedCube d n z, a x * vecNormSq (u.grad x) ∂volume ≤
      4096 * (d : ℝ) * Lam * t * ((3 : ℝ) ^ n)⁻¹ ^ 2 *
        ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := by
  classical
  set W : Set (Vec d) := translatedCube d (n + 1) z with hW_def
  set Q : Set (Vec d) := translatedCube d n z with hQ_def
  have hWdom : IsOpenBoundedConvexDomain W :=
    isOpenBoundedConvexDomain_translatedCube d (n + 1) z
  have hQdom : IsOpenBoundedConvexDomain Q :=
    isOpenBoundedConvexDomain_translatedCube d n z
  have hWmeas : MeasurableSet W := hWdom.isOpen.measurableSet
  have hQmeas : MeasurableSet Q := hQdom.isOpen.measurableSet
  have hQW : Q ⊆ W := translatedCube_subset_succ d n z
  obtain ⟨v, hval, hgrad, hsol⟩ := u.locally_weak_solution W hWdom
  -- the equation is homogeneous on `W`
  have hsol0 : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
      a (fun _ ↦ (1 : ℝ)) t⁻¹ W v (fun _ ↦ (0 : ℝ)) := by
    intro phi
    refine (hsol phi).trans ?_
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    simp [hf0 x hx]
  have hbase := localL2_resolvent_translatedCube_contraction hEll haNonneg hLam
    haLe ht v hsol0
  -- transport the three integrals to the carrier's global fields
  have hQval : ∫ x in Q, v.toFun x ^ 2 ∂volume =
      ∫ x in Q, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hQmeas fun x hx ↦ ?_
    rw [hval x (hQW hx)]
  have hWval : ∫ x in W, v.toFun x ^ 2 ∂volume =
      ∫ x in W, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    rw [hval x hx]
  have hQgrad : ∫ x in Q, a x * vecNormSq (v.grad x) ∂volume =
      ∫ x in Q, a x * vecNormSq (u.grad x) ∂volume := by
    refine integral_congr_ae ?_
    have hmono : volume.restrict Q ≤ volume.restrict W :=
      Measure.restrict_mono hQW le_rfl
    filter_upwards [Filter.Eventually.filter_mono (ae_mono hmono) hgrad] with x hx
    rw [hx]
  rw [hQval, hWval, hQgrad] at hbase
  exact hbase

/-- **The one-step mass contraction**, in the exact shape of the `hstep`
hypothesis of the established decay engine.

Source: `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem wholeSpaceSolution_cell_mass_contraction
    {a : Vec d → ℝ} {t : ℝ} {f : Vec d → ℝ} {lam Lam theta : ℝ} {n : ℤ}
    {z : Vec d} (ht : 0 < t)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) z)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hLam : 0 ≤ Lam)
    (haLe : ∀ x ∈ translatedCube d (n + 1) z, a x ≤ Lam)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) z, f x = 0)
    (hsmall : 4096 * (d : ℝ) * Lam * t * ((3 : ℝ) ^ n)⁻¹ ^ 2 ≤ theta) :
    ∫ x in translatedCube d n z, u.toFun x ^ 2 ∂volume ≤
      theta * ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := by
  have hbase := wholeSpaceSolution_cell_contraction ht hEll haNonneg hLam haLe
    u hf0
  have henergy : 0 ≤ t * ∫ x in translatedCube d n z,
      a x * vecNormSq (u.grad x) ∂volume := by
    refine mul_nonneg ht.le (setIntegral_nonneg
      (isOpenBoundedConvexDomain_translatedCube d n z).isOpen.measurableSet
      fun x _ ↦ ?_)
    exact mul_nonneg (haNonneg x) (vecNormSq_nonneg _)
  have hbig : 0 ≤ ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg
      (isOpenBoundedConvexDomain_translatedCube d (n + 1) z).isOpen.measurableSet
      fun x _ ↦ sq_nonneg _
  have hmul : 4096 * (d : ℝ) * Lam * t * ((3 : ℝ) ^ n)⁻¹ ^ 2 *
      (∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume) ≤
      theta * ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume :=
    mul_le_mul_of_nonneg_right hsmall hbig
  linarith


/-! ### The neighbour covering -/

/-- The `L²` mass of a function in `L²` is finite on every set. -/
theorem wholeSpaceL2Mass_ne_top {u : Vec d → ℝ} (hu : MemLp u 2 volume)
    (s : Set (Vec d)) : wholeSpaceL2Mass u s ≠ ⊤ := by
  have hfin : ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂volume ≠ ⊤ := by
    have h := hu.integrable_sq.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    have hcongr : ∫⁻ x, ‖u x ^ 2‖ₑ ∂volume = ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂volume := by
      refine lintegral_congr fun x ↦ ?_
      exact Real.enorm_eq_ofReal (sq_nonneg _)
    rw [hcongr] at h
    exact h.ne
  refine ne_top_of_le_ne_top hfin ?_
  exact lintegral_mono' Measure.restrict_le_self le_rfl

/-- **The neighbour covering.**  If a set is covered by finitely many sets,
its `L²` mass is at most the number of them times the largest of their masses.

This is the step "the neighbor covering and
the local contraction estimate give `a_Q ≤ C eta max_{Q' ∼ Q} a_{Q'}`"
of `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem exists_mem_integral_sq_le_card_mul_of_finset_cover
    {u : Vec d → ℝ} (hu : MemLp u 2 volume) {iota : Type*}
    (s : Finset iota) (hs : s.Nonempty) (T : iota → Set (Vec d))
    {S : Set (Vec d)} (hcover : S ⊆ ⋃ i ∈ s, T i) :
    ∃ i ∈ s, ∫ x in S, u x ^ 2 ∂volume ≤
      (s.card : ℝ) * ∫ x in T i, u x ^ 2 ∂volume := by
  classical
  obtain ⟨i0, hi0, hmax⟩ :=
    s.exists_max_image (fun i ↦ wholeSpaceL2Mass u (T i)) hs
  refine ⟨i0, hi0, ?_⟩
  -- the mass of `S` is at most the sum of the masses of the covering sets
  have hstep1 : wholeSpaceL2Mass u S ≤ wholeSpaceL2Mass u (⋃ i ∈ s, T i) :=
    lintegral_mono' (Measure.restrict_mono hcover le_rfl) le_rfl
  have hbi : (⋃ i ∈ s, T i) = ⋃ i : { x // x ∈ s }, T i.1 := by
    ext x
    simp
  have hstep2 : wholeSpaceL2Mass u (⋃ i : { x // x ∈ s }, T i.1) ≤
      ∑' i : { x // x ∈ s }, wholeSpaceL2Mass u (T i.1) :=
    lintegral_iUnion_le _ _
  have hstep3 : (∑' i : { x // x ∈ s }, wholeSpaceL2Mass u (T i.1)) =
      ∑ i ∈ s, wholeSpaceL2Mass u (T i) := by
    rw [tsum_fintype]
    exact Finset.sum_coe_sort s (fun i ↦ wholeSpaceL2Mass u (T i))
  have hstep4 : (∑ i ∈ s, wholeSpaceL2Mass u (T i)) ≤
      (s.card : ℝ≥0∞) * wholeSpaceL2Mass u (T i0) := by
    calc (∑ i ∈ s, wholeSpaceL2Mass u (T i)) ≤
          ∑ _i ∈ s, wholeSpaceL2Mass u (T i0) :=
          Finset.sum_le_sum fun i hi ↦ hmax i hi
      _ = (s.card : ℝ≥0∞) * wholeSpaceL2Mass u (T i0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hmass : wholeSpaceL2Mass u S ≤
      (s.card : ℝ≥0∞) * wholeSpaceL2Mass u (T i0) := by
    refine hstep1.trans ?_
    rw [hbi]
    exact hstep2.trans (le_of_eq hstep3 |>.trans hstep4)
  -- convert to real integrals
  have hne : (s.card : ℝ≥0∞) * wholeSpaceL2Mass u (T i0) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (wholeSpaceL2Mass_ne_top hu _)
  have hreal := ENNReal.toReal_mono hne hmass
  rw [integral_sq_eq_toReal_wholeSpaceL2Mass hu S,
    integral_sq_eq_toReal_wholeSpaceL2Mass hu (T i0)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  exact hreal

/-- **The one-step contraction through a neighbour**, exactly the `hstep`
hypothesis of the established decay engine
`H1Function.integral_sq_exterior_le_of_graph_cells`.

If the enlargement `Q̂` of the cell `Q` avoids the source and is covered by the
finite neighbour family `T`, then `∫_Q u² ≤ card * theta * ∫_{T i} u²` for some
neighbour `i`.

Source: `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem exists_neighbour_cell_mass_contraction
    {a : Vec d → ℝ} {t : ℝ} {f : Vec d → ℝ} {lam Lam theta : ℝ} {n : ℤ}
    {z : Vec d} (ht : 0 < t)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) z)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hLam : 0 ≤ Lam) (htheta : 0 ≤ theta)
    (haLe : ∀ x ∈ translatedCube d (n + 1) z, a x ≤ Lam)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) z, f x = 0)
    (hsmall : 4096 * (d : ℝ) * Lam * t * ((3 : ℝ) ^ n)⁻¹ ^ 2 ≤ theta)
    {iota : Type*} (s : Finset iota) (hs : s.Nonempty) (T : iota → Set (Vec d))
    (hcover : translatedCube d (n + 1) z ⊆ ⋃ i ∈ s, T i) :
    ∃ i ∈ s, ∫ x in translatedCube d n z, u.toFun x ^ 2 ∂volume ≤
      (s.card : ℝ) * theta * ∫ x in T i, u.toFun x ^ 2 ∂volume := by
  obtain ⟨i, hi, hcov⟩ :=
    exists_mem_integral_sq_le_card_mul_of_finset_cover u.memL2_toFun s hs T hcover
  refine ⟨i, hi, ?_⟩
  have hcell := wholeSpaceSolution_cell_mass_contraction ht hEll haNonneg hLam
    haLe u hf0 hsmall
  have := mul_le_mul_of_nonneg_left hcov htheta
  calc ∫ x in translatedCube d n z, u.toFun x ^ 2 ∂volume ≤
        theta * ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := hcell
    _ ≤ theta * ((s.card : ℝ) * ∫ x in T i, u.toFun x ^ 2 ∂volume) := this
    _ = (s.card : ℝ) * theta * ∫ x in T i, u.toFun x ^ 2 ∂volume := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
