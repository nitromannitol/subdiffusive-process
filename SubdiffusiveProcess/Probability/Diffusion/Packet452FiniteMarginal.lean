module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452PairingChain
public import SubdiffusiveProcess.Probability.Diffusion.Packet452Stationarity
public import MarkovProcess.Trajectory.Equivariance

@[expose] public section

/-!
# seed (i): the `m`-point Markov formula in `ℝ≥0∞`

Piece 2 of `PathReversalInvariance`.  The joint law of a continuous path at a strictly increasing
finite family of times is `SubMarkovKernelSemigroup.finiteTimeKernel`, whose recursion

```text
finiteTimeKernel P times = (P (times 0) ⊗ₖ prodMkLeft α (finiteTimeKernel P times.relativeTail)).map Fin.cons
```

is exactly the shape of the iterated pairing.  Unfolding it gives

```text
E_x[∏ᵢ fᵢ(ω tᵢ)] = P_{t₀}(f₀ · P_{t₁−t₀}(f₁ · ⋯))(x) = fddChain times f x,
```

and integrating over `x` against Lebesgue measure removes the outer average
(`lintegral_semigroupApply_invariant`), which is why the answer depends only on the **gaps**.

Three details that make this go through with no side conditions:

* `times.relativeTail i = times i.succ − times 0` is the family of times *relative to the first
  one*, so the recursion's own first time is the first **gap**, and the nesting produces the gap
  list without any separate bookkeeping;
* `lintegral_const_mul` needs only measurability -- the outer factor `f 0 z` is constant in the
  inner integration variable, and no finiteness of anything is required, so the `fᵢ` may be
  arbitrary nonnegative measurable functions rather than bounded ones;
* the invariance is extended to `s = 0` (`Kernel.id`), so a degenerate first time costs nothing.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set

open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- Invariance of Lebesgue measure, at every nonnegative time including `0`. -/
theorem lintegral_semigroupApply_invariant (s : ℝ≥0) {G : Vec d → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ x, semigroupApply s G x ∂volume) = ∫⁻ y, G y ∂volume := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | hpos
  · rw [← h0, semigroupApply_zero hG]
  · have hr : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hpos
    have h := lintegral_laplacianSemigroup_invariant (d := d) (t := (s : ℝ)) hr hG
    rw [Real.toNNReal_coe] at h
    exact h

/-- The iterated pairing attached to a strictly increasing family of times. -/
def fddChain : {n : ℕ} → FiniteOrderedTimes n → (Fin n → Vec d → ℝ≥0∞) → (Vec d → ℝ≥0∞)
  | 0, _, _ => fun _ => 1
  | (_ + 1), times, f => semigroupApply (times 0)
      (fun z => f 0 z * fddChain times.relativeTail (fun j => f j.succ) z)

@[simp] theorem fddChain_succ {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (f : Fin (n + 1) → Vec d → ℝ≥0∞) :
    fddChain times f = semigroupApply (times 0)
      (fun z => f 0 z * fddChain times.relativeTail (fun j => f j.succ) z) := rfl

theorem measurable_fddChain : ∀ {n : ℕ} (times : FiniteOrderedTimes n)
    (f : Fin n → Vec d → ℝ≥0∞), (∀ i, Measurable (f i)) → Measurable (fddChain times f)
  | 0, _, _, _ => measurable_const
  | (_ + 1), _times, _f, hf =>
      measurable_semigroupApply _ ((hf 0).mul (measurable_fddChain _ _ fun j => hf j.succ))

instance isMarkovKernel_finiteTimeKernel_laplacian {n : ℕ} (times : FiniteOrderedTimes n) :
    IsMarkovKernel ((laplacianSemigroup d).finiteTimeKernel times) :=
  SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteTimeKernel _
    isConservative_laplacianSemigroup times

/-- **The `m`-point Markov formula.** -/
theorem lintegral_finiteTimeKernel_prod : ∀ {n : ℕ} (times : FiniteOrderedTimes n)
    (f : Fin n → Vec d → ℝ≥0∞), (∀ i, Measurable (f i)) → ∀ x : Vec d,
    (∫⁻ p, ∏ i, f i (p i) ∂((laplacianSemigroup d).finiteTimeKernel times x))
      = fddChain times f x
  | 0, times, f, _, x => by
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_zero, Kernel.const_apply]
      simp [fddChain]
  | (n + 1), times, f, hf, x => by
      have hmeasF : Measurable fun p : Fin (n + 1) → Vec d => ∏ i, f i (p i) :=
        Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
      have hmeasTail : Measurable fun p : Fin n → Vec d => ∏ j, f j.succ (p j) :=
        Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)
      have hmeas2 : Measurable (Function.uncurry
          fun (z : Vec d) (p : Fin n → Vec d) => f 0 z * ∏ j, f j.succ (p j)) :=
        ((hf 0).comp measurable_fst).mul (hmeasTail.comp measurable_snd)
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.map_apply _ measurable_finCons,
        lintegral_map hmeasF measurable_finCons]
      have hrw : (fun q : Vec d × (Fin n → Vec d) =>
            ∏ i, f i (@Fin.cons n (fun _ : Fin (n + 1) => Vec d) q.1 q.2 i))
          = fun q : Vec d × (Fin n → Vec d) => f 0 q.1 * ∏ j, f j.succ (q.2 j) := by
        funext q
        rw [Fin.prod_univ_succ]
        simp
      rw [hrw, Kernel.lintegral_compProd' _ _ x hmeas2]
      rw [fddChain_succ, semigroupApply]
      refine lintegral_congr fun z => ?_
      rw [Kernel.prodMkLeft_apply, lintegral_const_mul _ hmeasTail,
        lintegral_finiteTimeKernel_prod times.relativeTail (fun j => f j.succ)
          (fun j => hf j.succ) z]




/-- The gap list of a strictly increasing family: each successive gap paired with the function at
the later time. -/
def gapList : {n : ℕ} → FiniteOrderedTimes (n + 1) → (Fin (n + 1) → Vec d → ℝ≥0∞) →
    List (ℝ≥0 × (Vec d → ℝ≥0∞))
  | 0, _, _ => []
  | (_ + 1), times, f =>
      (times.relativeTail 0, f 1) :: gapList times.relativeTail (fun j => f j.succ)

theorem measurable_gapList : ∀ {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (f : Fin (n + 1) → Vec d → ℝ≥0∞), (∀ i, Measurable (f i)) →
    ∀ p ∈ gapList times f, Measurable p.2
  | 0, _, _, _, p, hp => by simp [gapList] at hp
  | (n + 1), times, f, hf, p, hp => by
      rw [gapList, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hf 1
      · exact measurable_gapList times.relativeTail (fun j => f j.succ)
          (fun j => hf j.succ) p hp

/-- The finite-dimensional chain is the list chain, after the initial average. -/
theorem fddChain_eq_semigroupApply_pairingChain : ∀ {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) (f : Fin (n + 1) → Vec d → ℝ≥0∞),
    fddChain times f = semigroupApply (times 0) (pairingChain (f 0) (gapList times f))
  | 0, times, f => by
      rw [fddChain_succ, gapList, pairingChain_nil]
      congr 1
      funext z
      simp [fddChain]
  | (n + 1), times, f => by
      rw [fddChain_succ, gapList,
        fddChain_eq_semigroupApply_pairingChain times.relativeTail (fun j => f j.succ)]
      congr 1

/-- **Piece 2, in the form the reversal consumes.** -/
theorem lintegral_fddChain {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (f : Fin (n + 1) → Vec d → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, fddChain times f x ∂volume)
      = ∫⁻ z, pairingChain (f 0) (gapList times f) z ∂volume := by
  rw [fddChain_eq_semigroupApply_pairingChain times f]
  exact lintegral_semigroupApply_invariant (times 0)
    (measurable_pairingChain _ _ (hf 0) (measurable_gapList times f hf))

/-! ## The gap list in closed form, and its reversal -/

theorem gapList_eq_ofFn : ∀ {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (f : Fin (n + 1) → Vec d → ℝ≥0∞),
    gapList times f
      = List.ofFn (fun i : Fin n => (times i.succ - times i.castSucc, f i.succ))
  | 0, times, f => by simp [gapList]
  | (n + 1), times, f => by
      have key : ∀ i : Fin n,
          (times.relativeTail) i.succ - (times.relativeTail) i.castSucc
            = times i.succ.succ - times i.succ.castSucc := by
        intro i
        rw [FiniteOrderedTimes.relativeTail_apply, FiniteOrderedTimes.relativeTail_apply,
          tsub_tsub_tsub_cancel_right (times.monotone (Fin.zero_le _))]
        congr 1
      rw [gapList, gapList_eq_ofFn times.relativeTail (fun j => f j.succ), List.ofFn_succ]
      simp only [key]
      congr 1

theorem revList_ofFn : ∀ {n : ℕ} (Δ : Fin n → ℝ≥0) (f : Fin (n + 1) → Vec d → ℝ≥0∞),
    revList (f 0) (List.ofFn (fun i : Fin n => (Δ i, f i.succ)))
      = List.ofFn (fun i : Fin n => (Δ i.rev, f (i.rev).castSucc))
  | 0, _, _ => by simp [revList]
  | (n + 1), Δ, f => by
      rw [List.ofFn_succ, revList,
        revList_ofFn (fun i : Fin n => Δ i.succ) (fun i : Fin (n + 1) => f i.succ)]
      rw [List.ofFn_succ' (f := fun i : Fin (n + 1) => (Δ i.rev, f (i.rev).castSucc)),
        List.concat_eq_append]
      congr 1
      · congr 1
        funext i
        simp only [Fin.rev_castSucc, Fin.succ_castSucc]
      · simp

theorem revHead_ofFn : ∀ {n : ℕ} (Δ : Fin n → ℝ≥0) (f : Fin (n + 1) → Vec d → ℝ≥0∞),
    revHead (f 0) (List.ofFn (fun i : Fin n => (Δ i, f i.succ))) = f (Fin.last n)
  | 0, _, f => by simp [revHead]
  | (n + 1), Δ, f => by
      rw [List.ofFn_succ, revHead,
        revHead_ofFn (fun i : Fin n => Δ i.succ) (fun i : Fin (n + 1) => f i.succ)]
      simp

/-! ## The reversal at the level of a time family -/

theorem nnreal_sub_sub_sub {T a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) :
    (T - a) - (T - b) = b - a := by
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_sub (tsub_le_tsub_left hab T), NNReal.coe_sub (hab.trans hbT),
    NNReal.coe_sub hbT, NNReal.coe_sub hab]
  have ha : (a : ℝ) ≤ b := hab
  have hb : (b : ℝ) ≤ T := hbT
  linarith

/-- **The finite-dimensional reversal.**  Reversing a time family inside `[0, T]` reverses its gap
list, and the integrated pairing is unchanged. -/
theorem lintegral_pairingChain_gapList_rev {n : ℕ} {T : ℝ≥0}
    (times times' : FiniteOrderedTimes (n + 1))
    (htimes : ∀ i : Fin (n + 1), times i ≤ T)
    (hrev : ∀ i : Fin (n + 1), times' i = T - times i.rev)
    (f : Fin (n + 1) → Vec d → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ z, pairingChain (f 0) (gapList times f) z ∂volume)
      = ∫⁻ z, pairingChain ((fun i : Fin (n + 1) => f i.rev) 0)
          (gapList times' (fun i : Fin (n + 1) => f i.rev)) z ∂volume := by
  have hgap : ∀ i : Fin n, times' i.succ - times' i.castSucc
      = times (i.rev).succ - times (i.rev).castSucc := by
    intro i
    rw [hrev i.succ, hrev i.castSucc, Fin.rev_succ, Fin.rev_castSucc]
    exact nnreal_sub_sub_sub (times.monotone (le_of_lt Fin.castSucc_lt_succ))
      (htimes ((i.rev).succ))
  have hhead : f (Fin.last n) = f ((0 : Fin (n + 1)).rev) := by rw [Fin.rev_zero]
  have hlist : (List.ofFn (fun i : Fin n =>
        (times (i.rev).succ - times (i.rev).castSucc, f ((i.rev).castSucc))))
      = List.ofFn (fun i : Fin n =>
        (times' i.succ - times' i.castSucc, f ((i.succ).rev))) := by
    refine congrArg List.ofFn (funext fun i => ?_)
    rw [hgap i, Fin.rev_succ]
  rw [lintegral_pairingChain_eq_rev _ _ (hf 0) (measurable_gapList times f hf),
    gapList_eq_ofFn times f, revHead_ofFn, revList_ofFn,
    gapList_eq_ofFn times' (fun i : Fin (n + 1) => f i.rev), hhead, hlist]

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
