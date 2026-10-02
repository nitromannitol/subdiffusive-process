import SubdiffusiveProcess.Probability.Diffusion.Packet452Symmetry

/-!
# P-452 seed (i): the iterated semigroup pairing, and its reversal symmetry

The mathematical core of §1.2.  The finite-dimensional laws of the stationary Brownian path measure
are iterated semigroup pairings

```text
Φ(f₁, …, f_m; s₁, …, s_{m−1}) = ∫ f₁ · P_{s₁}(f₂ · P_{s₂}(f₃ ⋯ P_{s_{m−1}} f_m)),
```

and **reversing the list of functions together with the list of gaps leaves `Φ` unchanged**.  That
is J8's reversed-gaps identity, and it follows from semigroup self-adjointness
(`lintegral_semigroup_symm`, already PROVED) **alone** — no transition density ever appears.

The proof is one induction in accumulator form.  Peeling the outermost pairing,

```text
∫ (k·f) · P_s(pairingChain g l) = ∫ (pairingChain g l) · P_s(k·f)
```

by self-adjointness, so the recursion that threads the accumulator is

```text
pairingChainRev k f ((s, g) :: l) = pairingChainRev (P_s (k·f)) g l,   pairingChainRev k f [] = k·f,
```

and `pairingChainRev 1 f₁ [(s₁,f₂), …, (s_{m−1},f_m)]` is exactly the chain read right to left.  Gaps of
length zero (repeated times) are allowed: at `s = 0` the kernel is `Kernel.id` and the symmetry
step degenerates to `mul_comm`, so the caller never has to deduplicate times.

## A note on the names

The natural names here are `chain` and `chainRev`.  They are **not** used: `check_manifest`'s
closure hash resolves unqualified identifiers by unique global suffix, and `chain` already occurs
as a local binder inside `SubdiffusiveProcess/Frozen/Section8/LocalKilledLower.lean`, where the heuristic currently
resolves it to `IsLocalCubeGeometry.chain`.  Adding a second `…chain` would make that suffix
ambiguous, the heuristic would skip it, and the recorded closure hashes of `l.local.killed.lower`
and `l.weighted.good.cube.events` would change -- a spurious tripwire.  Hence `pairingChain`.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter

open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- The semigroup average of a nonnegative measurable function. -/
def semigroupApply (s : ℝ≥0) (h : Vec d → ℝ≥0∞) (z : Vec d) : ℝ≥0∞ :=
  ∫⁻ y, h y ∂(laplacianSemigroup d s z)

instance isMarkovKernel_laplacianSemigroupKernel (s : ℝ≥0) :
    IsMarkovKernel ((laplacianSemigroup d).kernel s) := by
  constructor
  intro x
  show IsProbabilityMeasure (laplacianSemigroup d s x)
  rw [laplacianSemigroup_apply]
  infer_instance

theorem measurable_semigroupApply (s : ℝ≥0) {h : Vec d → ℝ≥0∞} (hh : Measurable h) :
    Measurable (semigroupApply s h) :=
  Measurable.lintegral_kernel_prod_right' (κ := (laplacianSemigroup d).kernel s)
    (hh.comp measurable_snd)

theorem semigroupApply_zero {h : Vec d → ℝ≥0∞} (hh : Measurable h) :
    semigroupApply (0 : ℝ≥0) h = h := by
  funext z
  have hker : (laplacianSemigroup d (0 : ℝ≥0)) z = Measure.dirac z := by
    show ((laplacianSemigroup d).kernel 0) z = Measure.dirac z
    rw [(laplacianSemigroup d).kernel_zero, Kernel.id_apply]
  rw [semigroupApply, hker, lintegral_dirac' _ hh]

/-- **Self-adjointness of the semigroup pairing**, at every nonnegative time including `0`. -/
theorem lintegral_semigroupApply_symm (s : ℝ≥0) {u v : Vec d → ℝ≥0∞}
    (hu : Measurable u) (hv : Measurable v) :
    (∫⁻ z, u z * semigroupApply s v z ∂volume)
      = ∫⁻ z, v z * semigroupApply s u z ∂volume := by
  rcases eq_or_lt_of_le (zero_le s) with h0 | hpos
  · rw [← h0, semigroupApply_zero hu, semigroupApply_zero hv]
    exact lintegral_congr fun z => mul_comm _ _
  · have hr : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hpos
    have h := lintegral_semigroup_symm (d := d) (t := (s : ℝ)) hr hu hv
    rw [Real.toNNReal_coe] at h
    exact h

/-! ## The chain and its reversal -/

/-- The iterated pairing `f · P_{s₁}(g₁ · P_{s₂}(g₂ ⋯))`. -/
def pairingChain (f : Vec d → ℝ≥0∞) : List (ℝ≥0 × (Vec d → ℝ≥0∞)) → (Vec d → ℝ≥0∞)
  | [] => f
  | (s, g) :: l => fun z => f z * semigroupApply s (pairingChain g l) z

@[simp] theorem pairingChain_nil (f : Vec d → ℝ≥0∞) : pairingChain f [] = f := rfl

@[simp] theorem pairingChain_cons (f : Vec d → ℝ≥0∞) (s : ℝ≥0) (g : Vec d → ℝ≥0∞)
    (l : List (ℝ≥0 × (Vec d → ℝ≥0∞))) :
    pairingChain f ((s, g) :: l) = fun z => f z * semigroupApply s (pairingChain g l) z := rfl

theorem measurable_pairingChain : ∀ (l : List (ℝ≥0 × (Vec d → ℝ≥0∞))) (f : Vec d → ℝ≥0∞),
    Measurable f → (∀ p ∈ l, Measurable p.2) → Measurable (pairingChain f l)
  | [], f, hf, _ => hf
  | (s, g) :: l, f, hf, hl => by
    refine hf.mul (measurable_semigroupApply s ?_)
    exact measurable_pairingChain l g (hl (s, g) (List.mem_cons_self ..))
      (fun p hp => hl p (List.mem_cons_of_mem _ hp))

/-- The chain read right to left, in accumulator form. -/
def pairingChainRev (k f : Vec d → ℝ≥0∞) : List (ℝ≥0 × (Vec d → ℝ≥0∞)) → (Vec d → ℝ≥0∞)
  | [] => fun z => k z * f z
  | (s, g) :: l => pairingChainRev (semigroupApply s (fun z => k z * f z)) g l

@[simp] theorem pairingChainRev_nil (k f : Vec d → ℝ≥0∞) :
    pairingChainRev k f [] = fun z => k z * f z := rfl

@[simp] theorem pairingChainRev_cons (k f : Vec d → ℝ≥0∞) (s : ℝ≥0) (g : Vec d → ℝ≥0∞)
    (l : List (ℝ≥0 × (Vec d → ℝ≥0∞))) :
    pairingChainRev k f ((s, g) :: l)
      = pairingChainRev (semigroupApply s (fun z => k z * f z)) g l := rfl

/-- **The reversal identity.**  One induction, self-adjointness at each step. -/
theorem lintegral_pairingChain_rev : ∀ (l : List (ℝ≥0 × (Vec d → ℝ≥0∞))) (k f : Vec d → ℝ≥0∞),
    Measurable k → Measurable f → (∀ p ∈ l, Measurable p.2) →
    (∫⁻ z, k z * pairingChain f l z ∂volume) = ∫⁻ z, pairingChainRev k f l z ∂volume
  | [], k, f, _, _, _ => rfl
  | (s, g) :: l, k, f, hk, hf, hl => by
    have hgm : Measurable g := hl (s, g) (List.mem_cons_self ..)
    have hlm : ∀ p ∈ l, Measurable p.2 := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have hchain : Measurable (pairingChain g l) := measurable_pairingChain l g hgm hlm
    have hstep : (∫⁻ z, k z * pairingChain f ((s, g) :: l) z ∂volume)
        = ∫⁻ z, (fun w => k w * f w) z * semigroupApply s (pairingChain g l) z ∂volume := by
      refine lintegral_congr fun z => ?_
      rw [pairingChain_cons]
      ring
    rw [hstep, lintegral_semigroupApply_symm s (hk.mul hf) hchain, pairingChainRev_cons]
    have hIH := lintegral_pairingChain_rev l (semigroupApply s (fun z => k z * f z)) g
      (measurable_semigroupApply s (hk.mul hf)) hgm hlm
    rw [← hIH]
    exact lintegral_congr fun z => mul_comm _ _

/-! ## Identifying the accumulator form with the reversed chain -/

/-- The head of the reversed chain: the last function of the original. -/
def revHead (f : Vec d → ℝ≥0∞) : List (ℝ≥0 × (Vec d → ℝ≥0∞)) → (Vec d → ℝ≥0∞)
  | [] => f
  | (_, g) :: l => revHead g l

/-- The tail of the reversed chain: the gaps reversed, each carrying the function that preceded
it. -/
def revList (f : Vec d → ℝ≥0∞) : List (ℝ≥0 × (Vec d → ℝ≥0∞)) →
    List (ℝ≥0 × (Vec d → ℝ≥0∞))
  | [] => []
  | (s, g) :: l => revList g l ++ [(s, f)]

/-- Splicing a chain in at the innermost slot is concatenation of the lists. -/
theorem pairingChain_append_cons :
    ∀ (m : List (ℝ≥0 × (Vec d → ℝ≥0∞))) (h : Vec d → ℝ≥0∞) (s : ℝ≥0) (g : Vec d → ℝ≥0∞)
      (L : List (ℝ≥0 × (Vec d → ℝ≥0∞))),
    pairingChain h (m ++ (s, g) :: L) = pairingChain h (m ++ [(s, pairingChain g L)])
  | [], h, s, g, L => by
      simp only [List.nil_append, pairingChain_cons, pairingChain_nil]
  | (s', g') :: m, h, s, g, L => by
      simp only [List.cons_append, pairingChain_cons]
      rw [pairingChain_append_cons m g' s g L]

/-- **The accumulator form is the reversed chain**, on a nonempty gap list. -/
theorem pairingChainRev_cons_eq :
    ∀ (l : List (ℝ≥0 × (Vec d → ℝ≥0∞))) (s : ℝ≥0) (g f k : Vec d → ℝ≥0∞),
    pairingChainRev k f ((s, g) :: l)
      = pairingChain (revHead g l) (revList g l ++ [(s, fun z => k z * f z)])
  | [], s, g, f, k => by
      simp only [pairingChainRev_cons, pairingChainRev_nil, revHead, revList,
        List.nil_append, pairingChain_cons, pairingChain_nil]
      funext z
      exact mul_comm _ _
  | (s', g') :: l, s, g, f, k => by
      rw [pairingChainRev_cons,
        pairingChainRev_cons_eq l s' g' g (semigroupApply s (fun z => k z * f z))]
      show pairingChain (revHead g' l)
          (revList g' l ++ [(s', fun z => semigroupApply s (fun w => k w * f w) z * g z)]) = _
      show _ = pairingChain (revHead g' l)
          (revList g' l ++ [(s', g)] ++ [(s, fun z => k z * f z)])
      rw [List.append_assoc, show ([(s', g)] ++ [(s, fun z => k z * f z)])
          = (s', g) :: [(s, fun z => k z * f z)] from rfl,
        pairingChain_append_cons (revList g' l) (revHead g' l) s' g
          [(s, fun z => k z * f z)]]
      have hentry : (fun z => semigroupApply s (fun w => k w * f w) z * g z)
          = pairingChain g [(s, fun z => k z * f z)] := by
        funext z
        simp only [pairingChain_cons, pairingChain_nil]
        exact mul_comm _ _
      rw [hentry]

theorem pairingChainRev_one (l : List (ℝ≥0 × (Vec d → ℝ≥0∞))) (f : Vec d → ℝ≥0∞) :
    pairingChainRev (fun _ => 1) f l = pairingChain (revHead f l) (revList f l) := by
  cases l with
  | nil =>
      funext z
      simp only [pairingChainRev_nil, revHead, revList, pairingChain_nil, one_mul]
  | cons p l =>
      obtain ⟨s, g⟩ := p
      rw [pairingChainRev_cons_eq l s g f (fun _ => 1)]
      simp only [one_mul, revHead, revList]

/-- **The reversal identity, in chain form.**  Reversing the functions together with the gaps
leaves the integrated pairing unchanged. -/
theorem lintegral_pairingChain_eq_rev (l : List (ℝ≥0 × (Vec d → ℝ≥0∞))) (f : Vec d → ℝ≥0∞)
    (hf : Measurable f) (hl : ∀ p ∈ l, Measurable p.2) :
    (∫⁻ z, pairingChain f l z ∂volume)
      = ∫⁻ z, pairingChain (revHead f l) (revList f l) z ∂volume := by
  have h := lintegral_pairingChain_rev l (fun _ => 1) f measurable_const hf hl
  rw [pairingChainRev_one] at h
  rw [← h]
  exact lintegral_congr fun z => (one_mul _).symm

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
