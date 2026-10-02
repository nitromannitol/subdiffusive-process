import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDistance
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationConnectivity




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The concatenation calculus -/

/-- A single good site is a good path of one vertex from itself to itself. -/
theorem isShortGoodPath_self {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω}
    {bound : ℝ} {v : Lattice d} (hb : (1 : ℝ) ≤ bound)
    (hv : IsPercolationGoodSite E Cbox ω v) :
    IsShortGoodPath E Cbox ω bound v v := by
  refine ⟨[v], rfl, rfl, by simpa using hb, ?_, ?_⟩
  · intro k hk
    simp at hk
  · intro u hu
    rw [List.mem_singleton] at hu
    exact hu ▸ hv

/-- **Concatenation.**  Good paths compose, and the length budgets add.

The junction vertex is repeated in the concatenated list; that is legal because
`latticeDist v v = 0 ≤ 1`, and it is what makes the bookkeeping additive rather
than off-by-one. -/
theorem IsShortGoodPath.trans {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω}
    {b1 b2 : ℝ} {u v w : Lattice d}
    (h1 : IsShortGoodPath E Cbox ω b1 u v) (h2 : IsShortGoodPath E Cbox ω b2 v w) :
    IsShortGoodPath E Cbox ω (b1 + b2) u w := by
  obtain ⟨p1, hh1, hl1, hlen1, hs1, hg1⟩ := h1
  obtain ⟨p2, hh2, hl2, hlen2, hs2, hg2⟩ := h2
  have hne1 : p1 ≠ [] := by
    intro hempty
    rw [hempty] at hh1
    exact Option.noConfusion hh1
  have hne2 : p2 ≠ [] := by
    intro hempty
    rw [hempty] at hh2
    exact Option.noConfusion hh2
  refine ⟨p1 ++ p2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_append_of_ne_nil p1 hne1, hh1]
  · rw [List.getLast?_append_of_ne_nil p1 hne2, hl2]
  · rw [List.length_append]
    push_cast
    linarith
  · rw [isJStepListPath_iff_isChain]
    refine ((isJStepListPath_iff_isChain _).mp hs1).append
      ((isJStepListPath_iff_isChain _).mp hs2) (fun x hx y hy => ?_)
    rw [hl1] at hx
    rw [hh2] at hy
    have hxv : x = v := (Option.mem_some_iff.mp hx).symm
    have hyv : y = v := (Option.mem_some_iff.mp hy).symm
    rw [hxv, hyv, latticeDist_self]
    exact Nat.zero_le 1
  · intro x hx
    rw [List.mem_append] at hx
    exact hx.elim (hg1 x) (hg2 x)

/-- **The waypoint chain.**  `n` consecutive links of budget `b` compose into one
good path of budget `n * b`. -/
theorem isShortGoodPath_of_waypoints {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω}
    {b : ℝ} (x : ℕ → Lattice d) :
    ∀ n : ℕ, 0 < n → (∀ i, i < n → IsShortGoodPath E Cbox ω b (x i) (x (i + 1))) →
      IsShortGoodPath E Cbox ω (n * b) (x 0) (x n) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ n ih =>
    intro _ hlink
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact (hlink 0 (by omega)).mono (by push_cast; linarith)
    · have hpath := ih hn (fun i hi => hlink i (by omega))
      have hlast := hlink n (by omega)
      exact (hpath.trans hlast).mono (by push_cast; linarith)

/-! ## The DRS datum, and the reduction of `D_L(z)` to it -/



def GoodWaypointChain (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (steps : ℕ) (link : ℝ) (z : Lattice d) (L : ℕ) : Prop :=
  ∀ v w : Lattice d,
    InLatticeBallReal z v L → InLatticeBallReal z w L →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) v →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) w →
    ∃ x : ℕ → Lattice d, ∃ n : ℕ, 0 < n ∧ n ≤ steps ∧ x 0 = v ∧ x n = w ∧
      ∀ i, i < n → IsShortGoodPath E Cbox ω link (x i) (x (i + 1))

/-- **The chemical-length budget.**  A waypoint chain with
`steps * link ≤ Clen * L` rules out the chemical-distance failure event at
radius `L`. -/
theorem not_mem_chemicalDistanceFailureEvent_of_goodWaypointChain
    {E : ℕ → Lattice d → Set Ω} {Cbox steps : ℕ} {ω : Ω} {link Clen : ℝ}
    {z : Lattice d} {L : ℕ} (hlink : 0 ≤ link)
    (hbound : (steps : ℝ) * link ≤ Clen * L)
    (hchain : GoodWaypointChain E Cbox ω steps link z L) :
    ω ∉ chemicalDistanceFailureEvent E Cbox Clen z L := by
  rintro ⟨v, w, hv, hw, hvc, hwc, hno⟩
  obtain ⟨x, n, hn, hns, hx0, hxn, hlinks⟩ := hchain v w hv hw hvc hwc
  have hpath := isShortGoodPath_of_waypoints x n hn hlinks
  rw [hx0, hxn] at hpath
  refine hno (hpath.mono ?_)
  have hcast : (n : ℝ) ≤ (steps : ℝ) := by exact_mod_cast hns
  nlinarith

/-- **Clause (iii) from the DRS datum.**  If the waypoint chain is available at
every dyadic radius above the height `component`, with a budget linear in the
radius, then the third clause of `FiniteRangePercolationGeometry` holds verbatim.

This is the exact reduction of the manuscript's gap (α): what is missing is
`GoodWaypointChain`, nothing else. -/
theorem goodPathClause_of_goodWaypointChain
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω} {Clen C link : ℝ}
    {steps : ℕ → ℕ} {z : Lattice d} {component : ℕ}
    (hClen : 0 ≤ Clen) (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C) (hlink : 0 ≤ link)
    (hbound : ∀ n : ℕ, component ≤ n →
      (steps n : ℝ) * link ≤ Clen * ((2 ^ n : ℕ) : ℝ))
    (hchain : ∀ n : ℕ, component ≤ n →
      GoodWaypointChain E Cbox ω (steps n) link z (2 ^ n)) :
    ∀ l : ℕ, Real.exp (C * component) ≤ l →
      ∀ v w : Lattice d,
      InLatticeBallReal z v l → InLatticeBallReal z w l →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) v →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) w →
      ∃ path : List (Lattice d),
        path.head? = some v ∧ path.getLast? = some w ∧
          (path.length : ℝ) ≤ C * l ∧ IsJStepListPath 1 path ∧
            ∀ u ∈ path, IsPercolationGoodSite E Cbox ω u :=
  goodPathClause_of_dyadic_threshold hClen hC1 hC2 fun n hn =>
    not_mem_chemicalDistanceFailureEvent_of_goodWaypointChain hlink
      (hbound n hn) (hchain n hn)

/-! ## The hierarchy constant -/

/-- **The chemical-length recursion, honest form.**  If the level-`(k+1)` chemical
length costs `M k` level-`k` lengths while the scale grows by `rho k`, the linear
constant picks up the product `∏ M i / rho i`. -/
theorem le_prod_mul_of_scale_recursion {Len L M rho : ℕ → ℝ} {C : ℝ}
    (hMnn : ∀ k, 0 ≤ M k) (hrho : ∀ k, 0 < rho k)
    (hL : ∀ k, L (k + 1) = rho k * L k)
    (hstep : ∀ k, Len (k + 1) ≤ M k * Len k)
    (h0 : Len 0 ≤ C * L 0) :
    ∀ k, Len k ≤ (C * ∏ i ∈ Finset.range k, M i / rho i) * L k := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hprodrw : (C * ∏ i ∈ Finset.range (k + 1), M i / rho i) * L (k + 1) =
        M k * ((C * ∏ i ∈ Finset.range k, M i / rho i) * L k) := by
      have hne : rho k ≠ 0 := (hrho k).ne'
      rw [Finset.prod_range_succ, hL k]
      field_simp
    rw [hprodrw]
    exact (hstep k).trans (mul_le_mul_of_nonneg_left ih (hMnn k))

/-- **The nondegenerate case.**  If the multiplicity never outgrows the scale
ratio, the chemical length stays linear in the scale with the *initial*
constant: `Len k ≤ C L k` for every `k`. -/
theorem le_mul_of_scale_recursion {Len L M rho : ℕ → ℝ} {C : ℝ}
    (hMnn : ∀ k, 0 ≤ M k) (hLnn : ∀ k, 0 ≤ L k) (hrho : ∀ k, 0 < rho k)
    (hMrho : ∀ k, M k ≤ rho k)
    (hL : ∀ k, L (k + 1) = rho k * L k)
    (hstep : ∀ k, Len (k + 1) ≤ M k * Len k)
    (hC : 0 ≤ C) (h0 : Len 0 ≤ C * L 0) :
    ∀ k, Len k ≤ C * L k := by
  intro k
  refine (le_prod_mul_of_scale_recursion hMnn hrho hL hstep h0 k).trans ?_
  have hprod : (∏ i ∈ Finset.range k, M i / rho i) ≤ 1 := by
    refine Finset.prod_le_one (fun i _ => div_nonneg (hMnn i) (hrho i).le) (fun i _ => ?_)
    rw [div_le_one (hrho i)]
    exact hMrho i
  have hCprod : C * ∏ i ∈ Finset.range k, M i / rho i ≤ C :=
    (mul_le_mul_of_nonneg_left hprod hC).trans (le_of_eq (mul_one C))
  exact mul_le_mul_of_nonneg_right hCprod (hLnn k)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
