module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.SummableErrors

@[expose] public section

/-!
# The locally uniform limit of a path sequence with summable sup-increments

  §2.3, Steps 2–3,
**pathwise half**.  This file is measure-free: it is the deterministic statement that a sequence of
continuous paths whose successive sup-increments over each `[0, N]` are summable converges in
`C(ℝ≥0, ℝ)`, i.e. uniformly on compacts.

One might ask for a diagonal extraction over the horizons `T = 1, 2, 3, …`.  **That is
avoidable.**  The maximal estimate's right-hand side is `32(‖φ‖₂² + T · E(φ))`, so a subsequence
chosen once with a geometric rate in the `H¹` norm alone controls *every* horizon simultaneously,
with the horizon appearing only in the constant.  Accordingly the hypothesis here is a single
family of summability statements, one per integer horizon, and the conclusion is convergence in
`C(ℝ≥0, ℝ)` together with uniform convergence on every `Icc 0 T` — the latter being the exact shape
`zero_at_exit_of_tendstoUniformlyOn` (`SobolevPathLift/ScopeChecks.lean`) consumes in Step 7.

No completeness or metrizability instance for `C(ℝ≥0, ℝ)` is invoked: the limit is written down
explicitly as `F 0 + ∑ₖ (F (k+1) − F k)` and the Weierstrass M-test (`tendstoUniformlyOn_tsum_nat`)
does the work.
-/

set_option autoImplicit false

open Filter MeasureTheory Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

/-! ## The sup-increment functional -/

/-- `supIncr F T k = sup_{t ≤ T} |F (k+1) t − F k t|`, in `ℝ≥0∞` so that no finiteness has to be
carried around. -/
def supIncr (F : ℕ → ℝ≥0 → ℝ) (T : ℝ≥0) (k : ℕ) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal |F (k + 1) t - F k t|

theorem ofReal_abs_le_supIncr (F : ℕ → ℝ≥0 → ℝ) {T t : ℝ≥0} (ht : t ≤ T) (k : ℕ) :
    ENNReal.ofReal |F (k + 1) t - F k t| ≤ supIncr F T k :=
  le_iSup₂ (f := fun t (_ : t ≤ T) => ENNReal.ofReal |F (k + 1) t - F k t|) t ht

/-- The square of the sup-increment is the sup of the squared increments -- the shape in which the
maximal estimate delivers its bound. -/
theorem supIncr_sq (F : ℕ → ℝ≥0 → ℝ) (T : ℝ≥0) (k : ℕ) :
    supIncr F T k ^ 2
      = ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ((F (k + 1) t - F k t) ^ 2) := by
  rw [supIncr, ENNReal.iSup₂_pow_of_ne_zero _ (two_ne_zero)]
  refine iSup_congr fun t => iSup_congr fun _ => ?_
  rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem supIncr_mono (F : ℕ → ℝ≥0 → ℝ) {T T' : ℝ≥0} (hT : T ≤ T') (k : ℕ) :
    supIncr F T k ≤ supIncr F T' k :=
  iSup₂_le fun _t ht => ofReal_abs_le_supIncr F (ht.trans hT) k

theorem abs_le_toReal_supIncr (F : ℕ → ℝ≥0 → ℝ) {T t : ℝ≥0} (ht : t ≤ T) (k : ℕ)
    (hfin : supIncr F T k ≠ ⊤) :
    |F (k + 1) t - F k t| ≤ (supIncr F T k).toReal := by
  have h := ENNReal.toReal_mono hfin (ofReal_abs_le_supIncr F ht k)
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h

/-! ## The limit -/

/-- `Icc 0 T = Iic T` on `ℝ≥0`. -/
theorem icc_zero_eq_iic (T : ℝ≥0) : Icc (0 : ℝ≥0) T = Iic T := by
  ext s; simp

/-- **Steps 2–3, pathwise half.**  A sequence of continuous paths whose sup-increments over every
integer horizon are summable converges in `C(ℝ≥0, ℝ)`, uniformly on every `Icc 0 T`. -/
theorem exists_tendsto_of_summable_supIncr (F : ℕ → C(ℝ≥0, ℝ))
    (hsum : ∀ N : ℕ, (∑' k : ℕ, supIncr (fun k => ⇑(F k)) (N : ℝ≥0) k) ≠ ⊤) :
    ∃ g : C(ℝ≥0, ℝ), Tendsto F atTop (𝓝 g) ∧
      ∀ T : ℝ≥0, TendstoUniformlyOn (fun k => ⇑(F k)) ⇑g atTop (Icc 0 T) := by
  set f : ℕ → ℝ≥0 → ℝ := fun k => ⇑(F k) with hf
  set g : ℝ≥0 → ℝ := fun t => f 0 t + ∑' k : ℕ, (f (k + 1) t - f k t) with hg
  -- uniform convergence on each integer horizon
  have key : ∀ N : ℕ, TendstoUniformlyOn f g atTop (Icc (0 : ℝ≥0) (N : ℝ≥0)) := by
    intro N
    have hfin : ∀ k : ℕ, supIncr f (N : ℝ≥0) k ≠ ⊤ := fun k =>
      ne_top_of_le_ne_top (hsum N) (ENNReal.le_tsum k)
    have hu : Summable fun k : ℕ => (supIncr f (N : ℝ≥0) k).toReal :=
      ENNReal.summable_toReal (hsum N)
    have hfu : ∀ (k : ℕ) (t : ℝ≥0), t ∈ Icc (0 : ℝ≥0) (N : ℝ≥0) →
        ‖f (k + 1) t - f k t‖ ≤ (supIncr f (N : ℝ≥0) k).toReal := by
      intro k t ht
      exact abs_le_toReal_supIncr f ht.2 k (hfin k)
    have H := tendstoUniformlyOn_tsum_nat (f := fun k t => f (k + 1) t - f k t) hu hfu
    rw [Metric.tendstoUniformlyOn_iff] at H ⊢
    intro ε hε
    filter_upwards [H ε hε] with M hM t ht
    have h1 := hM t ht
    have h2 : ∑ k ∈ Finset.range M, (f (k + 1) t - f k t) = f M t - f 0 t :=
      Finset.sum_range_sub (fun k => f k t) M
    rw [h2, Real.dist_eq] at h1
    rw [Real.dist_eq, hg]
    have h3 : f 0 t + (∑' k : ℕ, (f (k + 1) t - f k t)) - f M t
        = (∑' k : ℕ, (f (k + 1) t - f k t)) - (f M t - f 0 t) := by ring
    rw [h3]
    exact h1
  -- uniform convergence on an arbitrary horizon
  have keyT : ∀ T : ℝ≥0, TendstoUniformlyOn f g atTop (Icc (0 : ℝ≥0) T) := by
    intro T
    refine (key ⌈(T : ℝ)⌉₊).mono (Icc_subset_Icc le_rfl ?_)
    have h : (T : ℝ) ≤ (⌈(T : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast h
  -- continuity of the limit
  have hcont : Continuous g := by
    have hcontOn : ∀ N : ℕ, ContinuousOn g (Icc (0 : ℝ≥0) (N : ℝ≥0)) := fun N =>
      (key N).continuousOn (.of_forall fun k => (F k).continuous.continuousOn)
    refine continuous_iff_continuousAt.mpr fun t => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt t
    refine (hcontOn N).continuousAt ?_
    rw [icc_zero_eq_iic]
    exact Iic_mem_nhds hN
  refine ⟨⟨g, hcont⟩, ?_, keyT⟩
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  obtain ⟨T, hT⟩ := hK.bddAbove
  exact (keyT T).mono fun t htK => ⟨bot_le, hT htK⟩

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
