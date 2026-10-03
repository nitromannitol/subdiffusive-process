module

public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Topology.EMetricSpace.Pi

@[expose] public section




open Homogenization.Book.Ch02
open scoped Matrix.Norms.Elementwise
open WithLp
open scoped Matrix

/-- The Euclidean operator norm `matrixNorm A = ‖toEuclideanCLM A‖` is bounded by `d` times the
entrywise sup norm `‖A‖` (Cauchy–Schwarz on each row, then Cauchy–Schwarz over the `d` rows). -/
theorem matrixNorm_le_card_mul_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    matrixNorm A ≤ (Fintype.card (Fin d) : ℝ) * ‖A‖ := by
  unfold matrixNorm
  rw [ContinuousLinearMap.opNorm_le_iff (by positivity)]
  intro x
  set y : Fin d → ℝ := ofLp x with hydef
  have hentry : ∀ i, (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x) i = (A *ᵥ y) i :=
    fun i => congrFun (Matrix.ofLp_toEuclideanCLM A x) i
  have hynorm : ‖x‖ = Real.sqrt (∑ j, |y j| ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [← hydef, Real.norm_eq_abs]
  have hcs : ∑ j, |y j| ≤ Real.sqrt (Fintype.card (Fin d)) * Real.sqrt (∑ j, |y j| ^ 2) := by
    have hsq := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun j => |y j|)
    have hnn : 0 ≤ ∑ j, |y j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have h2 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hnn] at h2
    rwa [Real.sqrt_mul (by positivity), Finset.card_univ] at h2
  have hbound : ∀ i, |(A *ᵥ y) i| ≤ ‖A‖ * ∑ j, |y j| := by
    intro i
    have h1 : (A *ᵥ y) i = ∑ j, A i j * y j := rfl
    calc |(A *ᵥ y) i| = |∑ j, A i j * y j| := by rw [h1]
      _ ≤ ∑ j, |A i j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j| * |y j| := by
          apply Finset.sum_congr rfl; intro j _; rw [abs_mul]
      _ ≤ ∑ j, ‖A‖ * |y j| := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_right (Matrix.norm_entry_le_entrywise_sup_norm A) (abs_nonneg _)
      _ = ‖A‖ * ∑ j, |y j| := by rw [Finset.mul_sum]
  have hc0 : (0:ℝ) ≤ ‖A‖ * ∑ j, |y j| := by positivity
  have hstep1 : ∑ i, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x) i‖ ^ 2 ≤
      (Fintype.card (Fin d) : ℝ) * (‖A‖ * ∑ j, |y j|) ^ 2 := by
    calc ∑ i, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x) i‖ ^ 2
        = ∑ i, |(A *ᵥ y) i| ^ 2 := by
          apply Finset.sum_congr rfl; intro i _; rw [hentry i, Real.norm_eq_abs]
      _ ≤ ∑ _i : Fin d, (‖A‖ * ∑ j, |y j|) ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          exact pow_le_pow_left₀ (abs_nonneg _) (hbound i) 2
      _ = (Fintype.card (Fin d) : ℝ) * (‖A‖ * ∑ j, |y j|) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ]; ring
  calc ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x‖
      = Real.sqrt (∑ i, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x) i‖ ^ 2) :=
        EuclideanSpace.norm_eq _
    _ ≤ Real.sqrt ((Fintype.card (Fin d) : ℝ) * (‖A‖ * ∑ j, |y j|) ^ 2) := Real.sqrt_le_sqrt hstep1
    _ = Real.sqrt (Fintype.card (Fin d)) * (‖A‖ * ∑ j, |y j|) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc0]
    _ ≤ Real.sqrt (Fintype.card (Fin d)) * (‖A‖ * (Real.sqrt (Fintype.card (Fin d)) *
          Real.sqrt (∑ j, |y j| ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hcs (norm_nonneg A)
    _ = (Fintype.card (Fin d) : ℝ) * ‖A‖ * ‖x‖ := by
        rw [hynorm]
        have hsqrtsq : Real.sqrt (Fintype.card (Fin d)) * Real.sqrt (Fintype.card (Fin d)) =
            (Fintype.card (Fin d) : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        rw [show Real.sqrt (Fintype.card (Fin d)) * (‖A‖ * (Real.sqrt (Fintype.card (Fin d)) *
              Real.sqrt (∑ j, |y j| ^ 2))) =
            (Real.sqrt (Fintype.card (Fin d)) * Real.sqrt (Fintype.card (Fin d))) *
              (‖A‖ * Real.sqrt (∑ j, |y j| ^ 2)) by ring, hsqrtsq]
        ring

/-- `matrixNorm` obeys the reverse triangle inequality, since it is `‖toEuclideanCLM ·‖` for the
linear (hence additive) map `toEuclideanCLM`. -/
theorem matrixNorm_sub_le {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    |matrixNorm A - matrixNorm B| ≤ matrixNorm (A - B) := by
  unfold matrixNorm
  have hlin : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A -
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B =
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (A - B) := by
    rw [← map_sub]
  calc |‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖ -
        ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B‖| ≤
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A -
        Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B‖ := abs_norm_sub_norm_le _ _
    _ = ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (A - B)‖ := by rw [hlin]

/-- The entrywise sup norm is dominated by the entrywise `ℓ¹` sum. -/
theorem matrixNorm_entrywise_sup_le_sum {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    ‖M‖ ≤ ∑ i, ∑ j, |M i j| := by
  apply (Matrix.norm_le_iff (A := M)
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)))).2
  intro i j
  rw [Real.norm_eq_abs]
  calc |M i j| ≤ ∑ j', |M i j'| := Finset.single_le_sum (fun j' _ => abs_nonneg (M i j')) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |M i' j'| := Finset.single_le_sum
        (fun i' _ => Finset.sum_nonneg (fun j' _ => abs_nonneg (M i' j'))) (Finset.mem_univ i)

/-- `matrixNorm` is Lipschitz with constant `d` with respect to the entrywise `ℓ¹` metric on
`d × d` real matrices. -/
theorem matrixNorm_lipschitz {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    |matrixNorm A - matrixNorm B| ≤ (Fintype.card (Fin d) : ℝ) * ∑ i, ∑ j, |A i j - B i j| := by
  refine (matrixNorm_sub_le A B).trans ?_
  refine (matrixNorm_le_card_mul_norm (A - B)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (matrixNorm_entrywise_sup_le_sum (A - B)).trans ?_
  apply le_of_eq
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  rfl

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]

/-- Any `g : (ι → ℝ) → ℝ` obeying an `ℓ¹`-Lipschitz bound is continuous. -/
theorem lipCombo_continuous (g : (ι → ℝ) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hglip : ∀ u v : ι → ℝ, |g u - g v| ≤ c * ∑ i, |u i - v i|) : Continuous g := by
  have hLip : LipschitzWith (c * Fintype.card ι).toNNReal g := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs,
      Real.coe_toNNReal (c * Fintype.card ι) (by positivity)]
    refine (hglip u v).trans ?_
    have hcard : ∑ i, |u i - v i| ≤ ∑ _i : ι, ‖u - v‖ :=
      Finset.sum_le_sum (fun i _ => norm_le_pi_norm (u - v) i)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcard
    calc c * ∑ i, |u i - v i| ≤ c * ((Fintype.card ι : ℝ) * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left hcard hc
      _ = c * Fintype.card ι * ‖u - v‖ := by ring
  exact hLip.continuous

/-- The composition of an `ℓ¹`-Lipschitz `g` with `g 0 = 0` and a finite tuple of `MemLp 1`
functions is again `MemLp 1`; isolated as a `have`-chain (not one `calc`) to keep each
higher-order `Finset.sum`/`eLpNorm` unification small enough for the default heartbeat budget
(a "sum of functions" vs "function of a sum" defeq mismatch is `whnf`-expensive otherwise). -/
theorem lipCombo_memLp (g : (ι → ℝ) → ℝ) (c : ℝ) (hc : 0 ≤ c) (hg0 : g 0 = 0)
    (hgcont : Continuous g)
    (hglip : ∀ u v : ι → ℝ, |g u - g v| ≤ c * ∑ i, |u i - v i|)
    (v : ι → α → ℝ) (hvmeas : ∀ i, AEStronglyMeasurable (v i) μ)
    (hvmem : ∀ i, MemLp (v i) 1 μ) :
    MemLp (fun ω => g (fun i => v i ω)) 1 μ := by
  have hae : AEStronglyMeasurable (fun ω => g (fun i => v i ω)) μ := by
    have hpi : AEMeasurable (fun ω i => v i ω) μ :=
      AEMeasurable.of_eval (fun i => (hvmeas i).aemeasurable)
    exact (hgcont.measurable.comp_aemeasurable hpi).aestronglyMeasurable
  change eLpNorm (fun ω => g (fun i => v i ω)) 1 μ < ⊤
  have hbound : ∀ ω, |g (fun i => v i ω)| ≤ c * ∑ i, |v i ω| := by
    intro ω
    have h1 := hglip (fun i => v i ω) 0
    simpa [hg0] using h1
  have hnn : ∀ ω, (0:ℝ) ≤ c * ∑ i, |v i ω| := fun ω =>
    mul_nonneg hc (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hs1 : eLpNorm (fun ω => g (fun i => v i ω)) 1 μ ≤ eLpNorm (fun ω => c * ∑ i, |v i ω|) 1 μ := by
    apply eLpNorm_mono hae
    intro ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn ω)]
    exact hbound ω
  have hs2 : eLpNorm (fun ω => c * ∑ i, |v i ω|) 1 μ =
      ENNReal.ofReal c * eLpNorm (fun ω => ∑ i, |v i ω|) 1 μ := by
    rw [show (fun ω => c * ∑ i, |v i ω|) = c • (fun ω => ∑ i, |v i ω|) from rfl,
      eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  have heq : (fun ω => ∑ i, |v i ω|) = ∑ i, (fun i ω => |v i ω|) i := by
    funext ω; rw [Finset.sum_apply]
  have hs3 : eLpNorm (fun ω => ∑ i, |v i ω|) 1 μ ≤ ∑ i, eLpNorm (fun ω => |v i ω|) 1 μ := by
    rw [heq]
    exact eLpNorm_sum_le le_rfl
  have hs4 : ∑ i, eLpNorm (fun ω => |v i ω|) 1 μ = ∑ i, eLpNorm (v i) 1 μ := by
    apply Finset.sum_congr rfl
    intro i _
    have habs : (fun ω => |v i ω|) = (fun ω => ‖v i ω‖) := by
      funext ω; rw [Real.norm_eq_abs]
    rw [habs, eLpNorm_norm _ (hvmeas i)]
  have hs5 : ∑ i, eLpNorm (v i) 1 μ < ⊤ := ENNReal.sum_lt_top.mpr (fun i _ => (hvmem i).eLpNorm_lt_top)
  calc eLpNorm (fun ω => g (fun i => v i ω)) 1 μ
      ≤ eLpNorm (fun ω => c * ∑ i, |v i ω|) 1 μ := hs1
    _ = ENNReal.ofReal c * eLpNorm (fun ω => ∑ i, |v i ω|) 1 μ := hs2
    _ ≤ ENNReal.ofReal c * ∑ i, eLpNorm (fun ω => |v i ω|) 1 μ := mul_le_mul_right hs3 _
    _ = ENNReal.ofReal c * ∑ i, eLpNorm (v i) 1 μ := by rw [hs4]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs5

/-- The `edist` bound underlying Lipschitz continuity, in `Lp`, of the tuple-composition map. -/
theorem lipCombo_flipBound (g : (ι → ℝ) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hglip : ∀ u v : ι → ℝ, |g u - g v| ≤ c * ∑ i, |u i - v i|)
    (v w : ι → Lp ℝ 1 μ) :
    eLpNorm (fun ω => g (fun i => (v i : α → ℝ) ω) - g (fun i => (w i : α → ℝ) ω)) 1 μ ≤
      ENNReal.ofReal c * ∑ i, edist (v i) (w i) := by
  have hgcont : Continuous g := lipCombo_continuous g c hc hglip
  have hmeas (z : ι → Lp ℝ 1 μ) :
      AEStronglyMeasurable (fun ω => g (fun i => (z i : α → ℝ) ω)) μ := by
    have hpi : AEMeasurable (fun ω i => (z i : α → ℝ) ω) μ :=
      AEMeasurable.of_eval (fun i => (Lp.aestronglyMeasurable (z i)).aemeasurable)
    exact (hgcont.measurable.comp_aemeasurable hpi).aestronglyMeasurable
  have hae := (hmeas v).sub (hmeas w)
  have hnn : ∀ ω, (0:ℝ) ≤ c * ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω| := fun ω =>
    mul_nonneg hc (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hs1 : eLpNorm (fun ω => g (fun i => (v i : α → ℝ) ω) - g (fun i => (w i : α → ℝ) ω)) 1 μ ≤
      eLpNorm (fun ω => c * ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) 1 μ := by
    apply eLpNorm_mono hae
    intro ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn ω)]
    exact hglip (fun i => (v i : α → ℝ) ω) (fun i => (w i : α → ℝ) ω)
  have hs2 : eLpNorm (fun ω => c * ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) 1 μ =
      ENNReal.ofReal c * eLpNorm (fun ω => ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) 1 μ := by
    rw [show (fun ω => c * ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) =
      c • (fun ω => ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) from rfl,
      eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  have heq : (fun ω => ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) =
      ∑ i, (fun i (ω : α) => |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) i := by
    funext ω; rw [Finset.sum_apply]
  have hs3 : eLpNorm (fun ω => ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) 1 μ ≤
      ∑ i, eLpNorm (fun ω => |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) 1 μ := by
    rw [heq]
    exact eLpNorm_sum_le le_rfl
  have hs4 : ∑ i, eLpNorm (fun ω => |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) 1 μ =
      ∑ i, edist (v i) (w i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (eLpNorm_norm ((v i : α → ℝ) - (w i : α → ℝ))
      ((Lp.aestronglyMeasurable (v i)).sub (Lp.aestronglyMeasurable (w i)))).trans (Lp.edist_def (v i) (w i)).symm
  calc eLpNorm (fun ω => g (fun i => (v i : α → ℝ) ω) - g (fun i => (w i : α → ℝ) ω)) 1 μ
      ≤ eLpNorm (fun ω => c * ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) 1 μ := hs1
    _ = ENNReal.ofReal c * eLpNorm (fun ω => ∑ i, |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) 1 μ := hs2
    _ ≤ ENNReal.ofReal c * ∑ i, eLpNorm (fun ω => |(v i : α → ℝ) ω - (w i : α → ℝ) ω|) 1 μ :=
        mul_le_mul_right hs3 _
    _ = ENNReal.ofReal c * ∑ i, edist (v i) (w i) := by rw [hs4]

/-- A finite `edist` sum on a `Fintype` index is bounded by `card` times the Pi `edist`. -/
theorem lipCombo_cardBound (c : ℝ) (hc : 0 ≤ c) (v w : ι → Lp ℝ 1 μ) :
    ENNReal.ofReal c * ∑ i, edist (v i) (w i) ≤
      ENNReal.ofReal c * (Fintype.card ι : ℝ≥0∞) * edist v w := by
  have hstep : ∑ i, edist (v i) (w i) ≤ ∑ _i : ι, edist v w := by
    apply Finset.sum_le_sum
    intro i _
    exact edist_pi_le_iff.mp le_rfl i
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstep
  calc ENNReal.ofReal c * ∑ i, edist (v i) (w i)
      ≤ ENNReal.ofReal c * ((Fintype.card ι : ℝ≥0∞) * edist v w) :=
        mul_le_mul_right hstep _
    _ = ENNReal.ofReal c * (Fintype.card ι : ℝ≥0∞) * edist v w := by
        rw [mul_assoc]

/-- A finite (`Fintype`-indexed) tuple of already `L¹`-relatively-compact real families stays
`L¹`-relatively compact after applying any `ℓ¹`-Lipschitz function `g` (with `g 0 = 0`) to the
tuple pointwise. This is the nonlinear counterpart of `isCompact_closure_range_combo3`
(`LpExponentCompact.lean`), needed whenever the target observable is a Lipschitz -- but not
linear -- function of finitely many jointly-compact coordinates (e.g. an operator norm of a
matrix built from already-compact entries). -/
theorem isCompact_closure_range_lipschitz_combo
    (f : ι → ℕ → α → ℝ) (hmem : ∀ i K, MemLp (f i K) 1 μ)
    (hf : ∀ i, IsCompact (closure (Set.range (fun K => (hmem i K).toLp (f i K)))))
    (g : (ι → ℝ) → ℝ) (c : ℝ) (hc : 0 ≤ c) (hg0 : g 0 = 0)
    (hglip : ∀ u v : ι → ℝ, |g u - g v| ≤ c * ∑ i, |u i - v i|) :
    ∃ hcomb : ∀ K, MemLp (fun ω => g (fun i => f i K ω)) 1 μ,
      IsCompact (closure (Set.range (fun K => (hcomb K).toLp (fun ω => g (fun i => f i K ω))))) := by
  have hgcont : Continuous g := lipCombo_continuous g c hc hglip
  have hcomb : ∀ K, MemLp (fun ω => g (fun i => f i K ω)) 1 μ := fun K =>
    lipCombo_memLp g c hc hg0 hgcont hglip (fun i => f i K) (fun i => (hmem i K).aestronglyMeasurable)
      (fun i => hmem i K)
  refine ⟨hcomb, ?_⟩
  set F : (ι → Lp ℝ 1 μ) → Lp ℝ 1 μ := fun v =>
    (lipCombo_memLp g c hc hg0 hgcont hglip (fun i => (v i : α → ℝ))
        (fun i => Lp.aestronglyMeasurable (v i)) (fun i => Lp.memLp (v i))).toLp
      (fun ω => g (fun i => (v i : α → ℝ) ω)) with hFdef
  have hFcoe : ∀ v : ι → Lp ℝ 1 μ,
      ⇑(F v) =ᵐ[μ] fun ω => g (fun i => (v i : α → ℝ) ω) := by
    intro v; rw [hFdef]; exact MemLp.coeFn_toLp _
  have hFcont : Continuous F := by
    have hLip : LipschitzWith (ENNReal.ofReal c * (Fintype.card ι : ℝ≥0∞)).toNNReal F := by
      intro v w
      rw [ENNReal.coe_toNNReal
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _))]
      have hedist : edist (F v) (F w) =
          eLpNorm (fun ω => g (fun i => (v i : α → ℝ) ω) - g (fun i => (w i : α → ℝ) ω)) 1 μ := by
        rw [hFdef]; exact Lp.edist_toLp_toLp _ _ _ _
      rw [hedist]
      exact (lipCombo_flipBound g c hc hglip v w).trans (lipCombo_cardBound c hc v w)
    exact hLip.continuous
  have hjoint : IsCompact (closure (Set.range (fun K : ℕ => fun i => (hmem i K).toLp (f i K)))) := by
    have hsub : closure (Set.range (fun K : ℕ => fun i => (hmem i K).toLp (f i K))) ⊆
        Set.pi Set.univ (fun i => closure (Set.range (fun K => (hmem i K).toLp (f i K)))) := by
      apply closure_minimal
      · rintro x ⟨K, rfl⟩; intro i _; exact subset_closure ⟨K, rfl⟩
      · exact isClosed_set_pi (fun i _ => isClosed_closure)
    exact IsCompact.of_isClosed_subset (isCompact_univ_pi hf) isClosed_closure hsub
  have hrep : (fun K => (hcomb K).toLp (fun ω => g (fun i => f i K ω))) =
      (fun K => F (fun i => (hmem i K).toLp (f i K))) := by
    funext K
    apply Lp.ext
    have hcombae := (hcomb K).coeFn_toLp
    have htupleae : ∀ i, ⇑((hmem i K).toLp (f i K)) =ᵐ[μ] f i K := fun i => (hmem i K).coeFn_toLp
    filter_upwards [hcombae, hFcoe (fun i => (hmem i K).toLp (f i K)),
      MeasureTheory.ae_all_iff.mpr htupleae] with ω hω1 hω0 hω2
    rw [hω1, hω0]
    congr 1
    funext i
    exact (hω2 i).symm
  rw [hrep]
  have him : IsCompact (F '' closure (Set.range (fun K : ℕ => fun i => (hmem i K).toLp (f i K)))) :=
    hjoint.image hFcont
  have hsub2 : closure (Set.range (fun K => F (fun i => (hmem i K).toLp (f i K)))) ⊆
      F '' closure (Set.range (fun K : ℕ => fun i => (hmem i K).toLp (f i K))) := by
    apply closure_minimal
    · rintro x ⟨K, rfl⟩; exact ⟨_, subset_closure ⟨K, rfl⟩, rfl⟩
    · exact him.isClosed
  exact IsCompact.of_isClosed_subset him isClosed_closure hsub2

end
