module

public import SubdiffusiveProcess.Lane3.RelativeResponseSlopes
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
public import SubdiffusiveProcess.Lane4.Inputs
public import Mathlib.Analysis.Matrix.Normed
public import SubdiffusiveProcess.Lane3.RelativeConcentration
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import Mathlib.Probability.ProductMeasure
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import SubdiffusiveProcess.Lane4.Scaling
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.CellSymmetry.MatrixLaw
public import SubdiffusiveProcess.CellSymmetry.Laws

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise ContDiff Distributions

noncomputable section
namespace SubdiffusiveProcess
namespace CellSymmetry

def cs_lc_rel {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (v : Fin d → ℝ) : ℝ :=
  (v ⬝ᵥ B.mulVec v - c * (v ⬝ᵥ A.mulVec v)) / Matrix.trace A

/-- The finite affine set of slopes `e_i`, `e_i + e_j` used for polarization. -/
def cs_lc_slope {d : ℕ} (v : Fin d → ℝ) : Prop :=
  (∃ i : Fin d, v = Pi.single i (1 : ℝ)) ∨
    (∃ i j : Fin d, v = Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))

theorem cs_lc_single_mulVec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    Pi.single i (1 : ℝ) ⬝ᵥ A.mulVec (Pi.single j (1 : ℝ)) = A i j := by exact SubdiffusiveProcess.Lane3.RelSlopes.single_dotProduct_mulVec_single (d := d) (A := A) (i := i) (j := j)

theorem cs_lc_symm_apply {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.transpose = A) (i j : Fin d) : A j i = A i j := by
  have h := congrFun (congrFun hA i) j
  simpa [Matrix.transpose_apply] using h

theorem cs_lc_pair_quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (i j : Fin d) :
    (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) ⬝ᵥ
        A.mulVec (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) =
      A i i + A j j + 2 * A i j := by exact SubdiffusiveProcess.Lane3.RelSlopes.pair_quadForm (d := d) (A := A) (hA := hA) (i := i) (j := j)

theorem cs_lc_diff_quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (i j : Fin d) :
    (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) ⬝ᵥ
        A.mulVec (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) =
      A i i + A j j - 2 * A i j := by exact SubdiffusiveProcess.Lane3.RelSlopes.diff_quadForm (d := d) (A := A) (hA := hA) (i := i) (j := j)

/-- Polarization: every entry of the centred matrix is a combination of three
relative scalar responses (paper line 3446, "after polarization over the finite
affine set"). -/
theorem cs_lc_entry_polar {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) (c : ℝ) (i j : Fin d) :
    ((Matrix.trace A)⁻¹ • (B - c • A)) i j =
      (cs_lc_rel A B c (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) -
        cs_lc_rel A B c (Pi.single i (1 : ℝ)) -
        cs_lc_rel A B c (Pi.single j (1 : ℝ))) / 2 := by
  simp only [cs_lc_rel, cs_lc_pair_quad A hA, cs_lc_pair_quad B hB,
    cs_lc_single_mulVec, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- On a slope, the quadratic value of a positive semidefinite matrix is at most
four times its trace. -/
theorem cs_lc_quad_le_trace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ A.mulVec v)
    (v : Fin d → ℝ) (hv : cs_lc_slope v) :
    v ⬝ᵥ A.mulVec v ≤ 4 * Matrix.trace A := by
  have hdiag : ∀ j : Fin d, 0 ≤ A j j := by
    intro j
    have h := hpsd (Pi.single j (1 : ℝ))
    rwa [cs_lc_single_mulVec] at h
  have hle : ∀ j : Fin d, A j j ≤ Matrix.trace A := by
    intro j
    have h := Finset.single_le_sum (f := fun l : Fin d => A l l)
      (fun l _ => hdiag l) (Finset.mem_univ j)
    simpa [Matrix.trace, Matrix.diag] using h
  have htr : 0 ≤ Matrix.trace A := (hdiag ⟨0, by
    rcases hv with ⟨i, _⟩ | ⟨i, _, _⟩ <;> exact lt_of_le_of_lt (Nat.zero_le _) i.2⟩).trans
      (hle _)
  rcases hv with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · rw [cs_lc_single_mulVec]
    linarith [hle i]
  · rw [cs_lc_pair_quad A hA]
    have hd := hpsd (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))
    rw [cs_lc_diff_quad A hA] at hd
    linarith [hle i, hle j]

/-- The relative scalar is bounded by `4 M` on the slopes under the form order. -/
theorem cs_lc_rel_abs_le {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ A.mulVec v)
    (m M c : ℝ) (hm : 0 ≤ m) (hc0 : 0 ≤ c) (hcM : c ≤ M)
    (htr : 0 < Matrix.trace A)
    (hord : ∀ v : Fin d → ℝ, m * (v ⬝ᵥ A.mulVec v) ≤ v ⬝ᵥ B.mulVec v ∧
      v ⬝ᵥ B.mulVec v ≤ M * (v ⬝ᵥ A.mulVec v))
    (v : Fin d → ℝ) (hv : cs_lc_slope v) :
    |cs_lc_rel A B c v| ≤ 4 * M := by
  have hq := cs_lc_quad_le_trace A hA hpsd v hv
  have hq0 := hpsd v
  have hB0 : 0 ≤ v ⬝ᵥ B.mulVec v := le_trans (mul_nonneg hm hq0) (hord v).1
  have hBle : v ⬝ᵥ B.mulVec v ≤ M * (4 * Matrix.trace A) :=
    (hord v).2.trans (mul_le_mul_of_nonneg_left hq (hc0.trans hcM))
  have hcle : c * (v ⬝ᵥ A.mulVec v) ≤ M * (4 * Matrix.trace A) :=
    mul_le_mul hcM hq hq0 (hc0.trans hcM)
  have hc0' : 0 ≤ c * (v ⬝ᵥ A.mulVec v) := mul_nonneg hc0 hq0
  unfold cs_lc_rel
  rw [abs_div, abs_of_pos htr, div_le_iff₀ htr, abs_le]
  constructor <;> nlinarith

/-! ### Probability assembly -/

section
variable {Ω : Type} [MeasurableSpace Ω]

/-- Mean value of a random variable almost surely in `[m, M]`. -/
theorem cs_lc_integral_mem_Icc (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f P) (m M : ℝ)
    (hfm : ∀ᵐ omega ∂P, m ≤ f omega ∧ f omega ≤ M) :
    Integrable f P ∧ (∫ omega, f omega ∂P) ∈ Icc m M := by
  have hint : Integrable f P := by
    refine Integrable.of_bound hf (max |m| |M|) ?_
    filter_upwards [hfm] with omega homega
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := neg_abs_le m; have := le_max_left |m| |M|; linarith [homega.1]
    · have := le_abs_self M; have := le_max_right |m| |M|; linarith [homega.2]
  refine ⟨hint, ?_, ?_⟩
  · have h := integral_mono_ae (integrable_const m) hint (hfm.mono fun omega homega => homega.1)
    simpa using h
  · have h := integral_mono_ae hint (integrable_const M) (hfm.mono fun omega homega => homega.2)
    simpa using h

end

section
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- Entry, trace and relative-scalar measurability from the quadratic values. -/
theorem cs_lc_gen_meas (P : Measure Ω)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymAE : ∀ k omega, (AE k omega).transpose = AE k omega)
    (hsymAF : ∀ k omega, (AF k omega).transpose = AF k omega)
    (hmE : ∀ (k : ℕ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => v ⬝ᵥ (AE k omega).mulVec v) P)
    (hmF : ∀ (k : ℕ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => v ⬝ᵥ (AF k omega).mulVec v) P) :
    (∀ (k : ℕ) (i j : Fin d), AEStronglyMeasurable (fun omega => AE k omega i j) P) ∧
    (∀ (k : ℕ) (i j : Fin d), AEStronglyMeasurable (fun omega => AF k omega i j) P) ∧
    (∀ k : ℕ, AEStronglyMeasurable (fun omega => Matrix.trace (AE k omega)) P) ∧
    (∀ k : ℕ, AEStronglyMeasurable (fun omega => Matrix.trace (AF k omega) / Matrix.trace (AE k omega)) P) ∧
    (∀ (k : ℕ) (c : ℝ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => cs_lc_rel (AE k omega) (AF k omega) c v) P) := by
  have hent : ∀ (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ),
      (∀ k omega, (A k omega).transpose = A k omega) →
      (∀ (k : ℕ) (v : Fin d → ℝ),
        AEStronglyMeasurable (fun omega => v ⬝ᵥ (A k omega).mulVec v) P) →
      ∀ (k : ℕ) (i j : Fin d), AEStronglyMeasurable (fun omega => A k omega i j) P := by
    intro A hA hm k i j
    have h : AEStronglyMeasurable (fun omega =>
        ((Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) ⬝ᵥ
            (A k omega).mulVec (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) -
          Pi.single i (1 : ℝ) ⬝ᵥ (A k omega).mulVec (Pi.single i (1 : ℝ)) -
          Pi.single j (1 : ℝ) ⬝ᵥ (A k omega).mulVec (Pi.single j (1 : ℝ))) * (1 / 2)) P :=
      (((hm k _).sub (hm k _)).sub (hm k _)).mul_const _
    refine h.congr (Eventually.of_forall fun omega => ?_)
    simp only [cs_lc_pair_quad _ (hA k omega), cs_lc_single_mulVec]
    ring
  have hE := hent AE hsymAE hmE
  have hF := hent AF hsymAF hmF
  have htr : ∀ (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ),
      (∀ (k : ℕ) (i j : Fin d), AEStronglyMeasurable (fun omega => A k omega i j) P) →
      ∀ k : ℕ, AEStronglyMeasurable (fun omega => Matrix.trace (A k omega)) P := by
    intro A hA k
    have : (fun omega => Matrix.trace (A k omega)) = ∑ j : Fin d, (fun omega => A k omega j j) := by
      funext omega; simp [Matrix.trace, Matrix.diag]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun j _ => hA k j j
  have htrE := htr AE hE
  have htrF := htr AF hF
  refine ⟨hE, hF, htrE, fun k => ?_, fun k c v => ?_⟩
  · exact ((htrF k).aemeasurable.div (htrE k).aemeasurable).aestronglyMeasurable
  · exact (((hmF k v).aemeasurable.sub ((hmE k v).aemeasurable.const_mul c)).div
      (htrE k).aemeasurable).aestronglyMeasurable

end


section Centering

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- Step 1 of `prop_conc`: `c_k ∈ [m, M]` and `E B_k = 0`. -/
theorem cs_centering_of_laws (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymAE : ∀ k omega, (AE k omega).transpose = AE k omega)
    (hsymAF : ∀ k omega, (AF k omega).transpose = AF k omega)
    (hmE : ∀ (k : ℕ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => v ⬝ᵥ (AE k omega).mulVec v) P)
    (hmF : ∀ (k : ℕ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => v ⬝ᵥ (AF k omega).mulVec v) P)
    (hpsd : ∀ᵐ omega ∂P, ∀ (k : ℕ) (v : Fin d → ℝ), 0 ≤ v ⬝ᵥ (AE k omega).mulVec v)
    (m M : ℝ) (hm : 0 ≤ m)
    (hord : ∀ᵐ omega ∂P, ∀ k : ℕ, 0 < Matrix.trace (AE k omega) ∧
      ∀ v : Fin d → ℝ, m * (v ⬝ᵥ (AE k omega).mulVec v) ≤ v ⬝ᵥ (AF k omega).mulVec v ∧
        v ⬝ᵥ (AF k omega).mulVec v ≤ M * (v ⬝ᵥ (AE k omega).mulVec v))
    (hsym : ∀ k : ℕ,
      (∀ i : Fin d, Measure.map (fun omega => cs_lc_normpair (AE k omega) (AF k omega)) P =
        Measure.map (fun omega => cs_lc_reflpair i
          (cs_lc_normpair (AE k omega) (AF k omega))) P) ∧
      (∀ σ : Equiv.Perm (Fin d),
        Measure.map (fun omega => cs_lc_normpair (AE k omega) (AF k omega)) P =
          Measure.map (fun omega => cs_lc_permpair σ
            (cs_lc_normpair (AE k omega) (AF k omega))) P)) :
    (∀ k : ℕ, (∫ omega, Matrix.trace (AF k omega) / Matrix.trace (AE k omega) ∂P) ∈ Icc m M) ∧
    (∀ (k : ℕ) (i j : Fin d),
      ∫ omega, ((Matrix.trace (AE k omega))⁻¹ •
        (AF k omega - (∫ omega', Matrix.trace (AF k omega') / Matrix.trace (AE k omega') ∂P) •
          AE k omega)) i j ∂P = 0) := by
  obtain ⟨hEntE, hEntF, htrE, hratm, hrelm⟩ :=
    cs_lc_gen_meas P AE AF hsymAE hsymAF hmE hmF
  have hrelInt : ∀ c, 0 ≤ c → c ≤ M → ∀ (k : ℕ) (v : Fin d → ℝ), cs_lc_slope v →
      Integrable (fun omega => cs_lc_rel (AE k omega) (AF k omega) c v) P := by
    intro c hc0 hcM k v hv
    refine Integrable.of_bound (hrelm k c v) (4 * M) ?_
    filter_upwards [hpsd, hord] with omega hp ho
    rw [Real.norm_eq_abs]
    exact cs_lc_rel_abs_le _ _ (hsymAE k omega) (hp k) m M c hm hc0 hcM (ho k).1 (ho k).2 v hv
  have hck : ∀ k : ℕ, Integrable (fun omega => Matrix.trace (AF k omega) / Matrix.trace (AE k omega)) P ∧
      (∫ omega, Matrix.trace (AF k omega) / Matrix.trace (AE k omega) ∂P) ∈ Icc m M := by
    intro k
    refine cs_lc_integral_mem_Icc P _ (hratm k) m M ?_
    filter_upwards [hord] with omega ho
    exact SubdiffusiveProcess.Lane3.trace_ratio_mem_Icc_of_form_order (AE k omega) (AF k omega) m M
      (ho k).1 (ho k).2
  refine ⟨fun k => (hck k).2, ?_⟩
  intro k
  have hc0 : 0 ≤ ∫ omega, Matrix.trace (AF k omega) / Matrix.trace (AE k omega) ∂P :=
    hm.trans (hck k).2.1
  have hcM : (∫ omega, Matrix.trace (AF k omega) / Matrix.trace (AE k omega) ∂P) ≤ M :=
    (hck k).2.2
  have hBint : ∀ (i j : Fin d), Integrable (fun omega => ((Matrix.trace (AE k omega))⁻¹ •
      (AF k omega - (∫ omega', Matrix.trace (AF k omega') / Matrix.trace (AE k omega') ∂P) •
        AE k omega)) i j) P := by
    intro i j
    have h := (((hrelInt _ hc0 hcM k _ (Or.inr ⟨i, j, rfl⟩)).sub
      (hrelInt _ hc0 hcM k _ (Or.inl ⟨i, rfl⟩))).sub
      (hrelInt _ hc0 hcM k _ (Or.inl ⟨j, rfl⟩))).div_const 2
    refine h.congr (Eventually.of_forall fun omega => ?_)
    simp only [Pi.sub_apply]
    exact (cs_lc_entry_polar (AE k omega) (AF k omega) (hsymAE k omega) (hsymAF k omega) _ i j).symm
  have htrace : ∫ omega, Matrix.trace ((Matrix.trace (AE k omega))⁻¹ •
      (AF k omega - (∫ omega', Matrix.trace (AF k omega') / Matrix.trace (AE k omega') ∂P) •
        AE k omega)) ∂P = 0 := by
    have hae : (fun omega => Matrix.trace ((Matrix.trace (AE k omega))⁻¹ •
        (AF k omega - (∫ omega', Matrix.trace (AF k omega') / Matrix.trace (AE k omega') ∂P) •
          AE k omega))) =ᵐ[P]
        fun omega => Matrix.trace (AF k omega) / Matrix.trace (AE k omega) -
          ∫ omega', Matrix.trace (AF k omega') / Matrix.trace (AE k omega') ∂P := by
      filter_upwards [hord] with omega ho
      have hne := (ho k).1.ne'
      rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
      field_simp
    rw [integral_congr_ae hae, integral_sub (hck k).1 (integrable_const _)]
    simp
  intro i j
  exact cs_lc_mean_zero hd P (AE k) (AF k)
    (∫ omega', Matrix.trace (AF k omega') / Matrix.trace (AE k omega') ∂P)
    (hEntE k) (hEntF k) hBint htrace (hsym k).1 (hsym k).2 i j

end Centering

end CellSymmetry
end SubdiffusiveProcess
