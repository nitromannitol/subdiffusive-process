module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lane3.Forms
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Lane3.DirichletForm
public import SubdiffusiveProcess.Lane3.ResamplingV2
public import SubdiffusiveProcess.Lane3.UpperDensity
public import SubdiffusiveProcess.Lane3.BandFiltration
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import SubdiffusiveProcess.Probability.ResponseCompactness
public import SubdiffusiveProcess.Variational.QuadraticSaving
public import SubdiffusiveProcess.Compactness.OperatorLimits
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Matrix.Norms.Elementwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_lem_conc_sq
    (Om : Type) [MeasurableSpace Om] (P : Measure Om) (g : Om → ℝ) :
    (∫⁻ ω, ‖g ω‖ₑ ^ (2 : ℝ) ∂P) = (SubdiffusiveProcess.RawLp.eLpNorm g 2 P) ^ 2 := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) (by norm_num)]
  norm_num [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  norm_num

theorem aux_lem_conc_sq_add (a b : ℝ≥0∞) :
    (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have hab : a + b ≤ max a b + max a b :=
    add_le_add (le_max_left _ _) (le_max_right _ _)
  have hpow : (a + b) ^ 2 ≤ (max a b + max a b) ^ 2 :=
    pow_le_pow_left' hab 2
  have hmax : (max a b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    by_cases h : a ≤ b
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left (le_of_not_ge h)]
      exact le_add_of_nonneg_right (by positivity)
  calc
    (a + b) ^ 2 ≤ (max a b + max a b) ^ 2 := hpow
    _ = 4 * (max a b) ^ 2 := by ring
    _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul_right hmax _

theorem aux_lem_conc_add_const
    (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (f : Om → ℝ) (c : ℝ) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun ω => f ω + c) 2 P ≤
      2 * (SubdiffusiveProcess.RawLp.eLpNorm f 2 P + ENNReal.ofReal |c|) := by
  have hc : ‖c‖ₑ = ENNReal.ofReal |c| := Real.enorm_eq_ofReal_abs c
  have hpoint : ∀ ω : Om,
      ‖f ω + c‖ₑ ^ (2 : ℝ) ≤
        4 * (‖f ω‖ₑ ^ (2 : ℝ) + ‖c‖ₑ ^ (2 : ℝ)) := by
    intro ω
    convert (pow_le_pow_left' (enorm_add_le _ _) 2).trans
      (aux_lem_conc_sq_add ‖f ω‖ₑ ‖c‖ₑ) using 1 <;>
      norm_num [ENNReal.rpow_natCast]
  have hinter : (∫⁻ ω, ‖f ω + c‖ₑ ^ (2 : ℝ) ∂P) ≤
      4 * ((∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P) + ‖c‖ₑ ^ (2 : ℝ)) := by
    calc
      (∫⁻ ω, ‖f ω + c‖ₑ ^ (2 : ℝ) ∂P) ≤
          ∫⁻ ω, 4 * (‖f ω‖ₑ ^ (2 : ℝ) + ‖c‖ₑ ^ (2 : ℝ)) ∂P :=
        lintegral_mono (fun ω => hpoint ω)
      _ = 4 * (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P + ‖c‖ₑ ^ (2 : ℝ)) := by
        rw [lintegral_const_mul' 4 _ (by norm_num)]
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ]
        simp
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) (by norm_num)]
  have hsum : (SubdiffusiveProcess.RawLp.eLpNorm f 2 P) ^ 2 + (ENNReal.ofReal |c|) ^ 2 ≤
      (SubdiffusiveProcess.RawLp.eLpNorm f 2 P + ENNReal.ofReal |c|) ^ 2 := by
    calc
      (SubdiffusiveProcess.RawLp.eLpNorm f 2 P) ^ 2 + (ENNReal.ofReal |c|) ^ 2 ≤
          (SubdiffusiveProcess.RawLp.eLpNorm f 2 P) ^ 2 + 2 * SubdiffusiveProcess.RawLp.eLpNorm f 2 P * ENNReal.ofReal |c| +
            (ENNReal.ofReal |c|) ^ 2 := by
              have hcross : 0 ≤ 2 * SubdiffusiveProcess.RawLp.eLpNorm f 2 P * ENNReal.ofReal |c| := by
                positivity
              have hbase : (SubdiffusiveProcess.RawLp.eLpNorm f 2 P) ^ 2 ≤
                  (SubdiffusiveProcess.RawLp.eLpNorm f 2 P) ^ 2 + 2 * SubdiffusiveProcess.RawLp.eLpNorm f 2 P * ENNReal.ofReal |c| :=
                le_add_of_nonneg_right hcross
              exact add_le_add hbase (le_refl _)
      _ = (SubdiffusiveProcess.RawLp.eLpNorm f 2 P + ENNReal.ofReal |c|) ^ 2 := by ring
  have hbound : (∫⁻ ω, ‖f ω + c‖ₑ ^ (2 : ℝ) ∂P) ≤
      (2 * (SubdiffusiveProcess.RawLp.eLpNorm f 2 P + ENNReal.ofReal |c|)) ^ 2 := by
    calc
      (∫⁻ ω, ‖f ω + c‖ₑ ^ (2 : ℝ) ∂P) ≤
          4 * ((SubdiffusiveProcess.RawLp.eLpNorm f 2 P) ^ 2 + ‖c‖ₑ ^ 2) := by
            calc
              (∫⁻ ω, ‖f ω + c‖ₑ ^ (2 : ℝ) ∂P) ≤
                  4 * ((∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P) + ‖c‖ₑ ^ 2) := hinter
              _ = 4 * ((SubdiffusiveProcess.RawLp.eLpNorm f 2 P) ^ 2 + ‖c‖ₑ ^ 2) := by
                rw [aux_lem_conc_sq (Om := Om) (P := P) f]
                norm_num [ENNReal.rpow_natCast]
      _ = 4 * ((SubdiffusiveProcess.RawLp.eLpNorm f 2 P) ^ 2 + (ENNReal.ofReal |c|) ^ 2) := by rw [hc]
      _ ≤ 4 * (SubdiffusiveProcess.RawLp.eLpNorm f 2 P + ENNReal.ofReal |c|) ^ 2 :=
        mul_le_mul_right hsum _
      _ = (2 * (SubdiffusiveProcess.RawLp.eLpNorm f 2 P + ENNReal.ofReal |c|)) ^ 2 := by ring
  calc
    (∫⁻ ω, ‖f ω + c‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤
        ((2 * (SubdiffusiveProcess.RawLp.eLpNorm f 2 P + ENNReal.ofReal |c|)) ^ 2) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = 2 * (SubdiffusiveProcess.RawLp.eLpNorm f 2 P + ENNReal.ofReal |c|) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

/-- lemma `mfd:lem-conc` (paper lines 3844-3878), Concentration of inverse responses: along a subsequence of `k` there are DETERMINISTIC matrices `P >= I`, `R >= I` with `sup_{k <= n <= 4k} ||E P_{i_k}(n) - P|| -> 0` and `sup_{2k <= n <= 4k} ||R_{i_k}(n) - R||_{L^2} -> 0`.  `EP j n` is the annealed matrix `E P_{i_j}(n)` and `R j n` the random inverse response `R_{i_j}(n)`, compared in `L^2(P)`.  `hPunif` is the uniform window estimate from the positive semidefinite defect `X_{n,k}` and the vanishing annealed Dirichlet defect; `hRunif` concentrates the random inverse responses on the DETERMINISTIC mean `ERmean j = E R_{i_j}(k)` of the base scale (`hERdef`), not on a random reference, which is what supplies the deterministic limit; it is the variance bound `Var(3^{-d(n-k)} sum_z R(z + cu_k)) <= C 3^{-d(n-k)} sup E|R|^2` for `n >= 2k`, which is where Assumption a.g1 (spatial finite-range independence of the scale-`k` cubes inside the fixed coefficient `A_N^0`) is consumed.  The conclusion is the Bolzano-Weierstrass extraction of the common limits, which inherit `>= I` from `mfd:lem-fmono`.  The `>= I` inputs are the ANNEALED ones supplied by `lem_fmono`: `hPI` for the annealed Dirichlet matrices and `hERmeanI` for the deterministic means `ERmean j = E R_{i_j}(k)`.  The paper never asserts `R_{i_j}(n, omega) >= I` pointwise in `omega` -- only the annealed bound -- and `hERmeanI` is all the conclusion needs, since `Rl` is the limit of the `ERmean j` in `L^2`.  `hPunif` and `hRunif` are the conclusion of `annealed_window_convergence` (paper lines 3857-3874), whose annealed half rests on `near_extremal_member` (3837-3841).  The symmetry hypotheses `hEPsym : ∀ j n, (EP j n).transpose = EP j n` and `hERmeanSym : ∀ j, (ERmean j).transpose = ERmean j` are SUPPLIED by the actual symmetric Dirichlet and inverse-Neumann response carriers of `stationary_defects` (expectation preserves symmetry); they assume no limit and no output, and the extracted limits accordingly satisfy `Pl.transpose = Pl` and `Rl.transpose = Rl`, so the two quadratic-form lower bounds are precisely `(Pl - I).PosSemidef` and `(Rl - I).PosSemidef` over the reals. -/
theorem lem_conc
    (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (d : ℕ) (hd : 1 ≤ d)
    (EP : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hEPsym : ∀ j n, (EP j n).transpose = EP j n)
    (R : ℕ → ℕ → Om → Matrix (Fin d) (Fin d) ℝ)
    (ks : ℕ → ℕ) (hks : StrictMono ks)
    (ERmean : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hERmeanSym : ∀ j, (ERmean j).transpose = ERmean j)
    (hERdef : ∀ (j : ℕ) (a b : Fin d),
      ERmean j a b = ∫ ω, R j (ks j) ω a b ∂P)
    (Kb : ℝ) (hKb : 0 ≤ Kb)
    (hERb : ∀ (j : ℕ) (a b : Fin d), |ERmean j a b| ≤ Kb)
    (hPb : ∀ (j : ℕ) (a b : Fin d), |EP j (4 * ks j) a b| ≤ Kb)
    (hRb : ∀ (j n : ℕ) (a b : Fin d),
      SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R j n ω a b) 2 P ≤ ENNReal.ofReal Kb)
    (hPI : ∀ (j n : ℕ) (x : Fin d → ℝ), x ⬝ᵥ x ≤ x ⬝ᵥ (EP j n).mulVec x)
    (hERmeanI : ∀ (j : ℕ) (x : Fin d → ℝ), x ⬝ᵥ x ≤ x ⬝ᵥ (ERmean j).mulVec x)
    (hPunif : ∀ eps : ℝ, 0 < eps → ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j →
      ∀ n ∈ Finset.Icc (ks j) (4 * ks j),
        ∑ a : Fin d, ∑ b : Fin d, |EP j n a b - EP j (4 * ks j) a b| ≤ eps)
    (hRunif : ∀ eps : ℝ, 0 < eps → ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j →
      ∀ n ∈ Finset.Icc (2 * ks j) (4 * ks j),
        ∑ a : Fin d, ∑ b : Fin d,
            SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R j n ω a b - ERmean j a b) 2 P ≤
          ENNReal.ofReal eps) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Pl Rl : Matrix (Fin d) (Fin d) ℝ,
        Pl.transpose = Pl ∧ Rl.transpose = Rl ∧
        (∀ x : Fin d → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ Pl.mulVec x) ∧
        (∀ x : Fin d → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ Rl.mulVec x) ∧
        (∀ eps : ℝ, 0 < eps → ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j →
          ∀ n ∈ Finset.Icc (ks (phi j)) (4 * ks (phi j)),
            ∑ a : Fin d, ∑ b : Fin d, |EP (phi j) n a b - Pl a b| ≤ eps) ∧
    ∀ eps : ℝ, 0 < eps → ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j →
          ∀ n ∈ Finset.Icc (2 * ks (phi j)) (4 * ks (phi j)),
            ∑ a : Fin d, ∑ b : Fin d,
                SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R (phi j) n ω a b - Rl a b) 2 P ≤
              ENNReal.ofReal eps := by
  letI : FirstCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin d → Fin d → ℝ))
  have hS : IsCompact {M : Matrix (Fin d) (Fin d) ℝ |
      ∀ a b, |M a b| ≤ Kb} := by
    have h : IsCompact {M : Matrix (Fin d) (Fin d) ℝ |
        ∀ a b, M a b ∈ Set.Icc (-Kb) Kb} :=
      isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_Icc))
    simpa only [Set.mem_setOf_eq, Set.mem_Icc, abs_le] using h
  have hERmem : ∀ j, ERmean j ∈ {M : Matrix (Fin d) (Fin d) ℝ | ∀ a b, |M a b| ≤ Kb} :=
    fun j => hERb j
  have hEPmem : ∀ j, EP j (4 * ks j) ∈ {M : Matrix (Fin d) (Fin d) ℝ | ∀ a b, |M a b| ≤ Kb} :=
    fun j => hPb j
  obtain ⟨Rl, -, phi₁, hphi₁, hRlim⟩ := hS.tendsto_subseq (x := ERmean) hERmem
  obtain ⟨Pl, -, phi₂, hphi₂, hPlim⟩ :=
    hS.tendsto_subseq (x := fun j => EP (phi₁ j) (4 * ks (phi₁ j)))
      (fun j => hEPmem (phi₁ j))
  set phi : ℕ → ℕ := phi₁ ∘ phi₂ with hphidef
  have hphi : StrictMono phi := by
    rw [hphidef]
    exact hphi₁.comp hphi₂
  have hphige : ∀ j, j ≤ phi j := by
    intro j
    exact hphi.id_le j
  have hphi₂_top : Tendsto phi₂ atTop atTop := hphi₂.tendsto_atTop
  have hRlim' : Tendsto (fun j => ERmean (phi j)) atTop (𝓝 Rl) := by
    have h := hRlim.comp hphi₂_top
    simpa [hphidef, Function.comp_def] using h
  have hPlim' : Tendsto (fun j => EP (phi j) (4 * ks (phi j))) atTop (𝓝 Pl) := by
    simpa [hphidef, Function.comp_def] using hPlim
  have hRentry : ∀ a b, Tendsto (fun j => ERmean (phi j) a b) atTop (𝓝 (Rl a b)) := by
    intro a b
    exact (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hRlim') a)) b
  have hPentry : ∀ a b, Tendsto (fun j => EP (phi j) (4 * ks (phi j)) a b)
      atTop (𝓝 (Pl a b)) := by
    intro a b
    exact (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hPlim') a)) b
  have hPlSym : Pl.transpose = Pl := by
    ext a b
    simp only [Matrix.transpose_apply]
    have h1 : ∀ j, EP (phi j) (4 * ks (phi j)) b a =
        EP (phi j) (4 * ks (phi j)) a b := by
      intro j
      have h := congrFun (congrFun (hEPsym (phi j) (4 * ks (phi j))) a) b
      simpa [Matrix.transpose_apply] using h
    have hb : Tendsto (fun j => EP (phi j) (4 * ks (phi j)) b a) atTop
        (𝓝 (Pl b a)) := hPentry b a
    have ha : Tendsto (fun j => EP (phi j) (4 * ks (phi j)) b a) atTop
        (𝓝 (Pl a b)) := by
      rw [show (fun j => EP (phi j) (4 * ks (phi j)) b a) =
            (fun j => EP (phi j) (4 * ks (phi j)) a b) from funext h1]
      exact hPentry a b
    exact tendsto_nhds_unique hb ha
  have hRlSym : Rl.transpose = Rl := by
    ext a b
    simp only [Matrix.transpose_apply]
    have h1 : ∀ j, ERmean (phi j) b a = ERmean (phi j) a b := by
      intro j
      have h := congrFun (congrFun (hERmeanSym (phi j)) a) b
      simpa [Matrix.transpose_apply] using h
    have hb : Tendsto (fun j => ERmean (phi j) b a) atTop (𝓝 (Rl b a)) := hRentry b a
    have ha : Tendsto (fun j => ERmean (phi j) b a) atTop (𝓝 (Rl a b)) := by
      rw [show (fun j => ERmean (phi j) b a) =
            (fun j => ERmean (phi j) a b) from funext h1]
      exact hRentry a b
    exact tendsto_nhds_unique hb ha
  have hdot : ∀ (y : Fin d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
      y ⬝ᵥ M.mulVec y = ∑ a, y a * ∑ b, M a b * y b := by
    intro y M
    simp [dotProduct, Matrix.mulVec]
  have hPlI : ∀ x : Fin d → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ Pl.mulVec x := by
    intro x
    have hterm : ∀ a : Fin d, Tendsto (fun j => ∑ b,
        EP (phi j) (4 * ks (phi j)) a b * x b) atTop
        (𝓝 (∑ b, Pl a b * x b)) := by
      intro a
      apply tendsto_finset_sum
      intro b _
      exact (hPentry a b).mul_const (x b)
    have hquad : Tendsto (fun j => ∑ a, x a * ∑ b,
        EP (phi j) (4 * ks (phi j)) a b * x b) atTop
        (𝓝 (∑ a, x a * ∑ b, Pl a b * x b)) := by
      apply tendsto_finset_sum
      intro a _
      exact (hterm a).const_mul (x a)
    have hquad' : Tendsto (fun j => x ⬝ᵥ
        (EP (phi j) (4 * ks (phi j))).mulVec x) atTop
        (𝓝 (x ⬝ᵥ Pl.mulVec x)) := by
      simp only [hdot]
      exact hquad
    exact ge_of_tendsto hquad'
      (Filter.Eventually.of_forall (fun j => hPI (phi j) (4 * ks (phi j)) x))
  have hRlI : ∀ x : Fin d → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ Rl.mulVec x := by
    intro x
    have hterm : ∀ a : Fin d, Tendsto (fun j => ∑ b,
        ERmean (phi j) a b * x b) atTop (𝓝 (∑ b, Rl a b * x b)) := by
      intro a
      apply tendsto_finset_sum
      intro b _
      exact (hRentry a b).mul_const (x b)
    have hquad : Tendsto (fun j => ∑ a, x a * ∑ b,
        ERmean (phi j) a b * x b) atTop
        (𝓝 (∑ a, x a * ∑ b, Rl a b * x b)) := by
      apply tendsto_finset_sum
      intro a _
      exact (hterm a).const_mul (x a)
    have hquad' : Tendsto (fun j => x ⬝ᵥ (ERmean (phi j)).mulVec x) atTop
        (𝓝 (x ⬝ᵥ Rl.mulVec x)) := by
      simp only [hdot]
      exact hquad
    exact ge_of_tendsto hquad'
      (Filter.Eventually.of_forall (fun j => hERmeanI (phi j) x))
  have hPne : P ≠ 0 := by
    intro h
    have hu := measure_univ (μ := P)
    rw [h] at hu
    simp at hu
  have hconst_le : ∀ c : ℝ, SubdiffusiveProcess.RawLp.eLpNorm (fun _ : Om => c) 2 P ≤ ENNReal.ofReal |c| := by
    intro c
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (aestronglyMeasurable_const (b := c))]
    rw [MeasureTheory.eLpNorm_const c (by norm_num) hPne, measure_univ,
      Real.enorm_eq_ofReal_abs]
    simp
  have hEPuni : ∀ eps : ℝ, 0 < eps → ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j →
      ∀ n ∈ Finset.Icc (ks (phi j)) (4 * ks (phi j)),
        ∑ a : Fin d, ∑ b : Fin d, |EP (phi j) n a b - Pl a b| ≤ eps := by
    intro eps heps
    obtain ⟨j0, hj0⟩ := hPunif (eps / 2) (by linarith)
    have hG : Tendsto (fun j => ∑ a : Fin d, ∑ b : Fin d,
        |EP (phi j) (4 * ks (phi j)) a b - Pl a b|) atTop (𝓝 0) := by
      have hrow : ∀ a : Fin d, Tendsto (fun j => ∑ b : Fin d,
          |EP (phi j) (4 * ks (phi j)) a b - Pl a b|) atTop (𝓝 0) := by
        intro a
        have hs := tendsto_finset_sum (s := Finset.univ)
          (f := fun (b : Fin d) (j : ℕ) =>
            |EP (phi j) (4 * ks (phi j)) a b - Pl a b|)
          (x := atTop) (a := fun _ : Fin d => (0 : ℝ)) (fun b _ => by
            have h1 : Tendsto (fun j => EP (phi j) (4 * ks (phi j)) a b - Pl a b)
                atTop (𝓝 0) := by
              simpa using (hPentry a b).sub_const (Pl a b)
            have hb : Tendsto (fun j =>
                |EP (phi j) (4 * ks (phi j)) a b - Pl a b|) atTop (𝓝 0) := by
              simpa using h1.abs
            simpa using hb)
        simpa using hs
      have h := tendsto_finset_sum (s := Finset.univ)
        (f := fun (a : Fin d) (j : ℕ) => ∑ b : Fin d,
          |EP (phi j) (4 * ks (phi j)) a b - Pl a b|)
        (a := fun _ : Fin d => (0 : ℝ)) (fun a _ => hrow a)
      simpa using h
    have hGev : ∀ᶠ j in atTop, (∑ a : Fin d, ∑ b : Fin d,
        |EP (phi j) (4 * ks (phi j)) a b - Pl a b|) < eps / 2 :=
      hG.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨j1, hj1⟩ := eventually_atTop.1 hGev
    refine ⟨max j0 j1, fun j hj n hn => ?_⟩
    have hj0' : j0 ≤ phi j := le_trans (le_trans (le_max_left _ _) hj) (hphige j)
    have hu : ∑ a : Fin d, ∑ b : Fin d,
        |EP (phi j) n a b - EP (phi j) (4 * ks (phi j)) a b| ≤ eps / 2 :=
      hj0 (phi j) hj0' n hn
    have hv : ∑ a : Fin d, ∑ b : Fin d,
        |EP (phi j) (4 * ks (phi j)) a b - Pl a b| ≤ eps / 2 :=
      le_of_lt (hj1 j (le_trans (le_max_right _ _) hj))
    have hsub : ∀ a b, |EP (phi j) n a b - Pl a b| ≤
        |EP (phi j) n a b - EP (phi j) (4 * ks (phi j)) a b| +
        |EP (phi j) (4 * ks (phi j)) a b - Pl a b| := by
      intro a b
      rw [show EP (phi j) n a b - Pl a b =
          (EP (phi j) n a b - EP (phi j) (4 * ks (phi j)) a b) +
          (EP (phi j) (4 * ks (phi j)) a b - Pl a b) from by ring]
      exact abs_add_le _ _
    calc
      ∑ a : Fin d, ∑ b : Fin d, |EP (phi j) n a b - Pl a b| ≤
          ∑ a : Fin d, ∑ b : Fin d,
            (|EP (phi j) n a b - EP (phi j) (4 * ks (phi j)) a b| +
             |EP (phi j) (4 * ks (phi j)) a b - Pl a b|) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hsub a b))
      _ = (∑ a : Fin d, ∑ b : Fin d,
              |EP (phi j) n a b - EP (phi j) (4 * ks (phi j)) a b|) +
          (∑ a : Fin d, ∑ b : Fin d,
              |EP (phi j) (4 * ks (phi j)) a b - Pl a b|) := by
          simp only [Finset.sum_add_distrib]
      _ ≤ eps / 2 + eps / 2 := add_le_add hu hv
      _ = eps := by ring
  have hRuni : ∀ eps : ℝ, 0 < eps → ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j →
      ∀ n ∈ Finset.Icc (2 * ks (phi j)) (4 * ks (phi j)),
        ∑ a : Fin d, ∑ b : Fin d,
            SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R (phi j) n ω a b - Rl a b) 2 P ≤
          ENNReal.ofReal eps := by
    intro eps heps
    obtain ⟨j0, hj0⟩ := hRunif (eps / 4) (by linarith)
    have hSreal : Tendsto (fun j => ∑ a : Fin d, ∑ b : Fin d,
        |ERmean (phi j) a b - Rl a b|) atTop (𝓝 0) := by
      have hrow : ∀ a : Fin d, Tendsto (fun j => ∑ b : Fin d,
          |ERmean (phi j) a b - Rl a b|) atTop (𝓝 0) := by
        intro a
        have hs := tendsto_finset_sum (s := Finset.univ)
          (f := fun (b : Fin d) (j : ℕ) => |ERmean (phi j) a b - Rl a b|)
          (x := atTop) (a := fun _ : Fin d => (0 : ℝ)) (fun b _ => by
            have h1 : Tendsto (fun j => ERmean (phi j) a b - Rl a b) atTop (𝓝 0) := by
              simpa using (hRentry a b).sub_const (Rl a b)
            have hb : Tendsto (fun j => |ERmean (phi j) a b - Rl a b|) atTop (𝓝 0) := by
              simpa using h1.abs
            simpa using hb)
        simpa using hs
      have h := tendsto_finset_sum (s := Finset.univ)
        (f := fun (a : Fin d) (j : ℕ) => ∑ b : Fin d,
          |ERmean (phi j) a b - Rl a b|)
        (a := fun _ : Fin d => (0 : ℝ)) (fun a _ => hrow a)
      simpa using h
    have hSev : ∀ᶠ j in atTop, (∑ a : Fin d, ∑ b : Fin d,
        |ERmean (phi j) a b - Rl a b|) < eps / 4 :=
      hSreal.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨j1, hj1⟩ := eventually_atTop.1 hSev
    have hofreal : ∀ j : ℕ,
        (∑ a : Fin d, ∑ b : Fin d, ENNReal.ofReal |ERmean (phi j) a b - Rl a b|) =
        ENNReal.ofReal (∑ a : Fin d, ∑ b : Fin d,
            |ERmean (phi j) a b - Rl a b|) := by
      intro j
      rw [ENNReal.ofReal_sum_of_nonneg (fun a _ =>
            Finset.sum_nonneg (fun b _ => abs_nonneg _))]
      apply Finset.sum_congr rfl
      intro a _
      exact (ENNReal.ofReal_sum_of_nonneg (fun b _ => abs_nonneg _)).symm
    refine ⟨max j0 j1, fun j hj n hn => ?_⟩
    have hj0' : j0 ≤ phi j := le_trans (le_trans (le_max_left _ _) hj) (hphige j)
    have hu : ∑ a : Fin d, ∑ b : Fin d,
        SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R (phi j) n ω a b - ERmean (phi j) a b) 2 P ≤
          ENNReal.ofReal (eps / 4) := hj0 (phi j) hj0' n hn
    have hv : ∑ a : Fin d, ∑ b : Fin d,
        SubdiffusiveProcess.RawLp.eLpNorm (fun _ : Om => ERmean (phi j) a b - Rl a b) 2 P ≤
          ENNReal.ofReal (eps / 4) := by
      calc
        ∑ a : Fin d, ∑ b : Fin d,
              SubdiffusiveProcess.RawLp.eLpNorm (fun _ : Om => ERmean (phi j) a b - Rl a b) 2 P ≤
            ∑ a : Fin d, ∑ b : Fin d,
              ENNReal.ofReal |ERmean (phi j) a b - Rl a b| :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hconst_le _))
        _ = ENNReal.ofReal (∑ a : Fin d, ∑ b : Fin d,
              |ERmean (phi j) a b - Rl a b|) := hofreal j
        _ ≤ ENNReal.ofReal (eps / 4) :=
            ENNReal.ofReal_le_ofReal
              (le_of_lt (hj1 j (le_trans (le_max_right _ _) hj)))
    have hsub : ∀ a b, SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R (phi j) n ω a b - Rl a b) 2 P ≤
        2 * (SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R (phi j) n ω a b - ERmean (phi j) a b) 2 P +
          SubdiffusiveProcess.RawLp.eLpNorm (fun _ : Om => ERmean (phi j) a b - Rl a b) 2 P) := by
      intro a b
      have hfun : (fun ω : Om => R (phi j) n ω a b - Rl a b) =
          (fun ω => R (phi j) n ω a b - ERmean (phi j) a b) +
          (fun _ : Om => ERmean (phi j) a b - Rl a b) := by
        funext ω
        simp only [Pi.add_apply]
        ring
      rw [hfun]
      have hc' : SubdiffusiveProcess.RawLp.eLpNorm (fun _ : Om => ERmean (phi j) a b - Rl a b) 2 P =
          ENNReal.ofReal |ERmean (phi j) a b - Rl a b| := by
        rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded aestronglyMeasurable_const]
        rw [MeasureTheory.eLpNorm_const _ (by norm_num) hPne, measure_univ,
          Real.enorm_eq_ofReal_abs]
        simp
      simpa only [Pi.add_def, hc'] using
        (aux_lem_conc_add_const Om P
          (fun ω => R (phi j) n ω a b - ERmean (phi j) a b)
          (ERmean (phi j) a b - Rl a b))
    calc
      ∑ a : Fin d, ∑ b : Fin d,
            SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R (phi j) n ω a b - Rl a b) 2 P ≤
          ∑ a : Fin d, ∑ b : Fin d,
            2 * (SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R (phi j) n ω a b - ERmean (phi j) a b) 2 P +
             SubdiffusiveProcess.RawLp.eLpNorm (fun _ : Om => ERmean (phi j) a b - Rl a b) 2 P) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hsub a b))
      _ = 2 * ((∑ a : Fin d, ∑ b : Fin d,
              SubdiffusiveProcess.RawLp.eLpNorm (fun ω => R (phi j) n ω a b - ERmean (phi j) a b) 2 P) +
          (∑ a : Fin d, ∑ b : Fin d,
              SubdiffusiveProcess.RawLp.eLpNorm (fun _ : Om => ERmean (phi j) a b - Rl a b) 2 P)) := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ 2 * (ENNReal.ofReal (eps / 4) + ENNReal.ofReal (eps / 4)) :=
        mul_le_mul_right (add_le_add hu hv) _
      _ = ENNReal.ofReal eps := by
          rw [← ENNReal.ofReal_add (show (0 : ℝ) ≤ eps / 4 by linarith)
                (show (0 : ℝ) ≤ eps / 4 by linarith)]
          rw [show eps / 4 + eps / 4 = eps / 2 by ring]
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  exact ⟨phi, hphi, Pl, Rl, hPlSym, hRlSym, hPlI, hRlI, hEPuni, hRuni⟩

end Paper
