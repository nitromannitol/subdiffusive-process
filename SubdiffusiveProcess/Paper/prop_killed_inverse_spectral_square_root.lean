import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.StarOrder
import SubdiffusiveProcess.Paper.killed_inverse_mosco
import SubdiffusiveProcess.Paper.prop_killed_inverse_injectivity
import SubdiffusiveProcess.Lane2.LimitForm


open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section AuxSpectral
def aux_spectralUnit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x : H) : H := ‖x‖⁻¹ • x

theorem aux_spectralUnit_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x : H} (hx : x ≠ 0) : ‖aux_spectralUnit x‖ = 1 := by
  simp only [aux_spectralUnit, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem aux_spectralUnit_recover {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x : H} (hx : x ≠ 0) : ‖x‖ • aux_spectralUnit x = x := by
  rw [aux_spectralUnit, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem aux_spectralUnit_inner {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x : H} (hx : x ≠ 0) :
    inner ℝ x (aux_spectralUnit x) = ‖x‖ := by
  rw [aux_spectralUnit, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hn] <;> ring

theorem aux_spectral_norm_le_of_unit_tests
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : H) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ y : H, ‖y‖ = 1 → inner ℝ x y ≤ C) : ‖x‖ ≤ C := by
  by_cases hx : x = 0
  · simpa only [hx, norm_zero] using hC
  · have hh := h (aux_spectralUnit x) (aux_spectralUnit_norm hx)
    rwa [aux_spectralUnit_inner hx] at hh

theorem aux_spectral_opNorm_le_of_unit_tests
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x y : H, ‖x‖ = 1 → ‖y‖ = 1 → inner ℝ (T x) y ≤ C) :
    ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hunit : ‖T (aux_spectralUnit x)‖ ≤ C :=
      aux_spectral_norm_le_of_unit_tests _ C hC
        (fun y hy => h (aux_spectralUnit x) y (aux_spectralUnit_norm hx) hy)
    have hTx : T x = ‖x‖ • T (aux_spectralUnit x) := by
      rw [← map_smul, aux_spectralUnit_recover hx]
    calc
      ‖T x‖ = ‖x‖ * ‖T (aux_spectralUnit x)‖ := by
        rw [hTx, norm_smul, norm_norm]
      _ ≤ ‖x‖ * C := mul_le_mul_of_nonneg_left hunit (norm_nonneg _)
      _ = C * ‖x‖ := mul_comm _ _

theorem aux_spectral_quadratic_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (c : ℝ) (x : H) :
    inner ℝ (T (c • x)) (c • x) = c ^ 2 * inner ℝ (T x) x := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The real polarization argument needed for the extremal Rayleigh value. -/
theorem aux_spectral_opNorm_le_of_quadratic_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x : H, ‖x‖ = 1 → |inner ℝ (T x) x| ≤ C) : ‖T‖ ≤ C := by
  have hall (x : H) : |inner ℝ (T x) x| ≤ C * ‖x‖ ^ 2 := by
    by_cases hx : x = 0
    · simp [hx]
    · have hs := aux_spectral_quadratic_smul T ‖x‖ (aux_spectralUnit x)
      rw [aux_spectralUnit_recover hx] at hs
      rw [hs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc
        ‖x‖ ^ 2 * |inner ℝ (T (aux_spectralUnit x)) (aux_spectralUnit x)|
            ≤ ‖x‖ ^ 2 * C :=
          mul_le_mul_of_nonneg_left (h _ (aux_spectralUnit_norm hx)) (sq_nonneg _)
        _ = C * ‖x‖ ^ 2 := mul_comm _ _
  apply aux_spectral_opNorm_le_of_unit_tests T C hC
  intro x y hx hy
  have hs : inner ℝ (T y) x = inner ℝ (T x) y :=
    (hT.isSymmetric y x).trans (real_inner_comm (T x) y)
  have hpolar :
      inner ℝ (T (x + y)) (x + y) - inner ℝ (T (x - y)) (x - y) =
        4 * inner ℝ (T x) y := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right]
    rw [hs]
    ring
  have hp := (abs_le.mp (hall (x + y))).2
  have hm := (abs_le.mp (hall (x - y))).1
  have hpar := parallelogram_law_with_norm ℝ x y
  rw [hx, hy] at hpar
  have hparC := congrArg (fun t : ℝ => C * t) hpar
  nlinarith [hparC]

theorem aux_spectral_near_extremum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (ε : ℝ) (hε : 0 < ε) (hεT : ε < ‖T‖) :
    ∃ x : H, ‖x‖ = 1 ∧ ‖T‖ - ε < |inner ℝ (T x) x| := by
  classical
  by_contra h
  push_neg at h
  have hbound := aux_spectral_opNorm_le_of_quadratic_bound T hT
    (‖T‖ - ε) (by linarith) h
  linarith

theorem aux_spectral_residual_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (μ : ℝ) (x : H) :
    ‖T x - μ • x‖ ^ 2 =
      ‖T x‖ ^ 2 - 2 * μ * inner ℝ (T x) x + μ ^ 2 * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm (T x) x]
  ring

/-- Task 6. Compactness supplies the attainment of the extremal absolute
Rayleigh value; no compact spectral theorem is assumed. -/
theorem aux_exists_eigenvector_of_compact_selfAdjoint {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator T) (hne : T ≠ 0) :
    ∃ (μ : ℝ) (e : H),
      (μ = ‖T‖ ∨ μ = -‖T‖) ∧ ‖e‖ = 1 ∧ T e = μ • e := by
  classical
  have hTpos : 0 < ‖T‖ := norm_pos_iff.mpr hne
  let ε : ℕ → ℝ := fun n => ‖T‖ / ((n : ℝ) + 2)
  have heps (n : ℕ) : 0 < ε n ∧ ε n < ‖T‖ := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor
    · exact div_pos hTpos (by linarith)
    · apply (div_lt_iff₀ (by linarith : (0 : ℝ) < n + 2)).mpr
      have hmul : 0 ≤ ‖T‖ * (n : ℝ) := mul_nonneg hTpos.le hn
      nlinarith only [hTpos, hmul]
  choose x hx hnear using fun n => aux_spectral_near_extremum T hT (ε n)
    (heps n).1 (heps n).2
  let q : ℕ → ℝ := fun n => inner ℝ (T (x n)) (x n)
  have hup (n : ℕ) : |q n| ≤ ‖T‖ := by
    calc
      |q n| ≤ ‖T (x n)‖ * ‖x n‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖x n‖) * ‖x n‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
      _ = ‖T‖ := by rw [hx]; ring
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) hnat
  have hepslim : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    simpa only [ε, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_mul ‖T‖
  have hcomp : IsCompact (closure (T '' Metric.closedBall (0 : H) 1)) :=
    IsCompactOperator.isCompact_closure_image_closedBall (f := T.toLinearMap) hc 1
  have himg (n : ℕ) : T (x n) ∈ closure (T '' Metric.closedBall (0 : H) 1) := by
    apply subset_closure
    refine ⟨x n, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, hx] using
      (le_rfl : (1 : ℝ) ≤ 1)
  obtain ⟨z, hz, φ, hφ, hTx⟩ := hcomp.tendsto_subseq himg
  have hqmem (n : ℕ) : q (φ n) ∈ Set.Icc (-‖T‖) ‖T‖ := abs_le.mp (hup _)
  obtain ⟨μ, hμmem, ψ, hψ, hq⟩ := isCompact_Icc.tendsto_subseq hqmem
  let σ : ℕ → ℕ := φ ∘ ψ
  have hσ : StrictMono σ := hφ.comp hψ
  have hTxσ : Tendsto (fun n => T (x (σ n))) atTop (𝓝 z) := hTx.comp hψ.tendsto_atTop
  have hqσ : Tendsto (fun n => q (σ n)) atTop (𝓝 μ) := hq
  have hupper : |μ| ≤ ‖T‖ :=
    le_of_tendsto hqσ.abs (Filter.Eventually.of_forall (fun n => hup (σ n)))
  have hlowerlim : Tendsto (fun n => ‖T‖ - ε (σ n)) atTop (𝓝 ‖T‖) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub (hepslim.comp hσ.tendsto_atTop))
  have hlower : ‖T‖ ≤ |μ| := le_of_tendsto_of_tendsto hlowerlim hqσ.abs
    (Filter.Eventually.of_forall (fun n => (hnear (σ n)).le))
  have habs : |μ| = ‖T‖ := le_antisymm hupper hlower
  have hμsq : μ ^ 2 = ‖T‖ ^ 2 := by
    calc
      μ ^ 2 = |μ| ^ 2 := (sq_abs μ).symm
      _ = ‖T‖ ^ 2 := congrArg (fun t : ℝ => t ^ 2) habs
  have hμne : μ ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at habs
    linarith
  have hsign : μ = ‖T‖ ∨ μ = -‖T‖ := by
    by_cases hμ : 0 ≤ μ
    · left
      simpa only [abs_of_nonneg hμ] using habs
    · right
      rw [abs_of_neg (lt_of_not_ge hμ)] at habs
      linarith
  let r : ℕ → H := fun n => T (x (σ n)) - μ • x (σ n)
  have hres (n : ℕ) : ‖r n‖ ^ 2 ≤ 2 * ‖T‖ ^ 2 - 2 * μ * q (σ n) := by
    have hnorm : ‖T (x (σ n))‖ ≤ ‖T‖ := by
      simpa only [hx, mul_one] using T.le_opNorm (x (σ n))
    have hsq : ‖T (x (σ n))‖ ^ 2 ≤ ‖T‖ ^ 2 := by
      simpa only [pow_two] using
        mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg T)
    change ‖T (x (σ n)) - μ • x (σ n)‖ ^ 2 ≤ _
    rw [aux_spectral_residual_sq, hx]
    dsimp [q]
    nlinarith only [hsq, hμsq]
  have hboundlim : Tendsto
      (fun n => 2 * ‖T‖ ^ 2 - 2 * μ * q (σ n)) atTop (𝓝 (0 : ℝ)) := by
    have h : Tendsto
        (fun n => 2 * ‖T‖ ^ 2 - 2 * μ * q (σ n)) atTop
        (𝓝 (2 * ‖T‖ ^ 2 - 2 * μ * μ)) :=
      tendsto_const_nhds.sub (hqσ.const_mul (2 * μ))
    have hzero : 2 * ‖T‖ ^ 2 - 2 * μ * μ = 0 := by nlinarith [hμsq]
    simpa only [hzero] using h
  have hrsq : Tendsto (fun n => ‖r n‖ ^ 2) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => sq_nonneg _) hres hboundlim
  have hrnorm : Tendsto (fun n => ‖r n‖) atTop (𝓝 (0 : ℝ)) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hrsq
    rw [Real.sqrt_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp, Real.sqrt_sq_eq_abs, abs_norm]
  have hr : Tendsto r atTop (𝓝 (0 : H)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using hrnorm
  have hscaled : Tendsto (fun n => μ • x (σ n)) atTop (𝓝 z) := by
    have h := hTxσ.sub hr
    have hid (n : ℕ) : T (x (σ n)) - r n = μ • x (σ n) := by
      dsimp [r]
      abel
    simpa only [hid, sub_zero] using h
  let e : H := μ⁻¹ • z
  have hxlim : Tendsto (fun n => x (σ n)) atTop (𝓝 e) := by
    simpa only [smul_smul, inv_mul_cancel₀ hμne, one_smul] using
      hscaled.const_smul μ⁻¹
  have hnorme : ‖e‖ = 1 := by
    apply tendsto_nhds_unique hxlim.norm
    simp only [hx]
    exact tendsto_const_nhds
  have hTe : T e = z :=
    tendsto_nhds_unique ((T.continuous.tendsto e).comp hxlim) hTxσ
  have hμe : μ • e = z := by
    dsimp [e]
    rw [smul_smul, mul_inv_cancel₀ hμne, one_smul]
  exact ⟨μ, e, hsign, hnorme, hTe.trans hμe.symm⟩

/-- A finite-dimensional invariant subspace already selected by the recursion. -/
structure aux_SpectralStage {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (G : H →L[ℝ] H) where
  space : Submodule ℝ H
  finite : FiniteDimensional ℝ space
  invariant : ∀ x ∈ space, G x ∈ space

/-- The maximal eigenvector chosen on the orthogonal complement of a stage. -/
structure aux_SpectralPick {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (G : H →L[ℝ] H) (P : Submodule ℝ H) where
  value : ℝ
  vector : H
  value_pos : 0 < value
  vector_norm : ‖vector‖ = 1
  vector_orth : vector ∈ P.orthogonal
  eigen : G vector = value • vector
  bound : ∀ x ∈ P.orthogonal, ‖G x‖ ≤ value * ‖x‖

theorem aux_spectral_pick_exists
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (G : H →L[ℝ] H) (hG : IsSelfAdjoint G) (hc : IsCompactOperator G)
    (hpos : ∀ x, 0 ≤ inner ℝ (G x) x) (hinj : Function.Injective G)
    (hinf : ¬ FiniteDimensional ℝ H) (P : aux_SpectralStage G) :
    Nonempty (aux_SpectralPick G P.space) := by
  classical
  letI : FiniteDimensional ℝ P.space := P.finite
  let Q : Submodule ℝ H := P.space.orthogonal
  have hQne : Q ≠ ⊥ := by
    intro hQ
    have htop : P.space = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hQ
    have hsurj : Function.Surjective P.space.subtype := by
      intro x
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [htop]
      trivial
    exact hinf (FiniteDimensional.of_surjective P.space.subtype hsurj)
  have hQi : ∀ x ∈ Q, G x ∈ Q := by
    intro x hx y hy
    calc
      inner ℝ y (G x) = inner ℝ (G y) x := (hG.isSymmetric y x).symm
      _ = 0 := hx (G y) (P.invariant y hy)
  let T : Q →L[ℝ] Q :=
    (G.toLinearMap.restrict hQi).mkContinuous ‖G‖ (by
      intro x
      exact G.le_opNorm x.1)
  have hTc : IsCompactOperator T :=
    IsCompactOperator.restrict' (f := G.toLinearMap) hc hQi
  have hTsym : T.toLinearMap.IsSymmetric := by
    intro x y
    exact hG.isSymmetric x.1 y.1
  have hTsa : IsSelfAdjoint T := hTsym.isSelfAdjoint
  have hTne : T ≠ 0 := by
    intro hT
    have hQzero : Q ≤ ⊥ := by
      intro x hx
      rw [Submodule.mem_bot]
      apply hinj
      have h := congrArg (fun S : Q →L[ℝ] Q => (S ⟨x, hx⟩).1) hT
      simpa only [map_zero] using h
    exact hQne (le_antisymm hQzero bot_le)
  obtain ⟨ν, e, hν, he, hTe⟩ :=
    aux_exists_eigenvector_of_compact_selfAdjoint T hTsa hTc hTne
  have hTnorm : 0 < ‖T‖ := by
    rcases (norm_nonneg T).lt_or_eq with h | h
    · exact h
    · exact absurd (ContinuousLinearMap.opNorm_zero_iff T |>.mp h.symm) hTne
  have hνnonneg : 0 ≤ ν := by
    have h := hpos e.1
    have hval : G e.1 = ν • e.1 := congrArg Subtype.val hTe
    rw [hval, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    have heval : ‖e.1‖ = 1 := he
    simpa only [heval, one_pow, mul_one] using h
  have hνeq : ν = ‖T‖ := by
    rcases hν with hν | hν
    · exact hν
    · exfalso
      linarith
  refine ⟨{
    value := ν
    vector := e.1
    value_pos := by rw [hνeq]; exact hTnorm
    vector_norm := he
    vector_orth := e.2
    eigen := congrArg Subtype.val hTe
    bound := ?_ }⟩
  intro x hx
  have h := T.le_opNorm (⟨x, hx⟩ : Q)
  change ‖G x‖ ≤ ‖T‖ * ‖x‖ at h
  rwa [← hνeq] at h

def aux_spectralInitial {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (G : H →L[ℝ] H) : aux_SpectralStage G where
  space := ⊥
  finite := inferInstance
  invariant := by
    intro x hx
    rw [Submodule.mem_bot] at hx ⊢
    simpa only [hx, map_zero]

def aux_spectralEnlarge {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (G : H →L[ℝ] H)
    (P : aux_SpectralStage G) (s : aux_SpectralPick G P.space) : aux_SpectralStage G where
  space := P.space ⊔ Submodule.span ℝ {s.vector}
  finite := by
    letI : FiniteDimensional ℝ P.space := P.finite
    infer_instance
  invariant := by
    let R : Submodule ℝ H := P.space ⊔ Submodule.span ℝ {s.vector}
    have hle : R ≤ R.comap G.toLinearMap := by
      apply sup_le
      · intro x hx
        exact (le_sup_left : P.space ≤ R) (P.invariant x hx)
      · apply Submodule.span_le.mpr
        intro x hx
        have hx' : x = s.vector := Set.mem_singleton_iff.mp hx
        change G x ∈ R
        rw [hx', s.eigen]
        apply R.smul_mem
        exact (le_sup_right : Submodule.span ℝ {s.vector} ≤ R)
          (Submodule.subset_span (Set.mem_singleton s.vector))
    exact fun x hx => hle hx

theorem aux_spectral_scaled_distance_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {e : ℕ → H} (he : Orthonormal ℝ e) {i j : ℕ} (hij : i ≠ j)
    (a b : ℝ) : ‖a • e i - b • e j‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    he.2 hij, he.2 hij.symm, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he.1]
  ring

/-- Compactness forces the eigenvalues of any orthonormal eigen-sequence to
vanish. This does not presume that the eigenvectors span the space. -/
theorem aux_spectral_values_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (G : H →L[ℝ] H) (hc : IsCompactOperator G)
    (μ : ℕ → ℝ) (e : ℕ → H) (he : Orthonormal ℝ e)
    (hμ : ∀ n, 0 < μ n) (hGe : ∀ n, G (e n) = μ n • e n) :
    Tendsto μ atTop (𝓝 0) := by
  classical
  have hcompact : IsCompact (closure (G '' Metric.closedBall (0 : H) 1)) :=
    IsCompactOperator.isCompact_closure_image_closedBall (f := G.toLinearMap) hc 1
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hev : ∀ᶠ n in atTop, μ n < ε := by
    by_contra hn
    have hfreq : ∃ᶠ n in atTop, ε ≤ μ n := by
      simpa only [not_lt] using (not_eventually.mp hn)
    obtain ⟨φ, hφ, hφε⟩ := extraction_of_frequently_atTop hfreq
    have himg (n : ℕ) : G (e (φ n)) ∈ closure (G '' Metric.closedBall (0 : H) 1) := by
      apply subset_closure
      refine ⟨e (φ n), ?_, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, he.1] using
        (le_rfl : (1 : ℝ) ≤ 1)
    obtain ⟨z, hz, ψ, hψ, hlim⟩ := hcompact.tendsto_subseq himg
    have hC := hlim.cauchySeq
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC ε hε
    have hd := hN N le_rfl (N + 1) (Nat.le_succ N)
    have hne : φ (ψ N) ≠ φ (ψ (N + 1)) :=
      ne_of_lt ((hφ.comp hψ) (Nat.lt_succ_self N))
    have hsq := aux_spectral_scaled_distance_sq he hne (μ (φ (ψ N))) (μ (φ (ψ (N + 1))))
    change dist (G (e (φ (ψ N)))) (G (e (φ (ψ (N + 1))))) < ε at hd
    rw [dist_eq_norm, hGe, hGe] at hd
    have hsmall : ‖μ (φ (ψ N)) • e (φ (ψ N)) -
        μ (φ (ψ (N + 1))) • e (φ (ψ (N + 1)))‖ ^ 2 < ε ^ 2 := by
      have hp : 0 < (ε - ‖μ (φ (ψ N)) • e (φ (ψ N)) -
          μ (φ (ψ (N + 1))) • e (φ (ψ (N + 1)))‖) *
          (ε + ‖μ (φ (ψ N)) • e (φ (ψ N)) -
          μ (φ (ψ (N + 1))) • e (φ (ψ (N + 1)))‖) :=
        mul_pos (sub_pos.mpr hd) (add_pos_of_pos_of_nonneg hε (norm_nonneg _))
      nlinarith
    have hfirst := hφε (ψ N)
    have hsecond := hφε (ψ (N + 1))
    have hfirstSq : ε ^ 2 ≤ μ (φ (ψ N)) ^ 2 := by
      simpa only [pow_two] using
        mul_le_mul hfirst hfirst hε.le (hμ _).le
    have hsecondSq : ε ^ 2 ≤ μ (φ (ψ (N + 1))) ^ 2 := by
      simpa only [pow_two] using
        mul_le_mul hsecond hsecond hε.le (hμ _).le
    rw [hsq] at hsmall
    nlinarith only [hsmall, hfirstSq, hsecondSq, sq_pos_of_pos hε]
  filter_upwards [hev] with n hn
  simpa only [Real.dist_eq, sub_zero, abs_of_pos (hμ n)] using hn

/-- Task 7, including the closed-span conclusion. The recursion takes a norm-
maximizing eigenvector on each finite-stage orthogonal complement. -/
theorem aux_exists_orthonormal_eigenbasis_of_compact_pos {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (G : H →L[ℝ] H) (hG : IsSelfAdjoint G) (hc : IsCompactOperator G)
    (hpos : ∀ x, 0 ≤ inner ℝ (G x) x) (hinj : Function.Injective G)
    (hinf : ¬ FiniteDimensional ℝ H) :
    ∃ (μ : ℕ → ℝ) (e : ℕ → H), (∀ n, 0 < μ n) ∧
      (∀ n, G (e n) = μ n • e n) ∧ Orthonormal ℝ e ∧
      Tendsto μ atTop (𝓝 0) ∧
      (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤ := by
  classical
  let pick (P : aux_SpectralStage G) : aux_SpectralPick G P.space :=
    Classical.choice (aux_spectral_pick_exists G hG hc hpos hinj hinf P)
  let stage : ℕ → aux_SpectralStage G :=
    Nat.rec (aux_spectralInitial G) (fun _ P => aux_spectralEnlarge G P (pick P))
  let μ : ℕ → ℝ := fun n => (pick (stage n)).value
  let e : ℕ → H := fun n => (pick (stage n)).vector
  have hstep (n : ℕ) : (stage (n + 1)).space =
      (stage n).space ⊔ Submodule.span ℝ {e n} := rfl
  have hle (n : ℕ) : (stage n).space ≤ (stage (n + 1)).space := by
    rw [hstep]
    exact le_sup_left
  have hmono : Monotone (fun n => (stage n).space) :=
    monotone_nat_of_le_succ hle
  have hemem (n : ℕ) : e n ∈ (stage (n + 1)).space := by
    rw [hstep]
    exact (le_sup_right : Submodule.span ℝ {e n} ≤ (stage n).space ⊔ Submodule.span ℝ {e n})
      (Submodule.subset_span (Set.mem_singleton (e n)))
  have heorth (n : ℕ) : e n ∈ (stage n).space.orthogonal :=
    (pick (stage n)).vector_orth
  have hnorm (n : ℕ) : ‖e n‖ = 1 := (pick (stage n)).vector_norm
  have hμ (n : ℕ) : 0 < μ n := (pick (stage n)).value_pos
  have hGe (n : ℕ) : G (e n) = μ n • e n := (pick (stage n)).eigen
  have hpair : Pairwise (fun i j => inner ℝ (e i) (e j) = 0) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact heorth j (e i) (hmono (Nat.succ_le_of_lt hlt) (hemem i))
    · rw [real_inner_comm]
      exact heorth i (e j) (hmono (Nat.succ_le_of_lt hgt) (hemem j))
  have he : Orthonormal ℝ e := ⟨hnorm, hpair⟩
  have hμlim : Tendsto μ atTop (𝓝 0) :=
    aux_spectral_values_tendsto_zero G hc μ e he hμ hGe
  refine ⟨μ, e, hμ, hGe, he, hμlim, ?_⟩
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range e)
  have hstage (n : ℕ) : (stage n).space ≤ S := by
    induction n with
    | zero => exact bot_le
    | succ n ih =>
      rw [hstep]
      apply sup_le ih
      apply Submodule.span_le.mpr
      intro x hx
      have hx' : x = e n := Set.mem_singleton_iff.mp hx
      rw [hx']
      exact Submodule.subset_span ⟨n, rfl⟩
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm
  · intro x hx
    have hxstage (n : ℕ) : x ∈ (stage n).space.orthogonal := by
      intro y hy
      exact hx y (hstage n hy)
    have hbound (n : ℕ) : ‖G x‖ ≤ μ n * ‖x‖ :=
      (pick (stage n)).bound x (hxstage n)
    have hlim : Tendsto (fun n => μ n * ‖x‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using hμlim.mul_const ‖x‖
    have hzero : ‖G x‖ ≤ 0 := le_of_tendsto_of_tendsto
      tendsto_const_nhds hlim (Filter.Eventually.of_forall hbound)
    have hGx : G x = 0 := norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))
    rw [Submodule.mem_bot]
    apply hinj
    simpa only [map_zero] using hGx
  · exact bot_le

end AuxSpectral

section AuxSquareRoot
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def aux_limitFormEnergy (G : H →L[ℝ] H) (u : H) : EReal :=
  ⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)

def aux_limitFormDomain (G : H →L[ℝ] H) : Set H :=
  {u : H | aux_limitFormEnergy G u < (⊤ : EReal)}

lemma aux_square_apply (G R : H →L[ℝ] H) (hsq : R.comp R = G) (x : H) :
    R (R x) = G x := by
  exact DFunLike.congr_fun hsq x

lemma aux_square_inner (G R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hsq : R.comp R = G) (f : H) :
    inner ℝ f (G f) = ‖R f‖ ^ 2 := by
  calc
    inner ℝ f (G f) = inner ℝ f (R (R f)) := by
      rw [aux_square_apply G R hsq]
    _ = inner ℝ (R f) (R f) := (hsym f (R f)).symm
    _ = ‖R f‖ ^ 2 := real_inner_self_eq_norm_sq _

lemma aux_energy_nonneg (G : H →L[ℝ] H) (u : H) :
    (0 : EReal) ≤ aux_limitFormEnergy G u := by
  have h := le_iSup
    (fun f : H => ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) (0 : H)
  simpa only [inner_zero_left, mul_zero, sub_self, EReal.coe_zero,
    aux_limitFormEnergy] using h

lemma aux_energy_real_bound (G : H →L[ℝ] H) (u : H)
    (hu : aux_limitFormEnergy G u < (⊤ : EReal)) (f : H) :
    2 * inner ℝ f u - inner ℝ f (G f) ≤ (aux_limitFormEnergy G u).toReal := by
  apply EReal.coe_le_coe_iff.mp
  exact (le_iSup
    (fun g : H => ((2 * inner ℝ g u - inner ℝ g (G g) : ℝ) : EReal)) f).trans
      (EReal.le_coe_toReal hu.ne)

lemma aux_energy_on_range_le (G R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hsq : R.comp R = G) (a : H) :
    aux_limitFormEnergy G (R a) ≤ ((‖a‖ ^ 2 : ℝ) : EReal) := by
  apply iSup_le
  intro f
  apply EReal.coe_le_coe_iff.mpr
  rw [aux_square_inner G R hsym hsq f, ← hsym f a]
  have h := norm_sub_sq_real a (R f)
  rw [real_inner_comm] at h
  nlinarith only [h, sq_nonneg ‖a - R f‖]

lemma aux_bounded_functional_on_range (G R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hsq : R.comp R = G) (hinj : Function.Injective R)
    (u : H) (hu : aux_limitFormEnergy G u < (⊤ : EReal)) :
    ∀ f : H, |inner ℝ f u| ≤ ((aux_limitFormEnergy G u).toReal + 1) * ‖R f‖ := by
  let C : ℝ := (aux_limitFormEnergy G u).toReal
  have hbound (f : H) : 2 * inner ℝ f u - ‖R f‖ ^ 2 ≤ C := by
    simpa only [C, aux_square_inner G R hsym hsq f] using
      aux_energy_real_bound G u hu f
  have hC : 0 ≤ C := by
    have h := hbound 0
    simpa only [map_zero, inner_zero_left, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, sub_self] using h
  intro f
  change |inner ℝ f u| ≤ (C + 1) * ‖R f‖
  by_cases hf : R f = 0
  · have hf0 : f = 0 := hinj (hf.trans (map_zero R).symm)
    subst f
    simp only [inner_zero_left, abs_zero, map_zero, norm_zero, mul_zero, le_refl]
  · have hb : 0 < ‖R f‖ := norm_pos_iff.mpr hf
    let w : H := ‖R f‖⁻¹ • f
    have hw : ‖R w‖ = 1 := by
      change ‖R (‖R f‖⁻¹ • f)‖ = 1
      rw [map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hb), inv_mul_cancel₀ hb.ne']
    have hplus := hbound w
    have hminus := hbound (-w)
    simp only [hw, one_pow] at hplus
    simp only [map_neg, inner_neg_left, norm_neg, hw, one_pow] at hminus
    have habs : |inner ℝ w u| ≤ C + 1 := by
      apply abs_le.mpr
      constructor <;> linarith only [hplus, hminus, hC]
    have hid : inner ℝ f u = ‖R f‖ * inner ℝ w u := by
      dsimp only [w]
      rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]
    calc
      |inner ℝ f u| = ‖R f‖ * |inner ℝ w u| := by
        rw [hid, abs_mul, abs_of_pos hb]
      _ ≤ ‖R f‖ * (C + 1) := mul_le_mul_of_nonneg_left habs hb.le
      _ = (C + 1) * ‖R f‖ := mul_comm _ _

lemma aux_domain_eq_range (G R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hsq : R.comp R = G) (hinj : Function.Injective R) :
    aux_limitFormDomain G = Set.range R := by
  classical
  apply Set.ext
  intro u
  constructor
  · intro hu
    change aux_limitFormEnergy G u < (⊤ : EReal) at hu
    let K : Submodule ℝ H := LinearMap.range R.toLinearMap
    let e : H ≃ₗ[ℝ] K := LinearEquiv.ofInjective R.toLinearMap hinj
    have he (f : H) : (e f : H) = R f := by
      exact LinearEquiv.ofInjective_apply R.toLinearMap f
    have he' (z : K) : R (e.symm z) = (z : H) := by
      exact LinearEquiv.ofInjective_symm_apply R.toLinearMap z
    let l : K →ₗ[ℝ] ℝ := (innerSL ℝ u).toLinearMap.comp e.symm.toLinearMap
    have hl (z : K) : ‖l z‖ ≤ ((aux_limitFormEnergy G u).toReal + 1) * ‖z‖ := by
      change |inner ℝ u (e.symm z)| ≤ ((aux_limitFormEnergy G u).toReal + 1) * ‖z‖
      rw [real_inner_comm]
      have h := aux_bounded_functional_on_range G R hsym hsq hinj u hu (e.symm z)
      rw [he' z] at h
      exact h
    let L : K →L[ℝ] ℝ := l.mkContinuous ((aux_limitFormEnergy G u).toReal + 1) hl
    obtain ⟨Lext, hExt, _⟩ := exists_extension_norm_eq K L
    let a : H := (InnerProductSpace.toDual ℝ H).symm Lext
    have hinner (f : H) : inner ℝ f (R a) = inner ℝ f u := by
      calc
        inner ℝ f (R a) = inner ℝ (R f) a := (hsym f a).symm
        _ = inner ℝ a (R f) := real_inner_comm _ _
        _ = Lext (R f) := InnerProductSpace.toDual_symm_apply
        _ = Lext (e f : H) := by rw [he f]
        _ = L (e f) := hExt (e f)
        _ = inner ℝ u f := by
          change inner ℝ u (e.symm (e f)) = inner ℝ u f
          rw [e.symm_apply_apply]
        _ = inner ℝ f u := real_inner_comm _ _
    refine ⟨a, ?_⟩
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [inner_sub_right, hinner (R a - u), sub_self]
  · rintro ⟨a, rfl⟩
    change aux_limitFormEnergy G (R a) < (⊤ : EReal)
    exact (aux_energy_on_range_le G R hsym hsq a).trans_lt (EReal.coe_lt_top _)

lemma aux_symmetric_injective_denseRange (R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hinj : Function.Injective R) : DenseRange R := by
  let K : Submodule ℝ H := LinearMap.range R.toLinearMap
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hRx : R x = 0 := by
        apply (inner_self_eq_zero (𝕜 := ℝ)).mp
        have h := hx (R (R x)) ⟨R x, rfl⟩
        rw [hsym (R x) x] at h
        exact h
      rw [Submodule.mem_bot]
      exact hinj (hRx.trans (map_zero R).symm)
    · exact bot_le
  have hclosure : K.topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr horth
  have hset : closure (Set.range R) = Set.univ := by
    change (K.topologicalClosure : Set H) = Set.univ
    rw [hclosure, Submodule.top_coe]
  intro x
  rw [hset]
  exact Set.mem_univ x

section Diagonal

variable {ι : Type*} {F : ι → Type*}
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]

lemma aux_lp_norm_mono (x y : lp F 2) (h : ∀ i, ‖x i‖ ≤ ‖y i‖) :
    ‖x‖ ≤ ‖y‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg y)
  intro s
  calc
    (∑ i ∈ s, ‖x i‖ ^ (2 : ENNReal).toReal) ≤
        ∑ i ∈ s, ‖y i‖ ^ (2 : ENNReal).toReal := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.rpow_le_rpow (norm_nonneg _) (h i) (by norm_num)
    _ ≤ ‖y‖ ^ (2 : ENNReal).toReal :=
      lp.sum_rpow_le_norm_rpow (by norm_num) y s

lemma aux_diagonal_pointwise (a : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (x : lp F 2) (i : ι) :
    ‖a i • x i‖ ≤ ‖(C • x) i‖ := by
  change ‖a i • x i‖ ≤ ‖C • x i‖
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)

def aux_diagonal (a : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) : lp F 2 →L[ℝ] lp F 2 := by
  let L : lp F 2 →ₗ[ℝ] lp F 2 :=
    { toFun := fun x => ⟨fun i => a i • x i,
        memℓp_gen (Summable.of_nonneg_of_le (fun i => by positivity)
          (fun i => Real.rpow_le_rpow (norm_nonneg _)
            (aux_diagonal_pointwise a C hC ha x i) (by norm_num))
          ((lp.memℓp (C • x)).summable (by norm_num)))⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        change a i • (x i + y i) = a i • x i + a i • y i
        exact smul_add _ _ _
      map_smul' := by
        intro t x
        apply lp.ext
        funext i
        change a i • (t • x i) = t • (a i • x i)
        exact smul_comm _ _ _ }
  apply L.mkContinuous C
  intro x
  calc
    ‖L x‖ ≤ ‖C • x‖ := aux_lp_norm_mono (L x) (C • x)
      (aux_diagonal_pointwise a C hC ha x)
    _ = C * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

lemma aux_diagonal_apply (a : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (x : lp F 2) (i : ι) :
    aux_diagonal a C hC ha x i = a i • x i := rfl

lemma aux_diagonal_symmetric (a : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (x y : lp F 2) :
    inner ℝ (aux_diagonal a C hC ha x) y =
      inner ℝ x (aux_diagonal a C hC ha y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [aux_diagonal_apply, real_inner_smul_left, real_inner_smul_right]

lemma aux_diagonal_nonneg (a : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (hpos : ∀ i, 0 ≤ a i) (x : lp F 2) :
    0 ≤ inner ℝ x (aux_diagonal a C hC ha x) := by
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro i
  rw [aux_diagonal_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
  exact mul_nonneg (hpos i) (sq_nonneg _)

lemma aux_diagonal_injective (a : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (hne : ∀ i, a i ≠ 0) :
    Function.Injective (aux_diagonal (F := F) a C hC ha) := by
  intro x y hxy
  apply lp.ext
  funext i
  have hcoord := congrArg (fun z : lp F 2 => z i) hxy
  change a i • x i = a i • y i at hcoord
  have h := congrArg (fun z : F i => (a i)⁻¹ • z) hcoord
  simpa only [smul_smul, inv_mul_cancel₀ (hne i), one_smul] using h

lemma aux_diagonal_single [DecidableEq ι]
    (a : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, |a i| ≤ C)
    (i : ι) (x : F i) :
    aux_diagonal (F := F) a C hC ha (lp.single 2 i x) = lp.single 2 i (a i • x) := by
  apply lp.ext
  funext j
  by_cases hji : j = i
  · subst j
    simp only [aux_diagonal_apply, lp.single_apply_self]
  · simp only [aux_diagonal_apply, lp.single_apply_ne 2 i x hji,
      lp.single_apply_ne 2 i (a i • x) hji, smul_zero]

lemma aux_sqrt_of_hilbertSum [DecidableEq ι]
    (G : H →L[ℝ] H) (e : H ≃ₗᵢ[ℝ] lp F 2)
    (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i) (hbound : ∀ i, μ i ≤ ‖G‖)
    (heigen : ∀ (i : ι) (x : F i),
      G (e.symm (lp.single 2 i x)) = μ i • e.symm (lp.single 2 i x)) :
    ∃ R : H →L[ℝ] H,
      (∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y)) ∧
      (∀ x : H, 0 ≤ inner ℝ x (R x)) ∧
      R.comp R = G ∧ aux_limitFormDomain G = Set.range R := by
  let a : ι → ℝ := fun i => Real.sqrt (μ i)
  let C : ℝ := Real.sqrt ‖G‖
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have ha : ∀ i, |a i| ≤ C := by
    intro i
    rw [abs_of_nonneg (Real.sqrt_nonneg (μ i))]
    exact Real.sqrt_le_sqrt (hbound i)
  let D : lp F 2 →L[ℝ] lp F 2 := aux_diagonal a C hC ha
  let E : H →L[ℝ] lp F 2 := e.toContinuousLinearEquiv.toContinuousLinearMap
  let Einv : lp F 2 →L[ℝ] H := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let R : H →L[ℝ] H := Einv.comp (D.comp E)
  have hR (x : H) : e (R x) = D (e x) := by
    change e (e.symm (D (e x))) = D (e x)
    exact e.apply_symm_apply _
  have hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y) := by
    intro x y
    calc
      inner ℝ (R x) y = inner ℝ (e (R x)) (e y) := (e.inner_map_map _ _).symm
      _ = inner ℝ (D (e x)) (e y) := by rw [hR x]
      _ = inner ℝ (e x) (D (e y)) := aux_diagonal_symmetric a C hC ha _ _
      _ = inner ℝ (e x) (e (R y)) := by rw [hR y]
      _ = inner ℝ x (R y) := e.inner_map_map _ _
  have hpos : ∀ x : H, 0 ≤ inner ℝ x (R x) := by
    intro x
    rw [← e.inner_map_map x (R x), hR x]
    exact aux_diagonal_nonneg a C hC ha (fun i => Real.sqrt_nonneg (μ i)) (e x)
  have hinj : Function.Injective R := by
    intro x y hxy
    apply e.injective
    apply aux_diagonal_injective a C hC ha
      (fun i => (Real.sqrt_pos.mpr (hμ i)).ne')
    have h := congrArg e hxy
    simpa only [hR] using h
  have hsingle (i : ι) (x : F i) :
      R (e.symm (lp.single 2 i x)) = a i • e.symm (lp.single 2 i x) := by
    change e.symm (D (e (e.symm (lp.single 2 i x)))) = _
    rw [e.apply_symm_apply]
    change e.symm (aux_diagonal a C hC ha (lp.single 2 i x)) = _
    rw [aux_diagonal_single, lp.single_smul, map_smul]
  have hmaps : (R.comp R).comp Einv = G.comp Einv := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro i
    apply ContinuousLinearMap.ext
    intro x
    change R (R (e.symm (lp.single 2 i x))) = G (e.symm (lp.single 2 i x))
    rw [hsingle, map_smul, hsingle, smul_smul, heigen]
    have ha2 : a i * a i = μ i := Real.mul_self_sqrt (hμ i).le
    rw [ha2]
  have hsq : R.comp R = G := by
    apply ContinuousLinearMap.ext
    intro x
    have h := DFunLike.congr_fun hmaps (e x)
    change R (R (e.symm (e x))) = G (e.symm (e x)) at h
    simpa only [e.symm_apply_apply] using h
  exact ⟨R, hsym, hpos, hsq, aux_domain_eq_range G R hsym hsq hinj⟩

end Diagonal

/-- PART A. -/
theorem aux_exists_sqrt_of_hilbertBasis {ι : Type*} (G : H →L[ℝ] H)
    (b : HilbertBasis ι ℝ H) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hG : ∀ i, G (b i) = μ i • b i) :
    ∃ R : H →L[ℝ] H,
      (∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y)) ∧
      (∀ x : H, 0 ≤ inner ℝ x (R x)) ∧
      R.comp R = G ∧ aux_limitFormDomain G = Set.range R := by
  classical
  have hbound : ∀ i, μ i ≤ ‖G‖ := by
    intro i
    simpa only [hG i, norm_smul, Real.norm_eq_abs, abs_of_pos (hμ i),
      b.orthonormal.1 i, mul_one] using G.le_opNorm (b i)
  have hsingle (i : ι) (t : ℝ) :
      b.repr.symm (lp.single 2 i t) = t • b i := by
    calc
      b.repr.symm (lp.single 2 i t) =
          b.repr.symm (lp.single 2 i (t • (1 : ℝ))) := by
        rw [smul_eq_mul, mul_one]
      _ = b.repr.symm (t • lp.single 2 i (1 : ℝ)) := by rw [lp.single_smul]
      _ = t • b i := by rw [map_smul, b.repr_symm_single]
  apply aux_sqrt_of_hilbertSum G b.repr μ hμ hbound
  intro i t
  simp only [hsingle, map_smul, hG, smul_smul, mul_comm]

/-- PART B, from an orthonormal eigen-sequence with dense span (the output of the
verified Task 7 lemma `exists_orthonormal_eigenbasis_of_compact_pos`). -/
theorem aux_exists_sqrt_of_eigen_sequence (G : H →L[ℝ] H)
    (μ : ℕ → ℝ) (e : ℕ → H) (hμ : ∀ n, 0 < μ n)
    (hG : ∀ n, G (e n) = μ n • e n) (hon : Orthonormal ℝ e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) :
    ∃ R : H →L[ℝ] H,
      (∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y)) ∧
      (∀ x : H, 0 ≤ inner ℝ x (R x)) ∧
      R.comp R = G ∧ aux_limitFormDomain G = Set.range R := by
  let b : HilbertBasis ℕ ℝ H := HilbertBasis.mk hon (le_of_eq hspan.symm)
  have hb : ∀ n, b n = e n := fun n => by
    change (HilbertBasis.mk hon (le_of_eq hspan.symm)) n = e n
    rw [HilbertBasis.coe_mk]
  apply aux_exists_sqrt_of_hilbertBasis G b μ hμ
  intro n
  rw [hb, hG]

theorem aux_sqrt_injective (G R : H →L[ℝ] H) (hsq : R.comp R = G)
    (hinj : Function.Injective G) : Function.Injective R := by
  intro x y hxy
  apply hinj
  calc
    G x = R (R x) := (aux_square_apply G R hsq x).symm
    _ = R (R y) := congrArg R hxy
    _ = G y := aux_square_apply G R hsq y

theorem aux_sqrt_denseRange (R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hinj : Function.Injective R) : DenseRange R :=
  aux_symmetric_injective_denseRange R hsym hinj

theorem aux_sqrt_comm (G R : H →L[ℝ] H) (hsq : R.comp R = G) :
    R.comp G = G.comp R := by
  apply ContinuousLinearMap.ext
  intro x
  change R (G x) = G (R x)
  calc
    R (G x) = R (R (R x)) := congrArg R (aux_square_apply G R hsq x).symm
    _ = G (R x) := aux_square_apply G R hsq (R x)

theorem aux_sqrt_norm_sq_le (G R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hsq : R.comp R = G) (x : H) :
    ‖R x‖ ^ 2 ≤ ‖G‖ * ‖x‖ ^ 2 := by
  calc
    ‖R x‖ ^ 2 = inner ℝ x (G x) := (aux_square_inner G R hsym hsq x).symm
    _ ≤ ‖x‖ * ‖G x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖G‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (G.le_opNorm x) (norm_nonneg _)
    _ = ‖G‖ * ‖x‖ ^ 2 := by ring

theorem aux_limitFormEnergy_eq_of_mem_range (G R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hsq : R.comp R = G) (hinj : Function.Injective G) (a : H) :
    aux_limitFormEnergy G (R a) = ((‖a‖ ^ 2 : ℝ) : EReal) := by
  have hupper := aux_energy_on_range_le G R hsym hsq a
  have htop : aux_limitFormEnergy G (R a) < (⊤ : EReal) :=
    hupper.trans_lt (EReal.coe_lt_top _)
  have hbot : aux_limitFormEnergy G (R a) ≠ (⊥ : EReal) :=
    ne_of_gt ((EReal.bot_lt_coe 0).trans_le (aux_energy_nonneg G (R a)))
  let C : ℝ := (aux_limitFormEnergy G (R a)).toReal
  let S : Set H := {y : H | 2 * inner ℝ y a - ‖y‖ ^ 2 ≤ C}
  have hcont : Continuous (fun y : H => 2 * inner ℝ y a - ‖y‖ ^ 2) :=
    (continuous_const.mul (continuous_id.inner continuous_const)).sub (continuous_norm.pow 2)
  have hclosed : IsClosed S := isClosed_le hcont continuous_const
  have hsub : Set.range R ⊆ S := by
    rintro y ⟨f, rfl⟩
    change 2 * inner ℝ (R f) a - ‖R f‖ ^ 2 ≤ C
    have h := aux_energy_real_bound G (R a) htop f
    rw [aux_square_inner G R hsym hsq f, ← hsym f a] at h
    exact h
  have hdense : DenseRange R := aux_sqrt_denseRange R hsym (aux_sqrt_injective G R hsq hinj)
  have haS : a ∈ S := (closure_minimal hsub hclosed) (hdense a)
  have hreal : ‖a‖ ^ 2 ≤ C := by
    change 2 * inner ℝ a a - ‖a‖ ^ 2 ≤ C at haS
    rw [real_inner_self_eq_norm_sq] at haS
    linarith only [haS]
  apply le_antisymm hupper
  calc
    ((‖a‖ ^ 2 : ℝ) : EReal) ≤ (C : EReal) := EReal.coe_le_coe_iff.mpr hreal
    _ ≤ aux_limitFormEnergy G (R a) := EReal.coe_toReal_le hbot


lemma aux_eigenvalue_pos {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H) (hpos : ∀ x : H, 0 ≤ inner ℝ x (G x)) (hinj : Function.Injective G)
    (μ : ℝ) (x : H) (hx0 : x ≠ 0) (hxe : G x = μ • x) : 0 < μ := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hnn : 0 ≤ μ * ‖x‖ ^ 2 := by
    simpa only [hxe, real_inner_smul_right, real_inner_self_eq_norm_sq] using hpos x
  have hi0 : 0 ≤ μ := by
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h (sq_pos_of_pos hnx)
    linarith
  have hne : μ ≠ 0 := by
    intro hi
    have hz : G x = 0 := by rw [hxe, hi, zero_smul]
    exact hx0 (hinj (hz.trans (map_zero G).symm))
  exact lt_of_le_of_ne hi0 (Ne.symm hne)

end AuxSquareRoot



theorem prop_killed_inverse_spectral_square_root
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hcompact : IsCompactOperator G)
    (hsym : ∀ x y : DomainL2 Q,
      inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (hinj : Function.Injective G) :
    ∃ Rroot : DomainL2 Q →L[ℝ] DomainL2 Q,
      (∀ x y : DomainL2 Q,
        inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (Rroot x)) ∧
      Rroot.comp Rroot = G ∧ limitFormDomain G = Set.range Rroot := by
  classical
  have hsymL : G.toLinearMap.IsSymmetric := fun x y => hsym x y
  have hself : IsSelfAdjoint G := hsymL.isSelfAdjoint
  have hpos' : ∀ x : DomainL2 Q, 0 ≤ inner ℝ (G x) x := fun x => by
    rw [real_inner_comm]; exact hpos x
  have hdom : limitFormDomain G = aux_limitFormDomain G := rfl
  rw [hdom]
  by_cases hfin : FiniteDimensional ℝ (DomainL2 Q)
  · let b := hsymL.eigenvectorBasis (rfl : Module.finrank ℝ (DomainL2 Q) = Module.finrank ℝ (DomainL2 Q))
    let μ : Fin (Module.finrank ℝ (DomainL2 Q)) → ℝ := hsymL.eigenvalues rfl
    have hGb : ∀ i, G (b i) = μ i • b i := fun i => by
      have h := hsymL.apply_eigenvectorBasis rfl i
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using h
    have hμ : ∀ i, 0 < μ i := fun i =>
      aux_eigenvalue_pos G hpos hinj (μ i) (b i) (b.orthonormal.ne_zero i) (hGb i)
    exact aux_exists_sqrt_of_hilbertBasis G b.toHilbertBasis μ hμ (fun i => by
      rw [OrthonormalBasis.coe_toHilbertBasis]; exact hGb i)
  · obtain ⟨μ, e, hμ, hGe, hon, _, hspan⟩ :=
      aux_exists_orthonormal_eigenbasis_of_compact_pos G hself hcompact hpos' hinj hfin
    exact aux_exists_sqrt_of_eigen_sequence G μ e hμ hGe hon hspan

end Paper
