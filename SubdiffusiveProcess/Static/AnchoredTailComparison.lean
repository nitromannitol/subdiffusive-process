module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpSuffixRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SuffixMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.Convergence
public import SubdiffusiveProcess.Static.AnchoredLawTransport
public import SubdiffusiveProcess.Static.LocalNormalization

@[expose] public section

/-! # Tail comparison on an arbitrary fixed spatial window -/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored Filter Topology
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

private theorem abs_exp_sub_one_le_exp_abs_sub_one (t : ℝ) :
    |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg
      (sub_nonneg.mpr (Real.one_le_exp ht))]
  · have ht0 : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht0, abs_of_nonpos
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr ht0))]
    have hpos := Real.add_one_le_exp t
    have hneg := Real.add_one_le_exp (-t)
    nlinarith

private theorem continuous_cutoffShellSum_in_space
    {d : ℕ} (L m : ℕ) (omega : PotentialSample d) :
    Continuous (fun x : Vec d => cutoffShellSum L (m : ℤ) x omega) := by
  unfold cutoffShellSum
  fun_prop

theorem tail_pair_ratio_le_oscillation_on_cube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (k : ℤ) (omega : PotentialSample d) {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d k))
    (hy : y ∈ openCubeSet (originCube d k)) :
    ENNReal.ofReal
        |(SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega x) /
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y /
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega y) - 1| ≤
      cutoffRatioOscillationSup m k omega := by
  by_cases hLm : L = m
  · subst L
    have hx0 := (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m omega x).ne'
    have hy0 := (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m omega y).ne'
    simp [hx0, hy0]
  have hmL' : m < L := lt_of_le_of_ne hmL (Ne.symm hLm)
  let S : Vec d → ℝ := fun u => cutoffShellSum L (m : ℤ) u omega
  let b : ℝ := (((L : ℤ) - (m : ℤ) : ℤ) : ℝ) *
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hxratio := cutoffRatioMinusOne_eq_exp_shell
    M L (m : ℤ) omega x (by omega) (by omega)
  have hyratio := cutoffRatioMinusOne_eq_exp_shell
    M L (m : ℤ) omega y (by omega) (by omega)
  have hxexp : SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega x = Real.exp (S x - b) := by
    rw [cutoffRatioMinusOne] at hxratio
    simp only [aCutoffAtInt, show ¬(m : ℤ) < 0 by omega, if_false,
      Int.toNat_natCast] at hxratio
    change _ - 1 = Real.exp (S x - b) - 1 at hxratio
    linarith
  have hyexp : SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega y = Real.exp (S y - b) := by
    rw [cutoffRatioMinusOne] at hyratio
    simp only [aCutoffAtInt, show ¬(m : ℤ) < 0 by omega, if_false,
      Int.toNat_natCast] at hyratio
    change _ - 1 = Real.exp (S y - b) - 1 at hyratio
    linarith
  have hratio :
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega x) /
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega y) =
        Real.exp (S x - S y) := by
    rw [hxexp, hyexp, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hdiff : |S x - S y| ≤ cubeOscillation k S := by
    rw [abs_le]
    constructor
    · have h := sub_le_cubeOscillation_of_continuous k
        (continuous_cutoffShellSum_in_space L m omega) hy hx
      dsimp only [S] at h ⊢
      linarith
    · exact sub_le_cubeOscillation_of_continuous k
        (continuous_cutoffShellSum_in_space L m omega) hx hy
  have hreal : |Real.exp (S x - S y) - 1| ≤
      Real.exp (cubeOscillation k S) - 1 := by
    exact (abs_exp_sub_one_le_exp_abs_sub_one _).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hdiff) 1)
  rw [hratio]
  unfold cutoffRatioOscillationSup
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  exact le_iSup_of_le L (le_iSup_of_le hmL le_rfl)

/-- One selected suffix factor controls all finite tail ratios throughout
an arbitrary physical cube, in both orientations. -/
theorem ae_tail_pair_ratios_on_cube {d : ℕ} (M : GMCModel d) (m : ℕ) (k : ℤ) :
    ∀ᵐ ω ∂M.P.toMeasure, ∀ L : ℕ, m ≤ L → ∀ x y : Vec d,
      x ∈ openCubeSet (originCube d k) → y ∈ openCubeSet (originCube d k) →
      |(aCutoff M L ω x / aCutoff M m ω x) /
          (aCutoff M L ω y / aCutoff M m ω y) - 1| ≤
        cutoffChangeSuffixRepresentative m k ω := by
  filter_upwards [ae_cutoffRatioOscillationSup_le_cutoffChangeSuffixRepresentative M m k]
    with ω hω
  intro L hmL x y hx hy
  have h := (tail_pair_ratio_le_oscillation_on_cube M hmL k ω hx hy).trans hω
  exact (ENNReal.ofReal_le_ofReal_iff
    (cutoffChangeSuffixRepresentative_nonneg m k ω)).mp h

/-- The normalized finite density lies between the same two scalar multiples
of the prefix density. This statement uses no distributional assumptions. -/
theorem finite_localDensity_comparison {d : ℕ} (M : GMCModel d) {L m : ℕ}
    (hmL : m ≤ L) (z : Vec d) (ω : AnchoredC11Sample d) (x : Vec d)
    {F : ℝ} (hF : 0 < F)
    (hforward : (aCutoff M L ω.1 (z + (3 : ℝ) ^ m • x) /
        aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x)) /
          (aCutoff M L ω.1 z / aCutoff M m ω.1 z) ≤ F)
    (hbackward : (aCutoff M L ω.1 z / aCutoff M m ω.1 z) /
        (aCutoff M L ω.1 (z + (3 : ℝ) ^ m • x) /
          aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x)) ≤ F) :
    F⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤
      SubdiffusiveProcess.Static.localDensity M (L : WithTop ℕ) m z ω x ∧
    SubdiffusiveProcess.Static.localDensity M (L : WithTop ℕ) m z ω x ≤
      F * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) := by
  have hx := aCutoff_pos M m ω.1 (z + (3 : ℝ) ^ m • x)
  have hz := aCutoff_pos M m ω.1 z
  have hLx := aCutoff_pos M L ω.1 (z + (3 : ℝ) ^ m • x)
  have hLz := aCutoff_pos M L ω.1 z
  change F⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤
    (aCutoff M L ω.1 z / aCutoff M (min m L) ω.1 z)⁻¹ *
      aCutoff M L ω.1 (z + (3 : ℝ) ^ m • x) ∧
    (aCutoff M L ω.1 z / aCutoff M (min m L) ω.1 z)⁻¹ *
      aCutoff M L ω.1 (z + (3 : ℝ) ^ m • x) ≤
        F * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x)
  rw [min_eq_left hmL]
  constructor
  · field_simp at hbackward ⊢
    nlinarith
  · field_simp at hforward ⊢
    nlinarith

/-- Finite normalized densities converge pointwise to the full normalized
coefficient on every anchored sample. -/
theorem tendsto_localDensity_finite {d : ℕ} (M : GMCModel d) (m : ℕ)
    (z : Vec d) (ω : AnchoredC11Sample d) (x : Vec d) :
    Tendsto (fun L : ℕ => SubdiffusiveProcess.Static.localDensity M (L : WithTop ℕ)
      m z ω x) atTop (nhds (SubdiffusiveProcess.Static.localDensity M ⊤ m z ω x)) := by
  let y := z + (3 : ℝ) ^ m • x
  have hy : Tendsto (fun L => anchoredCutoff M L ω.1 y) atTop
      (nhds (aAnchored M ω y)) :=
    (tendstoUniformlyOn_anchoredCutoff M ω isCompact_singleton).tendsto_at rfl
  have hz : Tendsto (fun L => anchoredCutoff M L ω.1 z) atTop
      (nhds (aAnchored M ω z)) :=
    (tendstoUniformlyOn_anchoredCutoff M ω isCompact_singleton).tendsto_at rfl
  have ht := (tendsto_const_nhds (x := aCutoff M m ω.1 z)).mul
    (hy.div hz (aAnchored_pos M ω z).ne')
  have hfull : aCutoff M m ω.1 z * (aAnchored M ω y / aAnchored M ω z) =
      SubdiffusiveProcess.Static.localDensity M ⊤ m z ω x := by
    change _ = (aAnchored M ω z / aCutoff M m ω.1 z)⁻¹ * aAnchored M ω y
    field_simp
  rw [hfull] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop m] with L hL
  change aCutoff M m ω.1 z * (aCutoff M L ω.1 y / aCutoff M L ω.1 0 /
    (aCutoff M L ω.1 z / aCutoff M L ω.1 0)) =
      (aCutoff M L ω.1 z / aCutoff M (min m L) ω.1 z)⁻¹ * aCutoff M L ω.1 y
  rw [min_eq_left hL]
  field_simp [(aCutoff_pos M L ω.1 0).ne', (aCutoff_pos M L ω.1 z).ne']
  <;> ring

/-- A uniform two-sided finite-cutoff comparison passes to the infinite
coefficient, with exactly the same factor. -/
theorem full_localDensity_comparison {d : ℕ} (M : GMCModel d) (m : ℕ)
    (z : Vec d) (ω : AnchoredC11Sample d) (x : Vec d) (F : ℝ)
    (h : ∀ L : ℕ, m ≤ L →
      F⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤
        SubdiffusiveProcess.Static.localDensity M (L : WithTop ℕ) m z ω x ∧
      SubdiffusiveProcess.Static.localDensity M (L : WithTop ℕ) m z ω x ≤
        F * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x)) :
    F⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤
      SubdiffusiveProcess.Static.localDensity M ⊤ m z ω x ∧
    SubdiffusiveProcess.Static.localDensity M ⊤ m z ω x ≤
      F * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) := by
  have ht := tendsto_localDensity_finite M m z ω x
  constructor
  · exact ge_of_tendsto ht (by
      filter_upwards [eventually_ge_atTop m] with L hL using (h L hL).1)
  · exact le_of_tendsto ht (by
      filter_upwards [eventually_ge_atTop m] with L hL using (h L hL).2)

end SubdiffusiveProcess.Static
