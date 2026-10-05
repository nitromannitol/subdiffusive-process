module

public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_cell_transport
public import SubdiffusiveProcess.Paper.g9_general_R_reference_split
public import SubdiffusiveProcess.Paper.g9_cell_entry
public import SubdiffusiveProcess.Sobolev.ScalarMultiplierCompactness
public import SubdiffusiveProcess.Analysis.GeneralRCompactness
public import SubdiffusiveProcess.Analysis.UniformLpBound
public import SubdiffusiveProcess.Analysis.LpExponentCompact
public import SubdiffusiveProcess.Paper.reference_point_moments
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_chart_response_transfer
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroRHS

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

/-! General-cell lift of `lem_prefix_limit_g9_cell_compact`'s coarse-entry `L¹`-compactness:
given origin-cube compactness of a `σ`/`σ_*^{-1}` entry family with a uniform `L²` bound, the same
family is `L¹`-relatively compact on every triadic sub-cube `R` of the origin, via the
cell-transport identity (`lem_prefix_limit_g9_cell_transport`), its reference-scalar det/random
split (`g9_general_R_reference_split`), and a generic compactness-under-multiplication argument.
Does not itself supply origin-cube compactness or the uniform `L²` bound; those are hypotheses. -/

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The infrared-transport "retained" correction at shift `0` vanishes identically: its defining
sum ranges over the empty index set `Finset.Ico 0 0`. -/
theorem aux_g9_reference_moments_centered_retained_zero {d : ℕ} (w : SpatialCoordinates d)
    (om : BilateralField d) :
    aux_g9chart_transport_retained (0 : ℤ) w om = 0 := by
  unfold aux_g9chart_transport_retained aux_g9chart_transport_ret
  simp only [le_refl, ite_true, Finset.Ico_self, Finset.sum_empty]

/-- The zero-scale infrared shift `aux_g9chart_transport_S 0 v` (a pure translation of every
layer's spatial argument by `v`) is inverted by the same map at `-v`. -/
theorem aux_g9_reference_moments_centered_S_comp_id {d : ℕ} (v : SpatialCoordinates d)
    (om : BilateralField d) :
    aux_g9chart_transport_S (0 : ℤ) v (aux_g9chart_transport_S (0 : ℤ) (-v) om) = om := by
  funext j
  apply ContinuousMap.ext
  intro y
  rw [aux_g9chart_transport_S_apply, aux_g9chart_transport_S_apply]
  simp only [sub_zero, neg_zero, zpow_zero, one_smul, neg_add_cancel_left]

/-- At scale `0`, the zero-scale infrared shift is exactly evaluation-point translation by `v`. -/
theorem aux_g9_reference_moments_centered_S_apply_shift {d : ℕ} (v y : SpatialCoordinates d)
    (om : BilateralField d) (j : ℤ) :
    aux_g9chart_transport_S (0 : ℤ) v om j y = om j (v + y) := by
  rw [aux_g9chart_transport_S_apply]
  simp only [sub_zero, neg_zero, zpow_zero, one_smul]

/-- Exponent-`8` clone of `g9_general_R_reference_split`'s two-sided moment bound, valid at an
arbitrary point of the closed unit cube `[0,1]^d`, not only the caller-supplied point. -/
theorem aux_g9_reference_moments_centered_atPoint {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta0le : delta0 ≤ 1) (hMdelta : M.delta ≤ delta0)
    (shift : ℕ) (w : SpatialCoordinates d)
    (hw : w ∈ ({x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} : Set (SpatialCoordinates d))) :
    MemLp (fun om => Real.exp ((H om) w + _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) w om))
      (8 : ℝ≥0∞) (chaosSampleLaw M).toMeasure ∧
    MemLp (fun om => (Real.exp ((H om) w +
        _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) w om))⁻¹)
      (8 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := by
  obtain ⟨Cmom, Crate, hCmom, hCrate, hall⟩ :=
    reference_point_moments d hd (4 : ℝ) (by norm_num)
  have h8 : (8 : ℝ) ∈ Set.Icc (1 : ℝ) (2 * 4) := by norm_num
  obtain ⟨-, -, hmem, hmeminv⟩ :=
    hall delta0 hdelta0 hdelta0le M Rm H hH hMdelta 8 h8 shift shift (le_refl shift) w hw
  dsimp only at hmem hmeminv
  have hc8 : ENNReal.ofReal (8 : ℝ) = (8 : ℝ≥0∞) := by norm_num
  rw [hc8] at hmem hmeminv
  set c0 : ℝ := ahom M (shift - shift) / ahom M shift * Real.exp (-(shift : ℝ) *
    _root_.SubdiffusiveProcess.Model.tauSq M.P) with hc0def
  have heqfun : (fun om : BilateralField d => ahom M (shift - shift) / ahom M shift *
      Real.exp ((H om) w + ∑ j ∈ Finset.range shift, (om (-(j : ℤ))) w -
        (shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) =
      (fun om => c0 * Real.exp ((H om) w +
        _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) w om)) := by
    funext om
    rw [hc0def]
    exact aux_g9_general_R_reference_split_s_eq_c0_mul_randFactor M H shift w om
  rw [heqfun] at hmem
  have hc0ne : c0 ≠ 0 := by
    rw [hc0def]
    have h1 : ahom M (shift - shift) ≠ 0 := (ahom_pos M (shift - shift)).ne'
    have h2 : ahom M shift ≠ 0 := (ahom_pos M shift).ne'
    positivity
  constructor
  · have := hmem.const_mul c0⁻¹
    simpa [inv_mul_cancel_left₀ hc0ne] using this
  · have heqfuninv : (fun om : BilateralField d => (ahom M (shift - shift) / ahom M shift *
        Real.exp ((H om) w + ∑ j ∈ Finset.range shift, (om (-(j : ℤ))) w -
          (shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))⁻¹) =
        (fun om => c0⁻¹ * (Real.exp ((H om) w +
          _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) w om))⁻¹) := by
      funext om
      rw [congrFun heqfun om]
      exact mul_inv c0 _
    rw [heqfuninv] at hmeminv
    have := hmeminv.const_mul c0
    simpa [mul_inv_cancel_left₀ hc0ne] using this

/-- `L^8 * L^8 ⊆ L^4` on a probability measure, as a Hölder triple instance. -/
theorem aux_g9_reference_moments_centered_holderTriple_8_8_4 :
    ENNReal.HolderTriple (8 : ℝ≥0∞) 8 4 := ⟨by
  have h1 : (8 : ℝ≥0∞) = ((8 : ℝ≥0) : ℝ≥0∞) := by norm_num
  have h2 : (4 : ℝ≥0∞) = ((4 : ℝ≥0) : ℝ≥0∞) := by norm_num
  rw [h1, h2, ← ENNReal.coe_inv (by norm_num : (8 : ℝ≥0) ≠ 0), ← ENNReal.coe_add,
    ← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0)]
  exact_mod_cast (by norm_num : (8 : ℝ≥0)⁻¹ + (8 : ℝ≥0)⁻¹ = (4 : ℝ≥0)⁻¹)⟩

/-- Two-sided fourth moments of the reference factor at centres in the closed origin cube. -/
theorem aux_g9_general_R_entry_lift_reference_moments_centered {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta0le : delta0 ≤ 1) (hMdelta : M.delta ≤ delta0)
    (shift : ℕ) (z : SpatialCoordinates d)
    (hz : z ∈ ({x : SpatialCoordinates d | ∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 1 / 2} :
      Set (SpatialCoordinates d))) :
    MemLp (fun om => Real.exp ((H om) z + aux_g9chart_transport_retained (shift : ℤ) z om))
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure ∧
    MemLp (fun om => (Real.exp ((H om) z + aux_g9chart_transport_retained (shift : ℤ) z om))⁻¹)
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := by
  set v : SpatialCoordinates d := fun _ => (1 / 2 : ℝ) with hvdef
  have hv : v ∈ ({x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} :
      Set (SpatialCoordinates d)) := by
    intro i; rw [hvdef]; norm_num
  have hvz : v + z ∈ ({x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} :
      Set (SpatialCoordinates d)) := by
    intro i
    have hzi := hz i
    simp only [Pi.add_apply, hvdef]
    constructor <;> linarith [hzi.1, hzi.2]
  obtain ⟨hA, hA'⟩ := aux_g9_reference_moments_centered_atPoint hd M Rm H hH delta0 hdelta0
    hdelta0le hMdelta shift (v + z) hvz
  obtain ⟨hB0, hB0'⟩ := aux_g9_reference_moments_centered_atPoint hd M Rm H hH delta0 hdelta0
    hdelta0le hMdelta 0 v hv
  have hB : MemLp (fun om => Real.exp ((H om) v)) (8 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := by
    have heq : (fun om : BilateralField d => Real.exp ((H om) v)) =
        (fun om => Real.exp ((H om) v + _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (0 : ℤ) v om)) := by
      funext om
      rw [aux_g9_reference_moments_centered_retained_zero v om, add_zero]
    rw [heq]; exact hB0
  have hB' : MemLp (fun om => Real.exp (-((H om) v))) (8 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := by
    have heq : (fun om : BilateralField d => Real.exp (-((H om) v))) =
        (fun om => (Real.exp ((H om) v +
          _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (0 : ℤ) v om))⁻¹) := by
      funext om
      rw [aux_g9_reference_moments_centered_retained_zero v om, add_zero, ← Real.exp_neg]
    rw [heq]; exact hB0'
  have hcompid : ∀ om, aux_g9chart_transport_S (0 : ℤ) v (aux_g9chart_transport_S (0 : ℤ) (-v) om) = om :=
    aux_g9_reference_moments_centered_S_comp_id v
  have hinfrared := aux_g9chart_transport_infrared (M := M) (H := H) hH (0 : ℤ) v
  have hretS : ∀ om : BilateralField d,
      _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z (aux_g9chart_transport_S (0 : ℤ) v om) =
        _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) (v + z) om := by
    intro om
    unfold _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained
    congr 1
    funext j
    exact aux_g9_reference_moments_centered_S_apply_shift v z om j
  have hcomb : (fun om : BilateralField d => Real.exp ((H (aux_g9chart_transport_S (0 : ℤ) v om)) z +
          _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
            (aux_g9chart_transport_S (0 : ℤ) v om))) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun om => Real.exp ((H om) (v + z) +
          _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) (v + z) om) *
        Real.exp (-((H om) v))) := by
    filter_upwards [hinfrared] with om hom
    have hy := hom z
    simp only [neg_zero, zpow_zero, one_smul] at hy
    rw [aux_g9_reference_moments_centered_retained_zero (v + z) om,
      aux_g9_reference_moments_centered_retained_zero v om] at hy
    simp only [add_zero, sub_zero] at hy
    show Real.exp ((H (aux_g9chart_transport_S (0 : ℤ) v om)) z +
        _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
          (aux_g9chart_transport_S (0 : ℤ) v om)) =
      Real.exp ((H om) (v + z) + _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) (v + z) om) *
        Real.exp (-((H om) v))
    rw [hretS om, hy, ← Real.exp_add]
    congr 1
    ring
  have hcombinv : (fun om : BilateralField d => (Real.exp
        ((H (aux_g9chart_transport_S (0 : ℤ) v om)) z +
          _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
            (aux_g9chart_transport_S (0 : ℤ) v om)))⁻¹) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun om => (Real.exp ((H om) (v + z) +
            _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) (v + z) om))⁻¹ *
          Real.exp ((H om) v)) := by
    filter_upwards [hcomb] with om hom
    show (Real.exp ((H (aux_g9chart_transport_S (0 : ℤ) v om)) z +
        _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
          (aux_g9chart_transport_S (0 : ℤ) v om)))⁻¹ =
      (Real.exp ((H om) (v + z) + _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) (v + z) om))⁻¹ *
        Real.exp ((H om) v)
    rw [hom, mul_inv, Real.exp_neg, inv_inv]
  have hHT88 := aux_g9_reference_moments_centered_holderTriple_8_8_4
  have hprod : MemLp (fun om => Real.exp ((H om) (v + z) +
      _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) (v + z) om) * Real.exp (-((H om) v)))
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := by simpa only [mul_comm] using! hB'.fun_mul hA (r := (4 : ℝ≥0∞))
  have hprodinv : MemLp (fun om => (Real.exp ((H om) (v + z) +
      _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) (v + z) om))⁻¹ * Real.exp ((H om) v))
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := by simpa only [mul_comm] using! hB.fun_mul hA' (r := (4 : ℝ≥0∞))
  have hSv4 : MemLp (fun om => Real.exp ((H (aux_g9chart_transport_S (0 : ℤ) v om)) z +
      _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
        (aux_g9chart_transport_S (0 : ℤ) v om)))
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := hprod.ae_eq hcomb.symm
  have hSv4inv : MemLp (fun om => (Real.exp ((H (aux_g9chart_transport_S (0 : ℤ) v om)) z +
      _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
        (aux_g9chart_transport_S (0 : ℤ) v om)))⁻¹)
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := hprodinv.ae_eq hcombinv.symm
  have hSmv : MeasurePreserving (aux_g9chart_transport_S (0 : ℤ) (-v))
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    aux_g9chart_transport_S_measurePreserving M 0 (-v)
  have hcompose : MemLp (fun om => Real.exp ((H (aux_g9chart_transport_S (0 : ℤ) v
      (aux_g9chart_transport_S (0 : ℤ) (-v) om))) z +
      _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
        (aux_g9chart_transport_S (0 : ℤ) v (aux_g9chart_transport_S (0 : ℤ) (-v) om))))
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := hSv4.comp_measurePreserving hSmv
  have hcomposeinv : MemLp (fun om => (Real.exp ((H (aux_g9chart_transport_S (0 : ℤ) v
      (aux_g9chart_transport_S (0 : ℤ) (-v) om))) z +
      _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
        (aux_g9chart_transport_S (0 : ℤ) v (aux_g9chart_transport_S (0 : ℤ) (-v) om))))⁻¹)
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := hSv4inv.comp_measurePreserving hSmv
  have hfe : (fun om : BilateralField d => Real.exp ((H (aux_g9chart_transport_S (0 : ℤ) v
      (aux_g9chart_transport_S (0 : ℤ) (-v) om))) z +
      _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
        (aux_g9chart_transport_S (0 : ℤ) v (aux_g9chart_transport_S (0 : ℤ) (-v) om)))) =
      (fun om => Real.exp ((H om) z + aux_g9chart_transport_retained (shift : ℤ) z om)) := by
    funext om; rw [hcompid om]
  have hfeinv : (fun om : BilateralField d => (Real.exp ((H (aux_g9chart_transport_S (0 : ℤ) v
      (aux_g9chart_transport_S (0 : ℤ) (-v) om))) z +
      _root_.SubdiffusiveProcess.Paper.aux_g9chart_transport_retained (shift : ℤ) z
        (aux_g9chart_transport_S (0 : ℤ) v (aux_g9chart_transport_S (0 : ℤ) (-v) om))))⁻¹) =
      (fun om => (Real.exp ((H om) z + aux_g9chart_transport_retained (shift : ℤ) z om))⁻¹) := by
    funext om; rw [hcompid om]
  rw [hfe] at hcompose
  rw [hfeinv] at hcomposeinv
  exact ⟨hcompose, hcomposeinv⟩

/-- `L^2 * L^2 ⊆ L^1` on a probability measure, as a Hölder triple instance. -/
theorem aux_g9_general_R_entry_lift_holderTriple_2_2_1 :
    ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by
  have hcancel : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 2 * (2 : ℝ≥0∞)⁻¹ := by ring
    _ = 1 := hcancel
    _ = (1 : ℝ≥0∞)⁻¹ := inv_one.symm⟩

/-- The `Lp`-space element of a constant multiple of an `L^p` function equals the scalar multiple,
in `Lp`, of that function's own `Lp`-space element. -/
theorem aux_g9_general_R_entry_lift_toLp_const_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} {f : α → ℝ} (hf : MemLp f p μ) (c : ℝ) :
    (hf.const_mul c).toLp (fun x => c * f x) = c • hf.toLp f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (hf.toLp f), hf.coeFn_toLp, (hf.const_mul c).coeFn_toLp]
    with x h1 h2 h3
  rw [h3, h1, Pi.smul_apply, h2, smul_eq_mul]

/-- Generic compactness core for the general-cell lift: given an origin-cell family
`entryOrigin` that is `L¹`-relatively compact with a uniform `L²` bound, a measure-preserving
self-map `S`, a `K`-independent random multiplier `φ ∈ L⁴`, and a deterministic multiplier
sequence `c` bounded within a fixed interval, such that `entryR (n + shift)` agrees a.e. with
`c n * (φ * (entryOrigin n ∘ S))`, the cell family `entryR` is `L¹`-relatively compact. -/
theorem aux_g9_general_R_entry_lift_core {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (entryR entryOrigin : ℕ → BilateralField d → ℝ)
    (S : BilateralField d → BilateralField d)
    (hS : MeasurePreserving S (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure)
    (shift : ℕ)
    (φ : BilateralField d → ℝ) (hφmem4 : MemLp φ (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure)
    (c : ℕ → ℝ) (Cbd : ℝ) (hcbound : ∀ n, |c n| ≤ Cbd)
    (h0mem : ∀ n, MemLp (entryOrigin n) 1 (chaosSampleLaw M).toMeasure)
    (h0cpt : IsCompact (closure (Set.range (fun n => (h0mem n).toLp (entryOrigin n)))))
    (B : ℝ)
    (h0L2 : ∀ n, MemLp (entryOrigin n) 2 (chaosSampleLaw M).toMeasure ∧
      eLpNorm (entryOrigin n) 2 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B)
    (hRmem : ∀ K, MemLp (entryR K) 1 (chaosSampleLaw M).toMeasure)
    (heq : ∀ n : ℕ, (entryR (n + shift)) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun om => c n * (φ om * entryOrigin n (S om)))) :
    IsCompact (closure (Set.range (fun K => (hRmem K).toLp (entryR K)))) := by
  have hmem1' : ∀ n, MemLp (fun om => entryOrigin n (S om)) 1 (chaosSampleLaw M).toMeasure :=
    fun n => (h0mem n).comp_measurePreserving hS
  have hmem2' : ∀ n, MemLp (fun om => entryOrigin n (S om)) 2 (chaosSampleLaw M).toMeasure :=
    fun n => (h0L2 n).1.comp_measurePreserving hS
  have hcompA : IsCompact (closure (Set.range
      (fun n => (hmem1' n).toLp (fun om => entryOrigin n (S om))))) :=
    aux_compact_comp_measurePreserving S hS entryOrigin h0mem h0cpt
  have hBabs0 : 0 ≤ |B| := abs_nonneg B
  have hBabsbd : ∀ n, eLpNorm (fun om => entryOrigin n (S om)) 2 (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal |B| := by
    intro n
    have heqn : eLpNorm (fun om => entryOrigin n (S om)) 2 (chaosSampleLaw M).toMeasure =
        eLpNorm (entryOrigin n) 2 (chaosSampleLaw M).toMeasure :=
      eLpNorm_comp_measurePreserving (h0L2 n).1.aestronglyMeasurable hS
    rw [heqn]
    exact (h0L2 n).2.trans (ENNReal.ofReal_le_ofReal (le_abs_self B))
  have hφmem2 : MemLp φ (2 : ℝ≥0∞) (chaosSampleLaw M).toMeasure :=
    hφmem4.mono_exponent (by norm_num)
  have hHT221 := aux_g9_general_R_entry_lift_holderTriple_2_2_1
  have hmemφ1' : ∀ n, MemLp (fun om => φ om * entryOrigin n (S om)) 1
      (chaosSampleLaw M).toMeasure := by
    intro n
    simpa only [mul_comm] using! (hmem2' n).fun_mul hφmem2 (r := (1 : ℝ≥0∞))
  have hq2 : (2 : ℝ≥0∞) < 4 := by norm_num
  have hqtop : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hcompB : IsCompact (closure (Set.range (fun n =>
      (hmemφ1' n).toLp (fun om => φ om * entryOrigin n (S om))))) :=
    isCompact_closure_range_smul_of_memLp_higher φ hq2 hqtop hφmem4
      (fun n om => entryOrigin n (S om)) hmem1' hmem2' |B| hBabs0 hBabsbd hmemφ1' hcompA
  have hcompC0 : IsCompact (closure (Set.range (fun n => c n •
      (hmemφ1' n).toLp (fun om => φ om * entryOrigin n (S om))))) :=
    isCompact_closure_range_bounded_scalar_smul
      (fun n => (hmemφ1' n).toLp (fun om => φ om * entryOrigin n (S om))) hcompB c Cbd hcbound
  have hmemc : ∀ n, MemLp (fun om => c n * (φ om * entryOrigin n (S om))) 1
      (chaosSampleLaw M).toMeasure := fun n => (hmemφ1' n).const_mul (c n)
  have hfun2 : (fun n => c n • (hmemφ1' n).toLp (fun om => φ om * entryOrigin n (S om))) =
      (fun n => (hmemc n).toLp (fun om => c n * (φ om * entryOrigin n (S om)))) := by
    funext n
    exact (aux_g9_general_R_entry_lift_toLp_const_mul (hmemφ1' n) (c n)).symm
  rw [hfun2] at hcompC0
  have hfun3 : (fun n => (hRmem (n + shift)).toLp (entryR (n + shift))) =
      (fun n => (hmemc n).toLp (fun om => c n * (φ om * entryOrigin n (S om)))) := by
    funext n
    exact MemLp.toLp_congr (hRmem (n + shift)) (hmemc n) (heq n)
  rw [← hfun3] at hcompC0
  exact isCompact_closure_range_of_shifted_compact (fun K => (hRmem K).toLp (entryR K)) shift
    hcompC0

/-- The centre of any triadic sub-cube `R` of the origin cube lies in the closed cube
`[-1/2, 1/2]^d`, via `R`'s centre lying in `R` itself, `R ⊆` the origin cube, and the origin
cube's identification with the centred unit cube. -/
theorem aux_g9_general_R_entry_lift_z_mem {d : ℕ} [NeZero d]
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    Homogenization.cubeCenter R ∈
      ({x : SpatialCoordinates d | ∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 1 / 2} :
        Set (SpatialCoordinates d)) := by
  have h1 : Homogenization.cubeCenter R ∈ Homogenization.openCubeSet R :=
    Homogenization.Book.Ch03.cubeCenter_mem_openCubeSet R
  have h2 : Homogenization.cubeCenter R ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) :=
    hR h1
  rw [← aux_chart_transfer_root_carrier] at h2
  rw [SubdiffusiveProcess.centeredCube_eq_pi (0 : SpatialCoordinates d) (by norm_num)] at h2
  intro i
  have hi := h2 i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi
  simp only [Pi.zero_apply, zero_sub, zero_add] at hi
  exact ⟨hi.1.le, hi.2.le⟩

/-- The origin-cube cutoff produced by the cell-transport identity at `K = n + shift` is exactly
`n`, once `shift = (-R.scale).toNat`. -/
theorem aux_g9_general_R_entry_lift_shift_cutoff_eq {d : ℕ} (R : Homogenization.TriadicCube d)
    (shift n : ℕ) (hshifteq : (shift : ℤ) = -R.scale) :
    (((n + shift : ℕ) : ℤ) + R.scale).toNat = n := by
  have heq : ((n + shift : ℕ) : ℤ) + R.scale = (n : ℤ) := by push_cast; omega
  rw [heq]
  simp

/-- Cell-transport identity for the `σ` (`b = true`) coarse entry, reindexed at `K = n + shift`
with the reference scalar spelled out at the shift exponent `shift : ℤ` rather than `-R.scale`. -/
theorem aux_g9_general_R_entry_lift_transport_true {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (i j : Fin d) (shift : ℕ) (hshifteq : (shift : ℤ) = -R.scale) (n : ℕ) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      g9_cell_entry I M H R true i j (n + shift) omega =
        aux_g9chart_transport_reference M H (n + shift) (shift : ℤ)
            (Homogenization.cubeCenter R) omega *
          g9_cell_entry I M H (Homogenization.originCube d 0) true i j n
            (aux_g9chart_transport_S (shift : ℤ) (Homogenization.cubeCenter R) omega) := by
  have hmK : -R.scale ≤ ((n + shift : ℕ) : ℤ) := by
    rw [← hshifteq]; exact_mod_cast Nat.le_add_left shift n
  have htr := lem_prefix_limit_g9_cell_transport I M H hH (n + shift) R hR hmK
  filter_upwards [htr] with omega htr'
  obtain ⟨-, hSig, -, -, -⟩ := htr'
  have hSigij := hSig i j
  have hcut := aux_g9_general_R_entry_lift_shift_cutoff_eq R shift n hshifteq
  rw [← hshifteq, hcut] at hSigij
  show Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
      ((aux_U2_unitChart I M H omega (n + shift)).coeffOn R) i j =
    aux_g9chart_transport_reference M H (n + shift) (shift : ℤ)
        (Homogenization.cubeCenter R) omega *
      Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((aux_U2_unitChart I M H (aux_g9chart_transport_S (shift : ℤ)
            (Homogenization.cubeCenter R) omega) n).coeffOn (Homogenization.originCube d 0)) i j
  exact hSigij

/-- Cell-transport identity for the `σ_*^{-1}` (`b = false`) coarse entry, reindexed at
`K = n + shift`, with the reference scalar's inverse spelled out at the shift exponent
`shift : ℤ` rather than `-R.scale`. -/
theorem aux_g9_general_R_entry_lift_transport_false {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (i j : Fin d) (shift : ℕ) (hshifteq : (shift : ℤ) = -R.scale) (n : ℕ) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      g9_cell_entry I M H R false i j (n + shift) omega =
        (aux_g9chart_transport_reference M H (n + shift) (shift : ℤ)
            (Homogenization.cubeCenter R) omega)⁻¹ *
          g9_cell_entry I M H (Homogenization.originCube d 0) false i j n
            (aux_g9chart_transport_S (shift : ℤ) (Homogenization.cubeCenter R) omega) := by
  have hmK : -R.scale ≤ ((n + shift : ℕ) : ℤ) := by
    rw [← hshifteq]; exact_mod_cast Nat.le_add_left shift n
  have htr := lem_prefix_limit_g9_cell_transport I M H hH (n + shift) R hR hmK
  filter_upwards [htr] with omega htr'
  obtain ⟨-, -, hSig, -, -⟩ := htr'
  have hSigij := hSig i j
  have hcut := aux_g9_general_R_entry_lift_shift_cutoff_eq R shift n hshifteq
  rw [← hshifteq, hcut] at hSigij
  show Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
      ((aux_U2_unitChart I M H omega (n + shift)).coeffOn R) i j =
    (aux_g9chart_transport_reference M H (n + shift) (shift : ℤ)
        (Homogenization.cubeCenter R) omega)⁻¹ *
      Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((aux_U2_unitChart I M H (aux_g9chart_transport_S (shift : ℤ)
            (Homogenization.cubeCenter R) omega) n).coeffOn (Homogenization.originCube d 0)) i j
  exact hSigij

/-- The reference scalar's deterministic `ahom`-ratio det-factor is strictly positive, from its
own lower bound (`aux_g9_general_R_reference_split_detFactor_bounded`) exceeding `0`. -/
theorem aux_g9_general_R_entry_lift_detFactor_pos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (K shift : ℕ) (hshift : shift ≤ K) :
    0 < Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
      (ahom M (K - shift) / ahom M K) :=
  lt_of_lt_of_le (Real.exp_pos _)
    (aux_g9_general_R_reference_split_detFactor_bounded M K shift hshift).1

/-- The deterministic det-factor's absolute value is bounded by the fixed, `K`-independent
constant `exp(shift * tauSq)`. -/
theorem aux_g9_general_R_entry_lift_detFactor_abs_le {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (K shift : ℕ) (hshift : shift ≤ K) :
    |Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        (ahom M (K - shift) / ahom M K)| ≤
      Real.exp ((shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  rw [abs_of_pos (aux_g9_general_R_entry_lift_detFactor_pos M K shift hshift)]
  exact (aux_g9_general_R_reference_split_detFactor_bounded M K shift hshift).2

/-- The deterministic det-factor's *inverse* absolute value is bounded by the same fixed constant
`exp(shift * tauSq)`, since the det-factor is bounded away from `0`. -/
theorem aux_g9_general_R_entry_lift_detFactor_inv_abs_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (K shift : ℕ) (hshift : shift ≤ K) :
    |(Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        (ahom M (K - shift) / ahom M K))⁻¹| ≤
      Real.exp ((shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  have hpos := aux_g9_general_R_entry_lift_detFactor_pos M K shift hshift
  rw [abs_of_pos (inv_pos.mpr hpos)]
  have hb := aux_g9_general_R_reference_split_detFactor_bounded M K shift hshift
  have h1 : (1 : ℝ) / (Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
      (ahom M (K - shift) / ahom M K)) ≤
      1 / Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
    one_div_le_one_div_of_le (Real.exp_pos _) hb.1
  rw [one_div, one_div] at h1
  have hfin : (Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))⁻¹ =
      Real.exp ((shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    rw [← Real.exp_neg]; ring_nf
  rwa [hfin] at h1

/-- General-cell lift: origin-cube `L¹` compactness plus a uniform `L²` bound of an entry family
gives `L¹` compactness of the same entry family on every triadic cell of the origin cube. -/
theorem g9_general_R_entry_lift {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta0le : delta0 ≤ 1) (hMdelta : M.delta ≤ delta0)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (b : Bool) (i j : Fin d)
    (h0mem : ∀ K, MemLp (g9_cell_entry I M H (Homogenization.originCube d 0) b i j K) 1
      (chaosSampleLaw M).toMeasure)
    (h0cpt : IsCompact (closure (Set.range (fun K =>
      (h0mem K).toLp (g9_cell_entry I M H (Homogenization.originCube d 0) b i j K)))))
    (B : ℝ) (h0L2 : ∀ K, MemLp (g9_cell_entry I M H (Homogenization.originCube d 0) b i j K) 2
      (chaosSampleLaw M).toMeasure ∧
      eLpNorm (g9_cell_entry I M H (Homogenization.originCube d 0) b i j K) 2
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B)
    (hRmem : ∀ K, MemLp (g9_cell_entry I M H R b i j K) 1 (chaosSampleLaw M).toMeasure) :
    IsCompact (closure (Set.range (fun K => (hRmem K).toLp (g9_cell_entry I M H R b i j K)))) := by
  set shift : ℕ := (-R.scale).toNat with hshiftdef
  have hscale_nonneg : 0 ≤ -R.scale :=
    neg_nonneg.mpr (aux_lem_prefix_limit_g9_cell_transport_scale_nonpos R hR)
  have hshifteq : (shift : ℤ) = -R.scale := by
    rw [hshiftdef]; exact Int.toNat_of_nonneg hscale_nonneg
  have hz := aux_g9_general_R_entry_lift_z_mem R hR
  obtain ⟨hrmem4, hrmeminv4⟩ := aux_g9_general_R_entry_lift_reference_moments_centered hd M Rm H hH delta0 hdelta0
    hdelta0le hMdelta shift (Homogenization.cubeCenter R) hz
  have hS : MeasurePreserving (aux_g9chart_transport_S (shift : ℤ) (Homogenization.cubeCenter R))
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    aux_g9chart_transport_S_measurePreserving M (shift : ℤ) (Homogenization.cubeCenter R)
  have hshiftle : ∀ n : ℕ, shift ≤ n + shift := fun n => Nat.le_add_left shift n
  cases b with
  | true =>
    have heq : ∀ n : ℕ,
        (g9_cell_entry I M H R true i j (n + shift)) =ᵐ[(chaosSampleLaw M).toMeasure]
        (fun om => (Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            (ahom M ((n + shift) - shift) / ahom M (n + shift))) *
          ((Real.exp ((H om) (Homogenization.cubeCenter R) +
              aux_g9chart_transport_retained (shift : ℤ) (Homogenization.cubeCenter R) om)) *
            g9_cell_entry I M H (Homogenization.originCube d 0) true i j n
              (aux_g9chart_transport_S (shift : ℤ) (Homogenization.cubeCenter R) om))) := by
      intro n
      filter_upwards [aux_g9_general_R_entry_lift_transport_true I M H hH R hR i j shift
        hshifteq n] with om hom
      rw [hom, aux_g9_general_R_reference_split_eq_detFactor_mul_randFactor M H (n + shift) shift
        (hshiftle n) (Homogenization.cubeCenter R) om]
      ring
    exact aux_g9_general_R_entry_lift_core M
      (g9_cell_entry I M H R true i j)
      (g9_cell_entry I M H (Homogenization.originCube d 0) true i j)
      (aux_g9chart_transport_S (shift : ℤ) (Homogenization.cubeCenter R)) hS shift
      (fun om => Real.exp ((H om) (Homogenization.cubeCenter R) +
        aux_g9chart_transport_retained (shift : ℤ) (Homogenization.cubeCenter R) om)) hrmem4
      (fun n => Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        (ahom M ((n + shift) - shift) / ahom M (n + shift)))
      (Real.exp ((shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
      (fun n => aux_g9_general_R_entry_lift_detFactor_abs_le M (n + shift) shift (hshiftle n))
      h0mem h0cpt B h0L2 hRmem heq
  | false =>
    have heq : ∀ n : ℕ,
        (g9_cell_entry I M H R false i j (n + shift)) =ᵐ[(chaosSampleLaw M).toMeasure]
        (fun om => (Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            (ahom M ((n + shift) - shift) / ahom M (n + shift)))⁻¹ *
          ((Real.exp ((H om) (Homogenization.cubeCenter R) +
              aux_g9chart_transport_retained (shift : ℤ) (Homogenization.cubeCenter R) om))⁻¹ *
            g9_cell_entry I M H (Homogenization.originCube d 0) false i j n
              (aux_g9chart_transport_S (shift : ℤ) (Homogenization.cubeCenter R) om))) := by
      intro n
      filter_upwards [aux_g9_general_R_entry_lift_transport_false I M H hH R hR i j shift
        hshifteq n] with om hom
      rw [hom, aux_g9_general_R_reference_split_eq_detFactor_mul_randFactor M H (n + shift) shift
        (hshiftle n) (Homogenization.cubeCenter R) om, mul_inv]
      ring
    exact aux_g9_general_R_entry_lift_core M
      (g9_cell_entry I M H R false i j)
      (g9_cell_entry I M H (Homogenization.originCube d 0) false i j)
      (aux_g9chart_transport_S (shift : ℤ) (Homogenization.cubeCenter R)) hS shift
      (fun om => (Real.exp ((H om) (Homogenization.cubeCenter R) +
        aux_g9chart_transport_retained (shift : ℤ) (Homogenization.cubeCenter R) om))⁻¹) hrmeminv4
      (fun n => (Real.exp (-(shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        (ahom M ((n + shift) - shift) / ahom M (n + shift)))⁻¹)
      (Real.exp ((shift : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
      (fun n => aux_g9_general_R_entry_lift_detFactor_inv_abs_le M (n + shift) shift (hshiftle n))
      h0mem h0cpt B h0L2 hRmem heq

end SubdiffusiveProcess.Paper
end
