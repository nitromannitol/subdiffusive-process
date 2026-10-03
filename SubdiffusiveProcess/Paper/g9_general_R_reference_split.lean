module

public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_chart_transport
public import SubdiffusiveProcess.Paper.lane4_reference_point_moments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.NormalizerSwap

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab MeasureTheory
open SubdiffusiveProcess
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false



namespace Paper
noncomputable section



theorem aux_g9_general_R_reference_split_detFactor_bounded {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (K shift : ℕ) (hshift : shift ≤ K) :
    Real.exp (-(shift : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
      Real.exp (-(shift : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        (ahom M (K - shift) / ahom M K) ∧
    Real.exp (-(shift : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        (ahom M (K - shift) / ahom M K) ≤
      Real.exp ((shift : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
  have hratio := SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.ahom_ratio_eq_exp_normalizerLogError
    M K (K - shift)
  have habs := SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.abs_normalizerLogError_le_of_le M
    (Nat.sub_le K shift)
  have hcast : ((K - (K - shift) : ℕ) : ℝ) = (shift : ℝ) := by
    have h : K - (K - shift) = shift := by omega
    rw [h]
  rw [hcast] at hratio habs
  rw [abs_le] at habs
  obtain ⟨hlo, hhi⟩ := habs
  refine ⟨?_, ?_⟩
  · rw [hratio, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  · rw [hratio, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)

/-- The reference scalar factors exactly as the (bounded) `ahom`-ratio deterministic factor
times the `K`-independent random factor `exp(H om z + retained shift z om)`. -/
theorem aux_g9_general_R_reference_split_eq_detFactor_mul_randFactor {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K shift : ℕ) (hshift : shift ≤ K) (z : SpatialCoordinates d) (om : BilateralField d) :
    Paper.aux_g9chart_transport_reference M H K (shift : ℤ) z om =
      (Real.exp (-(shift : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          (ahom M (K - shift) / ahom M K)) *
        Real.exp ((H om) z + Paper.aux_g9chart_transport_retained (shift : ℤ) z om) := by
  unfold Paper.aux_g9chart_transport_reference Paper.aux_g9chart_transport_kappa
  have hcast1 : ((K : ℤ) - (shift : ℤ)).toNat = K - shift := by omega
  rw [hcast1]
  have hcast2 : ((K - shift : ℕ) : ℝ) = (K : ℝ) - (shift : ℝ) := Nat.cast_sub hshift
  rw [hcast2]
  set tau := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hratio : Real.exp (-(shift : ℝ) * tau) * (ahom M (K - shift) / ahom M K) =
      Real.exp (((K : ℝ) - (shift : ℝ) + 1) * tau) * ahom M (K - shift) /
        (Real.exp (((K : ℝ) + 1) * tau) * ahom M K) := by
    rw [← div_mul_div_comm, ← Real.exp_sub]
    congr 2
    ring
  rw [hratio]

/-- `aux_g9chart_transport_retained` at a nonnegative shift is the same finite sum
`lane4_reference_point_moments`'s own `G` uses, via `aux_g9chart_transport_sum_range_shift`. -/
theorem aux_g9_general_R_reference_split_retained_eq_range_sum {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) (om : BilateralField d) :
    Paper.aux_g9chart_transport_retained (k : ℤ) z om =
      ∑ j ∈ Finset.range k, (om (-(j : ℤ))) z := by
  unfold Paper.aux_g9chart_transport_retained Paper.aux_g9chart_transport_ret
  rw [if_pos (by positivity)]
  have h := Paper.aux_g9chart_transport_sum_range_shift (fun j : ℤ => om (-j) z) 0 k
  simp only [zero_add] at h
  rw [← h]

/-- `lane4_reference_point_moments`'s `s` function at its own diagonal `N = k = shift` is exactly
a FIXED nonzero constant `c0` times the `K`-independent random factor. -/
theorem aux_g9_general_R_reference_split_s_eq_c0_mul_randFactor {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (shift : ℕ) (z : SpatialCoordinates d) (om : BilateralField d) :
    ahom M (shift - shift) / ahom M shift *
      Real.exp ((H om) z + ∑ j ∈ Finset.range shift, (om (-(j : ℤ))) z -
        (shift : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      (ahom M (shift - shift) / ahom M shift * Real.exp (-(shift : ℝ) *
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
        Real.exp ((H om) z + Paper.aux_g9chart_transport_retained (shift : ℤ) z om) := by
  rw [← aux_g9_general_R_reference_split_retained_eq_range_sum (d := d) shift z om]
  rw [sub_eq_add_neg, Real.exp_add]
  ring_nf

/-- Paper `mfd:sec-local-form` (Section 9): the `K`-independent random factor
`exp(H om z + retained shift z om)` in the reference scalar's det/random split, and its inverse,
both have a finite fourth moment under `chaosSampleLaw M`. Combined with
`aux_g9_general_R_reference_split_eq_detFactor_mul_randFactor` and
`aux_g9_general_R_reference_split_detFactor_bounded`, this gives everything needed to transport
`L^1`-relative compactness of an origin-cell family through multiplication by the FULL reference
scalar `aux_g9chart_transport_reference M H K (shift : ℤ) z` (uniformly in `K ≥ shift`) via a
bounded-deterministic-scalar step and a fixed-random-scalar-with-a-higher-moment step. -/
theorem g9_general_R_reference_split {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta0le : delta0 ≤ 1) (hMdelta : M.delta ≤ delta0)
    (shift : ℕ) (z : SpatialCoordinates d)
    (hz : z ∈ ({x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} : Set (SpatialCoordinates d))) :
    MemLp (fun om => Real.exp ((H om) z + Paper.aux_g9chart_transport_retained (shift : ℤ) z om))
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure ∧
    MemLp (fun om => (Real.exp ((H om) z +
        Paper.aux_g9chart_transport_retained (shift : ℤ) z om))⁻¹)
      (4 : ℝ≥0∞) (chaosSampleLaw M).toMeasure := by
  obtain ⟨Cmom, Crate, hCmom, hCrate, hall⟩ :=
    lane4_reference_point_moments d hd (2 : ℝ) (by norm_num)
  have h4 : (4 : ℝ) ∈ Set.Icc (1 : ℝ) (2 * 2) := by norm_num
  obtain ⟨-, -, hmem, hmeminv⟩ :=
    hall delta0 hdelta0 hdelta0le M Rm H hH hMdelta 4 h4 shift shift (le_refl shift) z hz
  dsimp only at hmem hmeminv
  have hc4 : ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) := by norm_num
  rw [hc4] at hmem hmeminv
  set c0 : ℝ := ahom M (shift - shift) / ahom M shift * Real.exp (-(shift : ℝ) *
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) with hc0def
  have heqfun : (fun om : BilateralField d => ahom M (shift - shift) / ahom M shift *
      Real.exp ((H om) z + ∑ j ∈ Finset.range shift, (om (-(j : ℤ))) z -
        (shift : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) =
      (fun om => c0 * Real.exp ((H om) z +
        Paper.aux_g9chart_transport_retained (shift : ℤ) z om)) := by
    funext om
    rw [hc0def]
    exact aux_g9_general_R_reference_split_s_eq_c0_mul_randFactor M H shift z om
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
        Real.exp ((H om) z + ∑ j ∈ Finset.range shift, (om (-(j : ℤ))) z -
          (shift : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))⁻¹) =
        (fun om => c0⁻¹ * (Real.exp ((H om) z +
          Paper.aux_g9chart_transport_retained (shift : ℤ) z om))⁻¹) := by
      funext om
      rw [congrFun heqfun om]
      exact mul_inv c0 _
    rw [heqfuninv] at hmeminv
    have := hmeminv.const_mul c0
    simpa [mul_inv_cancel_left₀ hc0ne] using this

end
end Paper
