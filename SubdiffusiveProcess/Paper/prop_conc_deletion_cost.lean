module

public import SubdiffusiveProcess.Paper.prop_conc_pair_mask
public import SubdiffusiveProcess.Paper.prop_conc_relative_context
public import SubdiffusiveProcess.Paper.prop_conc_strip_deletion_estimate

@[expose] public section

/-! Deletion cost of a bounded weight supported in a small set: the relative response of the weighted
pair differs from that of the pair by `C G e^{CG}[Δ ν(B) + √(ν(B) ζ(B))]` (relative variation), and by
`C G e^{CG} Δ (K a + √K √a)` when `ν(B) ≤ K a` (the total `ζ`-mass carries `Δ²`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

theorem aux_prop_conc_deletion_cost_mono {C1 C G' G : ℝ} (hC1 : C1 ≤ C) (hC1' : 0 ≤ C1)
    (h0 : 0 ≤ G') (hG : G' ≤ G) : C1 * G' * Real.exp (C1 * G') ≤ C * G * Real.exp (C * G) := by
  have hC : 0 ≤ C := hC1'.trans hC1
  have hG0 : 0 ≤ G := h0.trans hG
  refine mul_le_mul (mul_le_mul hC1 hG h0 hC) (Real.exp_le_exp.mpr (mul_le_mul hC1 hG h0 hC))
    (Real.exp_pos _).le (mul_nonneg hC hG0)

/-- Deletion cost `(30)` for the weighted pair, with `B = strips`, at the level of the limiting forms. -/
theorem prop_conc_deletion_cost (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {d : ℕ} {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
      {m M : ℝ} (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d,
      ∀ (g : SpatialCoordinates d → ℝ), Measurable g →
      ∀ (B : Set (SpatialCoordinates d)), MeasurableSet B →
        B ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      (∀ x, x ∉ B → g x = 0) → ∀ G : ℝ, 0 ≤ G → (∀ x, |g x| ≤ G) →
        |aux_prop_conc_pair_data_theta X c p g -
            aux_prop_conc_pair_data_theta X c p (fun _ => 0)| ≤
          C * G * Real.exp (C * G) *
            ((M - m) * (aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d) B).toReal +
              Real.sqrt ((aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d) B).toReal *
                (aux_prop_conc_pair_data_zeta X (aux_prop_conc_pair_data_slopes d) B).toReal)) ∧
        ∀ K a : ℝ, 0 ≤ K → 0 ≤ a →
          (aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d) B).toReal ≤ K * a →
          |aux_prop_conc_pair_data_theta X c p g -
              aux_prop_conc_pair_data_theta X c p (fun _ => 0)| ≤
            C * G * Real.exp (C * G) * (M - m) *
              (K * a + Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
                ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)) *
                Real.sqrt K * Real.sqrt a) := by
  obtain ⟨C1, hC1, h1⟩ := aux_prop_conc_strip_deletion_estimate_relative_variation_ctx C0 hC0
  obtain ⟨C2, hC2, h2⟩ := prop_conc_strip_deletion_estimate C0 hC0
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
  intro d Q z r hr m M X c hc p hp g hg B hB hBq hsupp G hG0 hG
  have hslopes := aux_prop_conc_pair_data_mem_slopes d
  have hbdd : BddAbove (Set.range fun x => |g x|) := ⟨G, by rintro _ ⟨x, rfl⟩; exact hG x⟩
  have hGlub : IsLUB (Set.range fun x => |g x|) (sSup (Set.range fun x => |g x|)) :=
    isLUB_csSup (Set.range_nonempty _) hbdd
  have hG'le : sSup (Set.range fun x => |g x|) ≤ G :=
    csSup_le (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hG x)
  have hG'0 : 0 ≤ sSup (Set.range fun x => |g x|) :=
    (abs_nonneg (g 0)).trans (le_csSup hbdd ⟨0, rfl⟩)
  let W := Classical.choice (aux_prop_conc_pair_mask_exists X g hg G hG)
  have ctx := prop_conc_relative_context X.hd Q X.hQ z r hr X.hinside X.E X.F X.GammaE X.GammaF
    X.D X.P X.hEc X.hFc C0 m M c X.hC0 X.hm X.hmM X.hM hc X.horder
    (aux_prop_conc_pair_data_slopes d) hslopes X.hDpos g hg B hB hBq hsupp
    (sSup (Set.range fun x => |g x|)) G X.CE X.CF hGlub hbdd W
  have hval : aux_prop_conc_pair_data_theta X c p g - aux_prop_conc_pair_data_theta X c p (fun _ => 0) =
      (W.QFg p - c * W.QEg p) / ∑ i : Fin d, W.QEg (Pi.single i 1) -
        (X.P.QF p - c * X.P.QE p) / ∑ i : Fin d, X.P.QE (Pi.single i 1) := by
    rw [aux_prop_conc_pair_mask_theta_data X W, aux_prop_conc_pair_mask_theta_zero]
  have hnu := aux_prop_conc_pair_mask_nu_toReal' X (aux_prop_conc_pair_data_slopes d) B
  have hze := aux_prop_conc_pair_mask_zeta_toReal X (aux_prop_conc_pair_data_slopes d) B
  have hnu0 : 0 ≤ (aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d) B).toReal :=
    ENNReal.toReal_nonneg
  have hze0 : 0 ≤ (aux_prop_conc_pair_data_zeta X (aux_prop_conc_pair_data_slopes d) B).toReal :=
    ENNReal.toReal_nonneg
  have hgap : 0 ≤ M - m := sub_nonneg.mpr X.hmM
  refine ⟨?_, ?_⟩
  · rw [hval]
    refine (h1 ctx p hp).trans ?_
    beta_reduce
    rw [← hnu, ← hze]
    exact mul_le_mul_of_nonneg_right
      (aux_prop_conc_deletion_cost_mono (le_max_left _ _) hC1.le hG'0 hG'le)
      (add_nonneg (mul_nonneg hgap hnu0) (Real.sqrt_nonneg _))
  · intro K a hK ha hn
    rw [hval]
    have hn' := hn
    rw [hnu] at hn'
    have hs := h2 ctx K a hK ha hn' p hp
    refine hs.trans ?_
    have hnn : 0 ≤ K * a + Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
        ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)) * Real.sqrt K * Real.sqrt a := by
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (aux_prop_conc_deletion_cost_mono (le_max_right _ _) hC2.le hG'0 hG'le) hgap) hnn

end
end SubdiffusiveProcess.Paper
