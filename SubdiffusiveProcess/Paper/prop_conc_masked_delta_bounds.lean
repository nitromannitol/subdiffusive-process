import SubdiffusiveProcess.Paper.prop_conc_pair_mask
import SubdiffusiveProcess.Paper.prop_conc_relative_context
import SubdiffusiveProcess.Paper.prop_conc_relative_total_mass
import SubdiffusiveProcess.Paper.prop_conc_masked_core_mass

/-! Mass bounds of the masked measures: the common form order bounds the total normalized masses
`ν̂(q) ≤ C` and `ζ̂(q) ≤ CΔ²` (for every pair, in particular every masked pair), and the core masses of
the masked measure are controlled by the core and strip masses of the original one. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- `ν̂(q) ≤ C`, `ζ̂(q) ≤ CΔ²` and `ν̂(A) ≤ C e^{CG}(ν(A) + ν(B))` for the masked measures. -/
theorem prop_conc_masked_delta_bounds (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
      {m M : ℝ} (X : prop_conc_pair_data Q z r hr C0 m M),
      (∀ Y : prop_conc_pair_data Q z r hr C0 m M,
        (aux_prop_conc_pair_data_nu Y (aux_prop_conc_pair_data_slopes d)
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤ C ∧
          (aux_prop_conc_pair_data_zeta Y (aux_prop_conc_pair_data_slopes d)
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤ C * (M - m) ^ 2) ∧
      ∀ (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K)
        (B : Set (SpatialCoordinates d)), MeasurableSet B →
          B ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        (∀ x, x ∉ B → g x = 0) → ∀ G : ℝ, 0 ≤ G → (∀ x, |g x| ≤ G) →
        ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          A ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          (aux_prop_conc_pair_data_nu (aux_prop_conc_pair_mask_pair X g hg K hK)
              (aux_prop_conc_pair_data_slopes d) A).toReal ≤
            C * Real.exp (C * G) *
              ((aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d) A).toReal +
                (aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d) B).toReal) := by
  obtain ⟨C1, hC1, h1⟩ := prop_conc_masked_core_mass C0 hC0
  let A0 : ℝ := (2 : ℝ) ^ d * ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2
  have hA0 : 0 ≤ A0 := by positivity
  refine ⟨max C1 ((1 + C0 ^ 2) * A0 + 1), lt_max_of_lt_left hC1, ?_⟩
  intro Q z r hr m M X
  have hslopes := aux_prop_conc_pair_data_mem_slopes d
  refine ⟨?_, ?_⟩
  · intro Y
    have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      (centeredCube z r hr).isOpen.measurableSet
    have hbdd : BddAbove (Set.range fun x : SpatialCoordinates d => |(fun _ => (0 : ℝ)) x|) :=
      ⟨0, by rintro _ ⟨x, rfl⟩; simp⟩
    have hGlub : IsLUB (Set.range fun x : SpatialCoordinates d => |(fun _ => (0 : ℝ)) x|) 0 := by
      have : (Set.range fun x : SpatialCoordinates d => |(fun _ => (0 : ℝ)) x|) = {0} := by
        ext y; simp
      rw [this]; exact isLUB_singleton
    let W := Classical.choice (aux_prop_conc_pair_mask_exists Y (fun _ => 0) measurable_const 0
      (by intro x; simp))
    have ctx := prop_conc_relative_context Y.hd Q Y.hQ z r hr Y.hinside Y.E Y.F Y.GammaE Y.GammaF
      Y.D Y.P Y.hEc Y.hFc C0 m M m Y.hC0 Y.hm Y.hmM Y.hM ⟨le_rfl, Y.hmM⟩ Y.horder
      (aux_prop_conc_pair_data_slopes d) hslopes Y.hDpos (fun _ => 0) measurable_const _ hq
      subset_rfl (fun x _ => rfl) 0 0 Y.CE Y.CF hGlub hbdd W
    obtain ⟨hnu, hze⟩ := prop_conc_relative_total_mass ctx
    have hnu' := aux_prop_conc_pair_mask_nu_toReal' Y (aux_prop_conc_pair_data_slopes d)
      (centeredCube z r hr : Set (SpatialCoordinates d))
    have hze' := aux_prop_conc_pair_mask_zeta_toReal Y (aux_prop_conc_pair_data_slopes d)
      (centeredCube z r hr : Set (SpatialCoordinates d))
    have hnu2 : (aux_prop_conc_pair_data_nu Y (aux_prop_conc_pair_data_slopes d)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤ (1 + C0 ^ 2) * A0 := by
      rw [hnu']; exact hnu
    have hze2 : (aux_prop_conc_pair_data_zeta Y (aux_prop_conc_pair_data_slopes d)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤ (C0 ^ 2 * A0) * (M - m) ^ 2 := by
      rw [hze']; exact hze
    refine ⟨hnu2.trans (le_max_of_le_right (by linarith)), hze2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_of_le_right (by nlinarith [sq_nonneg C0]))
      (sq_nonneg _)
  · intro g hg K hK B hB hBq hsupp G hG0 hG A hA hAq
    have hbdd : BddAbove (Set.range fun x => |g x|) := ⟨G, by rintro _ ⟨x, rfl⟩; exact hG x⟩
    have hGlub : IsLUB (Set.range fun x => |g x|) (sSup (Set.range fun x => |g x|)) :=
      isLUB_csSup (Set.range_nonempty _) hbdd
    have hG'le : sSup (Set.range fun x => |g x|) ≤ G :=
      csSup_le (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hG x)
    have hG'0 : 0 ≤ sSup (Set.range fun x => |g x|) :=
      (abs_nonneg (g 0)).trans (le_csSup hbdd ⟨0, rfl⟩)
    let W := Classical.choice (aux_prop_conc_pair_mask_exists X g hg K hK)
    have hmc : m ∈ Set.Icc m M := ⟨le_rfl, X.hmM⟩
    have ctx := prop_conc_relative_context X.hd Q X.hQ z r hr X.hinside X.E X.F X.GammaE X.GammaF
      X.D X.P X.hEc X.hFc C0 m M m X.hC0 X.hm X.hmM X.hM hmc X.horder
      (aux_prop_conc_pair_data_slopes d) hslopes X.hDpos g hg B hB hBq hsupp
      (sSup (Set.range fun x => |g x|)) K X.CE X.CF hGlub hbdd W
    have hmass := h1 ctx A hA hAq
    have hnn : 0 ≤ (aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d) A).toReal +
        (aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d) B).toReal :=
      add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    refine hmass.trans ?_
    have hCmax : C1 ≤ max C1 ((1 + C0 ^ 2) * A0 + 1) := le_max_left _ _
    have hmono : C1 * Real.exp (C1 * sSup (Set.range fun x => |g x|)) ≤
        max C1 ((1 + C0 ^ 2) * A0 + 1) * Real.exp (max C1 ((1 + C0 ^ 2) * A0 + 1) * G) :=
      mul_le_mul hCmax (Real.exp_le_exp.mpr (mul_le_mul hCmax hG'le hG'0 (hC1.le.trans hCmax)))
        (Real.exp_pos _).le (hC1.le.trans hCmax)
    exact mul_le_mul_of_nonneg_right hmono hnn

end
end Paper
