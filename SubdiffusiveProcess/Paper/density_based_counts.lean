module

public import SubdiffusiveProcess.Paper.density_based_tree
public import SubdiffusiveProcess.Paper.density_shifted_chain_counts
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- The same array count controls every absolute-grid base tree simultaneously.
The base mesh can consequently be chosen after the environment and source. -/
theorem density_based_counts {d : ℕ} (hd : 1 ≤ d) (H1 : ℕ) (hH1 : 0 < H1)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    {Field Ω : Type} [MeasurableSpace Field] [MeasurableSpace Ω]
    (mu : Measure Field) (P : Measure Ω) (field : Ω → Field)
    (hfield : MeasurePreserving field P mu)
    (Good : aux_goodext_admissible_grid_cells z0 R hR → Set Field)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hChain : ∀ (active : List (Fin d → Fin (3 ^ H1)) → Prop)
      (index : List (Fin d → Fin (3 ^ H1)) → aux_goodext_admissible_grid_cells z0 R hR),
      (∀ w, active w → (index w).val.1 = H1 * w.length) →
      ∃ B : Field → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
        ∀ᵐ omega ∂mu, ∀ (J : ℕ) (pi : Fin J → (Fin d → Fin (3 ^ H1))), 1 ≤ J →
          (Set.ncard {i : Fin J | ¬ (active ((List.ofFn pi).take (i.val + 1)) →
            omega ∈ Good (index ((List.ofFn pi).take (i.val + 1))))} : ℝ) ≤
              theta * (J : ℝ) + B omega) :
    let Roots := ℕ × (Fin d → ℤ)
    let zroot := fun b : Roots => fun i => z0 i + (3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ)) * (b.2 i : ℝ)
    let active := fun (b : Roots) => aux_density_based_tree_active H1 b.1 z0 R hR (zroot b)
    ∃ (index : Roots → List (OddGridIndex d (subdivisionHalfWidth H1)) →
        aux_goodext_admissible_grid_cells z0 R hR) (B : Roots → Ω → ℝ),
      (∀ b, Measurable (B b) ∧ ∀ omega, 0 ≤ B b omega) ∧
      (∀ b w, active b w → (index b w).val.1 = H1 * (b.1 + w.length) ∧
        aux_goodext_admissible_grid_centre z0 (index b w).val =
          descendantCenter (subdivisionHalfWidth H1) (zroot b)
            ((3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ))) w.length w.get) ∧
      (∀ (b : Roots) (n : ℕ) (w : Fin (n + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
        aux_lem_finite_stopping_partition_padLabel 3 (w (Fin.last n)) →
        (descendantCell (subdivisionHalfWidth H1) (zroot b)
          (zpow_pos (by norm_num : (0 : ℝ) < 3) (-((H1 * b.1 : ℕ) : ℤ)))
          n (fun i => w i.castSucc) : Set (SpatialCoordinates d)) ⊆
            (centeredCube z0 R hR : Set (SpatialCoordinates d)) →
        active b (List.ofFn w)) ∧
      ∀ᵐ omega ∂P, ∀ (b : Roots) (J : ℕ) (w : Fin J → OddGridIndex d (subdivisionHalfWidth H1)),
        (Set.ncard {i : Fin J | ¬ (active b ((List.ofFn w).take (i.val + 1)) →
          field omega ∈ Good (index b ((List.ofFn w).take (i.val + 1))))} : ℝ) ≤
            theta * (J : ℝ) + B b omega := by
  classical
  intro Roots zroot active
  choose index hIndex hPad using fun b : Roots =>
    density_based_tree hd H1 b.1 hH1 z0 R hR (zroot b) b.2 rfl
  rw [← two_mul_subdivisionHalfWidth_add_one H1] at hChain
  have hCount := density_shifted_chain_counts mu P field hfield Good
    (fun b => b.val.1) H1 theta htheta hChain (fun b : Roots => b.1) active index
    (fun b w hw => (hIndex b w hw).1)
  obtain ⟨B, hBm, hB⟩ := hCount
  exact ⟨index, B, hBm, hIndex, hPad, hB⟩
end SubdiffusiveProcess.Paper
