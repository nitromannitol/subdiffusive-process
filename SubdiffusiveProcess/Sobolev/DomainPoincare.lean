import SubdiffusiveProcess.Sobolev.NativeH10
import SubdiffusiveProcess.Sobolev.MeanZero
import Homogenization.Sobolev.Foundations.PoincareZeroTrace
import Homogenization.Sobolev.Foundations.PoincareMeanZero

/-! # Poincare inequalities on the local Sobolev graphs

The native bounded-convex-domain inequalities transfer through the proved
H1 and H10 representatives. The finite-dimensional norm comparison supplies
a dimension factor while keeping each constant before the function.
-/

open MeasureTheory Set TopologicalSpace
open scoped NNReal

namespace SubdiffusiveProcess

/-- Native Poincare produces both constants on the actual local graph carriers. -/
theorem exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] (Ω : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hΩ : Homogenization.IsOpenBoundedConvexDomain
      (Ω : Set (SpatialCoordinates d))) :
    (∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph Ω) u‖) ∧
    (∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖) := by
  have hnativeD :=
    Homogenization.H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
      (U := (Ω : Set (SpatialCoordinates d))) hΩ
  have hnativeN :=
    Homogenization.exists_poincare_constant_of_isOpenBoundedConvexDomain
      (U := (Ω : Set (SpatialCoordinates d))) hΩ
  rcases hnativeD with ⟨CD, hCD, hCD_bound⟩
  rcases hnativeN with ⟨CN, hCN, hCN_bound⟩
  have hcoord_bridge : ∀ {V : Submodule ℝ (SobolevData Ω)}
      (u : V) (v : Homogenization.H1Function (Ω : Set (SpatialCoordinates d))),
      v.grad = (fun x i => (u : SobolevData Ω).2 i x) →
      ∀ i : Fin d, v.gradCoordToScalarL2 i = (u : SobolevData Ω).2 i := by
    intro V u v hv i
    apply Lp.ext
    filter_upwards [v.coeFn_gradCoordToScalarL2 i] with x hx
    rw [hx]
    exact congrFun (congrFun hv x) i
  have hvalue_bridge : ∀ {V : Submodule ℝ (SobolevData Ω)}
      (u : V) (v : Homogenization.H1Function (Ω : Set (SpatialCoordinates d))),
      (v : SpatialCoordinates d → ℝ) = (fun x => (u : SobolevData Ω).1 x) →
      v.toScalarL2 = (u : SobolevData Ω).1 := by
    intro V u v hv
    apply Lp.ext
    filter_upwards [v.coeFn_toScalarL2] with x hx
    rw [hx]
    exact congrFun hv x
  have hsum_local : ∀ {V : Submodule ℝ (SobolevData Ω)} (u : V),
      (∑ i : Fin d, ‖(u : SobolevData Ω).2 i‖) ≤
        (d : ℝ) * ‖subspaceGradient V u‖ := by
    intro V u
    calc
      (∑ i : Fin d, ‖(u : SobolevData Ω).2 i‖) =
          ∑ i : Fin d, ‖subspaceGradient V u i‖ := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ ≤ ∑ _i : Fin d, ‖subspaceGradient V u‖ := by
            exact Finset.sum_le_sum fun i _ => PiLp.norm_apply_le
              (subspaceGradient V u) i
      _ = (d : ℝ) * ‖subspaceGradient V u‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnative_vector_le_local : ∀ {V : Submodule ℝ (SobolevData Ω)}
      (u : V) (v : Homogenization.H1Function (Ω : Set (SpatialCoordinates d))),
      v.grad = (fun x i => (u : SobolevData Ω).2 i x) →
      ‖v.gradToVectorL2‖ ≤
        (d : ℝ) * ‖subspaceGradient V u‖ := by
    intro V u v hv
    let D : SpatialCoordinates d → ℝ := fun x => ∑ i : Fin d, ‖v.grad x i‖
    have hDi : ∀ i : Fin d,
        MemLp (fun x => ‖v.grad x i‖) 2
          (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
      intro i
      exact (v.grad_memL2 i).norm
    have hD : MemLp D 2
          (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
      have hs := MeasureTheory.memLp_finset_sum
        (μ := volume.restrict (Ω : Set (SpatialCoordinates d)))
        (p := (2 : ENNReal)) (s := Finset.univ)
        (f := fun i : Fin d => fun x => ‖v.grad x i‖)
        (fun i hi => hDi i)
      simpa [D] using hs
    let gLp : Lp (SpatialCoordinates d) 2
          (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
      v.grad_memVectorL2.toLp v.grad
    let dLp : Lp ℝ 2
          (volume.restrict (Ω : Set (SpatialCoordinates d))) := hD.toLp D
    have hpoint : ∀ x : SpatialCoordinates d,
        ‖v.grad x‖ ≤ D x := by
      intro x
      have hnonneg : 0 ≤ ∑ i : Fin d, ‖v.grad x i‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      apply (pi_norm_le_iff_of_nonneg hnonneg).2
      intro i
      exact Finset.single_le_sum (fun j _ => norm_nonneg (v.grad x j))
        (Finset.mem_univ i)
    have hnorm : ‖gLp‖ ≤ ‖dLp‖ := by
      refine MeasureTheory.Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [MemLp.coeFn_toLp v.grad_memVectorL2,
        MemLp.coeFn_toLp hD] with x hxg hxd
      rw [hxg, hxd]
      have hDx : 0 ≤ D x := by
        exact Finset.sum_nonneg fun i _ => norm_nonneg (v.grad x i)
      simpa [Real.norm_eq_abs, abs_of_nonneg hDx] using hpoint x
    have hsum_norm : ‖dLp‖ ≤ ∑ i : Fin d, ‖v.gradCoordToScalarL2 i‖ := by
      have hsum_eLp : eLpNorm D 2
            (volume.restrict (Ω : Set (SpatialCoordinates d))) ≤
          ∑ i : Fin d, eLpNorm (fun x => ‖v.grad x i‖) 2
            (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
        have hDsum : D = ∑ i : Fin d, fun x => ‖v.grad x i‖ := by
          funext x
          simp [D]
        rw [hDsum]
        simpa using (MeasureTheory.eLpNorm_sum_le
          (μ := volume.restrict (Ω : Set (SpatialCoordinates d)))
          (s := Finset.univ) (f := fun i : Fin d => fun x => ‖v.grad x i‖)
          (fun i hi => (hDi i).1) (by norm_num : (1 : ENNReal) ≤ 2))
      calc
        ‖dLp‖ = ENNReal.toReal (eLpNorm D 2
            (volume.restrict (Ω : Set (SpatialCoordinates d)))) := by
              simp [dLp]
        _ ≤ ENNReal.toReal (∑ i : Fin d, eLpNorm
              (fun x => ‖v.grad x i‖) 2
                (volume.restrict (Ω : Set (SpatialCoordinates d)))) := by
              exact ENNReal.toReal_mono
                (ENNReal.sum_ne_top.2 fun i _ => (hDi i).2.ne) hsum_eLp
        _ = ∑ i : Fin d, ‖v.gradCoordToScalarL2 i‖ := by
              rw [ENNReal.toReal_sum (fun i hi => (hDi i).2.ne)]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Homogenization.H1Function.gradCoordToScalarL2,
                Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]
              rw [MeasureTheory.eLpNorm_norm]
    have hcoord_eq : ∀ i : Fin d,
        ‖v.gradCoordToScalarL2 i‖ = ‖(u : SobolevData Ω).2 i‖ := by
      intro i
      rw [hcoord_bridge u v hv i]
    calc
      ‖v.gradToVectorL2‖ = ‖gLp‖ := by rfl
      _ ≤ ‖dLp‖ := hnorm
      _ ≤ ∑ i : Fin d, ‖v.gradCoordToScalarL2 i‖ := hsum_norm
      _ = ∑ i : Fin d, ‖(u : SobolevData Ω).2 i‖ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hcoord_eq i]
      _ ≤ (d : ℝ) * ‖subspaceGradient V u‖ := hsum_local u
  constructor
  · let K : ℝ≥0 := Real.toNNReal (CD * d)
    have hK : (K : ℝ) = CD * d := by
      dsimp [K]
      exact max_eq_left (mul_nonneg hCD (Nat.cast_nonneg d))
    refine ⟨K, ?_⟩
    intro u
    rcases exists_nativeH10Function_of_killedSobolevGraph u with
      ⟨v, hv_val, hv_grad⟩
    have hval := hvalue_bridge u v.toH1Function hv_val
    have hcoord := hcoord_bridge u v.toH1Function hv_grad
    have hbase := hCD_bound v
    have hsum : v.toH1Function.gradientCoordL2NormSum =
        ∑ i : Fin d, ‖(u : SobolevData Ω).2 i‖ := by
      simp only [Homogenization.H1Function.gradientCoordL2NormSum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoord i]
    calc
      ‖(u : SobolevData Ω).1‖ = ‖v.toH1Function.toScalarL2‖ := by
        rw [hval]
      _ ≤ CD * v.toH1Function.gradientCoordL2NormSum := hbase
      _ = CD * ∑ i : Fin d, ‖(u : SobolevData Ω).2 i‖ := by rw [hsum]
      _ ≤ CD * ((d : ℝ) * ‖subspaceGradient (killedSobolevGraph Ω) u‖) := by
        exact mul_le_mul_of_nonneg_left (hsum_local u) hCD
      _ = K * ‖subspaceGradient (killedSobolevGraph Ω) u‖ := by
        rw [show (K : ℝ) = CD * d from hK]
        ring
  · let K : ℝ≥0 := Real.toNNReal (CN * d)
    have hK : (K : ℝ) = CN * d := by
      dsimp [K]
      exact max_eq_left (mul_nonneg hCN (Nat.cast_nonneg d))
    refine ⟨K, ?_⟩
    intro u
    have hu := (mem_meanZeroSobolevGraph_iff (u : SobolevData Ω)).mp u.property
    rcases exists_nativeH1Function_of_weakSobolevGraph
        (⟨u.val, hu.1⟩) with ⟨v, hv_val, hv_grad⟩
    have hmean : Homogenization.MeanZeroOn
        (Ω : Set (SpatialCoordinates d)) v.toFun := by
      unfold Homogenization.MeanZeroOn
      rw [hv_val]
      exact hu.2
    let w : Homogenization.H1MeanZeroFunction
        (Ω : Set (SpatialCoordinates d)) := ⟨v, hmean⟩
    have hval := hvalue_bridge u v hv_val
    have hgrad := hnative_vector_le_local u v hv_grad
    have hbase := hCN_bound w
    calc
      ‖(u : SobolevData Ω).1‖ = w.valueL2Norm := by
        change ‖(u : SobolevData Ω).1‖ = ‖v.toScalarL2‖
        rw [hval]
      _ ≤ CN * w.gradientL2Norm := hbase
      _ ≤ CN * ((d : ℝ) * ‖subspaceGradient
          (meanZeroSobolevGraph Ω) u‖) := by
        exact mul_le_mul_of_nonneg_left (by
          simpa [w, Homogenization.H1MeanZeroFunction.gradientL2Norm] using hgrad) hCN
      _ = K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖ := by
        rw [show (K : ℝ) = CN * d from hK]
        ring

end SubdiffusiveProcess
