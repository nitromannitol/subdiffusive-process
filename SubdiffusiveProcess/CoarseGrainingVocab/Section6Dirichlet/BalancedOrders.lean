import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ParameterBalance

/-!
# Fractional-order packaging for the balanced Dirichlet parameters
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization
open Homogenization.Book.Ch03.ABK26

noncomputable section

def dirichletS1Order (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) :
    FractionalOrder :=
  ⟨dirichletS1 vartheta,
    (dirichlet_parameter_orders hvartheta.1 hvartheta.2).1,
    (dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.1.trans
      ((dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.2.1.trans
        (dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.2.2)⟩

def dirichletSOrder (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) :
    FractionalOrder :=
  ⟨dirichletS vartheta,
    (dirichlet_parameter_orders hvartheta.1 hvartheta.2).1.trans
      (dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.1,
    (dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.2.1.trans
      (dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.2.2⟩

def dirichletS2Order (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) :
    FractionalOrder :=
  ⟨dirichletS2 vartheta,
    (dirichlet_parameter_orders hvartheta.1 hvartheta.2).1.trans
      ((dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.1.trans
        (dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.2.1),
    (dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.2.2⟩

@[simp] theorem dirichletS1Order_coe
    (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) :
    (dirichletS1Order vartheta hvartheta : ℝ) = dirichletS1 vartheta := rfl

@[simp] theorem dirichletSOrder_coe
    (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) :
    (dirichletSOrder vartheta hvartheta : ℝ) = dirichletS vartheta := rfl

@[simp] theorem dirichletS2Order_coe
    (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) :
    (dirichletS2Order vartheta hvartheta : ℝ) = dirichletS2 vartheta := rfl

theorem dirichletS1Order_lt_dirichletSOrder
    (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) :
    (dirichletS1Order vartheta hvartheta : ℝ) <
      (dirichletSOrder vartheta hvartheta : ℝ) :=
  (dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.1

theorem dirichletSOrder_lt_dirichletS2Order
    (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) :
    (dirichletSOrder vartheta hvartheta : ℝ) <
      (dirichletS2Order vartheta hvartheta : ℝ) :=
  (dirichlet_parameter_orders hvartheta.1 hvartheta.2).2.2.1

theorem dirichletBalanceScale_pos
    {vartheta delta : ℝ} (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    0 < dirichletBalanceScale vartheta delta := by
  rw [dirichletBalanceScale, Nat.ceil_pos]
  unfold dirichletBalanceArgument
  have hinv : 1 < delta⁻¹ := (one_lt_inv₀ hdelta).2 hdeltaOne
  have hlog : 0 < Real.logb 3 delta⁻¹ :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 3) hinv
  have hden : 0 < dirichletS1 vartheta + dirichletS2 vartheta := by
    obtain ⟨hs1, _, _, _⟩ :=
      dirichlet_parameter_orders hvartheta.1 hvartheta.2
    have hs2 : 0 < dirichletS2 vartheta := by
      unfold dirichletS2
      norm_num
    linarith
  exact div_pos hlog hden

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
