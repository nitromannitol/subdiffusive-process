module

public import SubdiffusiveProcess.Paper.gcat_array_pair_chain

@[expose] public section

open Filter MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_gcat_mass_grid_chain_prefix {A B : Type*}
    (F : (n : ℕ) → (Fin n → A) → B) (J n : ℕ) (hn : n ≤ J) (pi : Fin J → A) :
    F ((List.ofFn pi).take n).length ((List.ofFn pi).take n).get =
      F n (fun i => pi ⟨i.val, lt_of_lt_of_le i.isLt hn⟩) := by
  have hl : ((List.ofFn pi).take n).length = n := by
    simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hn]
  generalize hls : (List.ofFn pi).take n = l at hl ⊢
  subst n
  congr 1
  funext i
  have hh := congrArg (fun q : List A => q[i.val]?) hls
  have hiJ : i.val < J := lt_of_lt_of_le i.isLt hn
  simpa only [List.getElem?_take, List.getElem?_ofFn, if_pos i.isLt, if_pos hiJ, dif_pos hiJ,
    List.getElem?_eq_getElem i.isLt, Option.some.injEq, List.get_eq_getElem] using hh.symm



theorem gcat_mass_grid_prefix {A B : Type*}
    (F : (n : ℕ) → (Fin n → A) → B) (J n : ℕ) (hn : n ≤ J) (pi : Fin J → A) :
    F ((List.ofFn pi).take n).length ((List.ofFn pi).take n).get =
      F n (fun i => pi ⟨i.val, lt_of_lt_of_le i.isLt hn⟩) :=
  aux_gcat_mass_grid_chain_prefix F J n hn pi

end Paper
