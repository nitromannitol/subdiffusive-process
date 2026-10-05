module

public import SubdiffusiveProcess.Variational.DualEnergy

@[expose] public section

open Filter Set
open scoped Topology

/-! Parallelogram and scalar identities for the literal extended dual energy. -/
namespace SubdiffusiveProcess

theorem quadraticDual_parallelogram
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : H, 0 ≤ inner ℝ x (G x)) (u v : H) :
    (⨆ f : H, ((2 * inner ℝ f (u + v) - inner ℝ f (G f) : ℝ) : EReal)) +
      (⨆ f : H, ((2 * inner ℝ f (u - v) - inner ℝ f (G f) : ℝ) : EReal)) =
      (2 : EReal) * (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) +
        (2 : EReal) * (⨆ f : H, ((2 * inner ℝ f v - inner ℝ f (G f) : ℝ) : EReal)) := by
  let q : H → H → ℝ := fun f x => 2 * inner ℝ f x - inner ℝ f (G f)
  have sup_add_sup (a b : H → ℝ) :
      (⨆ i : H, ((a i : ℝ) : EReal)) + (⨆ j : H, ((b j : ℝ) : EReal)) =
        ⨆ i : H, ⨆ j : H, (((a i + b j : ℝ) : EReal)) := by
    apply le_antisymm
    · refine EReal.add_le_of_forall_lt fun a ha b hb => ?_
      obtain ⟨f, hf⟩ := lt_iSup_iff.mp ha
      obtain ⟨g, hg⟩ := lt_iSup_iff.mp hb
      exact (add_le_add hf.le hg.le).trans <|
        le_iSup_of_le f (le_iSup_of_le g (by rw [EReal.coe_add]))
    · refine iSup_le fun f => iSup_le fun g => ?_
      rw [EReal.coe_add]
      exact add_le_add (le_iSup (fun i : H => ((a i : ℝ) : EReal)) f)
        (le_iSup (fun j : H => ((b j : ℝ) : EReal)) g)
  have supPair_add_supPair (a b : H → H → ℝ) :
      (⨆ i : H, ⨆ j : H, ((a i j : ℝ) : EReal)) +
          (⨆ k : H, ⨆ l : H, ((b k l : ℝ) : EReal)) =
        ⨆ i : H, ⨆ j : H, ⨆ k : H, ⨆ l : H,
          (((a i j + b k l : ℝ) : EReal)) := by
    apply le_antisymm
    · refine EReal.add_le_of_forall_lt fun x hx y hy => ?_
      obtain ⟨i, hi⟩ := lt_iSup_iff.mp hx
      obtain ⟨j, hj⟩ := lt_iSup_iff.mp hi
      obtain ⟨k, hk⟩ := lt_iSup_iff.mp hy
      obtain ⟨l, hl⟩ := lt_iSup_iff.mp hk
      exact (add_le_add hj.le hl.le).trans <| le_iSup_of_le i <|
        le_iSup_of_le j <| le_iSup_of_le k <| le_iSup_of_le l (by rw [EReal.coe_add])
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun k => iSup_le fun l => ?_
      rw [EReal.coe_add]
      exact add_le_add (le_iSup_of_le i (le_iSup (fun j : H => ((a i j : ℝ) : EReal)) j))
        (le_iSup_of_le k (le_iSup (fun l : H => ((b k l : ℝ) : EReal)) l))
  have hforward (f g : H) :
      q f (u + v) + q g (u - v) =
        2 * q ((2 : ℝ)⁻¹ • (f + g)) u + 2 * q ((2 : ℝ)⁻¹ • (f - g)) v := by
    have hcross : inner ℝ f (G g) = inner ℝ g (G f) := by
      rw [← real_inner_comm, hsym g f]
    dsimp [q]
    simp only [map_smul, map_add, map_sub]
    simp only [inner_add_left, inner_sub_left, inner_add_right, inner_sub_right,
      inner_smul_left, inner_smul_right, real_inner_comm]
    rw [hcross]
    norm_num [starRingEnd_apply]
    ring
  have hbackward (f g : H) :
      2 * q f u + 2 * q g v = q (f + g) (u + v) + q (f - g) (u - v) := by
    have hcross : inner ℝ f (G g) = inner ℝ g (G f) := by
      rw [← real_inner_comm, hsym g f]
    dsimp [q]
    rw [map_add, map_sub]
    simp only [inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
    rw [hcross]
    ring
  have hmidpoint (f g x : H) :
      q f x + q g x ≤ 2 * q ((2 : ℝ)⁻¹ • (f + g)) x := by
    have hcross : inner ℝ f (G g) = inner ℝ g (G f) := by
      rw [← real_inner_comm, hsym g f]
    have hp := hpos (f - g)
    dsimp [q]
    rw [map_sub] at hp
    simp only [inner_sub_left, inner_sub_right] at hp
    simp only [map_smul, map_add, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right]
    rw [hcross]
    norm_num [starRingEnd_apply]
    linarith
  have htwo (x : EReal) : (2 : EReal) * x = x + x := by
    cases x with
    | bot => exact EReal.mul_bot_of_pos (by norm_num)
    | top => exact EReal.mul_top_of_pos (by norm_num)
    | coe x =>
        calc
          (2 : EReal) * (x : EReal) = (((2 : ℝ) * x : ℝ) : EReal) :=
            (EReal.coe_mul 2 x).symm
          _ = (((x + x : ℝ)) : EReal) := congrArg Real.toEReal (by ring)
  rw [show (⨆ f : H, ((2 * inner ℝ f (u + v) - inner ℝ f (G f) : ℝ) : EReal)) =
      ⨆ f : H, ((q f (u + v) : ℝ) : EReal) by rfl]
  rw [show (⨆ f : H, ((2 * inner ℝ f (u - v) - inner ℝ f (G f) : ℝ) : EReal)) =
      ⨆ f : H, ((q f (u - v) : ℝ) : EReal) by rfl]
  rw [show (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) =
      ⨆ f : H, ((q f u : ℝ) : EReal) by rfl]
  rw [show (⨆ f : H, ((2 * inner ℝ f v - inner ℝ f (G f) : ℝ) : EReal)) =
      ⨆ f : H, ((q f v : ℝ) : EReal) by rfl]
  calc
    _ = ⨆ f : H, ⨆ g : H, ((q f (u + v) + q g (u - v) : ℝ) : EReal) :=
      sup_add_sup (fun f : H => q f (u + v)) (fun f : H => q f (u - v))
    _ = _ := by
      rw [htwo (⨆ f : H, ((q f u : ℝ) : EReal)),
        htwo (⨆ f : H, ((q f v : ℝ) : EReal)),
        sup_add_sup (fun f : H => q f u) (fun f : H => q f u),
        sup_add_sup (fun f : H => q f v) (fun f : H => q f v),
        supPair_add_supPair (fun i j : H => q i u + q j u)
          (fun k l : H => q k v + q l v)]
      apply le_antisymm
      · refine iSup_le fun f => iSup_le fun g => ?_
        rw [hforward]
        exact le_iSup_of_le ((2 : ℝ)⁻¹ • (f + g)) <|
          le_iSup_of_le ((2 : ℝ)⁻¹ • (f + g)) <|
          le_iSup_of_le ((2 : ℝ)⁻¹ • (f - g)) <|
          le_iSup_of_le ((2 : ℝ)⁻¹ • (f - g)) <| by
            rw [EReal.coe_le_coe_iff]
            ring_nf
            exact le_rfl
      · refine iSup_le fun i => iSup_le fun j => iSup_le fun k => iSup_le fun l => ?_
        let a := (2 : ℝ)⁻¹ • (i + j)
        let b := (2 : ℝ)⁻¹ • (k + l)
        exact le_iSup_of_le (a + b) <| le_iSup_of_le (a - b) <| by
          rw [EReal.coe_le_coe_iff, ← hbackward a b]
          have hu : q i u + q j u ≤ 2 * q a u := hmidpoint i j u
          have hv : q k v + q l v ≤ 2 * q b v := hmidpoint k l v
          linarith

theorem quadraticDual_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H) (hpos : ∀ x : H, 0 ≤ inner ℝ x (G x))
    (r : ℝ) (u : H) :
    (⨆ f : H, ((2 * inner ℝ f (r • u) - inner ℝ f (G f) : ℝ) : EReal)) =
      ((r ^ 2 : ℝ) : EReal) *
        (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) := by
  by_cases hr : r = 0
  · subst r
    have hzero :
        (⨆ f : H, ((2 * inner ℝ f (0 • u) - inner ℝ f (G f) : ℝ) : EReal)) = 0 := by
      apply le_antisymm
      · refine iSup_le fun f => ?_
        rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
        simpa only [zero_smul, inner_zero_right, mul_zero, zero_sub] using neg_nonpos.mpr (hpos f)
      · refine le_iSup_of_le (0 : H) ?_
        simp only [zero_smul, inner_zero_right, map_zero, mul_zero, sub_zero,
          EReal.coe_zero, le_refl]
    simpa only [zero_smul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), EReal.coe_zero,
      zero_mul] using hzero
  · have hr2 : 0 < ((r ^ 2 : ℝ) : EReal) := by
      rw [EReal.coe_pos]
      exact sq_pos_of_ne_zero hr
    have hr2_ne : ((r ^ 2 : ℝ) : EReal) ≠ 0 := hr2.ne'
    have hcancel (x : EReal) :
        (((r ^ 2 : ℝ) : EReal) * x) / ((r ^ 2 : ℝ) : EReal) = x := by
      rw [EReal.mul_comm ((r ^ 2 : ℝ) : EReal) x, ← EReal.mul_div_right,
        EReal.div_mul_cancel (EReal.coe_ne_bot _) (EReal.coe_ne_top _) hr2_ne]
    let scale : EReal ≃o EReal :=
      { toFun := fun x => ((r ^ 2 : ℝ) : EReal) * x
        invFun := fun x => x / ((r ^ 2 : ℝ) : EReal)
        left_inv := by
          intro x
          dsimp
          exact hcancel x
        right_inv := by
          intro x
          dsimp
          exact EReal.mul_div_cancel (EReal.coe_ne_bot _) (EReal.coe_ne_top _) hr2_ne
        map_rel_iff' := by
          intro x y
          constructor
          · intro hxy
            change ((r ^ 2 : ℝ) : EReal) * x ≤ ((r ^ 2 : ℝ) : EReal) * y at hxy
            have hdiv := EReal.div_le_div_right_of_nonneg hr2.le hxy
            rw [hcancel x, hcancel y] at hdiv
            exact hdiv
          · intro hxy
            exact mul_le_mul_of_nonneg_left hxy hr2.le }
    let e : H ≃ H := Equiv.smulRight hr
    have hreindex :
        (⨆ f : H, ((2 * inner ℝ f (r • u) - inner ℝ f (G f) : ℝ) : EReal)) =
          ⨆ f : H,
            ((2 * inner ℝ (e f) (r • u) - inner ℝ (e f) (G (e f)) : ℝ) : EReal) := by
      exact (e.iSup_comp (g := fun f : H =>
        ((2 * inner ℝ f (r • u) - inner ℝ f (G f) : ℝ) : EReal))).symm
    rw [hreindex]
    calc
      (⨆ f : H,
          ((2 * inner ℝ (e f) (r • u) - inner ℝ (e f) (G (e f)) : ℝ) : EReal)) =
          ⨆ f : H, ((r ^ 2 : ℝ) : EReal) *
            ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) := by
              apply iSup_congr
              intro f
              rw [← EReal.coe_mul]
              congr 1
              dsimp [e, Equiv.smulRight]
              simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
              ring
      _ = ((r ^ 2 : ℝ) : EReal) *
          (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) := by
            change (⨆ f : H, scale
              ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) =
              scale (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal))
            exact (scale.map_iSup _).symm

end SubdiffusiveProcess
