import SubdiffusiveProcess.Geometry.TriadicShellPacking

/-!
# Cost of the leaves: boundary-layer counting by volume

Leaves at a depth `J > J0` are grid cells of depth `J` inside the shell of their parent
(whose closure meets the boundary). Their number is bounded through disjointness and the
shell volume; summing `side^s` over the depths gives a convergent geometric series.
-/
open Set MeasureTheory Metric
noncomputable section
namespace SubdiffusiveProcess
attribute [local instance] Classical.propDecidable
variable {d : ℕ}
variable (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)

/-- The number of leaves of depth `J`. -/
def triadicLeafCount (S : Set (SpatialCoordinates d)) (J0 n J : ℕ) : ℕ :=
  ((Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
    (fun k => TriadicIsLeaf z R hR S J0 n ⟨J, k⟩)).card

/-- The deep-layer constant of the cost bound. -/
def triadicDeepConst (d : ℕ) (s : ℝ) : ℝ :=
  12 * d * 2 ^ (d - 1) * ((3 : ℝ) ^ (-(s - d + 1)) / (1 - (3 : ℝ) ^ (-(s - d + 1))))

/-- The initial-layer constant of the local cost bound. -/
def triadicBaseConst (d : ℕ) (s : ℝ) (m : ℕ) : ℝ :=
  2 ^ d * max 1 ((1 / (12 * (3 : ℝ) ^ m)) ^ (s - d))

theorem triadicLeaves_sum (S : Set (SpatialCoordinates d)) (J0 n : ℕ)
    (g : TriadicGridLabel d → ℝ) :
    ∑ ℓ ∈ triadicLeaves z R hR S J0 n, g ℓ =
      ∑ J ∈ Finset.range (J0 + n + 1),
        ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
          (fun k => TriadicIsLeaf z R hR S J0 n ⟨J, k⟩), g ⟨J, k⟩ := by
  unfold triadicLeaves
  rw [Finset.sum_filter, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.sum_filter]

/-- Splitting a sum over `range (J0 + n + 1)` at the depth `J0`. -/
theorem triadicPart_range_split_sum (f : ℕ → ℝ) (J0 n : ℕ) :
    ∑ J ∈ Finset.range (J0 + n + 1), f J =
      ∑ J ∈ Finset.range J0, f J + f J0 + ∑ J ∈ Finset.Ioc J0 (J0 + n), f J := by
  have hdisj : Disjoint (Finset.range (J0 + 1)) (Finset.Ioc J0 (J0 + n)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_range] at hx
    simp only [Finset.mem_Ioc] at hx'
    omega
  have hunion : Finset.range (J0 + n + 1) =
      Finset.range (J0 + 1) ∪ Finset.Ioc J0 (J0 + n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [hunion, Finset.sum_union hdisj, Finset.sum_range_succ]

theorem triadicLeafCount_eq_zero_of_lt (S : Set (SpatialCoordinates d)) (J0 n : ℕ) {J : ℕ}
    (hJ : J < J0) : triadicLeafCount z R hR S J0 n J = 0 := by
  unfold triadicLeafCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk h
  unfold TriadicIsLeaf at h
  obtain ⟨h1, _, _, _⟩ := h
  exact absurd h1 (not_le.2 hJ)

theorem triadicLeafCount_le (S : Set (SpatialCoordinates d)) (J0 n J : ℕ) :
    (triadicLeafCount z R hR S J0 n J : ℝ) ≤ ((3 : ℝ) ^ J) ^ d := by
  have hcard : triadicLeafCount z R hR S J0 n J ≤ (2 * triadicHalf J + 1) ^ d := by
    unfold triadicLeafCount
    calc ((Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
            (fun k => TriadicIsLeaf z R hR S J0 n ⟨J, k⟩)).card
        ≤ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))).card :=
          Finset.card_filter_le _ _
      _ = Fintype.card (OddGridIndex d (triadicHalf J)) := Finset.card_univ
      _ = Fintype.card (Fin d → Fin (2 * triadicHalf J + 1)) := rfl
      _ = (2 * triadicHalf J + 1) ^ d := by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  calc (triadicLeafCount z R hR S J0 n J : ℝ)
      ≤ (((2 * triadicHalf J + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((3 : ℝ) ^ J) ^ d := by
        rw [two_mul_triadicHalf_add_one]
        push_cast
        ring

/-- A deep leaf lies in the shell of its parent. -/
theorem triadicPart_leaf_cell_subset_shell (w : SpatialCoordinates d) (ρ : ℝ)
    (J0 n : ℕ) {q : TriadicGridLabel d}
    (hq : q ∈ triadicLeaves z R hR (frontier (ball w ρ)) J0 n) (hJ : J0 < q.1) :
    triadicCell z R hR q ⊆
      closedBall w (ρ + R / (3 : ℝ) ^ (q.1 - 1)) \ ball w (ρ - R / (3 : ℝ) ^ (q.1 - 1)) := by
  have hleaf := (mem_triadicLeaves z R hR (S := frontier (ball w ρ)) (J0 := J0) (n := n)).mp hq
  have hnotmiss : ¬ TriadicMisses z R hR (frontier (ball w ρ)) (triadicParentLabel q) := by
    rcases hleaf.2.2.2 with h | h
    · omega
    · exact h
  have hshell := triadicPart_closure_cell_subset_shell z R hR w ρ (triadicParentLabel q) hnotmiss
  rw [triadicGridSide_eq, triadicParentLabel_depth] at hshell
  intro x hx
  exact hshell (subset_closure (triadicCell_subset_parentLabel z R hR q hx))

/-- Deep layers: the count against the cell volume is bounded by the shell volume. -/
theorem triadicLeafCount_deep_le (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (J0 n J : ℕ) (hJ0 : J0 < J) (_hJn : J ≤ J0 + n) (h0 : R / (3 : ℝ) ^ J0 ≤ r / 4) :
    (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / (3 : ℝ) ^ J) ^ d ≤
      12 * d * (R / (3 : ℝ) ^ J) * (2 * r) ^ (d - 1) := by
  let T : Finset (OddGridIndex d (triadicHalf J)) :=
    (Finset.univ.filter (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩))
  let h' : ℝ := R / (3 : ℝ) ^ (J - 1)
  have hJ1 : 1 ≤ J := by omega
  have hh' : 0 ≤ h' := by simp only [h']; positivity
  have hJ0le : J0 ≤ J - 1 := by omega
  have hpowle : (3 : ℝ) ^ J0 ≤ (3 : ℝ) ^ (J - 1) := pow_le_pow_right₀ (by norm_num) hJ0le
  have hle : h' ≤ R / (3 : ℝ) ^ J0 := by
    simp only [h']
    exact div_le_div_of_nonneg_left hR.le (by positivity) hpowle
  have hh'r : 2 * h' < r := by linarith [hle, h0, hr]
  have hsub : ∀ k ∈ T, triadicCell z R hR ⟨J, k⟩ ⊆
      (closedBall w (r / 2 + h') \ ball w (r / 2 - h')) := by
    intro k hk
    have hkT : TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩ :=
      (Finset.mem_filter.mp hk).2
    have hmem : (⟨J, k⟩ : TriadicGridLabel d) ∈
        triadicLeaves z R hR (frontier (ball w (r / 2))) J0 n := by
      rw [mem_triadicLeaves]; exact hkT
    exact triadicPart_leaf_cell_subset_shell z R hR w (r / 2) J0 n hmem hJ0
  have hpack := triadicPart_grid_packing z R hR J T (closedBall w (r / 2 + h') \ ball w (r / 2 - h'))
    (triadicPart_shell_volume_ne_top w (r / 2) h') hsub
  have hvol := triadicPart_shell_volume_le w hh' hh'r
  have hpoweq : (3 : ℝ) ^ J = (3 : ℝ) ^ (J - 1) * 3 := by
    nth_rewrite 1 [← Nat.sub_add_cancel hJ1]
    rw [pow_succ]
  have heq : 4 * (d : ℝ) * h' * (2 * r) ^ (d - 1) =
      12 * (d : ℝ) * (R / (3 : ℝ) ^ J) * (2 * r) ^ (d - 1) := by
    simp only [h']
    rw [hpoweq]
    field_simp
    ring
  show (T.card : ℝ) * (R / (3 : ℝ) ^ J) ^ d ≤
      12 * (d : ℝ) * (R / (3 : ℝ) ^ J) * (2 * r) ^ (d - 1)
  exact le_trans hpack (le_trans hvol (le_of_eq heq))

theorem triadicLeafCount_deep_cost_le (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (J0 n J : ℕ) (hJ0 : J0 < J) (hJn : J ≤ J0 + n) (h0 : R / (3 : ℝ) ^ J0 ≤ r / 4)
    {s : ℝ} (_hs : (d : ℝ) - 1 < s) :
    (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / (3 : ℝ) ^ J) ^ s ≤
      12 * d * (2 * r) ^ (d - 1) * (R / (3 : ℝ) ^ J) ^ (s - d + 1) := by
  have hxpos : 0 < R / (3 : ℝ) ^ J := by positivity
  have hnn : 0 ≤ (R / (3 : ℝ) ^ J) ^ (s - d) :=
    Real.rpow_nonneg (le_of_lt hxpos) _
  have hdeep := triadicLeafCount_deep_le z R hR w hr J0 n J hJ0 hJn h0
  have hs_eq : (R / (3 : ℝ) ^ J) ^ s =
      (R / (3 : ℝ) ^ J) ^ d * (R / (3 : ℝ) ^ J) ^ (s - d) := by
    conv_lhs => rw [show s = (d : ℝ) + (s - d) by ring]
    rw [Real.rpow_add hxpos, Real.rpow_natCast]
  have hs2 : (R / (3 : ℝ) ^ J) ^ (s - d + 1) =
      (R / (3 : ℝ) ^ J) ^ (s - d) * (R / (3 : ℝ) ^ J) := by
    conv_lhs => rw [show s - d + 1 = (s - d) + 1 by ring]
    rw [Real.rpow_add hxpos, Real.rpow_one]
  calc
    (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / (3 : ℝ) ^ J) ^ s
        = ((triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / (3 : ℝ) ^ J) ^ d)
            * (R / (3 : ℝ) ^ J) ^ (s - d) := by rw [hs_eq]; ring
    _ ≤ (12 * d * (R / (3 : ℝ) ^ J) * (2 * r) ^ (d - 1))
            * (R / (3 : ℝ) ^ J) ^ (s - d) :=
          mul_le_mul_of_nonneg_right hdeep hnn
    _ = 12 * d * (2 * r) ^ (d - 1) * (R / (3 : ℝ) ^ J) ^ (s - d + 1) := by
          rw [hs2]; ring

theorem triadicPart_scale_rpow_eq {J0 J : ℕ} (hJ : J0 ≤ J) {e : ℝ} :
    (R / (3 : ℝ) ^ J) ^ e = (R / (3 : ℝ) ^ J0) ^ e * ((3 : ℝ) ^ (-e)) ^ (J - J0) := by
  have h3 : (0:ℝ) < 3 := by norm_num
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hJ
  rw [show J0 + m - J0 = m by omega]
  have hmul : ∀ x y : ℝ, 0 < y → (x * y) ^ e = x ^ e * y ^ e := by
    intro x y hy
    rcases le_or_gt 0 x with hx | hx
    · exact Real.mul_rpow hx hy.le
    · rw [Real.rpow_def_of_neg (mul_neg_of_neg_of_pos hx hy) e, Real.rpow_def_of_neg hx e,
        Real.rpow_def_of_pos hy e]
      rw [Real.log_mul (ne_of_lt hx) (ne_of_gt hy), add_mul, Real.exp_add]
      ring
  have hbase : R / (3:ℝ)^(J0+m) = (R / (3:ℝ)^J0) * ((3:ℝ)^m)⁻¹ := by
    rw [pow_add, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hbase, hmul (R / (3:ℝ)^J0) ((3:ℝ)^m)⁻¹ (inv_pos.mpr (pow_pos h3 m))]
  have hpe : ((3:ℝ)^m)⁻¹ ^ e = ((3:ℝ)^(-e))^m := by
    rw [← Real.rpow_natCast (3:ℝ) m, ← Real.rpow_neg h3.le (m:ℝ), ← Real.rpow_mul h3.le (-(m:ℝ)) e]
    rw [show (-(m:ℝ))*e = (-e)*(m:ℝ) by ring]
    rw [Real.rpow_mul h3.le (-e) (m:ℝ), Real.rpow_natCast ((3:ℝ)^(-e)) m]
  rw [hpe]

theorem triadicPart_geom_partial_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (J0 n : ℕ) :
    ∑ J ∈ Finset.Ioc J0 (J0 + n), q ^ (J - J0) ≤ q / (1 - q) := by
  have hreindex : ∀ n : ℕ, ∑ j ∈ Finset.range n, q ^ (j + 1) =
      ∑ J ∈ Finset.Ioc J0 (J0 + n), q ^ (J - J0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show J0 + (n + 1) = J0 + n + 1 by omega,
        Finset.sum_Ioc_succ_top (Nat.le_add_right J0 n)]
      rw [show J0 + n + 1 - J0 = n + 1 by omega]
  rw [← hreindex n]
  have hle : ∑ j ∈ Finset.range n, q ^ j ≤ ∑' j : ℕ, q ^ j :=
    Summable.sum_le_tsum (Finset.range n) (fun i _ => pow_nonneg (le_of_lt hq0) i)
      (summable_geometric_of_lt_one (le_of_lt hq0) hq1)
  have hfactor : ∑ j ∈ Finset.range n, q ^ (j + 1) = q * ∑ j ∈ Finset.range n, q ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  calc ∑ j ∈ Finset.range n, q ^ (j + 1)
      = q * ∑ j ∈ Finset.range n, q ^ j := hfactor
    _ ≤ q * ∑' j : ℕ, q ^ j := mul_le_mul_of_nonneg_left hle (le_of_lt hq0)
    _ = q / (1 - q) := by
          rw [tsum_geometric_of_lt_one (le_of_lt hq0) hq1, div_eq_mul_inv]

include hR in
/-- Geometric series over the scales. -/
theorem triadicPart_geom_sum_scales (J0 n : ℕ) {e : ℝ} (he : 0 < e) :
    ∑ J ∈ Finset.Ioc J0 (J0 + n), (R / (3 : ℝ) ^ J) ^ e ≤
      (R / (3 : ℝ) ^ J0) ^ e * ((3 : ℝ) ^ (-e) / (1 - (3 : ℝ) ^ (-e))) := by
  have hbase : 0 < R / (3 : ℝ) ^ J0 := div_pos hR (pow_pos (by norm_num) J0)
  have hq0 : 0 < (3 : ℝ) ^ (-e) := Real.rpow_pos_of_pos (by norm_num) (-e)
  have hq1 : (3 : ℝ) ^ (-e) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1 : ∑ J ∈ Finset.Ioc J0 (J0 + n), (R / (3 : ℝ) ^ J) ^ e
      = (R / (3 : ℝ) ^ J0) ^ e *
          ∑ J ∈ Finset.Ioc J0 (J0 + n), ((3 : ℝ) ^ (-e)) ^ (J - J0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    exact triadicPart_scale_rpow_eq R (J0 := J0) (J := J) (le_of_lt (Finset.mem_Ioc.mp hJ).1)
  rw [h1]
  exact mul_le_mul_of_nonneg_left (triadicPart_geom_partial_le hq0 hq1 J0 n)
    (Real.rpow_nonneg (le_of_lt hbase) e)

theorem triadicPart_deep_cost_total (hd : 1 ≤ d) (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (J0 n : ℕ)
    (h0 : R / (3 : ℝ) ^ J0 ≤ r / 4) {s : ℝ} (hs : (d : ℝ) - 1 < s) :
    ∑ J ∈ Finset.Ioc J0 (J0 + n),
      (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / (3 : ℝ) ^ J) ^ s ≤
        triadicDeepConst d s * r ^ s := by
  have he : 0 < s - (d : ℝ) + 1 := by linarith
  have hC : 0 ≤ 12 * (d : ℝ) * (2 * r) ^ (d - 1) := by
    have h2r : (0:ℝ) ≤ 2 * r := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (pow_nonneg h2r _)
  have hx0_nonneg : 0 ≤ R / (3:ℝ)^J0 := div_nonneg hR.le (pow_pos (by norm_num) J0).le
  have hx0_le_r : R / (3:ℝ)^J0 ≤ r := by
    have h4 : r / 4 ≤ r := by linarith
    linarith
  have hx0e : (R / (3:ℝ)^J0) ^ (s - (d:ℝ) + 1) ≤ r ^ (s - (d:ℝ) + 1) :=
    Real.rpow_le_rpow hx0_nonneg hx0_le_r he.le
  have h3 : (0:ℝ) < 3 := by norm_num
  have hqpos : 0 < (3:ℝ) ^ (-(s - (d:ℝ) + 1)) := Real.rpow_pos_of_pos h3 _
  have hqlt : (3:ℝ) ^ (-(s - (d:ℝ) + 1)) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos h3]
    exact Or.inl ⟨by norm_num, by linarith⟩
  have hQ : 0 ≤ (3:ℝ)^(-(s-(d:ℝ)+1)) / (1 - (3:ℝ)^(-(s-(d:ℝ)+1))) :=
    div_nonneg hqpos.le (by linarith)
  have hterm : ∀ J ∈ Finset.Ioc J0 (J0 + n),
      (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / (3:ℝ)^J)^s ≤
        12 * (d:ℝ) * (2*r)^(d-1) * (R / (3:ℝ)^J)^(s - (d:ℝ) + 1) := by
    intro J hJ
    rw [Finset.mem_Ioc] at hJ
    exact triadicLeafCount_deep_cost_le z R hR w hr J0 n J hJ.1 hJ.2 h0 hs
  have hsum_le : ∑ J ∈ Finset.Ioc J0 (J0 + n),
        (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / (3:ℝ)^J)^s
      ≤ 12 * (d:ℝ) * (2*r)^(d-1) * ∑ J ∈ Finset.Ioc J0 (J0 + n), (R / (3:ℝ)^J)^(s - (d:ℝ) + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hgeom := triadicPart_geom_sum_scales R hR J0 n (e := s - (d:ℝ) + 1) he
  have hmul_geom : 12 * (d:ℝ) * (2*r)^(d-1) * ∑ J ∈ Finset.Ioc J0 (J0 + n), (R / (3:ℝ)^J)^(s - (d:ℝ) + 1)
      ≤ 12 * (d:ℝ) * (2*r)^(d-1) * ((R / (3:ℝ)^J0)^(s - (d:ℝ) + 1) *
          ((3:ℝ)^(-(s - (d:ℝ) + 1)) / (1 - (3:ℝ)^(-(s - (d:ℝ) + 1))))) :=
    mul_le_mul_of_nonneg_left hgeom hC
  have hstep2 : 12 * (d:ℝ) * (2*r)^(d-1) * ((R / (3:ℝ)^J0)^(s - (d:ℝ) + 1) *
          ((3:ℝ)^(-(s - (d:ℝ) + 1)) / (1 - (3:ℝ)^(-(s - (d:ℝ) + 1)))))
      ≤ 12 * (d:ℝ) * (2*r)^(d-1) * (r^(s - (d:ℝ) + 1) *
          ((3:ℝ)^(-(s - (d:ℝ) + 1)) / (1 - (3:ℝ)^(-(s - (d:ℝ) + 1))))) := by
    apply mul_le_mul_of_nonneg_left _ hC
    exact mul_le_mul_of_nonneg_right hx0e hQ
  have hpow : (2*r)^(d-1) * r^(s - (d:ℝ) + 1) = 2^(d-1) * r^s := by
    have hcast : ((d-1:ℕ):ℝ) = (d:ℝ) - 1 := by rw [Nat.cast_sub hd]; norm_num
    have hexp : ((d-1:ℕ):ℝ) + (s - (d:ℝ) + 1) = s := by rw [hcast]; ring
    have hmul : r^(((d-1:ℕ):ℝ)) * r^(s - (d:ℝ) + 1) = r^s := by
      rw [← Real.rpow_add hr, hexp]
    have hnat : (2*r)^(d-1) = 2^(d-1) * r^(((d-1:ℕ):ℝ)) := by
      rw [mul_pow, Real.rpow_natCast]
    calc (2*r)^(d-1) * r^(s - (d:ℝ) + 1)
        = 2^(d-1) * r^(((d-1:ℕ):ℝ)) * r^(s - (d:ℝ) + 1) := by rw [hnat]
      _ = 2^(d-1) * (r^(((d-1:ℕ):ℝ)) * r^(s - (d:ℝ) + 1)) := by ring
      _ = 2^(d-1) * r^s := by rw [hmul]
  have hfinal : 12 * (d:ℝ) * (2*r)^(d-1) * (r^(s - (d:ℝ) + 1) *
          ((3:ℝ)^(-(s - (d:ℝ) + 1)) / (1 - (3:ℝ)^(-(s - (d:ℝ) + 1)))))
      = triadicDeepConst d s * r^s := by
    have h1 : 12 * (d:ℝ) * (2*r)^(d-1) * (r^(s - (d:ℝ) + 1) *
          ((3:ℝ)^(-(s - (d:ℝ) + 1)) / (1 - (3:ℝ)^(-(s - (d:ℝ) + 1)))))
        = 12 * (d:ℝ) * ((2*r)^(d-1) * r^(s - (d:ℝ) + 1)) *
          ((3:ℝ)^(-(s - (d:ℝ) + 1)) / (1 - (3:ℝ)^(-(s - (d:ℝ) + 1)))) := by ring
    rw [h1, hpow]
    unfold triadicDeepConst
    ring
  calc ∑ J ∈ Finset.Ioc J0 (J0 + n),
        (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / (3:ℝ)^J)^s
      ≤ 12 * (d:ℝ) * (2*r)^(d-1) * ∑ J ∈ Finset.Ioc J0 (J0 + n), (R / (3:ℝ)^J)^(s - (d:ℝ) + 1) := hsum_le
    _ ≤ 12 * (d:ℝ) * (2*r)^(d-1) * ((R / (3:ℝ)^J0)^(s - (d:ℝ) + 1) *
          ((3:ℝ)^(-(s - (d:ℝ) + 1)) / (1 - (3:ℝ)^(-(s - (d:ℝ) + 1))))) := hmul_geom
    _ ≤ 12 * (d:ℝ) * (2*r)^(d-1) * (r^(s - (d:ℝ) + 1) *
          ((3:ℝ)^(-(s - (d:ℝ) + 1)) / (1 - (3:ℝ)^(-(s - (d:ℝ) + 1))))) := hstep2
    _ = triadicDeepConst d s * r^s := hfinal

/-- Initial layer: cells meeting the ball. -/
theorem triadicPart_baseMeet_le (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (J0 : ℕ)
    (h0 : R / (3 : ℝ) ^ J0 ≤ r / 4) :
    (((Finset.univ : Finset (OddGridIndex d (triadicHalf J0))).filter
      (fun k => (triadicCell z R hR ⟨J0, k⟩ ∩ ball w (r / 2)).Nonempty)).card : ℝ) *
        (R / (3 : ℝ) ^ J0) ^ d ≤ (2 * r) ^ d := by
  set s : ℝ := R / (3 : ℝ) ^ J0 with hs_def
  set T : Finset (OddGridIndex d (triadicHalf J0)) :=
    (Finset.univ : Finset (OddGridIndex d (triadicHalf J0))).filter
      (fun k => (triadicCell z R hR ⟨J0, k⟩ ∩ ball w (r / 2)).Nonempty) with hT_def
  set E : Set (SpatialCoordinates d) := ball w (r / 2 + s) with hE_def
  have hspos : 0 < s := by rw [hs_def]; positivity
  have hsle : s ≤ r / 4 := by rw [hs_def]; exact h0
  have hE : volume E ≠ ⊤ := by
    rw [hE_def]
    exact ne_of_lt (measure_ball_lt_top (x := w) (r := r / 2 + s))
  have hsub : ∀ k ∈ T, triadicCell z R hR ⟨J0, k⟩ ⊆ E := by
    intro k hk
    rw [hT_def] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [hE_def]
    have h := triadicPart_cell_subset_ball_of_meets z R hR w (r / 2) ⟨J0, k⟩ hk
    have hside : (⟨J0, k⟩ : TriadicGridLabel d).fst = J0 := rfl
    rw [triadicGridSide_eq, hside, ← hs_def] at h
    exact h
  have hpack : (T.card : ℝ) * s ^ d ≤ volume.real E := by
    have h := triadicPart_grid_packing z R hR J0 T E hE hsub
    simpa only [hs_def] using h
  have hvol : volume.real E = (r + 2 * s) ^ d := by
    change (volume (ball w (r / 2 + s))).toReal = (r + 2 * s) ^ d
    rw [Real.volume_pi_ball w (by linarith [hspos])]
    rw [ENNReal.toReal_ofReal (by positivity)]
    rw [Fintype.card_fin]
    rw [show 2 * (r / 2 + s) = r + 2 * s by ring]
  calc (T.card : ℝ) * s ^ d ≤ volume.real E := hpack
    _ = (r + 2 * s) ^ d := hvol
    _ ≤ (2 * r) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d

theorem triadicPart_rpow_ratio_le {c r x : ℝ} (hc : 0 < c) (hcx : c * r ≤ x) (hxr : x ≤ r) (hr : 0 < r) (t : ℝ) :
    x ^ t ≤ max 1 (c ^ t) * r ^ t := by
  by_cases ht : 0 ≤ t
  · have hxpos : 0 < x := lt_of_lt_of_le (mul_pos hc hr) hcx
    calc
      x ^ t ≤ r ^ t := Real.rpow_le_rpow (le_of_lt hxpos) hxr ht
      _ = 1 * r ^ t := by ring
      _ ≤ max 1 (c ^ t) * r ^ t :=
        mul_le_mul_of_nonneg_right (le_max_left 1 (c ^ t)) (Real.rpow_nonneg (le_of_lt hr) t)
  · have htneg : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    calc
      x ^ t ≤ (c * r) ^ t := Real.rpow_le_rpow_of_nonpos (mul_pos hc hr) hcx htneg
      _ = c ^ t * r ^ t := Real.mul_rpow (le_of_lt hc) (le_of_lt hr)
      _ ≤ max 1 (c ^ t) * r ^ t :=
        mul_le_mul_of_nonneg_right (le_max_right 1 (c ^ t)) (Real.rpow_nonneg (le_of_lt hr) t)

theorem triadicPart_baseMeet_cost_le (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (J0 m : ℕ) (s : ℝ)
    (h0 : R / (3 : ℝ) ^ J0 ≤ r / 4) (hlow : r / (12 * (3 : ℝ) ^ m) ≤ R / (3 : ℝ) ^ J0) :
    (((Finset.univ : Finset (OddGridIndex d (triadicHalf J0))).filter
      (fun k => (triadicCell z R hR ⟨J0, k⟩ ∩ ball w (r / 2)).Nonempty)).card : ℝ) *
        (R / (3 : ℝ) ^ J0) ^ s ≤ triadicBaseConst d s m * r ^ s := by
  have hx : 0 < R / (3 : ℝ) ^ J0 := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ J0 := by positivity
    exact div_pos hR h3
  have hxr : R / (3 : ℝ) ^ J0 ≤ r := by
    linarith [h0]
  have hcr : (1 / (12 * (3 : ℝ) ^ m)) * r ≤ R / (3 : ℝ) ^ J0 := by
    have h : (1 / (12 * (3 : ℝ) ^ m)) * r = r / (12 * (3 : ℝ) ^ m) := by ring
    rw [h]; exact hlow
  have hs_eq : s = (d : ℝ) + (s - d) := by ring
  have hN : (((Finset.univ : Finset (OddGridIndex d (triadicHalf J0))).filter
        (fun k => (triadicCell z R hR ⟨J0, k⟩ ∩ ball w (r / 2)).Nonempty)).card : ℝ) *
          (R / (3 : ℝ) ^ J0) ^ d ≤ (2 * r) ^ d := triadicPart_baseMeet_le z R hR w hr J0 h0
  have hratio : (R / (3 : ℝ) ^ J0) ^ (s - d) ≤
      max 1 ((1 / (12 * (3 : ℝ) ^ m)) ^ (s - d)) * r ^ (s - d) :=
    triadicPart_rpow_ratio_le (c := 1 / (12 * (3 : ℝ) ^ m)) (r := r) (x := R / (3 : ℝ) ^ J0)
      (by positivity) hcr hxr hr (s - d)
  calc
    (((Finset.univ : Finset (OddGridIndex d (triadicHalf J0))).filter
        (fun k => (triadicCell z R hR ⟨J0, k⟩ ∩ ball w (r / 2)).Nonempty)).card : ℝ) *
          (R / (3 : ℝ) ^ J0) ^ s
      = ((((Finset.univ : Finset (OddGridIndex d (triadicHalf J0))).filter
        (fun k => (triadicCell z R hR ⟨J0, k⟩ ∩ ball w (r / 2)).Nonempty)).card : ℝ) *
          (R / (3 : ℝ) ^ J0) ^ d) * (R / (3 : ℝ) ^ J0) ^ (s - d) := by
          rw [hs_eq, Real.rpow_add hx, Real.rpow_natCast]
          ring_nf
    _ ≤ (2 * r) ^ d * (R / (3 : ℝ) ^ J0) ^ (s - d) :=
          mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (le_of_lt hx) _)
    _ ≤ (2 * r) ^ d * (max 1 ((1 / (12 * (3 : ℝ) ^ m)) ^ (s - d)) * r ^ (s - d)) :=
          mul_le_mul_of_nonneg_left hratio (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * r) d)
    _ = triadicBaseConst d s m * r ^ s := by
          unfold triadicBaseConst
          rw [mul_pow]
          rw [← Real.rpow_natCast r d]
          rw [show (2:ℝ) ^ d * r ^ (d:ℝ) * (max 1 ((1/(12*(3:ℝ)^m))^(s-d)) * r^(s-d))
              = 2^d * max 1 ((1/(12*(3:ℝ)^m))^(s-d)) * (r ^ (d:ℝ) * r ^ (s-d)) from by ring]
          rw [← Real.rpow_add hr]
          rw [← hs_eq]

theorem triadicPart_total_cost_le (hd : 1 ≤ d) (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (J0 n : ℕ)
    (h0 : R / (3 : ℝ) ^ J0 ≤ r / 4) {s : ℝ} (hs : (d : ℝ) - 1 < s) :
    ∑ ℓ ∈ triadicLeaves z R hR (frontier (ball w (r / 2))) J0 n, (triadicGridSide R ℓ) ^ s ≤
      ((3 : ℝ) ^ J0) ^ d * (R / (3 : ℝ) ^ J0) ^ s + triadicDeepConst d s * r ^ s := by
  have hsum_eq : (∑ ℓ ∈ triadicLeaves z R hR (frontier (ball w (r / 2))) J0 n,
        (triadicGridSide R ℓ) ^ s) =
      ∑ J ∈ Finset.range (J0 + n + 1),
        (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) *
          (R / (3 : ℝ) ^ J) ^ s := by
    rw [triadicLeaves_sum z R hR (frontier (ball w (r / 2))) J0 n
        (fun ℓ => (triadicGridSide R ℓ) ^ s)]
    apply Finset.sum_congr rfl
    intro J hJ
    have hstep : (∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
          (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩),
            (triadicGridSide R ⟨J, k⟩) ^ s) =
        ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
          (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩),
            (R / (3 : ℝ) ^ J) ^ s := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [triadicGridSide_eq]
    rw [hstep, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [hsum_eq]
  rw [triadicPart_range_split_sum]
  have hrange : ∑ J ∈ Finset.range J0,
      (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) *
        (R / (3 : ℝ) ^ J) ^ s = 0 := by
    apply Finset.sum_eq_zero
    intro J hJ
    rw [triadicLeafCount_eq_zero_of_lt z R hR (frontier (ball w (r / 2))) J0 n
        (Finset.mem_range.mp hJ)]
    ring
  rw [hrange]
  have hJ0term : (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J0 : ℝ) *
      (R / (3 : ℝ) ^ J0) ^ s ≤ ((3 : ℝ) ^ J0) ^ d * (R / (3 : ℝ) ^ J0) ^ s := by
    have hle := triadicLeafCount_le z R hR (frontier (ball w (r / 2))) J0 n J0
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hdeep := triadicPart_deep_cost_total z R hR hd w hr J0 n h0 hs
  linarith [hJ0term, hdeep]

theorem triadicPart_local_cost_le (hd : 1 ≤ d) (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (J0 n m : ℕ)
    (h0 : R / (3 : ℝ) ^ J0 ≤ r / 4) (hlow : r / (12 * (3 : ℝ) ^ m) ≤ R / (3 : ℝ) ^ J0)
    {s : ℝ} (hs : (d : ℝ) - 1 < s) :
    ∑ ℓ ∈ triadicLeaves z R hR (frontier (ball w (r / 2))) J0 n,
      (if (triadicCell z R hR ℓ ∩ ball w (r / 2)).Nonempty then (triadicGridSide R ℓ) ^ s else 0) ≤
        (triadicBaseConst d s m + triadicDeepConst d s) * r ^ s := by
  let g : TriadicGridLabel d → ℝ :=
    fun ℓ => if (triadicCell z R hR ℓ ∩ ball w (r / 2)).Nonempty then (triadicGridSide R ℓ) ^ s else 0
  let F : ℕ → ℝ := fun J =>
    ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
      (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩), g ⟨J, k⟩
  have hgdef : ∀ ℓ, g ℓ = (if (triadicCell z R hR ℓ ∩ ball w (r / 2)).Nonempty then (triadicGridSide R ℓ) ^ s else 0) :=
    fun ℓ => rfl
  have hFdef : ∀ J, F J = ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
      (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩), g ⟨J, k⟩ :=
    fun J => rfl
  have hA : (∑ J ∈ Finset.range J0, F J) = 0 := by
    apply Finset.sum_eq_zero
    intro J hJ
    rw [Finset.mem_range] at hJ
    have hz : ((Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
        (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩)) = ∅ := by
      rw [← Finset.card_eq_zero]
      exact triadicLeafCount_eq_zero_of_lt z R hR (frontier (ball w (r / 2))) J0 n hJ
    rw [hFdef, hz, Finset.sum_empty]
  have hB : F J0 ≤ triadicBaseConst d s m * r ^ s := by
    rw [hFdef]
    have hx : (0 : ℝ) ≤ (R / 3 ^ J0) ^ s := Real.rpow_nonneg (by positivity) s
    calc
      ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J0))).filter
          (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J0, k⟩), g ⟨J0, k⟩
          = ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J0))).filter
              (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J0, k⟩),
              (if (triadicCell z R hR ⟨J0, k⟩ ∩ ball w (r / 2)).Nonempty then (R / 3 ^ J0) ^ s else 0) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [hgdef, triadicGridSide_eq]
      _ ≤ ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J0))),
              (if (triadicCell z R hR ⟨J0, k⟩ ∩ ball w (r / 2)).Nonempty then (R / 3 ^ J0) ^ s else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro k hk hknot
            split_ifs with hc
            · exact hx
            · exact le_refl 0
      _ = ((Finset.univ : Finset (OddGridIndex d (triadicHalf J0))).filter
              (fun k => (triadicCell z R hR ⟨J0, k⟩ ∩ ball w (r / 2)).Nonempty)).card * (R / 3 ^ J0) ^ s := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ triadicBaseConst d s m * r ^ s := triadicPart_baseMeet_cost_le z R hR w hr J0 m s h0 hlow
  have hC : (∑ J ∈ Finset.Ioc J0 (J0 + n), F J) ≤ triadicDeepConst d s * r ^ s := by
    calc
      ∑ J ∈ Finset.Ioc J0 (J0 + n), F J
          ≤ ∑ J ∈ Finset.Ioc J0 (J0 + n), (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / 3 ^ J) ^ s := by
            apply Finset.sum_le_sum
            intro J hJ
            rw [hFdef]
            have hx : (0 : ℝ) ≤ (R / 3 ^ J) ^ s := Real.rpow_nonneg (by positivity) s
            calc
              ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
                  (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩), g ⟨J, k⟩
                  = ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
                      (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩),
                      (if (triadicCell z R hR ⟨J, k⟩ ∩ ball w (r / 2)).Nonempty then (R / 3 ^ J) ^ s else 0) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    simp only [hgdef, triadicGridSide_eq]
              _ ≤ ∑ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))).filter
                      (fun k => TriadicIsLeaf z R hR (frontier (ball w (r / 2))) J0 n ⟨J, k⟩), (R / 3 ^ J) ^ s := by
                    apply Finset.sum_le_sum
                    intro k hk
                    split_ifs with hc
                    · exact le_refl _
                    · exact hx
              _ = (triadicLeafCount z R hR (frontier (ball w (r / 2))) J0 n J : ℝ) * (R / 3 ^ J) ^ s := by
                    simp only [triadicLeafCount, Finset.sum_const, nsmul_eq_mul]
      _ ≤ triadicDeepConst d s * r ^ s := triadicPart_deep_cost_total z R hR hd w hr J0 n h0 hs
  calc
    ∑ ℓ ∈ triadicLeaves z R hR (frontier (ball w (r / 2))) J0 n,
        (if (triadicCell z R hR ℓ ∩ ball w (r / 2)).Nonempty then (triadicGridSide R ℓ) ^ s else 0)
        = ∑ J ∈ Finset.range (J0 + n + 1), F J :=
          triadicLeaves_sum z R hR (frontier (ball w (r / 2))) J0 n g
    _ = ∑ J ∈ Finset.range J0, F J + F J0 + ∑ J ∈ Finset.Ioc J0 (J0 + n), F J :=
          triadicPart_range_split_sum F J0 n
    _ ≤ 0 + triadicBaseConst d s m * r ^ s + triadicDeepConst d s * r ^ s := by
          linarith [hA, hB, hC]
    _ = (triadicBaseConst d s m + triadicDeepConst d s) * r ^ s := by ring

/-- A starting depth adapted to the target scale. -/
theorem triadicPart_exists_start_depth {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) (m : ℕ) :
    ∃ J0 : ℕ, m ≤ J0 ∧ R / (3 : ℝ) ^ J0 ≤ r / 4 ∧ r / (12 * (3 : ℝ) ^ m) ≤ R / (3 : ℝ) ^ J0 := by
  have hex : ∃ J : ℕ, R / (3 : ℝ) ^ J ≤ r / 4 := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (4 * R / r) (by norm_num : (1 : ℝ) < 3)
    refine ⟨J, ?_⟩
    have hr4 : 0 < r / 4 := by linarith
    have hRlt : R < (3 : ℝ) ^ J * (r / 4) := by
      have h := mul_lt_mul_of_pos_right hJ hr4
      have heq : (4 * R / r) * (r / 4) = R := by field_simp
      rw [heq] at h
      exact h
    rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) J)]
    exact le_of_lt (by rw [mul_comm]; exact hRlt)
  set Jr := Nat.find hex with hJrdef
  have hspec : R / (3 : ℝ) ^ Jr ≤ r / 4 := by
    rw [hJrdef]; exact Nat.find_spec hex
  have hJr1 : 1 ≤ Jr := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have h : R ≤ r / 4 := by
      have := hspec
      rw [h0] at this
      simpa using this
    linarith
  have hJr0 : Jr ≠ 0 := by omega
  have hlt : Jr - 1 < Nat.find hex :=
    lt_of_lt_of_eq (Nat.sub_one_lt hJr0) hJrdef
  have hprev : ¬ (R / (3 : ℝ) ^ (Jr - 1) ≤ r / 4) := Nat.find_min hex hlt
  have hgt : r / 4 < R / (3 : ℝ) ^ (Jr - 1) := lt_of_not_ge hprev
  have hdiv := div_lt_div_of_pos_right hgt (by norm_num : (0 : ℝ) < 3)
  have hpow : (3 : ℝ) ^ Jr = (3 : ℝ) ^ (Jr - 1) * 3 := by
    conv_lhs => rw [← Nat.sub_add_cancel hJr1]
    rw [pow_add, pow_one]
  have hRdiv : R / (3 : ℝ) ^ Jr = (R / (3 : ℝ) ^ (Jr - 1)) / 3 := by
    rw [hpow, div_mul_eq_div_div]
  have hR12 : r / 12 < R / (3 : ℝ) ^ Jr := by
    rw [hRdiv]
    have hq : r / 4 / 3 = r / 12 := by ring
    linarith
  refine ⟨Jr + m, by omega, ?_, ?_⟩
  · calc R / (3 : ℝ) ^ (Jr + m) ≤ R / (3 : ℝ) ^ Jr :=
          div_le_div_of_nonneg_left hR.le (pow_pos (by norm_num : (0 : ℝ) < 3) Jr)
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_add_right Jr m))
      _ ≤ r / 4 := hspec
  · have hRscale : R / (3 : ℝ) ^ (Jr + m) = (R / (3 : ℝ) ^ Jr) / (3 : ℝ) ^ m := by
      rw [pow_add, div_mul_eq_div_div]
    have hrscale : r / (12 * (3 : ℝ) ^ m) = (r / 12) / (3 : ℝ) ^ m := by
      rw [div_mul_eq_div_div]
    rw [hRscale, hrscale]
    exact div_le_div_of_nonneg_right hR12.le (by positivity)

end SubdiffusiveProcess
