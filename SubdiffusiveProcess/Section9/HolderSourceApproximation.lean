module

public import SubdiffusiveProcess.Section9.HolderMollification

@[expose] public section

/-! Hölder approximation by the actual common-support smooth source catalogue. -/

open Set Filter MeasureTheory SubdiffusiveProcess
open SubdiffusiveProcess.CubeTrace _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Section9

theorem cAlphaNorm_bound_of_sup_and_increments {d : ℕ}
    (beta A C : ℝ) (hb : 0 ≤ beta) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (S : Set (SpatialCoordinates d)) (F : SpatialCoordinates d → ℝ)
    (habs : ∀ x ∈ S, |F x| ≤ A)
    (hinc : ∀ x ∈ S, ∀ y ∈ S, |F x - F y| ≤ C * ‖x - y‖ ^ beta) :
    IsHolderOn beta S F ∧
    BddAbove {v : ℝ | ∃ x ∈ S, v = |F x|} ∧
    cAlphaNorm beta S F ≤ A + C := by
  have hhol := isHolderOn_of_dist_holder_bound beta C hb hC S F
    (fun x hx y hy => by simpa only [dist_eq_norm] using hinc x hx y hy)
  have hsup : ∀ v ∈ {v : ℝ | ∃ x ∈ S, v = |F x|}, v ≤ A := by
    rintro v ⟨x, hx, rfl⟩
    exact habs x hx
  exact ⟨hhol.1, ⟨A, hsup⟩, add_le_add (Real.sSup_le hsup hA) hhol.2⟩

/-- Uniform zeroth- and first-derivative errors control all exponents up to one. -/
theorem holder_bound_of_sup_fderiv {d : ℕ} {beta eps : ℝ}
    (hb : 0 ≤ beta) (hb1 : beta ≤ 1) (heps : 0 ≤ eps)
    {F : SpatialCoordinates d → ℝ} (hF : Differentiable ℝ F)
    (hs : ∀ x, |F x| ≤ eps) (hd : ∀ x, ‖fderiv ℝ F x‖ ≤ eps)
    (x y : SpatialCoordinates d) : |F x - F y| ≤ 2 * eps * ‖x - y‖ ^ beta := by
  have hlip : |F x - F y| ≤ eps * ‖x - y‖ := by
    simpa only [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hF x) (fun x _ => hd x) (mem_univ y) (mem_univ x)
  by_cases hn : ‖x - y‖ ≤ 1
  · have hp : ‖x - y‖ ≤ ‖x - y‖ ^ beta := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hn hb hb1
    calc
      _ ≤ eps * ‖x - y‖ := hlip
      _ ≤ eps * ‖x - y‖ ^ beta := mul_le_mul_of_nonneg_left hp heps
      _ ≤ 2 * eps * ‖x - y‖ ^ beta := by
        have hp0 := Real.rpow_nonneg (norm_nonneg (x - y)) beta
        nlinarith only [heps, hp0]
  · have hp : 1 ≤ ‖x - y‖ ^ beta := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num)
        (le_of_not_ge hn) hb
    calc
      _ ≤ |F x| + |F y| := abs_sub _ _
      _ ≤ eps + eps := add_le_add (hs x) (hs y)
      _ ≤ 2 * eps * ‖x - y‖ ^ beta := by nlinarith only [heps, hp]

/-- Extract one source approximation with prescribed uniform C¹ error. -/
theorem exists_source_with_sup_fderiv_error {d : ℕ} {I : Type}
    (f : I → SpatialCoordinates d → ℝ) (phi : SpatialCoordinates d → ℝ)
    (g : ℕ → I)
    (ht : ∀ k : ℕ, TendstoUniformly
      (fun n x => iteratedFDeriv ℝ k (fun y => f (g n) y - phi y) x)
      (fun _ => 0) atTop)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ i : I, (∀ x, |f i x - phi x| ≤ eps) ∧
      (∀ x, ‖fderiv ℝ (fun y => f i y - phi y) x‖ ≤ eps) := by
  have h0 := Metric.tendstoUniformly_iff.mp (ht 0) eps heps
  have h1 := Metric.tendstoUniformly_iff.mp (ht 1) eps heps
  obtain ⟨n, hn0, hn1⟩ := (h0.and h1).exists
  refine ⟨g n, fun x => ?_, fun x => ?_⟩
  · have hv := (hn0 x).le
    simpa only [dist_zero_left, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hv
  · have hv := (hn1 x).le
    simpa only [dist_zero_left, ← norm_iteratedFDeriv_fderiv,
      norm_iteratedFDeriv_zero] using hv

/-- A genuine smooth-source density witness supplies global uniform and weaker Hölder
approximation of every compactly supported Hölder datum in the same open set. -/
theorem exists_holder_source_approximation {d : ℕ} [NeZero d] {I : Type}
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q)
    (f : I → SpatialCoordinates d → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i) ∧ tsupport (f i) ⊆ Q)
    (hdense : ∀ phi : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ Q →
      ∃ K : Set (SpatialCoordinates d), ∃ g : ℕ → I,
        IsCompact K ∧ K ⊆ Q ∧ tsupport phi ⊆ K ∧
        (∀ n, tsupport (f (g n)) ⊆ K) ∧
        (∀ k : ℕ, TendstoUniformly
          (fun n x => iteratedFDeriv ℝ k (fun y => f (g n) y - phi y) x)
          (fun _ => 0) atTop))
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 ≤ beta) (hba : beta < alpha)
    (hb1 : beta ≤ 1)
    (B : SpatialCoordinates d → ℝ) (hBc : Continuous B)
    (hBs : HasCompactSupport B) (hBQ : tsupport B ⊆ Q)
    (hB : IsHolderOn alpha Set.univ B) :
    ∃ g : ℕ → I,
      TendstoUniformly (fun n => f (g n)) B atTop ∧
      (∀ n, IsHolderOn beta (closure Q) (fun x => f (g n) x - B x)) ∧
      (∀ n, BddAbove {v : ℝ | ∃ x ∈ closure Q, v = |f (g n) x - B x|}) ∧
      Tendsto (fun n => cAlphaNorm beta (closure Q) (fun x => f (g n) x - B x))
        atTop (𝓝 0) := by
  obtain ⟨delta, hdelta, hdeltaQ⟩ := hBs.isCompact.exists_cthickening_subset_open hQ hBQ
  let hs : ℕ → ℝ := fun n => delta / 2 * (1 / ((n : ℝ) + 1))
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hp : ∀ n, 0 < hs n := fun n => by dsimp [hs]; positivity
  have he : ∀ n, 0 < eps n := fun n => by dsimp [eps]; positivity
  have ht : Tendsto hs atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (delta / 2)
  have het : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmQ : ∀ n, tsupport (ctMoll (hs n) B) ⊆ Q := by
    intro n
    have hsmall : hs n ≤ delta := by
      have hinv : 1 / ((n : ℝ) + 1) ≤ 1 := by
        apply (div_le_iff₀ (by positivity)).mpr
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      dsimp [hs]
      have hmul := mul_le_mul_of_nonneg_left hinv (half_pos hdelta).le
      nlinarith only [hmul, hdelta]
    exact (ctMoll_tsupport_subset_cthickening (hp n) B).trans
      ((Metric.cthickening_mono hsmall (tsupport B)).trans hdeltaQ)
  have hmc : ∀ n, HasCompactSupport (ctMoll (hs n) B) := by
    intro n
    exact (hBs.isCompact.cthickening (r := hs n)).of_isClosed_subset isClosed_closure
      (ctMoll_tsupport_subset_cthickening (hp n) B)
  have hchoice : ∀ n, ∃ i : I,
      (∀ x, |f i x - ctMoll (hs n) B x| ≤ eps n) ∧
      (∀ x, ‖fderiv ℝ (fun y => f i y - ctMoll (hs n) B y) x‖ ≤ eps n) := by
    intro n
    obtain ⟨K0, g0, _, _, _, _, h0⟩ := hdense (ctMoll (hs n) B)
      (ctMoll_contDiff (hp n) hBc) (hmc n) (hmQ n)
    exact exists_source_with_sup_fderiv_error f (ctMoll (hs n) B) g0 h0 (eps n) (he n)
  choose g hg0 hg1 using hchoice
  let C : ℝ := holderSeminorm alpha Set.univ B * (Real.sqrt d) ^ alpha
  have hC : 0 ≤ C := mul_nonneg (holderSeminorm_nonneg _ _ _)
    (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hincB : ∀ x y, |B x - B y| ≤ C * ‖x - y‖ ^ alpha := by
    intro x y
    simpa only [dist_eq_norm] using
      dist_holder_bound_of_isHolderOn ha.le hB x (mem_univ x) y (mem_univ y)
  have hresult : ∀ n, IsHolderOn beta (closure Q) (fun x => f (g n) x - B x) ∧
      BddAbove {v : ℝ | ∃ x ∈ closure Q, v = |f (g n) x - B x|} ∧
      cAlphaNorm beta (closure Q) (fun x => f (g n) x - B x) ≤
        3 * eps n + C * hs n ^ alpha + 2 * C * hs n ^ (alpha - beta) := by
    intro n
    have hlip := holder_bound_of_sup_fderiv hb hb1 (he n).le
      (((hf (g n)).1.sub (ctMoll_contDiff (hp n) hBc)).differentiable (by norm_num))
      (hg0 n) (hg1 n)
    have hm := ctMoll_error_holder_bound (hp n) hC ha hb hba hincB
    have he0 := ctMoll_sub_le (hp n) hC ha hincB
    have hbound := cAlphaNorm_bound_of_sup_and_increments beta
      (eps n + C * hs n ^ alpha) (2 * eps n + 2 * C * hs n ^ (alpha - beta)) hb
      (by positivity) (by positivity) (closure Q) (fun x => f (g n) x - B x)
      (fun x _ => by
        calc
          _ = |(f (g n) x - ctMoll (hs n) B x) + (ctMoll (hs n) B x - B x)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
          _ ≤ _ := add_le_add (hg0 n x) (he0 x))
      (fun x _ y _ => by
        calc
          _ = |((f (g n) x - ctMoll (hs n) B x) - (f (g n) y - ctMoll (hs n) B y)) +
              ((ctMoll (hs n) B x - B x) - (ctMoll (hs n) B y - B y))| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
          _ ≤ _ := add_le_add (hlip x y) (hm x y)
          _ = _ := by ring)
    refine ⟨hbound.1, hbound.2.1, ?_⟩
    calc
      _ ≤ (eps n + C * hs n ^ alpha) + (2 * eps n + 2 * C * hs n ^ (alpha - beta)) := hbound.2.2
      _ = _ := by ring
  refine ⟨g, ?_, fun n => (hresult n).1, fun n => (hresult n).2.1, ?_⟩
  · have hlim : Tendsto (fun n => eps n + C * hs n ^ alpha) atTop (𝓝 0) := by
      have hpow : Tendsto (fun n => C * hs n ^ alpha) atTop (𝓝 0) := by
        simpa [Real.zero_rpow (ne_of_gt ha)] using
          ((Real.continuousAt_rpow_const 0 alpha (Or.inr ha.le)).tendsto.comp ht).const_mul C
      simpa using het.add hpow
    apply Metric.tendstoUniformly_iff.mpr
    intro e heps
    filter_upwards [hlim.eventually (gt_mem_nhds heps)] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    calc
      _ = |(f (g n) x - ctMoll (hs n) B x) + (ctMoll (hs n) B x - B x)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (hg0 n x) (ctMoll_sub_le (hp n) hC ha hincB x)
      _ < e := hn
  · have h1 : Tendsto (fun n => C * hs n ^ alpha) atTop (𝓝 0) := by
      simpa [Real.zero_rpow (ne_of_gt ha)] using
        ((Real.continuousAt_rpow_const 0 alpha (Or.inr ha.le)).tendsto.comp ht).const_mul C
    have h2 : Tendsto (fun n => 2 * C * hs n ^ (alpha - beta)) atTop (𝓝 0) := by
      simpa [Real.zero_rpow (ne_of_gt (sub_pos.mpr hba))] using
        ((Real.continuousAt_rpow_const 0 (alpha - beta) (Or.inr (sub_pos.mpr hba).le)).tendsto.comp ht).const_mul (2 * C)
    apply squeeze_zero (fun n => ?_) (fun n => (hresult n).2.2)
      (by simpa only [add_zero, mul_zero] using ((het.const_mul 3).add h1).add h2)
    apply add_nonneg _ (holderSeminorm_nonneg _ _ _)
    apply Real.sSup_nonneg
    rintro v ⟨x, _, rfl⟩
    exact abs_nonneg _

end SubdiffusiveProcess.Section9
