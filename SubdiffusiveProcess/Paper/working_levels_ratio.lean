import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace Paper

lemma aux_working_levels_ratio_three_sets
    (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (A E B C : Set Om) (hA : 0 < P A) (hsub : A ⊆ E ∪ B ∪ C)
    (hE : P E < P A / 4) (hB : P B < P A / 4) (hC : P C < P A / 4) : False := by
  have htop : P A ≠ ∞ := measure_ne_top P A
  have hquarter : P A / 4 + P A / 4 + P A / 4 < P A := by
    rw [← ENNReal.add_div, ← ENNReal.add_div]
    rw [ENNReal.div_lt_iff (by simp) (by simp)]
    calc
      P A + P A + P A < (P A + P A + P A) + P A := by
        exact ENNReal.lt_add_right
          ((ENNReal.add_ne_top.2 ⟨(ENNReal.add_ne_top.2 ⟨htop, htop⟩), htop⟩)) hA.ne'
      _ = P A * 4 := by ring
  have hEB : P E + P B < P A / 4 + P A / 4 :=
    ENNReal.add_lt_add hE hB
  have hsum : P E + P B + P C < P A := by
    exact (ENNReal.add_lt_add hEB hC).trans
      (hquarter)
  have hle : P A ≤ P E + P B + P C := by
    calc
      P A ≤ P (E ∪ B ∪ C) := measure_mono hsub
      _ ≤ P (E ∪ B) + P C := measure_union_le _ _
      _ ≤ (P E + P B) + P C := add_le_add_left (measure_union_le _ _) _
  exact (lt_irrefl (P A)) (hle.trans_lt hsum)

lemma aux_working_levels_ratio_pos_level
    (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (f : Om → ℝ) (hf : ∀ᵐ ω ∂P, 0 < f ω) :
    ∃ a : ℝ, 0 < a ∧ 0 < P {ω | a ≤ f ω} := by
  let s : ℕ → Set Om := fun n => {ω | (1 / ((n : ℝ) + 1)) ≤ f ω}
  have hsubset : {ω | 0 < f ω} ⊆ ⋃ n, s n := by
    intro ω hω
    change 0 < f ω at hω
    obtain ⟨n, hn⟩ := exists_nat_gt (f ω)⁻¹
    have hnprod : 1 < f ω * (n : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left hn hω
      simpa [mul_inv_cancel₀ hω.ne', mul_comm] using hmul
    have hnprod' : 1 < f ω * ((n : ℝ) + 1) := by
      exact lt_of_lt_of_le hnprod (by nlinarith [hω.le])
    have hlt : 1 / ((n : ℝ) + 1) < f ω := by
      apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
      simpa [mul_comm] using hnprod'
    exact mem_iUnion.2 ⟨n, le_of_lt hlt⟩
  have hunion_ne : P (⋃ n, s n) ≠ 0 := by
    intro hzero
    have hzero' : P {ω | 0 < f ω} = 0 := measure_mono_null hsubset hzero
    have hcomp : P ({ω | 0 < f ω}ᶜ) = 0 := mem_ae_iff.mp hf
    have huniv : P (Set.univ : Set Om) ≤ P {ω | 0 < f ω} +
        P ({ω | 0 < f ω}ᶜ) := by
      calc
        P (Set.univ : Set Om) ≤ P ({ω | 0 < f ω} ∪ {ω | 0 < f ω}ᶜ) :=
          measure_mono (by simp)
        _ ≤ P {ω | 0 < f ω} + P ({ω | 0 < f ω}ᶜ) := measure_union_le _ _
    rw [hzero', hcomp, add_zero] at huniv
    rw [IsProbabilityMeasure.measure_univ] at huniv
    exact (by simpa using huniv)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion_ne
  exact ⟨1 / ((n : ℝ) + 1), by positivity, by simpa [s] using hn⟩

lemma aux_working_levels_ratio_core
    (a margin q t delta x y z : ℝ) (ha : 0 < a) (hm : 0 < margin)
    (hq : 0 < q) (hqle : q ≤ 1) (hqe : q = 1 - margin)
    (ht : t = margin * a / 8)
    (hdelta : delta < margin * a / 4) (hz : a ≤ z)
    (hx : |x - z| < t) (hy : |y - z| < t) : q * y + delta < x := by
  have hma : margin * a ≤ margin * z :=
    mul_le_mul_of_nonneg_left hz hm.le
  have hqz : q * z ≤ z - margin * a := by
    rw [hqe]
    calc
      (1 - margin) * z = z - margin * z := by ring
      _ ≤ z - margin * a := sub_le_sub_left hma _
  have hqt : q * t ≤ t := by
    have ht_nonneg : 0 ≤ t := by rw [ht]; positivity
    calc
      q * t ≤ 1 * t := mul_le_mul_of_nonneg_right hqle ht_nonneg
      _ = t := one_mul t
  have hcore : q * (z + t) + delta < z - t := by
    calc
      q * (z + t) + delta = q * z + q * t + delta := by ring
      _ ≤ (z - margin * a) + t + delta :=
        add_le_add (add_le_add hqz hqt) le_rfl
      _ < z - t := by
        rw [ht]
        have hma_pos : 0 < margin * a := mul_pos hm ha
        linarith only [hdelta, hma_pos]
  have hxlo : -t < x - z := (abs_lt.mp hx).1
  have hxhi : x - z < t := (abs_lt.mp hx).2
  have hyhi : y - z < t := (abs_lt.mp hy).2
  have hyupper : y < z + t := by linarith only [hyhi]
  have hxupper : z - t < x := by linarith only [hxlo]
  calc
    q * y + delta < q * (z + t) + delta :=
      add_lt_add_left (mul_lt_mul_of_pos_left hyupper hq) _
    _ < z - t := hcore
    _ < x := hxupper



theorem working_levels_ratio
    (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (kap elim : ℕ → ℝ) (hkap : ∀ n : ℕ, 0 < kap n) (helim : ∀ k : ℕ, 0 < elim k)
    (hconv : ∀ k : ℕ,
      Tendsto (fun N : ℕ => kap (N - k) / kap N) atTop (𝓝 (elim k)))
    (vartheta : ℝ) (hvar_0 : 0 < vartheta) (hvar_1 : vartheta < 1 / 3)
    (H1 : ℕ) (hH1 : 0 < H1) (Cgeom : ℝ) (hCgeom : 0 ≤ Cgeom)
    (Lam : ℕ → Om → ℝ) (LamE : Om → ℝ)
    (hLam_meas : ∀ N : ℕ, Measurable (Lam N)) (hLamE_meas : Measurable LamE)
    (hLamE_pos : ∀ᵐ ω ∂P, 0 < LamE ω)
    (hLamconv : TendstoInMeasure P Lam atTop LamE)
    (hfinite : ∀ eta : ℝ, 0 < eta →
      ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
      ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
      ∀ (c : ℝ), 0 < c → c ≤ 2 →
      ∀ (S : Finset ℕ),
        vartheta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ)
          ≤ (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ S} : ℝ) →
        ((∀ n : ℕ, n ∈ S → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
            (kap (N - H1 * n) / kap N) / (kap (M - H1 * n) / kap M) ≤ c) →
          P {ω : Om | c * (1 + Cgeom * eta) * Lam M ω +
              Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam N ω}
            ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))) ∧
        ((∀ n : ℕ, n ∈ S → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
            (kap (M - H1 * n) / kap M) / (kap (N - H1 * n) / kap N) ≤ c) →
          P {ω : Om | c * (1 + Cgeom * eta) * Lam N ω +
              Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam M ω}
            ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))))) :
    ∀ eps : ℝ, 0 < eps →
      ∃ Ne : ℕ, ∀ N : ℕ, Ne ≤ N →
        (1 - 2 * vartheta) *
            (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ)
          < (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧
              |(kap (N - H1 * n) / kap N) / elim (H1 * n) - 1| ≤ eps} : ℝ) := by
  intro eps heps
  let e : ℝ := min eps (1 / 2)
  have hepos : 0 < e := lt_min heps (by norm_num)
  have heleps : e ≤ eps := min_le_left _ _
  have hehalf : e ≤ (1 / 2 : ℝ) := min_le_right _ _
  obtain ⟨a, ha, hA⟩ := aux_working_levels_ratio_pos_level Om P LamE hLamE_pos
  let eta : ℝ := e / (16 * (Cgeom + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨Ceta, gamma, N0, hCeta, hgamma, hN0⟩ := hfinite eta heta
  have hCeta_pos : 0 < Ceta := hCeta
  have hgamma_pos : 0 < gamma := hgamma
  let c : ℝ := 1 - e / 2
  have hcpos : 0 < c := by
    dsimp [c]
    linarith
  have hcone : c ≤ 2 := by
    dsimp [c]
    linarith
  have hCeta_mul : Cgeom * eta ≤ e / 16 := by
    dsimp [eta]
    calc
      Cgeom * (e / (16 * (Cgeom + 1))) =
          (Cgeom * e) / (16 * (Cgeom + 1)) := by ring
      _ ≤ e / 16 := by
        apply (div_le_iff₀ (by positivity : 0 < 16 * (Cgeom + 1))).2
        nlinarith [hCgeom]
  have hqpos : 0 < c * (1 + Cgeom * eta) := by
    apply mul_pos hcpos
    nlinarith [hCgeom, hCeta_mul]
  let q : ℝ := c * (1 + Cgeom * eta)
  have hq_lt : q < 1 := by
    have hqbound : c * (1 + Cgeom * eta) ≤ c * (1 + e / 16) :=
      mul_le_mul_of_nonneg_left (by linarith [hCeta_mul]) (by linarith : 0 ≤ c)
    dsimp [q, c] at hqbound ⊢
    nlinarith [hqbound, sq_nonneg e]
  let margin : ℝ := 1 - q
  have hmargin : 0 < margin := by
    dsimp [margin]
    linarith
  let t : ℝ := margin * a / 8
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (mul_pos hmargin ha) (by norm_num)
  have hq_eq : q = 1 - margin := by
    dsimp [margin]
    ring
  have ht_eq : t = margin * a / 8 := by rfl
  have hp_top : P {ω | a ≤ LamE ω} ≠ ∞ := measure_ne_top P _
  have hpR : 0 < (P {ω | a ≤ LamE ω}).toReal :=
    ENNReal.toReal_pos (ne_of_gt hA) hp_top
  have hLamdist := (tendstoInMeasure_iff_dist.mp hLamconv) t ht
  have hLam_event : ∀ᶠ N : ℕ in atTop,
      P {ω | t ≤ dist (Lam N ω) (LamE ω)} < P {ω | a ≤ LamE ω} / 4 :=
    hLamdist.eventually_lt_const (ENNReal.div_pos hA.ne' (by norm_num))
  obtain ⟨Nlam, hNlam⟩ := eventually_atTop.1 hLam_event
  have hpow : Tendsto (fun N : ℕ => Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))
      atTop (𝓝 0) := by
    have hlin : Tendsto (fun N : ℕ => gamma * (N : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).const_mul_atTop'
        hgamma_pos
    have hbot : Tendsto (fun N : ℕ => -(gamma * (N : ℝ))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hlin
    have hpows : Tendsto (fun N : ℕ => (3 : ℝ) ^ (-(gamma * (N : ℝ))))
        atTop (𝓝 0) :=
      (tendsto_rpow_atBot_of_base_gt_one (3 : ℝ) (by norm_num)).comp hbot
    simpa [neg_mul] using hpows.const_mul Ceta
  have hdelta_event : ∀ᶠ N : ℕ in atTop,
      Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) <
        min ((P {ω | a ≤ LamE ω}).toReal / 4) (margin * a / 4) :=
    hpow.eventually_lt_const (by
      apply lt_min
      · positivity
      · positivity)
  obtain ⟨Ndelta, hNdelta⟩ := eventually_atTop.1 hdelta_event
  let Ne : ℕ := max N0 (max Nlam Ndelta)
  refine ⟨Ne, ?_⟩
  intro N hN
  classical
  let W : Finset ℕ := (Finset.range (3 * N + 1)).filter
    (fun n => N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N)
  have hH1nat : 0 < H1 := hH1
  have hWmem : ∀ n : ℕ, n ∈ W ↔
      N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N := by
    intro n
    constructor
    · intro hn
      exact (Finset.mem_filter.1 hn).2
    · intro hn
      have hnH : n ≤ H1 * n := Nat.le_mul_of_pos_left n hH1nat
      have hn4 : 4 * n ≤ 4 * (H1 * n) := Nat.mul_le_mul_left 4 hnH
      have hn3 : n ≤ 3 * N := by omega
      apply Finset.mem_filter.2
      exact ⟨Finset.mem_range.2 (by omega), hn⟩
  let ratio : ℕ → ℝ := fun n =>
    (kap (N - H1 * n) / kap N) / elim (H1 * n)
  let good : ℕ → Prop := fun n => |ratio n - 1| ≤ eps
  let low : ℕ → Prop := fun n => ratio n ≤ 1 - e
  let high : ℕ → Prop := fun n => 1 + e ≤ ratio n
  let G : Finset ℕ := W.filter good
  let L : Finset ℕ := W.filter low
  let U : Finset ℕ := W.filter high
  have hGsub : ∀ n ∈ G, n ∈ W := by
    intro n hn
    exact (Finset.mem_filter.1 hn).1
  have hLsub : ∀ n ∈ L, n ∈ W := by
    intro n hn
    exact (Finset.mem_filter.1 hn).1
  have hUsub : ∀ n ∈ U, n ∈ W := by
    intro n hn
    exact (Finset.mem_filter.1 hn).1
  have hcard_window : Nat.card {n : ℕ //
      N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} = W.card := by
    letI : Fintype {n : ℕ //
        N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} :=
      Fintype.ofFinset W (fun n => hWmem n)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofFinset W (fun n => hWmem n)
  have hcard_filter (p : ℕ → Prop) [DecidablePred p] :
      Nat.card {n : ℕ //
        N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ p n} =
        (W.filter p).card := by
    have hp_mem : ∀ n : ℕ, n ∈ W.filter p ↔
        N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ p n := by
      intro n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hnW, hnp⟩
        have hw := (hWmem n).1 hnW
        exact ⟨hw.1, hw.2, hnp⟩
      · rintro ⟨hn1, hn2, hnp⟩
        exact ⟨(hWmem n).2 ⟨hn1, hn2⟩, hnp⟩
    letI : Fintype {n : ℕ //
        N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ p n} :=
      Fintype.ofFinset (W.filter p) hp_mem
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofFinset (W.filter p) hp_mem
  have hcard_subfinset (T : Finset ℕ) (hT : ∀ n ∈ T,
      N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N) :
      Nat.card {n : ℕ //
        N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ T} = T.card := by
    have hT_mem : ∀ n : ℕ, n ∈ T ↔
        N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ T := by
      intro n
      constructor
      · intro hn
        have ht := hT n hn
        exact ⟨ht.1, ht.2, hn⟩
      · intro hn
        exact hn.2.2
    letI : Fintype {n : ℕ //
        N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ T} :=
      Fintype.ofFinset T hT_mem
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofFinset T hT_mem
  have hcard_L : Nat.card {n : ℕ //
      N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ L} = L.card := by
    apply hcard_subfinset L
    intro n hn
    exact (hWmem n).1 (hLsub n hn)
  have hcard_U : Nat.card {n : ℕ //
      N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ U} = U.card := by
    apply hcard_subfinset U
    intro n hn
    exact (hWmem n).1 (hUsub n hn)
  have hcard_G : Nat.card {n : ℕ //
      N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ good n} = G.card := by
    simpa [G] using hcard_filter good
  have hpartition : W ⊆ G ∪ L ∪ U := by
    intro n hn
    by_cases hg : good n
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hn, hg⟩))
    by_cases hnle : ratio n ≤ 1
    · have habs : eps < |ratio n - 1| := lt_of_not_ge hg
      have habs' : eps < 1 - ratio n := by
        simpa [abs_of_nonpos (sub_nonpos.mpr hnle)] using habs
      have hlow : low n := by
        dsimp [low]
        linarith
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hn, hlow⟩))
    · have habs : eps < |ratio n - 1| := lt_of_not_ge hg
      have habs' : eps < ratio n - 1 := by
        simpa [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hnle))] using habs
      have hhigh : high n := by
        dsimp [high]
        linarith
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hn, hhigh⟩)
  have hcard_le : W.card ≤ G.card + L.card + U.card := by
    calc
      W.card ≤ (G ∪ L ∪ U).card := Finset.card_le_card hpartition
      _ ≤ (G ∪ L).card + U.card := Finset.card_union_le _ _
      _ ≤ G.card + L.card + U.card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
  by_contra hnot
  have hnot' : (G.card : ℝ) ≤ (1 - 2 * vartheta) * (W.card : ℝ) := by
    apply le_of_not_gt
    intro hgt
    apply hnot
    rw [hcard_window, hcard_G]
    simpa [good, ratio] using hgt
  have hL_or_U : (vartheta : ℝ) * (W.card : ℝ) ≤ L.card ∨
      (vartheta : ℝ) * (W.card : ℝ) ≤ U.card := by
    by_cases hL : (vartheta : ℝ) * (W.card : ℝ) ≤ L.card
    · exact Or.inl hL
    · right
      by_contra hU
      have hL' : (L.card : ℝ) < vartheta * (W.card : ℝ) := lt_of_not_ge hL
      have hU' : (U.card : ℝ) < vartheta * (W.card : ℝ) := lt_of_not_ge hU
      have hcard_real : (W.card : ℝ) ≤ (G.card : ℝ) + L.card + U.card := by
        exact_mod_cast hcard_le
      nlinarith
  rcases hL_or_U with hL | hU
  · have hN0N : N0 ≤ N := by
      have hNeN : max N0 (max Nlam Ndelta) ≤ N := by simpa [Ne] using hN
      exact le_trans (le_max_left _ _) hNeN
    have hNlamN : Nlam ≤ N := by
      have hNeN : max N0 (max Nlam Ndelta) ≤ N := by simpa [Ne] using hN
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hNeN)
    have hNdN : Ndelta ≤ N := by
      have hNeN : max N0 (max Nlam Ndelta) ≤ N := by simpa [Ne] using hN
      exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hNeN)
    have hratio_each : ∀ n ∈ L, ∀ᶠ M : ℕ in atTop,
        (kap (N - H1 * n) / kap N) / (kap (M - H1 * n) / kap M) ≤ c := by
      intro n hn
      have hnlow : ratio n ≤ 1 - e := (Finset.mem_filter.1 hn).2
      have hlim : Tendsto
          (fun M : ℕ => (kap (N - H1 * n) / kap N) /
            (kap (M - H1 * n) / kap M)) atTop
          (𝓝 ((kap (N - H1 * n) / kap N) / elim (H1 * n))) := by
        simpa using (tendsto_const_nhds.div (hconv (H1 * n))
          (ne_of_gt (helim (H1 * n))))
      have hlt : (kap (N - H1 * n) / kap N) / elim (H1 * n) < c := by
        dsimp [ratio] at hnlow
        dsimp [c]
        linarith
      exact (hlim.eventually_lt_const hlt).mono fun _ h => h.le
    have hratio_all : ∀ᶠ M : ℕ in atTop, ∀ n ∈ L,
        (kap (N - H1 * n) / kap N) / (kap (M - H1 * n) / kap M) ≤ c :=
      (Finset.eventually_all L).2 hratio_each
    have hM_event : ∀ᶠ M : ℕ in atTop,
        (∀ n ∈ L, (kap (N - H1 * n) / kap N) /
          (kap (M - H1 * n) / kap M) ≤ c) ∧ N ≤ M ∧ Nlam ≤ M := by
      exact hratio_all.and ((eventually_ge_atTop N).and (eventually_ge_atTop Nlam))
    obtain ⟨M0, hM0⟩ := eventually_atTop.1 hM_event
    have hMratio := (hM0 M0 le_rfl).1
    have hNM : N ≤ M0 := (hM0 M0 le_rfl).2.1
    have hNlamM : Nlam ≤ M0 := (hM0 M0 le_rfl).2.2
    have hLd : vartheta *
        (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
        (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ L} : ℝ) := by
      simpa [hcard_window, hcard_L] using hL
    have hfinite_lower := hN0 N M0 hN0N hNM c hcpos hcone L hLd
    have hratio_finite : ∀ n : ℕ, n ∈ L → N ≤ 4 * (H1 * n) →
        4 * (H1 * n) ≤ 3 * N →
        (kap (N - H1 * n) / kap N) / (kap (M0 - H1 * n) / kap M0) ≤ c := by
      intro n hn _ _
      exact hMratio n hn
    have hEbound : P {ω : Om |
        q * Lam M0 ω + Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam N ω} ≤
        ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) := by
      simpa [q] using hfinite_lower.1 hratio_finite
    have hdeltaR : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) <
        (P {ω | a ≤ LamE ω}).toReal / 4 := by
      exact lt_of_lt_of_le (hNdelta N hNdN) (min_le_left _ _)
    have hdeltaM : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < margin * a / 4 := by
      exact lt_of_lt_of_le (hNdelta N hNdN) (min_le_right _ _)
    have hof : ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) <
        P {ω | a ≤ LamE ω} / 4 := by
      calc
        ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) <
            ENNReal.ofReal ((P {ω | a ≤ LamE ω}).toReal / 4) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hdeltaR
        _ = P {ω | a ≤ LamE ω} / 4 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal hp_top]
          norm_num
    let Aset : Set Om := {ω | a ≤ LamE ω}
    let BN : Set Om := {ω | t ≤ dist (Lam N ω) (LamE ω)}
    let BM : Set Om := {ω | t ≤ dist (Lam M0 ω) (LamE ω)}
    let Eset : Set Om := {ω | q * Lam M0 ω +
        Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam N ω}
    have hAset : 0 < P Aset := by simpa [Aset] using hA
    have hEset : P Eset < P Aset / 4 := by
      exact (show P Eset ≤ _ by simpa [Eset] using hEbound).trans_lt
        (by simpa [Aset] using hof)
    have hBN : P BN < P Aset / 4 := by
      simpa [BN, Aset] using hNlam N hNlamN
    have hBM : P BM < P Aset / 4 := by
      simpa [BM, Aset] using hNlam M0 hNlamM
    have hsub : Aset ⊆ Eset ∪ BN ∪ BM := by
      intro ω hω
      by_cases hωN : ω ∈ BN
      · exact Or.inl (Or.inr hωN)
      by_cases hωM : ω ∈ BM
      · exact Or.inr hωM
      have hNdist : dist (Lam N ω) (LamE ω) < t := lt_of_not_ge hωN
      have hMdist : dist (Lam M0 ω) (LamE ω) < t := lt_of_not_ge hωM
      have hNabs : |Lam N ω - LamE ω| < t := by
        simpa [Real.dist_eq] using hNdist
      have hMabs : |Lam M0 ω - LamE ω| < t := by
        simpa [Real.dist_eq] using hMdist
      have hω' : a ≤ LamE ω := hω
      have hE : ω ∈ Eset := by
        dsimp [Eset]
        exact aux_working_levels_ratio_core a margin q t
          (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) (Lam N ω) (Lam M0 ω)
          (LamE ω) ha hmargin hqpos hq_lt.le hq_eq ht_eq hdeltaM hω'
          hNabs hMabs
      exact Or.inl (Or.inl hE)
    exact aux_working_levels_ratio_three_sets Om P Aset Eset BN BM hAset hsub hEset hBN hBM

  · have hN0N : N0 ≤ N := by
      have hNeN : max N0 (max Nlam Ndelta) ≤ N := by simpa [Ne] using hN
      exact le_trans (le_max_left _ _) hNeN
    have hNlamN : Nlam ≤ N := by
      have hNeN : max N0 (max Nlam Ndelta) ≤ N := by simpa [Ne] using hN
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hNeN)
    have hNdN : Ndelta ≤ N := by
      have hNeN : max N0 (max Nlam Ndelta) ≤ N := by simpa [Ne] using hN
      exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hNeN)
    have hratio_each : ∀ n ∈ U, ∀ᶠ M : ℕ in atTop,
        (kap (M - H1 * n) / kap M) / (kap (N - H1 * n) / kap N) ≤ c := by
      intro n hn
      have hnhigh : 1 + e ≤ ratio n := (Finset.mem_filter.1 hn).2
      have hAn : 0 < kap (N - H1 * n) / kap N :=
        div_pos (hkap (N - H1 * n)) (hkap N)
      have hlim : Tendsto
          (fun M : ℕ => (kap (M - H1 * n) / kap M) /
            (kap (N - H1 * n) / kap N)) atTop
          (𝓝 (elim (H1 * n) / (kap (N - H1 * n) / kap N))) := by
        simpa using (hconv (H1 * n)).div tendsto_const_nhds (ne_of_gt hAn)
      have hbad : (1 + e) * elim (H1 * n) ≤
          kap (N - H1 * n) / kap N := by
        dsimp [ratio] at hnhigh
        exact (le_div_iff₀ (helim (H1 * n))).mp hnhigh
      have he_lt_one : e < 1 := lt_of_le_of_lt hehalf (by norm_num)
      have heprod : 0 < e * (1 - e) :=
        mul_pos hepos (sub_pos.mpr he_lt_one)
      have hprod_gt : 1 < c * (1 + e) := by
        dsimp [c]
        calc
          (1 : ℝ) < 1 + e * (1 - e) / 2 := by linarith
          _ = (1 - e / 2) * (1 + e) := by ring
      have hscale : elim (H1 * n) < c * ((1 + e) * elim (H1 * n)) := by
        have hs := mul_lt_mul_of_pos_right hprod_gt (helim (H1 * n))
        simpa [mul_assoc] using hs
      have hlt_num : elim (H1 * n) <
          c * (kap (N - H1 * n) / kap N) := by
        have hmul := mul_le_mul_of_nonneg_left hbad hcpos.le
        exact hscale.trans_le hmul
      have hlt : elim (H1 * n) / (kap (N - H1 * n) / kap N) < c :=
        (div_lt_iff₀ hAn).2 hlt_num
      exact (hlim.eventually_lt_const hlt).mono fun _ h => h.le
    have hratio_all : ∀ᶠ M : ℕ in atTop, ∀ n ∈ U,
        (kap (M - H1 * n) / kap M) /
          (kap (N - H1 * n) / kap N) ≤ c :=
      (Finset.eventually_all U).2 hratio_each
    have hM_event : ∀ᶠ M : ℕ in atTop,
        (∀ n ∈ U, (kap (M - H1 * n) / kap M) /
          (kap (N - H1 * n) / kap N) ≤ c) ∧ N ≤ M ∧ Nlam ≤ M := by
      exact hratio_all.and ((eventually_ge_atTop N).and (eventually_ge_atTop Nlam))
    obtain ⟨M0, hM0⟩ := eventually_atTop.1 hM_event
    have hMratio := (hM0 M0 le_rfl).1
    have hNM : N ≤ M0 := (hM0 M0 le_rfl).2.1
    have hNlamM : Nlam ≤ M0 := (hM0 M0 le_rfl).2.2
    have hUd : vartheta *
        (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
        (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ U} : ℝ) := by
      simpa [hcard_window, hcard_U] using hU
    have hfinite_upper := hN0 N M0 hN0N hNM c hcpos hcone U hUd
    have hratio_finite : ∀ n : ℕ, n ∈ U → N ≤ 4 * (H1 * n) →
        4 * (H1 * n) ≤ 3 * N →
        (kap (M0 - H1 * n) / kap M0) / (kap (N - H1 * n) / kap N) ≤ c := by
      intro n hn _ _
      exact hMratio n hn
    have hEbound : P {ω : Om |
        q * Lam N ω + Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam M0 ω} ≤
        ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) := by
      simpa [q] using hfinite_upper.2 hratio_finite
    have hdeltaR : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) <
        (P {ω | a ≤ LamE ω}).toReal / 4 := by
      exact lt_of_lt_of_le (hNdelta N hNdN) (min_le_left _ _)
    have hdeltaM : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < margin * a / 4 := by
      exact lt_of_lt_of_le (hNdelta N hNdN) (min_le_right _ _)
    have hof : ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) <
        P {ω | a ≤ LamE ω} / 4 := by
      calc
        ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) <
            ENNReal.ofReal ((P {ω | a ≤ LamE ω}).toReal / 4) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hdeltaR
        _ = P {ω | a ≤ LamE ω} / 4 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal hp_top]
          norm_num
    let Aset : Set Om := {ω | a ≤ LamE ω}
    let BN : Set Om := {ω | t ≤ dist (Lam N ω) (LamE ω)}
    let BM : Set Om := {ω | t ≤ dist (Lam M0 ω) (LamE ω)}
    let Eset : Set Om := {ω | q * Lam N ω +
        Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam M0 ω}
    have hAset : 0 < P Aset := by simpa [Aset] using hA
    have hEset : P Eset < P Aset / 4 := by
      exact (show P Eset ≤ _ by simpa [Eset] using hEbound).trans_lt
        (by simpa [Aset] using hof)
    have hBN : P BN < P Aset / 4 := by
      simpa [BN, Aset] using hNlam N hNlamN
    have hBM : P BM < P Aset / 4 := by
      simpa [BM, Aset] using hNlam M0 hNlamM
    have hsub : Aset ⊆ Eset ∪ BN ∪ BM := by
      intro ω hω
      by_cases hωN : ω ∈ BN
      · exact Or.inl (Or.inr hωN)
      by_cases hωM : ω ∈ BM
      · exact Or.inr hωM
      have hNdist : dist (Lam N ω) (LamE ω) < t := lt_of_not_ge hωN
      have hMdist : dist (Lam M0 ω) (LamE ω) < t := lt_of_not_ge hωM
      have hNabs : |Lam N ω - LamE ω| < t := by
        simpa [Real.dist_eq] using hNdist
      have hMabs : |Lam M0 ω - LamE ω| < t := by
        simpa [Real.dist_eq] using hMdist
      have hω' : a ≤ LamE ω := hω
      have hE : ω ∈ Eset := by
        dsimp [Eset]
        exact aux_working_levels_ratio_core a margin q t
          (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) (Lam M0 ω) (Lam N ω)
          (LamE ω) ha hmargin hqpos hq_lt.le hq_eq ht_eq hdeltaM hω'
          hMabs hNabs
      exact Or.inl (Or.inl hE)
    exact aux_working_levels_ratio_three_sets Om P Aset Eset BN BM hAset hsub hEset hBN hBM

end Paper
