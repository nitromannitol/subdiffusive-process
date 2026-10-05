module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology BigOperators ENNReal NNReal

namespace SubdiffusiveProcess.Paper

lemma aux_reference_coefficients_kappa_ratio_bounds
    (d : ℕ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (kappa : ℕ → ℝ)
    (hkappa : ∀ N, kappa N =
      Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)
    (N k : ℕ) (hkn : k ≤ N) :
    Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ≤
        kappa (N-k) / kappa N ∧
      kappa (N-k) / kappa N ≤
        Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  have hahom_pos : ∀ n, 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M n := by
    intro n
    exact SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M n
  have hkappa_pos : ∀ n, 0 < kappa n := by
    intro n
    rw [hkappa]
    exact mul_pos (Real.exp_pos _) (hahom_pos n)
  by_cases hk : k = 0
  · subst k
    have hN0 : kappa N ≠ 0 := ne_of_gt (hkappa_pos N)
    constructor <;> simp [hN0]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hlt : N - k < N := by omega
    obtain ⟨hmono, hupper⟩ :=
      (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).2 M N (N-k) hlt
    have hdiff : N - (N-k) = k := by omega
    rw [hdiff] at hupper
    have hN : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := hahom_pos N
    have hNk : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) := hahom_pos (N-k)
    have hratio_lower :
        1 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
      (one_le_div₀ hN).2 hmono
    have hratio_upper :
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤
          Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) := by
      rw [div_le_iff₀ hN]
      exact hupper
    have hratio :
        kappa (N-k) / kappa N =
          Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := by
      rw [hkappa, hkappa]
      field_simp [ne_of_gt hN, ne_of_gt hNk]
      rw [← Real.exp_add]
      congr 1
      rw [Nat.cast_sub hkn]
      ring
    constructor
    · rw [hratio]
      calc
        Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) =
            Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) * 1 := by
          rw [mul_one]
        _ ≤
            Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
              (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) :=
          mul_le_mul_of_nonneg_left hratio_lower (Real.exp_pos _).le
    · rw [hratio]
      calc
        Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
              (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) ≤
            Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
              Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio_upper (Real.exp_pos _).le
        _ = Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
          rw [← Real.exp_add]
          congr 1
          ring

lemma aux_reference_coefficients_extract_bounded
    (N : ℕ → ℕ) (_hN : StrictMono N)
    (f : ℕ → ℕ → ℝ) (lo hi : ℕ → ℝ)
    (hlo : ∀ k, 0 < lo k) (hlohi : ∀ k, lo k ≤ hi k)
    (hr : ∀ n k, k ≤ n → lo k ≤ f n k ∧ f n k ≤ hi k) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ e : ℕ → ℝ,
      (∀ k, 0 < e k) ∧
      (∀ k, Tendsto (fun j => f (N (s j)) k) atTop (𝓝 (e k))) := by
  let X : ℕ → Type := fun k => Set.Icc (lo k) (hi k)
  let : ∀ k, CompactSpace (X k) := by
    intro k
    dsimp [X]
    infer_instance
  let x : ℕ → (∀ k, X k) := fun n k =>
    if h : k ≤ N n then
      ⟨f (N n) k, (hr (N n) k h).1, (hr (N n) k h).2⟩
    else
      ⟨lo k, le_rfl, hlohi k |>.trans (le_rfl : hi k ≤ hi k)⟩
  obtain ⟨a, s, hs, hconv⟩ := CompactSpace.tendsto_subseq x
  refine ⟨s, hs, (fun k => (a k : ℝ)), ?_, ?_⟩
  · intro k
    exact lt_of_lt_of_le (hlo k) (a k).property.1
  · intro k
    have hcoord :
        Tendsto (fun j => ((x (s j)) k : ℝ)) atTop (𝓝 (a k : ℝ)) := by
      have hcont : Continuous (fun y : (∀ k, X k) => ((y k : X k) : ℝ)) :=
        continuous_subtype_val.comp (continuous_apply k)
      exact (hcont.tendsto a).comp hconv
    have hev : ∀ᶠ j in atTop, k ≤ N (s j) := by
      exact (StrictMono.tendsto_atTop _hN |>.comp hs.tendsto_atTop).eventually
        (eventually_ge_atTop k)
    have heq : ∀ᶠ j in atTop, ((x (s j)) k : ℝ) = f (N (s j)) k := by
      filter_upwards [hev] with j hj
      simp [x, hj]
    exact (hcoord.congr' heq)



theorem reference_coefficients
    (d : ℕ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (kappa : ℕ → ℝ)
    (hkappa : ∀ N, kappa N =
      Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
    (C : ℝ) (_hC : 0 < C)
    (_hordering : ∀ N k : ℕ, k ≤ N →
      |SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) - 1| ≤
        C * M.delta^2 * (k : ℝ) * Real.exp (C * M.delta^2 * (k : ℝ)))
    (_horderpos : ∀ N k : ℕ, k ≤ N →
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k))
    (H : SpatialCoordinates d → ℝ) (g : ℤ → SpatialCoordinates d → ℝ) :
    (∀ k, ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ ∀ N, k ≤ N →
      lo ≤ kappa (N-k) / kappa N ∧ kappa (N-k) / kappa N ≤ hi) ∧
    (∃ sE sF : ℕ → ℕ, StrictMono sE ∧ StrictMono sF ∧ ∃ eE eF : ℕ → ℝ,
      (∀ k, 0 < eE k ∧ 0 < eF k) ∧
      (∀ k, Tendsto (fun j => kappa (NE (sE j)-k) / kappa (NE (sE j)))
        atTop (𝓝 (eE k))) ∧
      (∀ k, Tendsto (fun j => kappa (NF (sF j)-k) / kappa (NF (sF j)))
        atTop (𝓝 (eF k))) ∧
      (∀ k z,
        (eF k * Real.exp (H z + ∑ j ∈ Finset.range k, g (-(j : ℤ)) z)) /
        (eE k * Real.exp (H z + ∑ j ∈ Finset.range k, g (-(j : ℤ)) z)) =
          eF k / eE k)) := by
  let lo : ℕ → ℝ := fun k =>
    Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
  let hi : ℕ → ℝ := fun k =>
    Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
  have hlo : ∀ k, 0 < lo k := by
    intro k
    exact Real.exp_pos _
  have hlohi : ∀ k, lo k ≤ hi k := by
    intro k
    dsimp [lo, hi]
    rw [Real.exp_le_exp]
    exact neg_le_self (mul_nonneg (by positivity) M.G4.tauSq_pos.le)
  have hr : ∀ N k, k ≤ N → lo k ≤ kappa (N-k) / kappa N ∧
      kappa (N-k) / kappa N ≤ hi k := by
    intro N k hkn
    exact aux_reference_coefficients_kappa_ratio_bounds d M kappa hkappa N k hkn
  have hbounds : ∀ k, ∃ lo' hi' : ℝ, 0 < lo' ∧ lo' ≤ hi' ∧
      ∀ N, k ≤ N → lo' ≤ kappa (N-k) / kappa N ∧
        kappa (N-k) / kappa N ≤ hi' := by
    intro k
    exact ⟨lo k, hi k, hlo k, hlohi k, fun N hN => hr N k hN⟩
  constructor
  · exact hbounds
  · obtain ⟨sE, hsE, eE, heE, hlimE⟩ :=
      aux_reference_coefficients_extract_bounded NE hNE
        (fun N k => kappa (N-k) / kappa N) lo hi hlo hlohi
        (fun N k hNk => hr N k hNk)
    obtain ⟨sF, hsF, eF, heF, hlimF⟩ :=
      aux_reference_coefficients_extract_bounded NF hNF
        (fun N k => kappa (N-k) / kappa N) lo hi hlo hlohi
        (fun N k hNk => hr N k hNk)
    refine ⟨sE, sF, hsE, hsF, eE, eF, ?_, ?_, ?_, ?_⟩
    · exact fun k => ⟨heE k, heF k⟩
    · intro k
      simpa only using hlimE k
    · intro k
      simpa only using hlimF k
    · intro k z
      have heE0 : eE k ≠ 0 := ne_of_gt (heE k)
      have hexp0 : Real.exp (H z + ∑ j ∈ Finset.range k, g (-(j : ℤ)) z) ≠ 0 :=
        ne_of_gt (Real.exp_pos _)
      field_simp

end SubdiffusiveProcess.Paper
