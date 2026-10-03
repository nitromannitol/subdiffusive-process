module

public import SubdiffusiveProcess.Paper.Support.Cor32ProbabilitySupport

@[expose] public section





open MeasureTheory Filter Set SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

lemma aux_cor_32_prefix {A B : Type*}
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

/-- Literal nonempty-prefix count transferred through the actual represented law. -/
lemma aux_cor_32_transfer_chain {A X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (P : Measure Ω) (mu : Measure X) (field : Ω → X)
    (hf : Measurable field) (hlaw : Measure.map field P = mu)
    (Good : (n : ℕ) → (Fin n → A) → Set X)
    (theta : ℝ) (B : X → ℝ) (hB : Measurable B) (hB0 : ∀ x, 0 ≤ B x)
    (hc : ∀ᵐ x ∂mu, ∀ (J : ℕ) (pi : Fin J → A), 1 ≤ J →
      (Set.ncard {i : Fin J | x ∉ Good ((List.ofFn pi).take (i.val + 1)).length
        ((List.ofFn pi).take (i.val + 1)).get} : ℝ) ≤ theta * (J : ℝ) + B x) :
    ∃ B' : Ω → ℝ, Measurable B' ∧ (∀ omega, 0 ≤ B' omega) ∧
      ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J → ∀ pi : Fin J → A,
        (Nat.card {j : Fin J // field omega ∉ Good (j.val + 1)
          (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          theta * (J : ℝ) + B' omega := by
  rw [← hlaw] at hc
  have hae := ae_of_ae_map hf.aemeasurable hc
  refine ⟨B ∘ field, hB.comp hf, fun omega => hB0 (field omega), ?_⟩
  filter_upwards [hae] with omega h J hJ pi
  have heq (i : Fin J) := aux_cor_32_prefix Good J (i.val + 1) (by omega) pi
  simpa only [heq, Nat.card_coe_set_eq, Function.comp_apply] using! h J pi hJ

/-- A guard proved on the first actual event does not increase the a.s. union budget. -/
lemma aux_cor_32_guarded_pair_chain {d H1 : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (Good0 Good1 : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω)
    (Guard : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω → Prop)
    (hGuard : ∀ n w, ∀ᵐ omega ∂P, omega ∈ Good0 n w → Guard n w omega)
    (theta : ℝ)
    (h0 : ∃ B0 : Ω → ℝ, Measurable B0 ∧ (∀ omega, 0 ≤ B0 omega) ∧
      ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
        ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
        (Nat.card {j : Fin J // omega ∉ Good0 (j.val + 1)
          (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          (theta / 4) * J + B0 omega)
    (h1 : ∃ B1 : Ω → ℝ, Measurable B1 ∧ (∀ omega, 0 ≤ B1 omega) ∧
      ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
        ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
        (Nat.card {j : Fin J // omega ∉ Good1 (j.val + 1)
          (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          (theta / 4) * J + B1 omega) :
    let Base := fun n w => {omega | omega ∈ Good0 n w ∧ omega ∈ Good1 n w ∧ Guard n w omega}
    ∃ B : Ω → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
      ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
        ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
        (Nat.card {j : Fin J // omega ∉ Base (j.val + 1)
          (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          (theta / 2) * J + B omega := by
  intro Base
  obtain ⟨B0, hB0m, hB00, hb0⟩ := h0
  obtain ⟨B1, hB1m, hB10, hb1⟩ := h1
  have hg : ∀ᵐ omega ∂P, ∀ c : Σ n : ℕ, Fin n → OddGridIndex d (subdivisionHalfWidth H1),
      omega ∈ Good0 c.1 c.2 → Guard c.1 c.2 omega :=
    ae_all_iff.mpr fun c => hGuard c.1 c.2
  refine ⟨fun omega => B0 omega + B1 omega, hB0m.add hB1m,
    fun omega => add_nonneg (hB00 omega) (hB10 omega), ?_⟩
  filter_upwards [hg, hb0, hb1] with omega hg hb0 hb1 J hJ pi
  have heq : ∀ n w, (omega ∈ Base n w) ↔ (omega ∈ Good0 n w ∧ omega ∈ Good1 n w) := by
    intro n w
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hg ⟨n, w⟩ h.1⟩⟩
  simp only [heq]
  have h := aux_cor_32_card_and_le H1 Good0 Good1 omega J pi
    (theta / 4) (theta / 4) (B0 omega) (B1 omega) (hb0 J hJ pi) (hb1 J hJ pi)
  convert h using 1
  ring

end Paper
