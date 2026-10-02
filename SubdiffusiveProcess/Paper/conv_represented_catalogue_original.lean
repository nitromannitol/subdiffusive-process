import Mathlib
import SubdiffusiveProcess.Paper.conv_represented_env_interface
import SubdiffusiveProcess.Paper.conv_represented_estimates_transfer
import SubdiffusiveProcess.Paper.conv_represented_catalogue_sources
import SubdiffusiveProcess.Paper.conv_represented_catalogue_traces_buffered
import SubdiffusiveProcess.Paper.conv_represented_env_interface_buffered
import SubdiffusiveProcess.Paper.conv_represented_catalogue_coercivity_clause
import SubdiffusiveProcess.Paper.conv_represented_catalogue_source_clause
import SubdiffusiveProcess.Paper.conv_represented_catalogue_cell_clause
import SubdiffusiveProcess.Paper.conv_represented_catalogue_source_response
import SubdiffusiveProcess.Paper.conv_represented_catalogue_cell_response
import SubdiffusiveProcess.Paper.conv_represented_catalogue_smooth_class
import SubdiffusiveProcess.Paper.conv_represented_tight_of_bounded
import SubdiffusiveProcess.Paper.model_triadic_cube_coercivity
import SubdiffusiveProcess.Paper.model_cube_coarse_bank
import SubdiffusiveProcess.Paper.model_cube_trace_bound
import SubdiffusiveProcess.Paper.conv_represented_grid_clause_bank

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Countable key type of the catalogue: coercivity, extension, lambda (per cube), source growth and
Hölder (per source), cell growth and Hölder (per trace), grid constants, and the two response families. -/
abbrev aux_conv_represented_catalogue_original_Key (D : ℕ → Type) : Type :=
  ℕ ⊕ ℕ ⊕ ℕ ⊕ (Σ i, D i) ⊕ (Σ i, D i) ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ ⊕ (Σ i, D i) ⊕ (ℕ × ℕ)

open Classical in
/-- A keyed family extended by zero off the range of the key map. -/
def aux_conv_represented_catalogue_original_ext {Key Ω : Type} (κ : Key → ℕ)
    (c : Key → ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ := fun idx N β =>
  if h : ∃ k, κ k = idx then c (Classical.choose h) N β else 0

theorem aux_conv_represented_catalogue_original_ext_cases {Key Ω : Type} (κ : Key → ℕ)
    (c : Key → ℕ → Ω → ℝ) (idx : ℕ) :
    (∃ k, κ k = idx ∧ ∀ N β, aux_conv_represented_catalogue_original_ext κ c idx N β = c k N β) ∨
      (∀ N β, aux_conv_represented_catalogue_original_ext κ c idx N β = 0) := by
  classical
  by_cases h : ∃ k, κ k = idx
  · left
    refine ⟨Classical.choose h, Classical.choose_spec h, fun N β => ?_⟩
    unfold aux_conv_represented_catalogue_original_ext
    rw [dif_pos h]
  · right
    intro N β
    unfold aux_conv_represented_catalogue_original_ext
    rw [dif_neg h]

theorem aux_conv_represented_catalogue_original_ext_apply {Key Ω : Type} (κ : Key → ℕ)
    (hκ : Function.Injective κ) (c : Key → ℕ → Ω → ℝ) (k : Key) (N : ℕ) (β : Ω) :
    aux_conv_represented_catalogue_original_ext κ c (κ k) N β = c k N β := by
  classical
  have h : ∃ k', κ k' = κ k := ⟨k, rfl⟩
  unfold aux_conv_represented_catalogue_original_ext
  rw [dif_pos h]
  rw [hκ (Classical.choose_spec h)]

theorem aux_conv_represented_catalogue_original_ext_measurable {Key Ω : Type} [MeasurableSpace Ω]
    (κ : Key → ℕ) (c : Key → ℕ → Ω → ℝ)
    (hm : ∀ k N, Measurable (c k N)) :
    ∀ idx N, Measurable (aux_conv_represented_catalogue_original_ext κ c idx N) := by
  intro idx N
  rcases aux_conv_represented_catalogue_original_ext_cases κ c idx with ⟨k, -, hk⟩ | h0
  · have : aux_conv_represented_catalogue_original_ext κ c idx N = c k N := funext (hk N)
    rw [this]; exact hm k N
  · have : aux_conv_represented_catalogue_original_ext κ c idx N = fun _ => 0 := funext (h0 N)
    rw [this]; exact measurable_const

theorem aux_conv_represented_catalogue_original_ext_nonneg {Key Ω : Type}
    (κ : Key → ℕ) (c : Key → ℕ → Ω → ℝ) (G : Set Ω)
    (hn : ∀ k N β, β ∈ G → 0 ≤ c k N β) :
    ∀ idx N β, β ∈ G → 0 ≤ aux_conv_represented_catalogue_original_ext κ c idx N β := by
  intro idx N β hβ
  rcases aux_conv_represented_catalogue_original_ext_cases κ c idx with ⟨k, -, hk⟩ | h0
  · rw [hk]; exact hn k N β hβ
  · rw [h0]

theorem aux_conv_represented_catalogue_original_ext_bank {Key Ω : Type} [MeasurableSpace Ω]
    (κ : Key → ℕ) (c : Key → ℕ → Ω → ℝ) (μ : Measure Ω) (p : ℝ≥0∞)
    (hb : ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (c k N) p μ ∧ eLpNorm (c k N) p μ ≤ ENNReal.ofReal B) :
    ∀ idx, ∃ B : ℝ, 0 ≤ B ∧ ∀ N,
      MemLp (aux_conv_represented_catalogue_original_ext κ c idx N) p μ ∧
        eLpNorm (aux_conv_represented_catalogue_original_ext κ c idx N) p μ ≤ ENNReal.ofReal B := by
  intro idx
  rcases aux_conv_represented_catalogue_original_ext_cases κ c idx with ⟨k, -, hk⟩ | h0
  · obtain ⟨B, hB0, hB⟩ := hb k
    refine ⟨B, hB0, fun N => ?_⟩
    have : aux_conv_represented_catalogue_original_ext κ c idx N = c k N := funext (hk N)
    rw [this]; exact hB N
  · refine ⟨0, le_rfl, fun N => ?_⟩
    have : aux_conv_represented_catalogue_original_ext κ c idx N = fun _ => 0 := funext (h0 N)
    rw [this]
    refine ⟨MemLp.zero, ?_⟩
    simp

theorem aux_conv_represented_catalogue_original_ext_tight {Key Ω : Type} [MeasurableSpace Ω]
    (κ : Key → ℕ) (c : Key → ℕ → Ω → ℝ) (μ : Measure Ω) (Ns : ℕ → ℕ)
    (ht : ∀ k, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n, μ {β | Mb < |c k (Ns n) β|} ≤
      ENNReal.ofReal rho) :
    ∀ idx, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      μ {β | Mb < |aux_conv_represented_catalogue_original_ext κ c idx (Ns n) β|} ≤
        ENNReal.ofReal rho := by
  intro idx rho hrho
  rcases aux_conv_represented_catalogue_original_ext_cases κ c idx with ⟨k, -, hk⟩ | h0
  · obtain ⟨Mb, hMb⟩ := ht k rho hrho
    refine ⟨Mb, fun n => ?_⟩
    have : (fun β => aux_conv_represented_catalogue_original_ext κ c idx (Ns n) β) =
        c k (Ns n) := funext (hk (Ns n))
    simpa only [this] using hMb n
  · refine ⟨0, fun n => ?_⟩
    have : {β : Ω | (0 : ℝ) < |aux_conv_represented_catalogue_original_ext κ c idx (Ns n) β|} =
        ∅ := by
      ext β; simp [h0]
    rw [this]; simp

/-- Constants along keys: measurability, nonnegativity and the first-moment bank, from the same facts
for each kind of key (`Ω` generic, so that the proof does not see the model). -/
theorem aux_conv_represented_catalogue_original_const_props {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Type)
    (c : aux_conv_represented_catalogue_original_Key D → ℕ → Ω → ℝ)
    (KH Lam lam Kgs Khs Kgc Khc : ℕ → ℕ → Ω → ℝ) (Zg : ℕ → ℕ → Ω → ℝ)
    (hc0 : ∀ j N β, c (Sum.inl j) N β = KH j N β)
    (hc1 : ∀ j N β, c (Sum.inr (Sum.inl j)) N β = Lam j N β)
    (hc2 : ∀ j N β, c (Sum.inr (Sum.inr (Sum.inl j))) N β = lam j N β)
    (hc3 : ∀ i (g : D i) N β, c (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))) N β = Kgs i N β)
    (hc4 : ∀ i (g : D i) N β,
      c (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩))))) N β = Khs i N β)
    (hc5 : ∀ i (h : ℕ) N β,
      c (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h))))))) N β = Kgc i N β)
    (hc6 : ∀ i (h : ℕ) N β,
      c (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h)))))))) N β =
        Khc i N β)
    (hc7 : ∀ g N β,
      c (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl g)))))))) N β =
        Zg g N β)
    (hc8 : ∀ x N β,
      c (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))))))) N β = 0)
    (hm : (∀ j N, Measurable (KH j N)) ∧ (∀ j N, Measurable (Lam j N)) ∧
      (∀ j N, Measurable (lam j N)) ∧ (∀ j N, Measurable (Kgs j N)) ∧
      (∀ j N, Measurable (Khs j N)) ∧ (∀ j N, Measurable (Kgc j N)) ∧
      (∀ j N, Measurable (Khc j N)) ∧ (∀ g N, Measurable (Zg g N)))
    (hn : (∀ j N β, 0 ≤ KH j N β) ∧ (∀ j N β, 0 ≤ Lam j N β) ∧ (∀ j N β, 0 ≤ lam j N β) ∧
      (∀ j N β, 0 ≤ Kgs j N β) ∧ (∀ j N β, 0 ≤ Khs j N β) ∧ (∀ j N β, 0 ≤ Kgc j N β) ∧
      (∀ j N β, 0 ≤ Khc j N β) ∧ (∀ g N β, 0 ≤ Zg g N β))
    (hb : (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (KH j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (KH j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Lam j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Lam j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (lam j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (lam j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Kgs j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Kgs j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Khs j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Khs j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Kgc j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Kgc j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Khc j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Khc j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ g, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Zg g N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Zg g N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B)) :
    (∀ k N, Measurable (c k N)) ∧ (∀ k N β, 0 ≤ c k N β) ∧
      (∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (c k N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (c k N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) := by
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7⟩ := hm
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := hn
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hb
  have hzeroM : ∀ k N, (∀ β, c k N β = 0) → Measurable (c k N) := fun k N h => by
    have : c k N = fun _ => 0 := funext h
    rw [this]; exact measurable_const
  have hzeroB : ∀ k N, (∀ β, c k N β = 0) → MemLp (c k N) (ENNReal.ofReal 1) μ ∧
      eLpNorm (c k N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal 0 := fun k N h => by
    have : c k N = fun _ => 0 := funext h
    rw [this]
    exact ⟨MemLp.zero, by simp⟩
  have heqM : ∀ k N (f : Ω → ℝ), (∀ β, c k N β = f β) → Measurable f → Measurable (c k N) :=
    fun k N f h hf => by
      have : c k N = f := funext h
      rw [this]; exact hf
  have heqB : ∀ k N (f : Ω → ℝ) (B : ℝ), (∀ β, c k N β = f β) →
      (MemLp f (ENNReal.ofReal 1) μ ∧ eLpNorm f (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) →
      (MemLp (c k N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (c k N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) := fun k N f B h hf => by
    have : c k N = f := funext h
    rw [this]; exact hf
  refine ⟨?_, ?_, ?_⟩
  · intro k N
    rcases k with j | j | j | ⟨i, g⟩ | ⟨i, g⟩ | ⟨i, h⟩ | ⟨i, h⟩ | g | x
    · exact heqM _ _ _ (hc0 j N) (m0 j N)
    · exact heqM _ _ _ (hc1 j N) (m1 j N)
    · exact heqM _ _ _ (hc2 j N) (m2 j N)
    · exact heqM _ _ _ (hc3 i g N) (m3 i N)
    · exact heqM _ _ _ (hc4 i g N) (m4 i N)
    · exact heqM _ _ _ (hc5 i h N) (m5 i N)
    · exact heqM _ _ _ (hc6 i h N) (m6 i N)
    · exact heqM _ _ _ (hc7 g N) (m7 g N)
    · exact hzeroM _ _ (hc8 x N)
  · intro k N β
    rcases k with j | j | j | ⟨i, g⟩ | ⟨i, g⟩ | ⟨i, h⟩ | ⟨i, h⟩ | g | x
    · rw [hc0]; exact n0 j N β
    · rw [hc1]; exact n1 j N β
    · rw [hc2]; exact n2 j N β
    · rw [hc3]; exact n3 i N β
    · rw [hc4]; exact n4 i N β
    · rw [hc5]; exact n5 i N β
    · rw [hc6]; exact n6 i N β
    · rw [hc7]; exact n7 g N β
    · rw [hc8]
  · intro k
    rcases k with j | j | j | ⟨i, g⟩ | ⟨i, g⟩ | ⟨i, h⟩ | ⟨i, h⟩ | g | x
    · obtain ⟨B, hB0, hB⟩ := b0 j
      exact ⟨B, hB0, fun N => heqB _ _ _ _ (hc0 j N) (hB N)⟩
    · obtain ⟨B, hB0, hB⟩ := b1 j
      exact ⟨B, hB0, fun N => heqB _ _ _ _ (hc1 j N) (hB N)⟩
    · obtain ⟨B, hB0, hB⟩ := b2 j
      exact ⟨B, hB0, fun N => heqB _ _ _ _ (hc2 j N) (hB N)⟩
    · obtain ⟨B, hB0, hB⟩ := b3 i
      exact ⟨B, hB0, fun N => heqB _ _ _ _ (hc3 i g N) (hB N)⟩
    · obtain ⟨B, hB0, hB⟩ := b4 i
      exact ⟨B, hB0, fun N => heqB _ _ _ _ (hc4 i g N) (hB N)⟩
    · obtain ⟨B, hB0, hB⟩ := b5 i
      exact ⟨B, hB0, fun N => heqB _ _ _ _ (hc5 i h N) (hB N)⟩
    · obtain ⟨B, hB0, hB⟩ := b6 i
      exact ⟨B, hB0, fun N => heqB _ _ _ _ (hc6 i h N) (hB N)⟩
    · obtain ⟨B, hB0, hB⟩ := b7 g
      exact ⟨B, hB0, fun N => heqB _ _ _ _ (hc7 g N) (hB N)⟩
    · exact ⟨0, le_rfl, fun N => hzeroB _ _ (hc8 x N)⟩

/-- Responses along keys: measurability and tightness along every cutoff sequence. -/
theorem aux_conv_represented_catalogue_original_resp_props {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Type)
    (rr : aux_conv_represented_catalogue_original_Key D → ℕ → Ω → ℝ)
    (sR : ∀ i, D i → ℕ → Ω → ℝ) (cR : ℕ → ℕ → ℕ → Ω → ℝ)
    (hz : ∀ k : aux_conv_represented_catalogue_original_Key D, ∀ N β,
      (∀ x, k ≠ Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))))))) →
        rr k N β = 0)
    (hs : ∀ i (g : D i) N β,
      rr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl ⟨i, g⟩))))))))) N β = sR i g N β)
    (hc : ∀ i (h : ℕ) N β,
      rr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (i, h)))))))))) N β = cR i h N β)
    (hsm : ∀ i g N, Measurable (sR i g N))
    (hst : ∀ i g (Ns : ℕ → ℕ), ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      μ {β | Mb < |sR i g (Ns n) β|} ≤ ENNReal.ofReal rho)
    (hcm : ∀ i h N, Measurable (cR i h N))
    (hct : ∀ i h (Ns : ℕ → ℕ), ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      μ {β | Mb < |cR i h (Ns n) β|} ≤ ENNReal.ofReal rho) :
    (∀ k N, Measurable (rr k N)) ∧ (∀ (Ns : ℕ → ℕ) (k : aux_conv_represented_catalogue_original_Key D),
      ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      μ {β | Mb < |rr k (Ns n) β|} ≤ ENNReal.ofReal rho) := by
  have hzero : ∀ k : aux_conv_represented_catalogue_original_Key D, (∀ x, k ≠
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))))))) →
      (∀ N, Measurable (rr k N)) ∧ (∀ (Ns : ℕ → ℕ), ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
        μ {β | Mb < |rr k (Ns n) β|} ≤ ENNReal.ofReal rho) := by
    intro k hk
    refine ⟨fun N => ?_, fun Ns rho hrho => ⟨0, fun n => ?_⟩⟩
    · have : rr k N = fun _ => 0 := funext fun β => hz k N β hk
      rw [this]; exact measurable_const
    · have : {β : Ω | (0 : ℝ) < |rr k (Ns n) β|} = ∅ := by
        ext β; simp [hz k _ β hk]
      rw [this]; simp
  have hmeas : ∀ k N, Measurable (rr k N) := by
    intro k N
    rcases k with j | j | j | ⟨i, g⟩ | ⟨i, g⟩ | ⟨i, h⟩ | ⟨i, h⟩ | g | ⟨i, g⟩ | ⟨i, h⟩
    · exact (hzero (Sum.inl j) (fun x h => by cases h)).1 N
    · exact (hzero (Sum.inr (Sum.inl j)) (fun x h => by cases h)).1 N
    · exact (hzero (Sum.inr (Sum.inr (Sum.inl j))) (fun x h => by cases h)).1 N
    · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))) (fun x h => by cases h)).1 N
    · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩))))) (fun x h => by cases h)).1 N
    · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h))))))) (fun x h => by cases h)).1 N
    · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h)))))))) (fun x h => by cases h)).1 N
    · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl g)))))))) (fun x h => by cases h)).1 N
    · have : rr _ N = sR i g N := funext fun β => hs i g N β
      rw [this]; exact hsm i g N
    · have : rr _ N = cR i h N := funext fun β => hc i h N β
      rw [this]; exact hcm i h N
  refine ⟨hmeas, ?_⟩
  intro Ns k
  rcases k with j | j | j | ⟨i, g⟩ | ⟨i, g⟩ | ⟨i, h⟩ | ⟨i, h⟩ | g | ⟨i, g⟩ | ⟨i, h⟩
  · exact (hzero (Sum.inl j) (fun x h => by cases h)).2 Ns
  · exact (hzero (Sum.inr (Sum.inl j)) (fun x h => by cases h)).2 Ns
  · exact (hzero (Sum.inr (Sum.inr (Sum.inl j))) (fun x h => by cases h)).2 Ns
  · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))) (fun x h => by cases h)).2 Ns
  · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩))))) (fun x h => by cases h)).2 Ns
  · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h))))))) (fun x h => by cases h)).2 Ns
  · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h)))))))) (fun x h => by cases h)).2 Ns
  · exact (hzero (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl g)))))))) (fun x h => by cases h)).2 Ns
  · intro rho hrho
    obtain ⟨Mb, hMb⟩ := hst i g Ns rho hrho
    refine ⟨Mb, fun n => ?_⟩
    have : (fun β => rr _ (Ns n) β) = sR i g (Ns n) := funext fun β => hs i g (Ns n) β
    simpa only [this] using hMb n
  · intro rho hrho
    obtain ⟨Mb, hMb⟩ := hct i h Ns rho hrho
    refine ⟨Mb, fun n => ?_⟩
    have : (fun β => rr _ (Ns n) β) = cR i h (Ns n) := funext fun β => hc i h (Ns n) β
    simpa only [this] using hMb n

/-- The keyed constants of the catalogue (generic in the families). -/
def aux_conv_represented_catalogue_original_constOf {D : ℕ → Type} {Ω : Type}
    (KH Lam lam Kgs Khs Kgc Khc Zg : ℕ → ℕ → Ω → ℝ) :
    aux_conv_represented_catalogue_original_Key D → ℕ → Ω → ℝ := fun k N β =>
  match k with
  | Sum.inl j => KH j N β
  | Sum.inr (Sum.inl j) => Lam j N β
  | Sum.inr (Sum.inr (Sum.inl j)) => lam j N β
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) => Kgs p.1 N β
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) => Khs p.1 N β
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) => Kgc p.1 N β
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))))) => Khc p.1 N β
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl g))))))) => Zg g N β
  | _ => 0

/-- The keyed responses of the catalogue (generic in the families). -/
def aux_conv_represented_catalogue_original_respOf {D : ℕ → Type} {Ω : Type}
    (sR : ∀ i, D i → ℕ → Ω → ℝ) (cR : ℕ → ℕ → ℕ → Ω → ℝ) :
    aux_conv_represented_catalogue_original_Key D → ℕ → Ω → ℝ := fun k N β =>
  match k with
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inl p)))))))) => sR p.1 p.2 N β
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inr p)))))))) => cR p.1 p.2 N β
  | _ => 0

/-- **Keyed catalogue.**  From measurability, nonnegativity and first-moment banks of the per-kind
families, and measurability and tightness (along every cutoff sequence) of the two response families,
the zero-extended keyed constants `const0` and responses `resp0` (with an injective key map `κ`)
satisfy: the pinned values at the keys, and for EVERY index measurability, nonnegativity, the bank,
and tightness of the responses. -/
theorem aux_conv_represented_catalogue_original_keyed {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Type) (κ : aux_conv_represented_catalogue_original_Key D → ℕ)
    (hκ : Function.Injective κ)
    (KH Lam lam Kgs Khs Kgc Khc Zg : ℕ → ℕ → Ω → ℝ)
    (sR : ∀ i, D i → ℕ → Ω → ℝ) (cR : ℕ → ℕ → ℕ → Ω → ℝ)
    (hm : (∀ j N, Measurable (KH j N)) ∧ (∀ j N, Measurable (Lam j N)) ∧
      (∀ j N, Measurable (lam j N)) ∧ (∀ j N, Measurable (Kgs j N)) ∧
      (∀ j N, Measurable (Khs j N)) ∧ (∀ j N, Measurable (Kgc j N)) ∧
      (∀ j N, Measurable (Khc j N)) ∧ (∀ g N, Measurable (Zg g N)))
    (hn : (∀ j N β, 0 ≤ KH j N β) ∧ (∀ j N β, 0 ≤ Lam j N β) ∧ (∀ j N β, 0 ≤ lam j N β) ∧
      (∀ j N β, 0 ≤ Kgs j N β) ∧ (∀ j N β, 0 ≤ Khs j N β) ∧ (∀ j N β, 0 ≤ Kgc j N β) ∧
      (∀ j N β, 0 ≤ Khc j N β) ∧ (∀ g N β, 0 ≤ Zg g N β))
    (hb : (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (KH j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (KH j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Lam j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Lam j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (lam j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (lam j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Kgs j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Kgs j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Khs j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Khs j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Kgc j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Kgc j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Khc j N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Khc j N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ g, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (Zg g N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Zg g N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B))
    (hsm : ∀ i g N, Measurable (sR i g N))
    (hst : ∀ i g (Ns : ℕ → ℕ), ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      μ {β | Mb < |sR i g (Ns n) β|} ≤ ENNReal.ofReal rho)
    (hcm : ∀ i h N, Measurable (cR i h N))
    (hct : ∀ i h (Ns : ℕ → ℕ), ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      μ {β | Mb < |cR i h (Ns n) β|} ≤ ENNReal.ofReal rho) :
    ∃ const0 resp0 : ℕ → ℕ → Ω → ℝ,
      (∀ j N β, const0 (κ (Sum.inl j)) N β = KH j N β) ∧
      (∀ j N β, const0 (κ (Sum.inr (Sum.inl j))) N β = Lam j N β) ∧
      (∀ j N β, const0 (κ (Sum.inr (Sum.inr (Sum.inl j)))) N β = lam j N β) ∧
      (∀ i (g : D i) N β, const0 (κ (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩))))) N β =
        Kgs i N β) ∧
      (∀ i (g : D i) N β,
        const0 (κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))))) N β = Khs i N β) ∧
      (∀ i (h : ℕ) N β,
        const0 (κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h)))))))) N β =
          Kgc i N β) ∧
      (∀ i (h : ℕ) N β,
        const0 (κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h))))))))) N β
          = Khc i N β) ∧
      (∀ g N β, const0 (κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl g))))))))) N β = Zg g N β) ∧
      (∀ i (g : D i) N β, resp0 (κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))))))))) N β = sR i g N β) ∧
      (∀ i (h : ℕ) N β, resp0 (κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, h))))))))))) N β = cR i h N β) ∧
      (∀ idx N, Measurable (const0 idx N)) ∧ (∀ idx N β, 0 ≤ const0 idx N β) ∧
      (∀ idx, ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (const0 idx N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (const0 idx N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal B) ∧
      (∀ idx N, Measurable (resp0 idx N)) ∧
      (∀ (Ns : ℕ → ℕ) idx, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
        μ {β | Mb < |resp0 idx (Ns n) β|} ≤ ENNReal.ofReal rho) := by
  have hcP := aux_conv_represented_catalogue_original_const_props μ D
    (aux_conv_represented_catalogue_original_constOf KH Lam lam Kgs Khs Kgc Khc Zg)
    KH Lam lam Kgs Khs Kgc Khc Zg (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hm hn hb
  have hrP := aux_conv_represented_catalogue_original_resp_props μ D
    (aux_conv_represented_catalogue_original_respOf sR cR) sR cR
    (fun k N β hk => by
      rcases k with j | j | j | ⟨i, g⟩ | ⟨i, g⟩ | ⟨i, h⟩ | ⟨i, h⟩ | g | ⟨i, g⟩ | ⟨i, h⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hk (Sum.inl ⟨i, g⟩))
      · exact absurd rfl (hk (Sum.inr (i, h))))
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hsm hst hcm hct
  refine ⟨aux_conv_represented_catalogue_original_ext κ
      (aux_conv_represented_catalogue_original_constOf KH Lam lam Kgs Khs Kgc Khc Zg),
    aux_conv_represented_catalogue_original_ext κ
      (aux_conv_represented_catalogue_original_respOf sR cR), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact fun j N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact fun j N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact fun i g N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact fun i g N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact fun i h N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact fun i h N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact fun g N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact fun i g N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact fun i h N β => aux_conv_represented_catalogue_original_ext_apply κ hκ _ _ N β
  · exact aux_conv_represented_catalogue_original_ext_measurable κ _ hcP.1
  · exact fun idx N β => aux_conv_represented_catalogue_original_ext_nonneg κ _ Set.univ
      (fun k N β _ => hcP.2.1 k N β) idx N β (Set.mem_univ _)
  · exact aux_conv_represented_catalogue_original_ext_bank κ _ μ (ENNReal.ofReal 1) hcP.2.2
  · exact aux_conv_represented_catalogue_original_ext_measurable κ _ hrP.1
  · exact fun Ns => aux_conv_represented_catalogue_original_ext_tight κ _ μ Ns
      (fun k => hrP.2 Ns k)

/-- A countable family of measurable full-measure events and one more have a common measurable
full-measure event. -/
theorem aux_conv_represented_catalogue_original_events {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B C : ℕ → Set Ω) (G : Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hC : ∀ i, MeasurableSet (C i)) (hG : MeasurableSet G)
    (hA0 : ∀ i, μ (A i)ᶜ = 0) (hB0 : ∀ i, μ (B i)ᶜ = 0) (hC0 : ∀ i, μ (C i)ᶜ = 0)
    (hG0 : μ Gᶜ = 0) :
    ∃ G0 : Set Ω, MeasurableSet G0 ∧ μ G0ᶜ = 0 ∧ (∀ β ∈ G0, ∀ j, β ∈ A j) ∧
      (∀ β ∈ G0, ∀ j, β ∈ B j) ∧ (∀ β ∈ G0, ∀ j, β ∈ C j) ∧ (∀ β ∈ G0, β ∈ G) := by
  refine ⟨(⋂ i, (A i ∩ B i ∩ C i)) ∩ G,
    (MeasurableSet.iInter fun i => ((hA i).inter (hB i)).inter (hC i)).inter hG, ?_,
    fun β hβ j => (Set.mem_iInter.1 hβ.1 j).1.1, fun β hβ j => (Set.mem_iInter.1 hβ.1 j).1.2,
    fun β hβ j => (Set.mem_iInter.1 hβ.1 j).2, fun β hβ => hβ.2⟩
  have hsub' : ((⋂ i, (A i ∩ B i ∩ C i)) ∩ G)ᶜ ⊆
      (⋃ i, (A i)ᶜ) ∪ (⋃ i, (B i)ᶜ) ∪ (⋃ i, (C i)ᶜ) ∪ Gᶜ := by
    intro β hβ
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, not_or, not_exists,
      not_not] at hcon
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
    exact hβ ⟨Set.mem_iInter.2 fun i => ⟨⟨h1 i, h2 i⟩, h3 i⟩, h4⟩
  exact measure_mono_null hsub' (measure_union_null (measure_union_null (measure_union_null
    (measure_iUnion_null hA0) (measure_iUnion_null hB0)) (measure_iUnion_null hC0)) hG0)

/-- Clause K of the core from the source-clause supplier, for one cube (choosing `srcRep`). -/
theorem aux_conv_represented_catalogue_original_K
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (f : D → SpatialCoordinates d → ℝ)
    (hf : ∀ g : D, ContDiff ℝ ∞ (f g) ∧ HasCompactSupport (f g) ∧
      tsupport (f g) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (g.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f g)
    (t alpha : ℝ) (Kg Kh : ℕ → BilateralField d → ℝ) (G : Set (BilateralField d))
    (hK : ∀ (N : ℕ), ∀ β ∈ G, ∀ (g : DomainL2 (centeredCube z r hr))
          (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
          AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          ((g : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] F) →
          (∀ (x : SpatialCoordinates d) (rr : ℝ), 0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal
                ((Lane4.cutoffPositiveCoefficient M H β N z hr).val y *
                  ∑ i : Fin d, (((responseSolution S
                    (Lane4.cutoffPositiveCoefficient M H β N z hr)
                    ((sobolevVolumeLoad g).comp S.space.subtypeL)).val.2 i) y) ^ 2)))
              (Metric.ball x rr) ≤
            ENNReal.ofReal (Kg N β * Kf ^ 2 * rr ^ t)) ∧
          ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            (((responseSolution S (Lane4.cutoffPositiveCoefficient M H β N z hr)
                ((sobolevVolumeLoad g).comp S.space.subtypeL)).val.1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
            (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) ∧
            IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) U ∧
            cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) U ≤
              Kh N β * Kf) :
    ∃ srcRep : D → ℕ → BilateralField d → SpatialCoordinates d → ℝ,
      ∀ (g : D) (N : ℕ), ∀ β ∈ G,
        ((((responseSolution S (Lane4.cutoffPositiveCoefficient M H β N z hr)
            ((sobolevVolumeLoad g.val).comp S.space.subtypeL)).val.1 :
              DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
            srcRep g N β) ∧
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
          ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal
              ((Lane4.cutoffPositiveCoefficient M H β N z hr).val y *
                ∑ i : Fin d, (((responseSolution S
                  (Lane4.cutoffPositiveCoefficient M H β N z hr)
                  ((sobolevVolumeLoad g.val).comp S.space.subtypeL)).val.2 i) y) ^ 2)))
            (Metric.ball x rr) ≤
          ENNReal.ofReal (Kg N β *
            (sSup {v : ℝ | ∃ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
              v = |f g x|}) ^ 2 * rr ^ t)) ∧
        ContinuousOn (srcRep g N β)
          (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          srcRep g N β x = 0) ∧
        IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          (srcRep g N β) ∧
        cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          (srcRep g N β) ≤
          Kh N β * sSup {v : ℝ | ∃ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
            v = |f g x|} := by
  classical
  have hex : ∀ (g : D) (N : ℕ), ∀ β ∈ G, ∃ U : SpatialCoordinates d → ℝ,
      ((((responseSolution S (Lane4.cutoffPositiveCoefficient M H β N z hr)
          ((sobolevVolumeLoad g.val).comp S.space.subtypeL)).val.1 :
            DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal
            ((Lane4.cutoffPositiveCoefficient M H β N z hr).val y *
              ∑ i : Fin d, (((responseSolution S
                (Lane4.cutoffPositiveCoefficient M H β N z hr)
                ((sobolevVolumeLoad g.val).comp S.space.subtypeL)).val.2 i) y) ^ 2)))
          (Metric.ball x rr) ≤
        ENNReal.ofReal (Kg N β *
          (sSup {v : ℝ | ∃ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
            v = |f g x|}) ^ 2 * rr ^ t)) ∧
      ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) ∧
      IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) U ∧
      cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) U ≤
        Kh N β * sSup {v : ℝ | ∃ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          v = |f g x|} := by
    intro g N β hβ
    obtain ⟨h1, h2, h3, h4⟩ := hf g
    set Kf : ℝ := sSup {v : ℝ | ∃ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      v = |f g x|} with hKf
    have hcomp : IsCompact (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      (centeredCube_isBounded z hr).isCompact_closure
    have hbdd : BddAbove {v : ℝ | ∃ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        v = |f g x|} := by
      obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn h1.continuous.continuousOn
      refine ⟨C, ?_⟩
      rintro v ⟨x, hx, rfl⟩
      exact hC x hx
    have hKf0 : 0 ≤ Kf := Real.sSup_nonneg (by rintro v ⟨x, hx, rfl⟩; exact abs_nonneg _)
    have hle : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        |f g x| ≤ Kf := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
    have hae : ∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
        |f g x| ≤ Kf := by
      refine (ae_restrict_iff' (centeredCube z r hr).isOpen.measurableSet).2 ?_
      exact Filter.Eventually.of_forall fun x hx => hle x (subset_closure hx)
    obtain ⟨hgrowth, U, hUc, hUae, hUfr, hUh, hUn⟩ := hK N β hβ g.val (f g) Kf hKf0
      h1.continuous.aemeasurable hae h4
    exact ⟨U, hUae, fun x hx rr h1r h2r => hgrowth x rr h1r h2r, hUc.continuousOn, hUfr, hUh, hUn⟩
  choose! srcRep hsrc using hex
  refine ⟨srcRep, fun g N β hβ => ?_⟩
  exact hsrc g N β hβ

/-- Cell part of clauses F and L of the core from the cell-clause supplier, for one cube (choosing
`ucell`). -/
theorem aux_conv_represented_catalogue_original_L
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (theta : ℕ → SpatialCoordinates d → ℝ)
    (thetaH1 : ℕ → H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hth : ∀ h, ContDiff ℝ ∞ (theta h) ∧ (thetaH1 h).toFun = theta h)
    (t alpha : ℝ) (Kg Kh : ℕ → BilateralField d → ℝ) (G : Set (BilateralField d))
    (hL : ∀ (N : ℕ), ∀ β ∈ G, ∀ (theta : SpatialCoordinates d → ℝ)
          (thetaH1 : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))),
          ContDiff ℝ 2 theta → thetaH1.toFun = theta →
          ∃ ucell : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
            IsWeaklyHarmonicOn (cutoffCoefficient M H β N)
              (centeredCube z r hr : Set (SpatialCoordinates d)) ucell ∧
            HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d))
              ucell thetaH1 ∧
            ContinuousOn ucell.toFun
              (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
            (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
              ucell.toFun x = theta x) ∧
            (∀ (x : SpatialCoordinates d) (rr : ℝ), 0 < rr → rr ≤ 1 →
              ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
                (fun y => ENNReal.ofReal
                  ((Lane4.cutoffPositiveCoefficient M H β N z hr).val y *
                    ∑ i : Fin d, (((sobolevDataOfH1 ucell).2 i) y) ^ 2)))
                (Metric.ball x rr) ≤
              ENNReal.ofReal (Kg N β *
                (c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d))) theta) ^ 2 *
                  rr ^ t)) ∧
            IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
              ucell.toFun ∧
            cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
              ucell.toFun ≤
              Kh N β * c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d))) theta) :
    ∃ ucell : ℕ → ℕ → BilateralField d →
        H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ (h : ℕ) (N : ℕ), ∀ β ∈ G,
        IsWeaklyHarmonicOn (cutoffCoefficient M H β N)
          (centeredCube z r hr : Set (SpatialCoordinates d)) (ucell h N β) ∧
        HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d))
          (ucell h N β) (thetaH1 h) ∧
        ContinuousOn (ucell h N β).toFun
          (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          (ucell h N β).toFun x = theta h x) ∧
        ((∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
          ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal
              ((Lane4.cutoffPositiveCoefficient M H β N z hr).val y *
                ∑ i : Fin d, (((sobolevDataOfH1 (ucell h N β)).2 i) y) ^ 2)))
            (Metric.ball x rr) ≤
          ENNReal.ofReal (Kg N β *
            (c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (theta h)) ^ 2 *
              rr ^ t)) ∧
        IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          (ucell h N β).toFun ∧
        cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          (ucell h N β).toFun ≤
          Kh N β * c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
            (theta h)) := by
  classical
  have hex : ∀ (h : ℕ) (N : ℕ), ∀ β ∈ G,
      ∃ u : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
        IsWeaklyHarmonicOn (cutoffCoefficient M H β N)
          (centeredCube z r hr : Set (SpatialCoordinates d)) u ∧
        HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d))
          u (thetaH1 h) ∧
        ContinuousOn u.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          u.toFun x = theta h x) ∧
        ((∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
          ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal
              ((Lane4.cutoffPositiveCoefficient M H β N z hr).val y *
                ∑ i : Fin d, (((sobolevDataOfH1 u).2 i) y) ^ 2)))
            (Metric.ball x rr) ≤
          ENNReal.ofReal (Kg N β *
            (c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (theta h)) ^ 2 *
              rr ^ t)) ∧
        IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          u.toFun ∧
        cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          u.toFun ≤
          Kh N β * c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
            (theta h)) := by
    intro h N β hβ
    obtain ⟨u, hu1, hu2, hu3, hu4, hu5, hu6, hu7⟩ := hL N β hβ (theta h) (thetaH1 h)
      ((hth h).1.of_le (by norm_cast)) (hth h).2
    exact ⟨u, hu1, hu2, hu3, hu4, fun x _ rr h1 h2 => hu5 x rr h1 h2, hu6, hu7⟩
  haveI : Nonempty (H1Function (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    ⟨thetaH1 0⟩
  choose! ucell hucell using hex
  exact ⟨ucell, fun h N β hβ => hucell h N β hβ⟩

/-- Shift of the finite-cutoff catalogue: the catalogue for the identity cutoff (all `N`) gives the
catalogue for any strictly increasing cutoff, with all objects composed with the cutoff. -/
theorem aux_conv_represented_catalogue_original_shift
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (cutoff : ℕ → ℕ) (hcut : StrictMono cutoff)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → BilateralField d → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → BilateralField d → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → BilateralField d →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp constants : Index → ℕ → BilateralField d → ℝ) (G0 : Set (BilateralField d))
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (h : aux_conv_represented_estimates_transfer_core d hd M H (fun N => N) J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp constants G0 coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey) :
    aux_conv_represented_estimates_transfer_core d hd M H cutoff J j0 z r hr S D f T theta thetaH1 (fun j g n β => usrc j g (cutoff n) β) (fun j g n β => srcRep j g (cutoff n) β) (fun j h n β => ucell j h (cutoff n) β) Cext beta alpha eta t orders E Index (fun i n β => resp i (cutoff n) β) (fun i n β => constants i (cutoff n) β) G0 coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey := by
  classical
  unfold aux_conv_represented_estimates_transfer_core at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩ := h
  refine ⟨h1, h2, h3, h4, h5, hcut, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i n => h25 i (cutoff n)
  · intro i p hp
    obtain ⟨B, hB0, hB⟩ := h26 i p hp
    exact ⟨B, hB0, fun n => hB (cutoff n)⟩
  · exact fun i β hβ n => h27 i β hβ (cutoff n)
  · exact fun j n β hβ => h28 j (cutoff n) β hβ
  · exact fun j n β hβ => h29 j (cutoff n) β hβ
  · exact fun j n β hβ => h30 j (cutoff n) β hβ
  · exact fun j n β hβ => h31 j (cutoff n) β hβ
  · exact fun g n k j β hβ => h32 g (cutoff n) k j β hβ
  · exact fun j g n β hβ => h33 j g (cutoff n) β hβ
  · exact fun j h n β hβ => h34 j h (cutoff n) β hβ



theorem conv_represented_catalogue_original
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha) (hb : 1 / 2 < beta) (hba : beta < alpha) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
        (root : ℕ) (origin : ℕ → SpatialCoordinates d) (gridRoot : ℕ → ℕ)
        (hunit : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
        (hsub : ∀ j, (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
        (hrat : ∀ (j : ℕ) (c : Fin d), ∃ q : ℚ, z j c = (q : ℝ))
        (htri : ∀ j, ∃ m : ℤ, r j = (3 : ℝ) ^ m)
        (hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
          (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) → (∃ m : ℤ, r' = (3 : ℝ) ^ m) →
          (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
            (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)) →
          ∃ j, z j = z' ∧ r j = r')
        (horat : ∀ (g : ℕ) (c : Fin d), ∃ q : ℚ, origin g c = (q : ℝ))
        (hgrid : ∀ (j : ℕ) (o : SpatialCoordinates d), (∀ c : Fin d, ∃ q : ℚ, o c = (q : ℝ)) →
          ∃ g : ℕ, gridRoot g = j ∧ origin g = o)
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      conv_represented_env_interface_buffered d hd M H z r hr Sspace NE NF alpha eta := by
  classical
  have hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1 := ⟨hb, hba.trans ha1⟩
  obtain ⟨δ1, hδ1, hcoerc⟩ := model_triadic_cube_coercivity d hd E Pin Sob
  obtain ⟨δ2, hδ2, hsrc⟩ := conv_represented_catalogue_source_clause d hd E Pin X W Cp Sob t alpha
    ht htd ha0 ha1
  obtain ⟨δ3, hδ3, hcell⟩ := conv_represented_catalogue_cell_clause d hd E Pin X W Cp Sob t alpha
    ht htd ha0 ha1
  obtain ⟨δ4, hδ4, hcube⟩ := model_cube_coarse_bank d hd E beta 1 hbeta le_rfl
  obtain ⟨Cext, hCext, hI⟩ := model_cube_trace_bound d hd E X Sob beta hbeta
  obtain ⟨δ5, hδ5, hgridb⟩ :=
    conv_represented_grid_clause_bank d hd E X Sob eta 1 beta heta le_rfl hbeta
  refine ⟨min (min (min δ1 δ2) (min δ3 δ4)) δ5,
    lt_min (lt_min (lt_min hδ1 hδ2) (lt_min hδ3 hδ4)) hδ5, ?_⟩
  intro M Rm Sreg It H hH hδ z r hr Sspace hS root origin gridRoot hunit hsub hrat htri hcomp
    horat hgrid NE NF hNE hNF
  have hδ1' : M.delta ≤ δ1 := hδ.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδ2' : M.delta ≤ δ2 := hδ.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδ3' : M.delta ≤ δ3 := hδ.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ4' : M.delta ≤ δ4 := hδ.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ5' : M.delta ≤ δ5 := hδ.trans (min_le_right _ _)
  -- deterministic catalogue: sources, traces
  choose Dcat hDc fcat hDdense hf3 hf4 using fun i =>
    conv_represented_catalogue_sources d (z i) (r i) (hr i)
  haveI hDcI : ∀ i, Countable (Dcat i) := hDc
  obtain ⟨theta, thetaH1, hth5, hth6, hth7, hth8, hth9, hth10⟩ :=
    conv_represented_catalogue_traces_buffered d hd beta alpha hb hba ha1 ℕ z r hr
      (fun i => ↥(Dcat i)) fcat (fun j g => (hf3 j g).1)
  -- coercivity (clause H)
  have hrad : ∀ i, r i ≤ 1 ∨ ∃ k : ℕ, 0 < k ∧ r i = (3 : ℝ) ^ k := by
    intro i
    obtain ⟨m, hm⟩ := htri i
    by_cases hm0 : m ≤ 0
    · left
      rw [hm]
      exact zpow_le_one_of_nonpos₀ (by norm_num) hm0
    · right
      refine ⟨m.toNat, by omega, ?_⟩
      rw [hm, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  obtain ⟨Kc, Cbc, hCbc, hKcm, hKcn, hKcae, hKcb, hKctight⟩ :=
    hcoerc M Rm H hH hδ1' z r hr hrad
  have hHcl := fun i => conv_represented_catalogue_coercivity_clause d hd M H (z i) (r i) (hr i)
    (Sspace i) (hS i) (Kc i) (hKcm i) (hKcn i) (hKcae i) (Cbc i)
    (fun N => by simpa only [ENNReal.ofReal_one] using hKcb i N)
  choose KH BH GH hGHm hGHnull hKHm hKHn hBH0 hKHb hKH using hHcl
  -- source and cell growth clauses
  choose Kgs Khs Cbgs Cbhs Gs hGsm hGsnull hCbgs hCbhs hKgsm hKgsn hKgsb hKhsm hKhsn hKhsb hKs
    using fun i => hsrc M Rm Sreg It H hH hδ2' (z i) (r i) (hr i) (Sspace i) (hS i)
  choose srcRepB hsrcB using fun i =>
    aux_conv_represented_catalogue_original_K M H (z i) (r i) (hr i) (Sspace i) (Dcat i)
      (fcat i) (hf3 i) t alpha (Kgs i) (Khs i) (Gs i) (hKs i)
  choose Kgc Khc Cbgc Cbhc Gc hGcm hGcnull hCbgc hCbhc hKgcm hKgcn hKgcb hKhcm hKhcn hKhcb hLc
    using fun i => hcell M Rm Sreg It H hH hδ3' (z i) (r i) (hr i)
  choose ucellB hucellB using fun i =>
    aux_conv_represented_catalogue_original_L M H (z i) (r i) (hr i) (theta i) (thetaH1 i)
      (hth5 i) t alpha (Kgc i) (Khc i) (Gc i) (hLc i)
  -- coarse constants and grid constants
  obtain ⟨CbL, hCbL0, hLamm, hlamm, hLampos, hLambank, hLamtight⟩ :=
    hcube M Rm H hH hδ4' ℕ z r hr htri
  obtain ⟨Zg, Cbg, Ggrid, hCbg0, hZgm, hZgn, hZgb, hZgt, hGgm, hGgnull, hJ⟩ :=
    hgridb M Rm H hH hδ5' ℕ z r hr ℕ origin gridRoot
  clear hcoerc hsrc hcell hcube hgridb
  obtain ⟨κ, hκ⟩ := Countable.exists_injective_nat
    (aux_conv_represented_catalogue_original_Key (fun i => ↥(Dcat i)))
  -- tightness of the coercivity constants and the killed-space form of clause H
  have hKHtight : ∀ i (Ns : ℕ → ℕ), ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw M).toMeasure {β | Mb < KH i (Ns n) β} ≤ ENNReal.ofReal rho := by
    intro i Ns rho hrho
    obtain ⟨Mb, hMb⟩ := aux_conv_represented_tight_of_bounded_L1_bounded
      (chaosSampleLaw M).toMeasure
      (fun n => KH i (Ns n)) (fun n => hKHm i (Ns n)) (BH i) (hBH0 i) (fun n => by
        have := (hKHb i (Ns n)).2
        rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm] at this
        exact this) rho hrho
    refine ⟨Mb, fun n => le_trans (measure_mono ?_) (hMb n)⟩
    intro β hβ
    have hβ' : Mb < KH i (Ns n) β := hβ
    exact lt_of_lt_of_le hβ' (le_abs_self _)
  have hKHc : ∀ i N, ∀ β ∈ GH i, ∀ v : (Sspace i).space,
      ‖(v : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ^ 2 ≤
        KH i N β * responseForm (Sspace i)
          (cutoffPositiveCoefficient M H β N (z i) (hr i)) v v := by
    intro i N β hβ v
    have h := (hKH i N β hβ v).2
    have hnn : 0 ≤ volume.real (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
          (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 :=
      mul_nonneg measureReal_nonneg (sq_nonneg _)
    exact le_trans (le_add_of_nonneg_right hnn) h
  -- cell responses: boundary class and the absolute trace estimate
  have hcellcls : ∀ i h, ContinuousOn (thetaH1 i h).toFun
      (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) ∧
      IsCellBoundaryClass beta (z i) (r i) (thetaH1 i h).toFun := by
    intro i h
    have h1 := hth5 i h
    rw [h1.2]
    exact ⟨h1.1.continuous.continuousOn, conv_represented_catalogue_smooth_class beta
      (by linarith) (by linarith) (z i) (r i) (theta i h) h1.1⟩
  have hcellI : ∀ i h N β, cellDirichletInfimum (cutoffCoefficient M H β N)
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) (thetaH1 i h) ≤
      (Cext * (r i) ^ ((d : ℝ) - 2) *
        (cellBoundaryQuotientNorm beta (z i) (r i) (thetaH1 i h).toFun) ^ 2) *
        E.Lam (z i) (r i) (hr i) (cutoffPositiveCoefficient M H β N (z i) (hr i))
          (z i) (r i) ((beta - 1 / 2) / 4) 2 := by
    intro i h N β
    have := hI M H β N (z i) (r i) (hr i) (thetaH1 i h) (hcellcls i h).1 (hcellcls i h).2
    calc _ ≤ _ := this
      _ = _ := by ring
  have hcellc : ∀ i h, 0 ≤ Cext * (r i) ^ ((d : ℝ) - 2) *
      (cellBoundaryQuotientNorm beta (z i) (r i) (thetaH1 i h).toFun) ^ 2 := fun i h =>
    mul_nonneg (mul_nonneg hCext.le (Real.rpow_nonneg (hr i).le _)) (sq_nonneg _)
  have hLamT : ∀ i (Ns : ℕ → ℕ), ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw M).toMeasure {β |
      Mb < E.Lam (z i) (r i) (hr i) (cutoffPositiveCoefficient M H β (Ns n) (z i) (hr i))
        (z i) (r i) ((beta - 1 / 2) / 4) 2} ≤ ENNReal.ofReal rho := by
    intro i Ns rho hrho
    obtain ⟨Mb, hMb⟩ := hLamtight i rho hrho
    exact ⟨Mb, fun n => (hMb (Ns n)).1⟩
  have hd0 : 0 < d := lt_of_lt_of_le two_pos hd
  -- keyed constants and responses
  obtain ⟨const0, resp0, hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hR0, hR1, hconstM, hconstN,
      hconstB, hresp0M, hresp0T⟩ :=
    aux_conv_represented_catalogue_original_keyed (chaosSampleLaw M).toMeasure
    (fun i => ↥(Dcat i)) κ hκ KH
    (fun j N β => E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
      (z j) (r j) ((beta - 1 / 2) / 4) 2)
    (fun j N β => (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
      (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ)))
    Kgs Khs Kgc Khc Zg
    (fun i g N β => inverseResponse (Sspace i)
      (cutoffPositiveCoefficient M H β N (z i) (hr i))
      ((sobolevVolumeLoad g.val).comp (Sspace i).space.subtypeL))
    (fun i h N β => cellDirichletInfimum (cutoffCoefficient M H β N)
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) (thetaH1 i h))
    ⟨hKHm, hLamm, hlamm, hKgsm, hKhsm, hKgcm, hKhcm, hZgm⟩
    ⟨hKHn, fun j N β => (hLampos j N β).1.le, fun j N β => (hLampos j N β).2.le,
      hKgsn, hKhsn, hKgcn, hKhcn, hZgn⟩
    ⟨fun j => ⟨BH j, hBH0 j, hKHb j⟩,
     fun j => ⟨CbL j, hCbL0 j, fun N => (hLambank j N 1 one_pos le_rfl).1⟩,
     fun j => ⟨CbL j, hCbL0 j, fun N => (hLambank j N 1 one_pos le_rfl).2⟩,
     fun j => ⟨Cbgs j, hCbgs j, hKgsb j⟩, fun j => ⟨Cbhs j, hCbhs j, hKhsb j⟩,
     fun j => ⟨Cbgc j, hCbgc j, hKgcb j⟩, fun j => ⟨Cbhc j, hCbhc j, hKhcb j⟩,
     fun g => ⟨Cbg g, hCbg0 g, fun N => hZgb g N 1 one_pos le_rfl⟩⟩
    (fun i g N => (conv_represented_catalogue_source_response d M H hH (z i) (r i) (hr i)
      (Sspace i) (KH i) (GH i) (hKHn i) (hKHc i) g.val (chaosSampleLaw M).toMeasure (hGHnull i)
      (fun n => n) (hKHtight i (fun n => n))).1 N)
    (fun i g Ns => (conv_represented_catalogue_source_response d M H hH (z i) (r i) (hr i)
      (Sspace i) (KH i) (GH i) (hKHn i) (hKHc i) g.val (chaosSampleLaw M).toMeasure (hGHnull i)
      Ns (hKHtight i Ns)).2.2.2)
    (fun i h N => (conv_represented_catalogue_cell_response d hd0 M H hH (z i) (r i) (hr i)
      (thetaH1 i h) (fun N β => E.Lam (z i) (r i) (hr i)
        (cutoffPositiveCoefficient M H β N (z i) (hr i)) (z i) (r i) ((beta - 1 / 2) / 4) 2)
      Set.univ _ (hcellc i h) (fun N β _ => hcellI i h N β) (chaosSampleLaw M).toMeasure
      (by simp) (fun n => n) (hLamT i (fun n => n))).1 N)
    (fun i h Ns => (conv_represented_catalogue_cell_response d hd0 M H hH (z i) (r i) (hr i)
      (thetaH1 i h) (fun N β => E.Lam (z i) (r i) (hr i)
        (cutoffPositiveCoefficient M H β N (z i) (hr i)) (z i) (r i) ((beta - 1 / 2) / 4) 2)
      Set.univ _ (hcellc i h) (fun N β _ => hcellI i h N β) (chaosSampleLaw M).toMeasure
      (by simp) Ns (hLamT i Ns)).2.2)
  -- the full-measure event
  obtain ⟨G0, hG0m, hG0null, hβGH, hβGs, hβGc, hβGg⟩ :=
    aux_conv_represented_catalogue_original_events (chaosSampleLaw M).toMeasure GH Gs Gc Ggrid
      hGHm hGsm hGcm hGgm hGHnull hGsnull hGcnull hGgnull
  -- the catalogue at the identity cutoff
  have hpin1 : ∀ (j n : ℕ) (β : BilateralField d), β ∈ G0 →
      const0 (κ (Sum.inr (Sum.inl j))) n β =
        E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β n (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2 ∧
      const0 (κ (Sum.inr (Sum.inr (Sum.inl j)))) n β =
        (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β n (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ)) := fun j n β _ =>
    ⟨hC1 j n β, hC2 j n β⟩
  have hpin2 : ∀ (g n : ℕ) (β : BilateralField d), β ∈ G0 →
      const0 (κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl g))))))))) n β = Zg g n β := fun g n β _ => hC7 g n β
  have hJfin := hJ ℕ const0 (fun j => κ (Sum.inr (Sum.inl j)))
    (fun j => κ (Sum.inr (Sum.inr (Sum.inl j))))
    (fun g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inl g))))))))) (fun N => N) G0 hpin1 hpin2
  have hcoreid : aux_conv_represented_estimates_transfer_core d hd M H (fun N => N) ℕ root z r hr
      Sspace Dcat fcat (fun _ => ℕ) theta thetaH1
      (fun j g N β => responseSolution (Sspace j)
        (cutoffPositiveCoefficient M H β N (z j) (hr j))
        ((sobolevVolumeLoad g.val).comp (Sspace j).space.subtypeL))
      srcRepB ucellB Cext beta alpha eta t {1} E ℕ resp0 const0 G0
      (fun j => κ (Sum.inl j)) (fun j => κ (Sum.inr (Sum.inl j)))
      (fun j => κ (Sum.inr (Sum.inr (Sum.inl j))))
      (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl ⟨i, g⟩))))))))))
      (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))))
      (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩))))))
      (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr (i, h)))))))))))
      (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h))))))))
      (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h)))))))))
      ℕ origin gridRoot
      (fun g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl g)))))))))  := by
    unfold aux_conv_represented_estimates_transfer_core
    refine ⟨⟨ht, htd⟩, ⟨ha1, heta, hAeta⟩, ⟨hb, hba⟩, hCext, ?_, fun a b hab => hab, hH, hG0m,
      hG0null, hsub, hrat, htri, hcomp, horat, fun j => hgrid j (z j) (hrat j), hS, hDdense, hf3,
      hf4, hth5, hth6, hth7, hth8, hth9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rw [Finset.mem_singleton] at hp
      rw [hp]; norm_num
    · exact fun i N => hconstM i N
    · intro i p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact hconstB i
    · exact fun i β _ N => hconstN i N β
    · intro j N β hβ
      refine ⟨fun g => ⟨rfl, (hsrcB j g N β (hβGs β hβ j)).1, hR0 j g N β⟩,
        fun h => ⟨?_, ?_, ?_, ?_, hR1 j h N β⟩⟩
      · exact (hucellB j h N β (hβGc β hβ j)).1
      · exact (hucellB j h N β (hβGc β hβ j)).2.1
      · exact (hucellB j h N β (hβGc β hβ j)).2.2.1
      · exact (hucellB j h N β (hβGc β hβ j)).2.2.2.1
    · exact fun j N β hβ => ⟨hC1 j N β, hC2 j N β⟩
    · intro j N β hβ v
      have := hKH j N β (hβGH β hβ j) v
      exact ⟨this.1, this.2.trans (le_of_eq (by rw [hC0 j N β]))⟩
    · intro j N β hβ e hec hcls
      have := hI M H β N (z j) (r j) (hr j) e hec hcls
      exact this.trans (le_of_eq (by rw [hC1 j N β]))
    · exact fun g n k j β hβ => hJfin g n k j β hβ (hβGg β hβ)
    · intro j g N β hβ
      obtain ⟨_, hgr, hco, hfr, hho, hno⟩ := hsrcB j g N β (hβGs β hβ j)
      refine ⟨fun x hx rr h1 h2 => (hgr x hx rr h1 h2).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hC3 j g N β]))), hco, hfr, hho,
        hno.trans (le_of_eq (by rw [hC4 j g N β]))⟩
    · intro j h N β hβ
      obtain ⟨_, _, _, _, hgr, hho, hno⟩ := hucellB j h N β (hβGc β hβ j)
      refine ⟨fun x hx rr h1 h2 => (hgr x hx rr h1 h2).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hC5 j h N β]))), hho,
        hno.trans (le_of_eq (by rw [hC6 j h N β]))⟩
  refine ⟨resp0, const0, root, hunit, Dcat, hDc, fcat, theta, thetaH1,
    (fun j g n β => responseSolution (Sspace j)
      (cutoffPositiveCoefficient M H β (NE n) (z j) (hr j))
      ((sobolevVolumeLoad g.val).comp (Sspace j).space.subtypeL)),
    (fun j g n β => responseSolution (Sspace j)
      (cutoffPositiveCoefficient M H β (NF n) (z j) (hr j))
      ((sobolevVolumeLoad g.val).comp (Sspace j).space.subtypeL)),
    (fun j g n β => srcRepB j g (NE n) β), (fun j g n β => srcRepB j g (NF n) β),
    (fun j h n β => ucellB j h (NE n) β), (fun j h n β => ucellB j h (NF n) β),
    Cext, beta, t, E,
    (fun j => κ (Sum.inl j)),
    (fun j => κ (Sum.inr (Sum.inl j))),
    (fun j => κ (Sum.inr (Sum.inr (Sum.inl j)))),
    (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))))))))),
    (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩))))),
    (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))))),
    (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, h))))))))))),
    (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h)))))))),
    (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h))))))))),
    origin, gridRoot,
    (fun g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl g))))))))), G0, G0, ?_, ?_, ?_, ?_⟩
  · exact fun i n => ⟨hresp0M i (NE n), hresp0M i (NF n)⟩
  · intro i rho hrho
    obtain ⟨M1, hM1⟩ := hresp0T NE i rho hrho
    obtain ⟨M2, hM2⟩ := hresp0T NF i rho hrho
    refine ⟨max M1 M2, fun n => ⟨le_trans (measure_mono ?_) (hM1 n),
      le_trans (measure_mono ?_) (hM2 n)⟩⟩
    · intro β hβ
      have hβ' : max M1 M2 < |resp0 i (NE n) β| := hβ
      exact lt_of_le_of_lt (le_max_left _ _) hβ'
    · intro β hβ
      have hβ' : max M1 M2 < |resp0 i (NF n) β| := hβ
      exact lt_of_le_of_lt (le_max_right _ _) hβ'
  · exact hth10
  · letI : ∀ i, Countable (Dcat i) := hDc
    exact ⟨aux_conv_represented_catalogue_original_shift d hd M H NE hNE ℕ root z r hr Sspace
      Dcat fcat (fun _ => ℕ) theta thetaH1 _ srcRepB ucellB Cext beta alpha eta t {1} E ℕ resp0
      const0 G0 _ _ _ _ _ _ _ _ _ ℕ origin gridRoot _ hcoreid,
      aux_conv_represented_catalogue_original_shift d hd M H NF hNF ℕ root z r hr Sspace
      Dcat fcat (fun _ => ℕ) theta thetaH1 _ srcRepB ucellB Cext beta alpha eta t {1} E ℕ resp0
      const0 G0 _ _ _ _ _ _ _ _ _ ℕ origin gridRoot _ hcoreid⟩

end Paper
