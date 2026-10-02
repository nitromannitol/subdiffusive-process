import SubdiffusiveProcess.Lane3.Forms
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic




open Filter Topology

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

theorem positive_density_comparison
    (Hs : Type) [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]
    (X : Type) [MeasurableSpace X]
    (E F : DomainedEnergy Hs X)
    (core : Set Hs) (hcore : core ⊆ (E.dom : Set Hs))
    (Cstar a : ℝ) (hCstar : 0 < Cstar) (ha : 0 < a)
    (hglue : ∀ (u : Hs) (hu : u ∈ core) (eps : ℝ), 0 < eps →
      ∃ (w : Hs) (hw : w ∈ F.dom), ‖w - u‖ ≤ eps ∧
        F.formAt w hw ≤ Cstar * a * E.formAt u (hcore hu) + eps)
    (hclosed : ∀ (u : Hs) (w : ℕ → Hs) (hw : ∀ k, w k ∈ F.dom) (c : ℝ),
      Tendsto w atTop (𝓝 u) → (∀ k, F.formAt (w k) (hw k) ≤ c) →
      ∃ hu : u ∈ F.dom, F.formAt u hu ≤ c)
    (hdense : ∀ (v : Hs) (hv : v ∈ E.dom) (eps : ℝ), 0 < eps →
      ∃ (u : Hs) (hu : u ∈ core), ‖u - v‖ ≤ eps ∧
        E.formAt u (hcore hu) ≤ E.formAt v hv + eps) :
    ∀ (v : Hs) (hv : v ∈ E.dom), ∃ hvF : v ∈ F.dom,
      F.formAt v hvF ≤ Cstar * a * E.formAt v hv := by
  classical
  intro v hv
  have hCa : 0 < Cstar * a := mul_pos hCstar ha
  -- one approximating sequence per tolerance
  have hstep : ∀ eps : ℝ, 0 < eps →
      ∃ hvF : v ∈ F.dom, F.formAt v hvF ≤ Cstar * a * E.formAt v hv + eps := by
    intro eps heps
    set c0 : ℝ := eps / (2 * (Cstar * a + 1)) with hc0
    have hc0pos : 0 < c0 := by
      rw [hc0]; positivity
    set δ : ℕ → ℝ := fun k => min c0 (1 / ((k : ℝ) + 1)) with hδ
    have hδpos : ∀ k, 0 < δ k := by
      intro k
      rw [hδ]
      exact lt_min hc0pos (by positivity)
    have hδle : ∀ k, δ k ≤ c0 := fun k => min_le_left _ _
    have hδsmall : ∀ k, δ k ≤ 1 / ((k : ℝ) + 1) := fun k => min_le_right _ _
    have hδlim : Tendsto δ atTop (𝓝 0) := by
      apply squeeze_zero (fun k => (hδpos k).le) hδsmall
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    choose u hu hu1 hu2 using fun k : ℕ => hdense v hv (δ k) (hδpos k)
    choose w hw hwAB using fun k : ℕ => hglue (u k) (hu k) (δ k) (hδpos k)
    have hbound : ∀ k, F.formAt (w k) (hw k) ≤ Cstar * a * E.formAt v hv + eps := by
      intro k
      have h1 := (hwAB k).2
      have h2 := hu2 k
      have h3 : Cstar * a * E.formAt (u k) (hcore (hu k)) ≤
          Cstar * a * (E.formAt v hv + δ k) := mul_le_mul_of_nonneg_left h2 hCa.le
      have h4 : (Cstar * a + 1) * δ k ≤ (Cstar * a + 1) * c0 :=
        mul_le_mul_of_nonneg_left (hδle k) (by linarith)
      have h5 : (Cstar * a + 1) * c0 ≤ eps := by
        have hd : (0 : ℝ) < Cstar * a + 1 := by linarith
        have heq : (Cstar * a + 1) * c0 = eps / 2 := by
          rw [hc0]
          field_simp
        rw [heq]
        linarith
      nlinarith [h1, h3, h4, h5]
    have htend : Tendsto w atTop (𝓝 v) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero (fun k => norm_nonneg _) (g := fun k => 2 * δ k)
      · intro k
        calc ‖w k - v‖ = ‖(w k - u k) + (u k - v)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖w k - u k‖ + ‖u k - v‖ := norm_add_le _ _
          _ ≤ δ k + δ k := add_le_add (hwAB k).1 (hu1 k)
          _ = 2 * δ k := by ring
      · have h2 := hδlim.const_mul (2 : ℝ)
        rw [mul_zero] at h2
        exact h2
    exact hclosed v w hw _ htend hbound
  obtain ⟨hvF, -⟩ := hstep 1 one_pos
  refine ⟨hvF, ?_⟩
  refine le_of_forall_pos_le_add ?_
  intro eps heps
  obtain ⟨hvF', hle⟩ := hstep eps heps
  exact hle

end Lane3
end SubdiffusiveProcess
