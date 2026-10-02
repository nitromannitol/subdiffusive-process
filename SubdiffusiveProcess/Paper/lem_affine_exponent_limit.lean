import SubdiffusiveProcess.Lane3.Forms
import Mathlib.Topology.Basic

open Filter TopologicalSpace Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_affine_exponent_limit
    (d : ℕ) (hd : 2 ≤ d) (beta : ℝ)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    affineExponent (d : ℝ) 1 beta 1 0 =
        -((1 - beta) / (1 + (d : ℝ) / 2)) ∧
      affineExponent (d : ℝ) 1 beta 1 0 < 0 ∧
      Tendsto
        (fun v : ℝ × (ℝ × ℝ) =>
          affineExponent (d : ℝ) v.1 beta v.2.1 v.2.2)
        (nhdsWithin ((1 : ℝ), ((1 : ℝ), (0 : ℝ)))
          {v : ℝ × (ℝ × ℝ) |
            beta < v.1 ∧ v.1 < 1 ∧ 0 < v.2.1 ∧ v.2.1 < 1 ∧ 0 < v.2.2})
        (𝓝 (-((1 - beta) / (1 + (d : ℝ) / 2)))) ∧
      ∃ a g z0 : ℝ,
        beta < a ∧ a < 1 ∧ 0 < g ∧ g < 1 ∧ 0 < z0 ∧
          affineExponent (d : ℝ) a beta g z0 < 0 := by
  have hden : (0 : ℝ) < 1 + (d : ℝ) / 2 := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  set L : ℝ := -((1 - beta) / (1 + (d : ℝ) / 2)) with hLdef
  set S : Set (ℝ × (ℝ × ℝ)) :=
    {v | beta < v.1 ∧ v.1 < 1 ∧ 0 < v.2.1 ∧ v.2.1 < 1 ∧ 0 < v.2.2} with hS
  set pt : ℝ × (ℝ × ℝ) := ((1 : ℝ), ((1 : ℝ), (0 : ℝ))) with hpt
  let f : ℝ × (ℝ × ℝ) → ℝ := fun v => affineExponent (d : ℝ) v.1 beta v.2.1 v.2.2
  have heq : affineExponent (d : ℝ) 1 beta 1 0 = L := by
    rw [hLdef]
    unfold affineExponent
    field_simp
    ring
  have hLneg : L < 0 := by
    rw [hLdef]
    have h1 : 0 < 1 - beta := by linarith
    have hpos : 0 < (1 - beta) / (1 + (d : ℝ) / 2) := div_pos h1 hden
    linarith
  have hneg : affineExponent (d : ℝ) 1 beta 1 0 < 0 := by
    rw [heq]; exact hLneg
  have hcont : ContinuousAt f pt := by
    have hne : pt.1 + (d : ℝ) / 2 ≠ 0 := by rw [hpt]; exact ne_of_gt hden
    show ContinuousAt
      (fun v : ℝ × (ℝ × ℝ) => affineExponent (d : ℝ) v.1 beta v.2.1 v.2.2) pt
    simp only [affineExponent]
    fun_prop (disch := assumption)
  have hfpt : f pt = L := by
    show affineExponent (d : ℝ) pt.1 beta pt.2.1 pt.2.2 = L
    rw [hpt]; exact heq
  have htend : Tendsto f (nhdsWithin pt S) (𝓝 L) := by
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := S))
    rwa [hfpt] at h
  have hmem : pt ∈ closure S := by
    rw [hpt, hS]
    rw [show {v : ℝ × (ℝ × ℝ) | beta < v.1 ∧ v.1 < 1 ∧ 0 < v.2.1 ∧ v.2.1 < 1 ∧ 0 < v.2.2}
          = (Ioo beta 1) ×ˢ ((Ioo 0 1) ×ˢ (Ioi 0)) from by
      ext v; simp only [mem_setOf_eq, mem_prod, mem_Ioo, mem_Ioi]; tauto]
    rw [closure_prod_eq, closure_prod_eq, closure_Ioo (ne_of_lt hbeta1),
      closure_Ioo (by norm_num), closure_Ioi]
    simp only [mem_prod, mem_Icc, mem_Ici]
    norm_num [le_of_lt hbeta1]
  have hU : f ⁻¹' (Iio 0) ∈ 𝓝 pt := by
    have hfp : f pt < 0 := by rw [hfpt]; exact hLneg
    exact hcont.tendsto (isOpen_Iio.mem_nhds hfp)
  obtain ⟨v, hvU, hvS⟩ := mem_closure_iff_nhds.mp hmem (f ⁻¹' (Iio 0)) hU
  rw [hS] at hvS
  change affineExponent (d : ℝ) v.1 beta v.2.1 v.2.2 < 0 at hvU
  exact ⟨heq, hneg, htend, v.1, v.2.1, v.2.2, hvS.1, hvS.2.1, hvS.2.2.1, hvS.2.2.2.1,
    hvS.2.2.2.2, hvU⟩


end Paper
