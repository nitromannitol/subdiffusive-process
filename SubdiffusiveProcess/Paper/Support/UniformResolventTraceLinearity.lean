module

public import SubdiffusiveProcess.Paper.prop_speed_resolvent
public import SubdiffusiveProcess.Paper.lem_19_smooth_density
public import SubdiffusiveProcess.Section9.CubeTrace

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Section9
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace Paper

theorem aux_mfd_prop_uniform_resolvent_smooth_memLp {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g) :
    MemLp g 2 ν := by
  have hK : IsCompact (closure (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    exact (centeredCube_isBounded z hr).isCompact_closure
  have hcont : Continuous g := hg.continuous
  obtain ⟨C, hC⟩ := bddAbove_def.mp (hK.bddAbove_image hcont.norm.continuousOn)
  apply MemLp.of_bound hcont.aestronglyMeasurable C
  rw [ae_iff]
  apply measure_mono_null ?_ hsupp
  intro x hx
  by_contra hxK
  have hxK' : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    simpa only [mem_compl_iff, not_not] using hxK
  exact hx (hC _ ⟨x, hxK', rfl⟩)

theorem aux_mfd_prop_uniform_resolvent_trace_smooth_linear {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : CubeTraceCharacterization hd z hr ν K C T) (c : ℝ)
    (a b e : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder)
    (f g : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (ha : (a.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr :
        Set (SpatialCoordinates d))] f)
    (hb : (b.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr :
        Set (SpatialCoordinates d))] g)
    (he : (e.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr :
        Set (SpatialCoordinates d))] fun x => c * f x + g x) :
    T e = c • T a + T b := by
  have hfm := aux_mfd_prop_uniform_resolvent_smooth_memLp z r hr ν hsupp f hf
  have hgm := aux_mfd_prop_uniform_resolvent_smooth_memLp z r hr ν hsupp g hg
  have hsm : ContDiff ℝ ∞ (fun x => c * f x + g x) := (contDiff_const.mul hf).add hg
  have hem := aux_mfd_prop_uniform_resolvent_smooth_memLp z r hr ν hsupp _ hsm
  rw [hT.2.2 f hf a ha hfm, hT.2.2 g hg b hb hgm, hT.2.2 _ hsm e he hem,
    ← MemLp.toLp_const_smul c hfm, ← MemLp.toLp_add (hfm.const_smul c) hgm]
  exact MemLp.toLp_congr hem _ (Eventually.of_forall fun x => by simp)

theorem aux_mfd_prop_uniform_resolvent_trace_tendsto {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : CubeTraceCharacterization hd z hr ν K C T)
    (x : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder)
    (y δ : ℕ → CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder)
    (hδ : ∀ n, (δ n).val 0 = x.val 0 - (y n).val 0)
    (hlim : Tendsto (fun n => cubeFractionalL2Norm hd z
      r hr halfFractionalOrder (δ n)) atTop (𝓝 0)) :
    Tendsto (fun n => T (y n)) atTop (𝓝 (T x)) := by
  set Lc := C * (K + (ν (closure (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) with hLc
  set L := max 1 Lc with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLL : Lc ≤ L ^ 2 := by
    have : L ≤ L ^ 2 := by nlinarith
    exact (le_max_right _ _).trans this
  have hbd : ∀ n, ‖T (y n) - T x‖ ≤ L * cubeFractionalL2Norm hd z
      r hr halfFractionalOrder (δ n) := by
    intro n
    have hN := aux_prop_speed_resolvent_norm_nonneg hd z
      r hr halfFractionalOrder (δ n)
    have h := hT.2.1 x (y n) (δ n) (hδ n)
    have hsq : ‖T x - T (y n)‖ ^ 2 ≤ (L * cubeFractionalL2Norm hd z
        r hr halfFractionalOrder (δ n)) ^ 2 := by
      calc ‖T x - T (y n)‖ ^ 2 ≤ _ := h
        _ ≤ L ^ 2 * (cubeFractionalL2Norm hd z
            r hr halfFractionalOrder (δ n)) ^ 2 :=
            mul_le_mul_of_nonneg_right hLL (sq_nonneg _)
        _ = _ := by ring
    rw [norm_sub_rev]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (by linarith) hN) two_ne_zero).1 hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) hbd ?_
  simpa using hlim.const_mul L

/-- Linearity of the completion trace (density of smooth functions plus the common
Lipschitz bound). -/
theorem aux_mfd_prop_uniform_resolvent_trace_linear {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : CubeTraceCharacterization hd z hr ν K C T) (c : ℝ)
    (u v w : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder)
    (hw : w.val 0 = c • u.val 0 + v.val 0) :
    T w = c • T u + T v := by
  obtain ⟨a, f, wa, hf, hfa, hwa, hwalim⟩ :=
    lem_19_smooth_density d hd z r hr u
  obtain ⟨b, g, wb, hg, hgb, hwb, hwblim⟩ :=
    lem_19_smooth_density d hd z r hr v
  choose e he1 he2 using fun n => aux_prop_speed_resolvent_frac_lincomb hd
    z r hr halfFractionalOrder
    c (a n) (b n)
  have hTe : ∀ n, T (e n) = c • T (a n) + T (b n) := by
    intro n
    refine aux_mfd_prop_uniform_resolvent_trace_smooth_linear hd z r hr ν hsupp K C T hT c (a n) (b n) (e n)
      (f n) (g n) (hf n) (hg n) (hfa n) (hgb n) ?_
    rw [he1 n]
    filter_upwards [Lp.coeFn_add (c • (a n).val 0) ((b n).val 0),
      Lp.coeFn_smul c ((a n).val 0), hfa n, hgb n] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  choose dd hdd1 hdd2 using fun n => aux_prop_speed_resolvent_frac_lincomb hd
    z r hr halfFractionalOrder
    c (wa n) (wb n)
  have hddv : ∀ n, (dd n).val 0 = w.val 0 - (e n).val 0 := by
    intro n
    rw [hdd1 n, hwa n, hwb n, hw, he1 n, smul_sub]
    abel
  have hddlim : Tendsto (fun n => cubeFractionalL2Norm hd z
      r hr halfFractionalOrder (dd n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => aux_prop_speed_resolvent_norm_nonneg hd _ _ hr _ (dd n))
      hdd2 ?_
    simpa using (hwalim.const_mul |c|).add hwblim
  have hL1 := aux_mfd_prop_uniform_resolvent_trace_tendsto hd z r hr ν K C T hT u a wa hwa hwalim
  have hL2 := aux_mfd_prop_uniform_resolvent_trace_tendsto hd z r hr ν K C T hT v b wb hwb hwblim
  have hL3 := aux_mfd_prop_uniform_resolvent_trace_tendsto hd z r hr ν K C T hT w e dd hddv hddlim
  have hlim2 : Tendsto (fun n => T (e n)) atTop (𝓝 (c • T u + T v)) := by
    simp_rw [hTe]
    exact (hL1.const_smul c).add hL2
  exact tendsto_nhds_unique hL3 hlim2

open Classical in
/-- The finite-energy trace `A w = T (i w hw)` is linear on the energy domain:
the `hAlin` input of `aux_prop_speed_resolvent_abstract_min`. -/
theorem aux_mfd_prop_uniform_resolvent_trace_energy_linear {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : CubeTraceCharacterization hd z hr ν K C T)
    (E : DomainL2 (centeredCube z
      r hr) → ℝ≥0∞)
    (hclosed : ∀ (c : ℝ) (w1 w2 : DomainL2 (centeredCube z
      r hr)), E w1 ≠ ⊤ → E w2 ≠ ⊤ → E (c • w1 + w2) ≠ ⊤)
    (i : (u : DomainL2 (centeredCube z
        r hr)) → E u ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd z
        r hr halfFractionalOrder)
    (hi0 : ∀ (u : DomainL2 (centeredCube z
      r hr)) (hu : E u ≠ ⊤), (i u hu).val 0 = u)
    (c : ℝ) (w1 w2 : DomainL2 (centeredCube z
      r hr)) (h1 : E w1 ≠ ⊤) (h2 : E w2 ≠ ⊤) :
    (if h : E (c • w1 + w2) ≠ ⊤ then T (i (c • w1 + w2) h) else 0) =
      c • (if h : E w1 ≠ ⊤ then T (i w1 h) else 0) +
        (if h : E w2 ≠ ⊤ then T (i w2 h) else 0) := by
  rw [dif_pos (hclosed c w1 w2 h1 h2), dif_pos h1, dif_pos h2]
  exact aux_mfd_prop_uniform_resolvent_trace_linear hd z r hr ν hsupp K C T hT c _ _ _
    (by rw [hi0, hi0, hi0])


end Paper
