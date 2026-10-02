import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLowerSobolevClosure

/-!
# Locally continuously differentiable multipliers on the Dirichlet graph

Multipliers need only be `C¹` inside the domain, with essentially bounded
value and first derivatives. Multiplying a compactly supported approximant
gives a globally `C¹` compactly supported function; zero-trace closure then
gives the multiplier on the full graph. No smoothness across the boundary is
assumed.
-/

set_option autoImplicit false

open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Probability.BrownianProduct
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower

/-- A local `C¹` multiplier times a function supported inside its domain is globally `C¹`. -/
theorem contDiff_one_mul_of_tsupport_subset {d : ℕ} {W : Set (Vec d)}
    (hW : IsOpen W) {φ f : Vec d → ℝ} (hφ : ContDiffOn ℝ 1 φ W)
    (hf : ContDiff ℝ 1 f) (hs : tsupport f ⊆ W) :
    ContDiff ℝ 1 (fun x => φ x * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ W
  · exact (hφ.contDiffAt (hW.mem_nhds hx)).mul hf.contDiffAt
  · have hxs : x ∉ tsupport f := fun h => hx (hs h)
    have he : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxs
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    change φ y * f y = 0
    simp only [Pi.zero_apply, hy, mul_zero]

/-- Multiplication by an `L∞` function preserves convergence in `L²`. -/
theorem tendsto_eLpNorm_mul_of_memLp_top {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {φ u : X → ℝ} (hφ : MemLp φ ∞ μ) (hu : MemLp u 2 μ)
    (f : ℕ → X → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => φ x * f n x - φ x * u x) 2 μ) atTop (𝓝 0) := by
  have hb (n : ℕ) : eLpNorm (fun x => φ x * f n x - φ x * u x) 2 μ ≤
      eLpNorm φ ∞ μ * eLpNorm (fun x => f n x - u x) 2 μ := by
    have he : (fun x => φ x * f n x - φ x * u x) = φ • (fun x => f n x - u x) := by
      funext x
      change φ x * f n x - φ x * u x = φ x * (f n x - u x)
      ring
    rw [he]
    exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 ((hf n).sub hu).aestronglyMeasurable φ
  have ht := ENNReal.Tendsto.const_mul hlim (Or.inr hφ.eLpNorm_lt_top.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using ht) (fun _ => zero_le _) hb

/-- The product rule on the closed Dirichlet Sobolev domain for local `C¹` multipliers. -/
theorem sobolevGraph_mul_of_contDiffOn_one {d : ℕ} {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) {φ u : Vec d → ℝ} {g : Vec d → Vec d}
    (hφ : ContDiffOn ℝ 1 φ W) (hφtop : MemLp φ ∞ (volume.restrict W))
    (hdφtop : ∀ i, MemLp (fun x => fderiv ℝ φ x (Pi.single i 1)) ∞ (volume.restrict W))
    (hu : SobolevGraph W u g) :
    SobolevGraph W (fun x => φ x * u x)
      (fun x i => φ x * g x i + u x * fderiv ℝ φ x (Pi.single i 1)) := by
  obtain ⟨hum, hgm, f, hf, hc, hs, hlim, hglim⟩ := hu
  let μ := volume.restrict W
  let Dφ (i : Fin d) (x : Vec d) := fderiv ℝ φ x (Pi.single i 1)
  let Df (n : ℕ) (i : Fin d) (x : Vec d) := fderiv ℝ (f n) x (Pi.single i 1)
  have hfm (n : ℕ) : MemLp (f n) 2 μ :=
    ((hf n).continuous.memLp_of_hasCompactSupport (hc n)).restrict W
  have hdfm (n : ℕ) (i : Fin d) : MemLp (Df n i) 2 μ :=
    (((hf n).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.memLp_of_hasCompactSupport ((hc n).fderiv_apply (𝕜 := ℝ) (Pi.single i 1))).restrict W
  have hprod (n : ℕ) : SobolevGraph W (fun x => φ x * f n x)
      (fun x i => fderiv ℝ (fun y => φ y * f n y) x (Pi.single i 1)) :=
    sobolevGraph_of_contDiff_one hW
      (contDiff_one_mul_of_tsupport_subset hW.isOpen hφ ((hf n).of_le (by simp)) (hs n))
      ((hc n).mul_left) ((tsupport_mul_subset_right (f := φ) (g := f n)).trans (hs n))
  have hd (n : ℕ) (i : Fin d) (x : Vec d) (hx : x ∈ W) :
      fderiv ℝ (fun y => φ y * f n y) x (Pi.single i 1) =
        φ x * Df n i x + f n x * Dφ i x := by
    have hφd := (hφ.contDiffAt (hW.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
    have hfd : DifferentiableAt ℝ (f n) x := (hf n).contDiffAt.differentiableAt (by simp)
    rw [show (fun y => φ y * f n y) = φ * f n from rfl, fderiv_mul hφd hfd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Dφ, Df]
  apply sobolevGraph_of_tendsto (hum.mul' hφtop)
    (fun i => ((hgm i).mul' hφtop).add ((hdφtop i).mul' hum))
    (fun n x => φ x * f n x)
    (fun n x i => fderiv ℝ (fun y => φ y * f n y) x (Pi.single i 1)) hprod
    (tendsto_eLpNorm_mul_of_memLp_top hφtop hum f hfm hlim)
  intro i
  let A (n : ℕ) (x : Vec d) := φ x * Df n i x - φ x * g x i
  let B (n : ℕ) (x : Vec d) := Dφ i x * f n x - Dφ i x * u x
  have hAm (n : ℕ) : MemLp (A n) 2 μ := ((hdfm n i).mul' hφtop).sub ((hgm i).mul' hφtop)
  have hBm (n : ℕ) : MemLp (B n) 2 μ := ((hfm n).mul' (hdφtop i)).sub (hum.mul' (hdφtop i))
  have hAlim : Tendsto (fun n => eLpNorm (A n) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_mul_of_memLp_top hφtop (hgm i) (fun n => Df n i) (fun n => hdfm n i) (hglim i)
  have hBlim : Tendsto (fun n => eLpNorm (B n) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_mul_of_memLp_top (hdφtop i) hum f hfm hlim
  have hbound (n : ℕ) :
      eLpNorm (fun x => fderiv ℝ (fun y => φ y * f n y) x (Pi.single i 1) -
        (φ x * g x i + u x * fderiv ℝ φ x (Pi.single i 1))) 2 μ ≤
          eLpNorm (A n) 2 μ + eLpNorm (B n) 2 μ := by
    calc
      _ = eLpNorm (A n + B n) 2 μ := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hW.isOpen.measurableSet] with x hx
        dsimp only [Pi.add_apply, A, B]
        rw [hd n i x hx]
        dsimp only [Dφ]
        ring
      _ ≤ _ := eLpNorm_add_le (hAm n).aestronglyMeasurable (hBm n).aestronglyMeasurable (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using hAlim.add hBlim) (fun _ => zero_le _) hbound




end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower
