module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.ReflectedWindow
public import Homogenization.Sobolev.H1.LocalizedZeroTrace




@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

open MeasureTheory Filter Topology
open Homogenization (Vec H1Function H10Function MemH10 MemL2On GradMemL2On HasWeakGradientOn
  LocalizedZeroTraceFunctionOn basisVec openCubeSet originCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ### The reflected window meets the domain cube in the window -/

/-- **The reflected window crosses `∂□_m` only through the met faces.**  Inside
`□_m` the partial reflection adds nothing: coordinatewise, a met edge is extended
only *beyond* the corresponding face of `□_m`, and an unmet edge is not moved at
all. -/
theorem reflectedWindow_inter_openCubeSet (x : Vec d) (m k : ℤ) :
    reflectedWindow x m k ∩ openCubeSet (originCube d m) = truncatedWindow x m k := by
  ext y
  constructor
  · rintro ⟨hyR, hym⟩
    rw [mem_reflectedWindow_iff] at hyR
    rw [Homogenization.mem_openCubeSet_originCube_iff] at hym
    rw [truncatedWindow_eq_coordBox, mem_coordBox_iff]
    intro i
    obtain ⟨hlo, hhi⟩ := hyR i
    obtain ⟨hmlo, hmhi⟩ := hym i
    constructor
    · by_cases hlow : MeetsLowerFace x m k i
      · rw [windowLo_of_meetsLowerFace hlow]
        exact hmlo
      · rw [← reflectedLo_of_not_meetsLowerFace hlow]
        exact hlo
    · by_cases hup : MeetsUpperFace x m k i
      · rw [windowHi_of_meetsUpperFace hup]
        exact hmhi
      · rw [← reflectedHi_of_not_meetsUpperFace hup]
        exact hhi
  · intro hy
    exact ⟨truncatedWindow_subset_reflectedWindow x m k hy,
      truncatedWindow_subset_domain x m k hy⟩

/-! ### `H¹₀` localization by a cutoff -/

/-- **Cutoff localization of `H¹₀`.**  If `f ∈ H¹₀(B)` and `η` is a smooth compactly
supported cutoff with `tsupport η ⊆ V`, then `η·f ∈ H¹₀(V ∩ B)`: the `H¹₀(B)`
approximants of the product are supported in
`tsupport η ∩ tsupport (approx) ⊆ V ∩ B`, and every field of the witness
restricts. -/
theorem memH10_mul_of_tsupport_subset {B V : Set (Vec d)} (hB : IsOpen B)
    (hV : IsOpen V) {f : Vec d → ℝ} (hf : MemH10 B f) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) :
    MemH10 (V ∩ B) (fun y => η y * f y) := by
  obtain ⟨w, hw⟩ := hf
  set W : H10Function B := w.mulContDiffHasCompactSupport hη hηc with hWdef
  have hWfun : W.toH1Function.toFun = fun y => η y * f y := by
    rw [hWdef, Homogenization.H10Function.mulContDiffHasCompactSupport_toFun]
    funext y
    rw [show w y = w.toH1Function.toFun y from rfl, hw]
  have happrox : ∀ n, W.approx n = fun x => η x * w.approx n x := fun n => rfl
  have hmono : volume.restrict (V ∩ B) ≤ volume.restrict B :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  have hmemL2 : MemL2On (V ∩ B) fun y => η y * f y := by
    have h := W.toH1Function.memL2
    rw [hWfun] at h
    exact h.mono_measure hmono
  have hgradL2 : GradMemL2On (V ∩ B) W.toH1Function.grad :=
    fun i => (W.toH1Function.gradMemL2 i).mono_measure hmono
  have hweak : HasWeakGradientOn (V ∩ B) (fun y => η y * f y) W.toH1Function.grad := by
    have h := W.toH1Function.hasWeakGradient
    rw [hWfun] at h
    exact h.restrict (hV.inter hB) Set.inter_subset_right
  have hsupp : ∀ n, tsupport (W.approx n) ⊆ V ∩ B := by
    intro n
    rw [happrox n]
    refine Set.subset_inter ?_ ?_
    · exact (tsupport_mul_subset_left (f := η) (g := w.approx n)).trans hηV
    · exact (tsupport_mul_subset_right (f := η) (g := w.approx n)).trans
        (w.approx_support_subset n)
  have htend : Tendsto
      (fun n => eLpNorm (fun x => W.approx n x - η x * f x) 2
        (volume.restrict (V ∩ B))) atTop (nhds 0) := by
    have hbase := W.tendsto_approx
    rw [hWfun] at hbase
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbase
      (fun n => zero_le) (fun n => ?_)
    exact eLpNorm_mono_measure _ hmono
  have htendg : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x => (fderiv ℝ (W.approx n) x) (basisVec i) - W.toH1Function.grad x i) 2
        (volume.restrict (V ∩ B))) atTop (nhds 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (W.tendsto_approx_grad i) (fun n => zero_le) (fun n => ?_)
    exact eLpNorm_mono_measure _ hmono
  refine ⟨⟨⟨fun y => η y * f y, W.toH1Function.grad, hmemL2, hgradL2, hweak⟩,
    W.approx, W.approx_smooth, W.approx_hasCompactSupport, hsupp, htend, htendg⟩,
    rfl⟩

/-! ### Functions vanishing on the window are trivially `H¹₀` -/

/-- **A function vanishing pointwise on `Ω` is `H¹₀(Ω)`.**  CoarseGraining's
`MemH10` constrains its witness only on `Ω`, so the zero approximation sequence
serves. -/
theorem memH10_of_forall_eq_zero {Ω : Set (Vec d)} (hΩ : MeasurableSet Ω)
    {f : Vec d → ℝ} (hf : ∀ y ∈ Ω, f y = 0) : MemH10 Ω f := by
  have hae : f =ᵐ[volume.restrict Ω] (fun _ => (0 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hΩ] with y hy
    exact hf y hy
  have hzeroLp : MemLp (fun _ : Vec d => (0 : ℝ)) 2 (volume.restrict Ω) := by
    change eLpNorm (fun _ : Vec d => (0 : ℝ)) 2 (volume.restrict Ω) < ∞
    have hz : eLpNorm (fun _ : Vec d => (0 : ℝ)) 2 (volume.restrict Ω) = 0 := eLpNorm_fun_zero
    rw [hz]
    exact ENNReal.zero_lt_top
  have hmemL2 : MemL2On Ω f := hzeroLp.ae_eq hae.symm
  have htsupp0 : tsupport (fun _ : Vec d => (0 : ℝ)) = (∅ : Set (Vec d)) := by
    have hsupp : Function.support (fun _ : Vec d => (0 : ℝ)) = (∅ : Set (Vec d)) := by
      ext z
      simp
    show closure (Function.support fun _ : Vec d => (0 : ℝ)) = (∅ : Set (Vec d))
    rw [hsupp, closure_empty]
  have hznorm : eLpNorm (fun y => (0 : ℝ) - f y) 2 (volume.restrict Ω) = 0 := by
    have hcongr : (fun y => (0 : ℝ) - f y)
        =ᵐ[volume.restrict Ω] (fun _ => (0 : ℝ)) := by
      filter_upwards [hae] with y hy
      rw [hy, sub_self]
    rw [eLpNorm_congr_ae hcongr]
    exact eLpNorm_fun_zero
  have hgradL2 : GradMemL2On Ω (fun _ : Vec d => (0 : Vec d)) := fun _ => hzeroLp
  have hweak : HasWeakGradientOn Ω f (fun _ : Vec d => (0 : Vec d)) := by
    intro i φ hφ hφc hφΩ
    have hL : ∫ y in Ω, f y * (fderiv ℝ φ y) (basisVec i) ∂volume = 0 := by
      rw [MeasureTheory.setIntegral_congr_fun hΩ
        (g := fun _ : Vec d => (0 : ℝ)) (fun y hy => by rw [hf y hy, zero_mul])]
      exact MeasureTheory.integral_zero _ _
    have hR : ∫ y in Ω, (fun _ : Vec d => (0 : Vec d)) y i * φ y ∂volume = 0 := by
      rw [MeasureTheory.setIntegral_congr_fun hΩ
        (g := fun _ : Vec d => (0 : ℝ)) (fun y _ => by simp)]
      exact MeasureTheory.integral_zero _ _
    rw [hL, hR, neg_zero]
  have hcompact : HasCompactSupport (fun _ : Vec d => (0 : ℝ)) := by
    rw [HasCompactSupport, htsupp0]
    exact isCompact_empty
  have hsupp : tsupport (fun _ : Vec d => (0 : ℝ)) ⊆ Ω := by
    rw [htsupp0]
    exact Set.empty_subset _
  have htend : Tendsto (fun _ : ℕ => eLpNorm (fun x => (0 : ℝ) - f x) 2
      (volume.restrict Ω)) atTop (nhds 0) := by
    rw [show (fun _ : ℕ => eLpNorm (fun x => (0 : ℝ) - f x) 2
        (volume.restrict Ω)) = fun _ : ℕ => (0 : ℝ≥0∞) from funext fun _ => hznorm]
    exact tendsto_const_nhds
  have hgradzero : ∀ (i : Fin d) (x : Vec d),
      (fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x) (basisVec i)
        - (fun _ : Vec d => (0 : Vec d)) x i = 0 := by
    intro i x
    rw [show (fun _ : Vec d => (0 : ℝ)) = (Function.const (Vec d) (0 : ℝ))
      from rfl, fderiv_const]
    simp
  have htendg : ∀ i : Fin d, Tendsto (fun _ : ℕ => eLpNorm
      (fun x => (fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x) (basisVec i)
        - (fun _ : Vec d => (0 : Vec d)) x i) 2 (volume.restrict Ω))
      atTop (nhds 0) := by
    intro i
    have hz : eLpNorm
        (fun x => (fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x) (basisVec i)
          - (fun _ : Vec d => (0 : Vec d)) x i) 2 (volume.restrict Ω) = 0 := by
      rw [show (fun x : Vec d => (fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x)
          (basisVec i) - (fun _ : Vec d => (0 : Vec d)) x i)
          = fun _ : Vec d => (0 : ℝ) from funext fun x => hgradzero i x]
      exact eLpNorm_fun_zero
    rw [show (fun _ : ℕ => eLpNorm
        (fun x => (fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x) (basisVec i)
          - (fun _ : Vec d => (0 : Vec d)) x i) 2 (volume.restrict Ω))
        = fun _ : ℕ => (0 : ℝ≥0∞) from funext fun _ => hz]
    exact tendsto_const_nhds
  refine ⟨⟨⟨f, fun _ => (0 : Vec d), hmemL2, hgradL2, hweak⟩,
    fun _ _ => (0 : ℝ), fun _ => contDiff_const, fun _ => hcompact, fun _ => hsupp,
    htend, htendg⟩, rfl⟩

/-! ### Localized zero-trace producers -/

/-- Any `H¹₀(Ω)` function has the localized zero trace, in any window. -/
theorem localizedZeroTraceFunctionOn_of_memH10 {Ω V : Set (Vec d)}
    {f : Vec d → ℝ} (hf : MemH10 Ω f) : LocalizedZeroTraceFunctionOn Ω V f := by
  obtain ⟨w, hw⟩ := hf
  rw [← hw]
  exact Homogenization.localizedZeroTraceFunctionOn_of_h10_any w

/-- A function vanishing pointwise on `Ω` has the localized zero trace, in any
window. -/
theorem localizedZeroTraceFunctionOn_of_forall_eq_zero {Ω V : Set (Vec d)}
    (hΩ : MeasurableSet Ω) {f : Vec d → ℝ} (hf : ∀ y ∈ Ω, f y = 0) :
    LocalizedZeroTraceFunctionOn Ω V f := by
  intro η hη hηc hηV
  exact memH10_of_forall_eq_zero hΩ fun y hy => by rw [hf y hy, mul_zero]

/-- **The cube-datum localization.**  A function of `H¹₀(□_m)` has the face-only
localized zero trace on every window, against the reflected window: a cutoff
supported in `reflectedWindow x m k` localizes the global zero trace to
`reflectedWindow ∩ □_m = (x+□_k) ∩ □_m`. -/
theorem localizedZeroTraceFunctionOn_truncatedWindow_of_memH10_cube {m k : ℤ}
    (x : Vec d) {f : Vec d → ℝ}
    (hf : MemH10 (openCubeSet (originCube d m)) f) :
    LocalizedZeroTraceFunctionOn (truncatedWindow x m k) (reflectedWindow x m k) f := by
  intro η hη hηc hηV
  have h := memH10_mul_of_tsupport_subset (Homogenization.isOpen_openCubeSet (originCube d m))
    (isOpen_coordBox (reflectedLo x m k) (reflectedHi x m k)) hf hη hηc hηV
  rwa [show (coordBox (reflectedLo x m k) (reflectedHi x m k)
        ∩ openCubeSet (originCube d m)) = truncatedWindow x m k from
      reflectedWindow_inter_openCubeSet x m k] at h

/-- Localized zero trace is invariant under pointwise-equal functions. -/
theorem localizedZeroTraceFunctionOn_congr {Ω V : Set (Vec d)}
    {f g : Vec d → ℝ} (hfg : ∀ y, f y = g y)
    (hf : LocalizedZeroTraceFunctionOn Ω V f) :
    LocalizedZeroTraceFunctionOn Ω V g := by
  have h : f = g := funext hfg
  rwa [h] at hf

/-! ### The `hzt` supplier -/



theorem localizedZeroTraceFunctionOn_datumSplit {m k : ℤ} {x : Vec d}
    {u h ℓ : Vec d → ℝ}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m k)}
    (hvu : MemH10 (truncatedWindow x m k) (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m k)}
    (hΨ : ∀ y ∈ truncatedWindow x m k, Ψ.toFun y = h y - ℓ y)
    (hv₁Ψ : MemH10 (truncatedWindow x m k) (fun y => v₁.toFun y - Ψ.toFun y)) :
    LocalizedZeroTraceFunctionOn (truncatedWindow x m k) (reflectedWindow x m k)
      (fun y => v.toFun y - ℓ y - v₁.toFun y) := by
  have h1 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) (fun y => v.toFun y - u y) :=
    localizedZeroTraceFunctionOn_of_memH10 hvu
  have h2 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) (fun y => u y - h y) :=
    localizedZeroTraceFunctionOn_truncatedWindow_of_memH10_cube x hdat
  have h3 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) (fun y => h y - ℓ y - Ψ.toFun y) :=
    localizedZeroTraceFunctionOn_of_forall_eq_zero
      (isOpen_truncatedWindow x m k).measurableSet
      (fun y hy => by rw [hΨ y hy]; ring)
  have h4 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) (fun y => Ψ.toFun y - v₁.toFun y) := by
    have hneg := Homogenization.memH10_neg hv₁Ψ
    refine localizedZeroTraceFunctionOn_of_memH10 ?_
    have hfun : (fun y => -(v₁.toFun y - Ψ.toFun y))
        = fun y => Ψ.toFun y - v₁.toFun y := by
      funext y
      ring
    rwa [hfun] at hneg
  have h12 := Homogenization.localizedZeroTraceFunctionOn_add h1 h2
  have h34 := Homogenization.localizedZeroTraceFunctionOn_add h3 h4
  have h := Homogenization.localizedZeroTraceFunctionOn_add h12 h34
  exact localizedZeroTraceFunctionOn_congr (fun y => by ring) h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
