import Mathlib
import SubdiffusiveProcess.Sobolev.WeakGradient
import SubdiffusiveProcess.Main.MeasuresConvergeLocally
import SubdiffusiveProcess.Main.DiffusionPath
import MarkovProcess.Path.ExitTime
open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace Paper
/-- Section 10, auditor Fixes 9/10, L:258–399. Independently harvested order `astra10r3_0927_martingale_condexp_retry`. -/
theorem aux_lim_measure_martingale_condexp
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hmart : Martingale X F P) (hui : UniformIntegrable X 1 P)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => X n w) atTop (𝓝 (Y w))) (n : ℕ) :
    X n =ᵐ[P] P[Y|F n] := by
  have hsub : Submartingale X F P := hmart.submartingale
  have hlim' : ∀ᵐ w ∂P, Tendsto (fun n => X n w) atTop (𝓝 (Filtration.limitProcess X F P w)) :=
    Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hsub hui
  have hae : Y =ᵐ[P] Filtration.limitProcess X F P := by
    filter_upwards [hlim, hlim'] with w hw hw'
    exact tendsto_nhds_unique hw hw'
  calc X n =ᵐ[P] P[Filtration.limitProcess X F P|F n] :=
        MeasureTheory.Martingale.ae_eq_condExp_limitProcess hmart hui n
    _ =ᵐ[P] P[Y|F n] := (MeasureTheory.condExp_congr_ae hae).symm

/-- Section 10, auditor Fixes 9/10, L:258–399. Independently harvested order `astra10r3_0927_condexp_rectangle_retry`. -/
theorem aux_lim_measure_condexp_rectangle
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ m0) (Y Z : Ω → ℝ) (hY : Integrable Y P)
    (n : ℕ) (hZ : Z =ᵐ[P] P[Y|F n])
    (A : Set Ω) (hA : MeasurableSet[F n] A) :
    (∫ w in A, Y w ∂P) = ∫ w in A, Z w ∂P := by
  have hA_meas : MeasurableSet A := F.le n A hA
  have h1 : ∫ w in A, P[Y|F n] w ∂P = ∫ w in A, Y w ∂P :=
    setIntegral_condExp (F.le n) hY hA
  have h2 : ∫ w in A, Z w ∂P = ∫ w in A, P[Y|F n] w ∂P :=
    setIntegral_congr_ae (mX := m0) hA_meas (hZ.mono fun x hx _ => hx)
  rw [h2, h1]

/-- Section 10, auditor Fixes 9/10, L:258–399. Independently harvested order `astra10r3_0927_trim_rectangles_retry`. -/
theorem aux_lim_measure_trim_rectangles
    {Ω X : Type*} {m0 m : MeasurableSpace Ω} {mX : MeasurableSpace X}
    (hm : m.prod mX ≤ m0.prod mX)
    (mu nu : @Measure (Ω × X) (m0.prod mX)) [IsFiniteMeasure mu]
    (hrect : ∀ (A : Set Ω) (B : Set X), MeasurableSet[m] A → MeasurableSet B →
      mu (A ×ˢ B) = nu (A ×ˢ B)) :
    mu.trim hm = nu.trim hm := by
  apply MeasureTheory.Measure.ext_prod
  intro s t hs ht
  rw [MeasureTheory.trim_measurableSet_eq hm (MeasurableSet.prod hs ht),
      MeasureTheory.trim_measurableSet_eq hm (MeasurableSet.prod hs ht)]
  exact hrect s t hs ht

/-- Section 10, auditor Fixes 9/10, L:258–399. Independently harvested order `astra10r3_0927_random_section_identity_retry`. -/
theorem aux_lim_measure_random_section_identity
    {Ω X : Type*} {m0 m : MeasurableSpace Ω} {mX : MeasurableSpace X}
    (hm : m.prod mX ≤ m0.prod mX) (P : @Measure Ω m0) [SFinite P]
    (k l : @Kernel Ω X m0 mX) [IsSFiniteKernel k] [IsSFiniteKernel l]
    (heq : (P ⊗ₘ k).trim hm = (P ⊗ₘ l).trim hm)
    (B : Set (Ω × X)) (hB : MeasurableSet[m.prod mX] B) :
    (∫⁻ w, k w {x | (w,x) ∈ B} ∂P) = ∫⁻ w, l w {x | (w,x) ∈ B} ∂P := by
  have hk : ∫⁻ w, k w {x : X | (w, x) ∈ B} ∂P = ((P ⊗ₘ k).trim hm) B := by
    rw [MeasureTheory.trim_measurableSet_eq hm hB,
      MeasureTheory.Measure.compProd_apply (s := B) (hm B hB)]
    rfl
  have hl : ∫⁻ w, l w {x : X | (w, x) ∈ B} ∂P = ((P ⊗ₘ l).trim hm) B := by
    rw [MeasureTheory.trim_measurableSet_eq hm hB,
      MeasureTheory.Measure.compProd_apply (s := B) (hm B hB)]
    rfl
  rw [hk, hl, heq]

/-- Section 10, auditor Fixes 9/10, L:258–399. Independently harvested order `astra10r3_0927_random_section_measurable_retry`. -/
theorem aux_lim_measure_random_section_measurable
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (k : Kernel Ω X) [IsSFiniteKernel k]
    (U : Set X) (hU : MeasurableSet U)
    (B : Set (Ω × X)) (hB : MeasurableSet B) :
    Measurable (fun w => k w {x | x ∈ U ∧ (w,x) ∈ B}) := by
  have hT : MeasurableSet ((Set.univ ×ˢ U) ∩ B : Set (Ω × X)) :=
    (MeasurableSet.univ.prod hU).inter hB
  have h := Kernel.measurable_kernel_prodMk_left (κ := k) hT
  convert h using 1
  ext w
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and,
    Set.mem_setOf_eq]


/-- Fix 9, L:283–295: random section masses are measurable on any fixed finite-mass window. -/
theorem aux_lim_measure_measurable_finite_window
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (M : Ω → Measure X) (hM : Measurable M) (U : Set X) (hU : MeasurableSet U)
    (hfin : ∀ w, M w U ≠ ⊤) (B : Set (Ω × X)) (hB : MeasurableSet B) :
    Measurable (fun w => M w {x | x ∈ U ∧ (w,x) ∈ B}) := by
  let k : Kernel Ω X := ⟨fun w => (M w).restrict U, by
    apply Measure.measurable_measure.2
    intro s hs
    simp only [Measure.restrict_apply hs]
    exact (Measure.measurable_coe (hs.inter hU)).comp hM⟩
  have hk : ∀ w, IsFiniteMeasure (k w) := fun w =>
    isFiniteMeasure_restrict.mpr (hfin w)
  have h := Kernel.measurable_kernel_prodMk_left_of_finite (κ := k) hB hk
  convert h using 1
  funext w
  rw [show k w = (M w).restrict U from rfl, Measure.restrict_apply (measurable_prodMk_left hB)]
  congr 1
  ext x
  exact and_comm

/-- Fix 9: equality of finite retained-layer rectangular tests implies equality of random tests. -/
theorem aux_lim_measure_random_test_of_rectangles
    {Ω X : Type*} {m0 m : MeasurableSpace Ω} {mX : MeasurableSpace X}
    (hm : m.prod mX ≤ m0.prod mX) (hm0 : m ≤ m0)
    (P : @Measure Ω m0) [SFinite P] (k l : @Kernel Ω X m0 mX)
    [IsSFiniteKernel k] [IsSFiniteKernel l] [IsFiniteMeasure (P ⊗ₘ k)]
    (hrect : ∀ (A : Set Ω) (D : Set X), MeasurableSet[m] A → MeasurableSet D →
      (∫⁻ w in A, k w D ∂P) = ∫⁻ w in A, l w D ∂P)
    (B : Set (Ω × X)) (hB : MeasurableSet[m.prod mX] B) :
    (∫⁻ w, k w {x | (w,x) ∈ B} ∂P) = ∫⁻ w, l w {x | (w,x) ∈ B} ∂P := by
  apply aux_lim_measure_random_section_identity hm P k l _ B hB
  apply aux_lim_measure_trim_rectangles hm
  intro A D hA hD
  simpa only [Measure.compProd_apply_prod (hm0 A hA) hD] using hrect A D hA hD

/-- Fix 9: the actual almost-sure martingale limit has the required rectangular identities. -/
theorem aux_lim_measure_martingale_rectangle_identity
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hmart : Martingale X F P) (hui : UniformIntegrable X 1 P)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => X n w) atTop (𝓝 (Y w)))
    (hY : Integrable Y P) (n : ℕ) (A : Set Ω) (hA : MeasurableSet[F n] A) :
    (∫ w in A, Y w ∂P) = ∫ w in A, X n w ∂P := by
  exact aux_lim_measure_condexp_rectangle P F Y (X n) hY n
    (aux_lim_measure_martingale_condexp P F X Y hmart hui hlim n) A hA

end Paper
