module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452PathMeasure
public import SubdiffusiveProcess.Probability.Diffusion.Packet452Stationarity
public import SubdiffusiveProcess.Probability.Diffusion.Packet452Dirichlet

@[expose] public section

/-!
# the reversed maximal bound, and `maximalEstimateGoal`

Everything of §1 and §4 that is transport rather than new probability, assuming only
`PathReversalInvariance d` (the invariance of `∫ₓ P_x dx` under `reversePath T`).

* `lintegral_x_iSup_sq_reversedDynkin_le` -- the reversed maximal bound, obtained from the forward
  one by §1.1's deterministic identity plus the invariance.  **No second Doob application**, and no
  Riemann-sum approximation of the compensator.
* `maximalEstimateGoal_of_reversalInvariance` -- the target.

The algebraic step is the forward/reversed averaging.  For `t ≤ T`,

```text
M_t + (M̂_{T−t} − M̂_T) = 2(φ(ω t) − φ(ω 0)),
```

because the two compensators are `∫₀ᵗ` and `∫ₜᵀ − ∫₀ᵀ = −∫₀ᵗ`.  Hence
`φ(ω t) = φ(ω 0) + ½M_t + ½M̂_{T−t} − ½M̂_T`, and the **four**-term Cauchy--Schwarz
`(a+b+c+d)² ≤ 4(a²+b²+c²+d²)` gives

```text
φ(ω t)² ≤ 4φ(ω 0)² + M_t² + M̂_{T−t}² + M̂_T²,
```

so the integrated maximal square is at most `4‖φ‖₂² + 8T·E(φ) + 2·8T·E(φ) = 4‖φ‖₂² + 24T·E(φ)`,
which is below `32(‖φ‖₂² + T·E(φ))`.  This is a cleaner route than the three-term split:
it never needs `(sup|M|)² = sup M²`, which would require the supremum to be attained.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- The Dynkin increment, written out. -/
theorem dynkin_increment_eq (f g : C₀(Vec d, ℝ))
    (hf2 : ContDiff ℝ 2 (f : Vec d → ℝ)) (hfsupp : HasCompactSupport (f : Vec d → ℝ))
    (hgdef : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
    (t : ℝ≥0) (ω : ContinuousPath (Vec d)) :
    isFeller_laplacianSemigroup.dynkinProcess
        ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩ t ω
      - isFeller_laplacianSemigroup.dynkinProcess
        ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩ 0 ω
      = (f : Vec d → ℝ) (ω t) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g t ω := by
  rw [dynkinProcess_eq_sub_timeIntegralPath f g hf2 hfsupp hgdef t ω,
    dynkinProcess_eq_sub_timeIntegralPath f g hf2 hfsupp hgdef 0 ω]
  have h0 : timeIntegralPath g 0 ω = 0 := by simp [timeIntegralPath]
  rw [h0]
  ring

/-- The `ℝ≥0∞` readout of a one-time path average. -/
theorem lintegral_path_eval {G : Vec d → ℝ≥0∞} (hG : Measurable G) (t : ℝ≥0) (x : Vec d) :
    (∫⁻ ω, G (ω t) ∂(laplacianContinuousLaw d x))
      = ∫⁻ z, G z ∂(laplacianSemigroup d t x) := by
  have heval : Measurable fun w : ContinuousPath (Vec d) => w t :=
    ContinuousPath.measurable_coordinateProcess t
  rw [← laplacianContinuousLaw_map_eval t, Kernel.map_apply _ heval,
    lintegral_map hG heval]

theorem lintegral_path_eval_zero {G : Vec d → ℝ≥0∞} (hG : Measurable G) (x : Vec d) :
    (∫⁻ ω, G (ω 0) ∂(laplacianContinuousLaw d x)) = G x := by
  rw [lintegral_path_eval hG 0 x]
  have hker : (laplacianSemigroup d (0 : ℝ≥0)) x = Measure.dirac x := by
    show ((laplacianSemigroup d).kernel 0) x = Measure.dirac x
    rw [(laplacianSemigroup d).kernel_zero, Kernel.id_apply]
  rw [hker, lintegral_dirac' _ hG]

/-! ## The reversed maximal bound -/

/-- The maximal functional of the Dynkin increment over `[0, T]` is measurable for the **canonical
filtration at `T`** -- which is what the reversal invariance consumes, the unrestricted invariance
being false. -/
theorem measurable_iSup_sq_dynkin_increment_filtration
    (F : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain) (T : ℝ≥0) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) T]
      fun ω : ContinuousPath (Vec d) => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal
      ((isFeller_laplacianSemigroup.dynkinProcess F t ω
        - isFeller_laplacianSemigroup.dynkinProcess F 0 ω) ^ 2) := by
  refine measurable_iSup_le_of_continuous'
    (m := ContinuousPath.canonicalFiltration (alpha := Vec d) T)
    (F := fun (ω : ContinuousPath (Vec d)) (t : ℝ≥0) => ENNReal.ofReal
      ((isFeller_laplacianSemigroup.dynkinProcess F t ω
        - isFeller_laplacianSemigroup.dynkinProcess F 0 ω) ^ 2)) T ?_ ?_
  · intro ω
    exact ENNReal.continuous_ofReal.comp
      (((isFeller_laplacianSemigroup.continuous_dynkinProcess F ω).sub continuous_const).pow 2)
  · intro t ht
    have h1 : Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) T]
        (isFeller_laplacianSemigroup.dynkinProcess F t) :=
      ((isFeller_laplacianSemigroup.stronglyMeasurable_dynkinProcess_canonicalFiltration
        F t).mono (ContinuousPath.canonicalFiltration.mono ht)).measurable
    have h0 : Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) T]
        (isFeller_laplacianSemigroup.dynkinProcess F 0) :=
      ((isFeller_laplacianSemigroup.stronglyMeasurable_dynkinProcess_canonicalFiltration
        F 0).mono (ContinuousPath.canonicalFiltration.mono (show (0 : ℝ≥0) ≤ T from bot_le))).measurable
    exact ((h1.sub h0).pow_const 2).ennreal_ofReal

theorem measurable_iSup_sq_dynkin_increment
    (F : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain) (T : ℝ≥0) :
    Measurable fun ω : ContinuousPath (Vec d) => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal
      ((isFeller_laplacianSemigroup.dynkinProcess F t ω
        - isFeller_laplacianSemigroup.dynkinProcess F 0 ω) ^ 2) :=
  (measurable_iSup_sq_dynkin_increment_filtration F T).mono
    (ContinuousPath.canonicalFiltration.le T) le_rfl

/-- **The reversed maximal bound**, from the forward one by §1.1 and the invariance of the path
measure -- no second application of Doob. -/
theorem lintegral_x_iSup_sq_reversedDynkin_le (hinv : PathReversalInvariance d)
    (f g : C₀(Vec d, ℝ)) (hf2 : ContDiff ℝ 2 (f : Vec d → ℝ))
    (hfsupp : HasCompactSupport (f : Vec d → ℝ))
    (hgsupp : HasCompactSupport (g : Vec d → ℝ))
    (hgdef : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
    {T : ℝ≥0} (hT : 0 < (T : ℝ)) :
    (∫⁻ x, (∫⁻ ω, (⨆ u : ℝ≥0, ⨆ (_ : u ≤ T), ENNReal.ofReal
        ((reversedDynkin ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩
          T u ω) ^ 2)) ∂(laplacianContinuousLaw d x)) ∂volume)
      ≤ ENNReal.ofReal (8 * (T : ℝ) *
          (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)) := by
  set F : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain :=
    ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩ with hFdef
  set G : ContinuousPath (Vec d) → ℝ≥0∞ := fun ω => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal
    ((isFeller_laplacianSemigroup.dynkinProcess F t ω
      - isFeller_laplacianSemigroup.dynkinProcess F 0 ω) ^ 2) with hGdef
  have hGmeas : Measurable G := measurable_iSup_sq_dynkin_increment F T
  have hGmeasF : Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) T] G :=
    measurable_iSup_sq_dynkin_increment_filtration F T
  have hrev : ∀ ω : ContinuousPath (Vec d),
      (⨆ u : ℝ≥0, ⨆ (_ : u ≤ T), ENNReal.ofReal ((reversedDynkin F T u ω) ^ 2))
        = G (reversePath T ω) := fun ω => iSup_sq_reversedDynkin_eq F T ω
  calc (∫⁻ x, (∫⁻ ω, (⨆ u : ℝ≥0, ⨆ (_ : u ≤ T), ENNReal.ofReal
          ((reversedDynkin F T u ω) ^ 2)) ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫⁻ x, (∫⁻ ω, G (reversePath T ω) ∂(laplacianContinuousLaw d x)) ∂volume := by
        simp only [hrev]
    _ = ∫⁻ ω, G (reversePath T ω) ∂(pathMeasure d) :=
        (lintegral_pathMeasure (hGmeas.comp (measurable_reversePath T))).symm
    _ = ∫⁻ ω, G ω ∂(pathMeasure d) := lintegral_reversePath hinv T hGmeasF
    _ = ∫⁻ x, (∫⁻ ω, G ω ∂(laplacianContinuousLaw d x)) ∂volume :=
        lintegral_pathMeasure hGmeas
    _ ≤ ENNReal.ofReal (8 * (T : ℝ) *
          (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)) := by
        have h := lintegral_x_iSup_sq_dynkin_increment_le f g hf2 hfsupp hgsupp hgdef hT
        refine le_trans (le_of_eq ?_) h
        refine lintegral_congr fun x => lintegral_congr fun ω => ?_
        rw [hGdef]
        refine iSup_congr fun t => iSup_congr fun _ => ?_
        rw [dynkin_increment_eq f g hf2 hfsupp hgdef t ω]

/-! ## The forward/reversed averaging identity -/

/-- **The averaging identity.**  For `t ≤ T`, the forward and reversed compensators cancel:
`M_t + (M̂_{T−t} − M̂_T) = 2(φ(ω t) − φ(ω 0))`. -/
theorem two_mul_sub_eq_dynkin_add_reversed (f g : C₀(Vec d, ℝ))
    (hf2 : ContDiff ℝ 2 (f : Vec d → ℝ)) (hfsupp : HasCompactSupport (f : Vec d → ℝ))
    (hgdef : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
    {T t : ℝ≥0} (ht : t ≤ T) (ω : ContinuousPath (Vec d)) :
    2 * ((f : Vec d → ℝ) (ω t) - (f : Vec d → ℝ) (ω 0))
      = ((f : Vec d → ℝ) (ω t) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g t ω)
        + (reversedDynkin ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩
            T (T - t) ω
          - reversedDynkin ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩
            T T ω) := by
  set F : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain :=
    ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩ with hFdef
  have hgen : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generator F = g := by
    rw [hFdef]
    exact generator_laplacianSemigroup f g hf2 hfsupp hgdef
  have hcont : Continuous fun s : ℝ => (g : Vec d → ℝ) (ω (Real.toNNReal s)) :=
    (map_continuous g).comp (ω.continuous.comp continuous_real_toNNReal)
  have hsub1 : T - (T - t) = t := tsub_tsub_cancel_of_le ht
  have hsub2 : ((T - t : ℝ≥0) : ℝ) = (T : ℝ) - (t : ℝ) := NNReal.coe_sub ht
  have hlow : (T : ℝ) - ((T - t : ℝ≥0) : ℝ) = (t : ℝ) := by rw [hsub2]; ring
  have hA : reversedDynkin F T (T - t) ω
      = (f : Vec d → ℝ) (ω t) - (f : Vec d → ℝ) (ω T)
        - ∫ s in (t : ℝ)..(T : ℝ), (g : Vec d → ℝ) (ω (Real.toNNReal s)) := by
    rw [reversedDynkin, hgen, hsub1, hlow]
  have hB : reversedDynkin F T T ω
      = (f : Vec d → ℝ) (ω 0) - (f : Vec d → ℝ) (ω T)
        - ∫ s in (0 : ℝ)..(T : ℝ), (g : Vec d → ℝ) (ω (Real.toNNReal s)) := by
    rw [reversedDynkin, hgen, tsub_self, sub_self]
  have hsplit : (∫ s in (0 : ℝ)..(t : ℝ), (g : Vec d → ℝ) (ω (Real.toNNReal s)))
      + (∫ s in (t : ℝ)..(T : ℝ), (g : Vec d → ℝ) (ω (Real.toNNReal s)))
      = ∫ s in (0 : ℝ)..(T : ℝ), (g : Vec d → ℝ) (ω (Real.toNNReal s)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [hA, hB, timeIntegralPath]
  linarith [hsplit]

/-! ## `maximalEstimateGoal` -/

/-- **`maximalEstimateGoal`, granted the reversal invariance of the path measure.** -/
theorem maximalEstimateGoal_of_reversalInvariance (hinv : PathReversalInvariance d) :
    maximalEstimateGoal d := by
  intro phi hphi hsupp T
  classical
  -- the `C₀` carriers
  set f : C₀(Vec d, ℝ) := c0OfCompactSupport hphi.continuous hsupp with hfdef
  have hfsupp : HasCompactSupport (f : Vec d → ℝ) := hsupp
  have hLcont : Continuous fun x : Vec d => iteratedFDeriv ℝ 2 phi x :=
    hphi.continuous_iteratedFDeriv le_rfl
  have hgcont : Continuous (fullLaplacian phi) := by
    refine continuous_finsetSum _ fun i _ => ?_
    have hev : Continuous fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Vec d) ℝ =>
        L ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)] :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Vec d) ℝ
        ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)]).continuous
    exact hev.comp hLcont
  have hgsupp0 : HasCompactSupport (fullLaplacian phi) := by
    refine (hsupp.iteratedFDeriv (𝕜 := ℝ) 2).mono ?_
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by simp [fullLaplacian, h0])
  set g : C₀(Vec d, ℝ) := c0OfCompactSupport hgcont hgsupp0 with hgdefC
  have hgsupp : HasCompactSupport (g : Vec d → ℝ) := hgsupp0
  have hgdef : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)] := fun x => rfl
  have hf2 : ContDiff ℝ 2 (f : Vec d → ℝ) := hphi
  -- the energy
  have hE : (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)
      = ∫ x, energyDensity phi x ∂volume := by
    rw [show (∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)
        = ∫ y, phi y * fullLaplacian phi y ∂volume from rfl,
      integral_mul_fullLaplacian hphi hsupp]
    ring
  have hEnn : 0 ≤ ∫ x, energyDensity phi x ∂volume :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hNnn : 0 ≤ ∫ x, phi x ^ 2 ∂volume := integral_nonneg fun x => sq_nonneg _
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ T from bot_le) with hT0 | hTpos
  · -- degenerate horizon
    have hTz : (T : ℝ) = 0 := by rw [← hT0]; simp
    have hsup : ∀ ω : ContinuousPath (Vec d),
        (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ((phi (ω t)) ^ 2))
          = ENNReal.ofReal ((phi (ω 0)) ^ 2) := by
      intro ω
      refine le_antisymm (iSup_le fun t => iSup_le fun ht => ?_)
        (le_iSup_of_le 0 (le_iSup_of_le (by rw [← hT0]) le_rfl))
      rw [le_antisymm ht (by rw [← hT0]; exact bot_le)]
      rw [← hT0]
    simp only [hsup]
    have hkey : ∀ x : Vec d, (∫⁻ ω, ENNReal.ofReal ((phi (ω 0)) ^ 2)
        ∂(laplacianContinuousLaw d x)) = ENNReal.ofReal ((phi x) ^ 2) := fun x =>
      lintegral_path_eval_zero (G := fun z => ENNReal.ofReal ((phi z) ^ 2))
        ((hphi.continuous.measurable.pow_const 2).ennreal_ofReal) x
    simp only [hkey]
    have hphi2supp : HasCompactSupport fun x : Vec d => phi x ^ 2 := by
      refine hsupp.mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by simp [h0])
    have hphi2int : Integrable (fun x : Vec d => phi x ^ 2) volume :=
      (hphi.continuous.pow 2).integrable_of_hasCompactSupport hphi2supp
    rw [← ofReal_integral_eq_lintegral_ofReal hphi2int
      (Eventually.of_forall fun x => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hTz]
    nlinarith [hNnn]
  · -- the main case
    have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
    set F : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain :=
      ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩ with hFdef
    set SupM : ContinuousPath (Vec d) → ℝ≥0∞ := fun ω => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
      ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess F t ω
        - isFeller_laplacianSemigroup.dynkinProcess F 0 ω) ^ 2) with hSupMdef
    set SupMhat : ContinuousPath (Vec d) → ℝ≥0∞ := fun ω => ⨆ u : ℝ≥0, ⨆ (_ : u ≤ T),
      ENNReal.ofReal ((reversedDynkin F T u ω) ^ 2) with hSupMhatdef
    set A0 : ContinuousPath (Vec d) → ℝ≥0∞ :=
      fun ω => ENNReal.ofReal (4 * (phi (ω 0)) ^ 2) with hA0def
    have hSupMmeas : Measurable SupM := measurable_iSup_sq_dynkin_increment F T
    have hSupMhat_eq : SupMhat = SupM ∘ reversePath T :=
      funext fun ω => iSup_sq_reversedDynkin_eq F T ω
    have hSupMhatmeas : Measurable SupMhat := by
      rw [hSupMhat_eq]
      exact hSupMmeas.comp (measurable_reversePath T)
    have hA0meas : Measurable A0 :=
      (measurable_const.mul (((hphi.continuous.measurable).comp
        (ContinuousPath.measurable_coordinateProcess 0)).pow_const 2)).ennreal_ofReal
    -- the pointwise bound
    have hpt : ∀ ω : ContinuousPath (Vec d),
        (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ((phi (ω t)) ^ 2))
          ≤ A0 ω + SupM ω + 2 * SupMhat ω := by
      intro ω
      refine iSup_le fun t => iSup_le fun ht => ?_
      have hM : isFeller_laplacianSemigroup.dynkinProcess F t ω
          - isFeller_laplacianSemigroup.dynkinProcess F 0 ω
          = phi (ω t) - phi (ω 0) - timeIntegralPath g t ω :=
        dynkin_increment_eq f g hf2 hfsupp hgdef t ω
      have hid : 2 * (phi (ω t) - phi (ω 0))
          = (phi (ω t) - phi (ω 0) - timeIntegralPath g t ω)
            + (reversedDynkin F T (T - t) ω - reversedDynkin F T T ω) :=
        two_mul_sub_eq_dynkin_add_reversed f g hf2 hfsupp hgdef ht ω
      set M : ℝ := phi (ω t) - phi (ω 0) - timeIntegralPath g t ω with hMdef
      set B : ℝ := reversedDynkin F T (T - t) ω with hBdef
      set C : ℝ := reversedDynkin F T T ω with hCdef
      have hp : phi (ω t) = phi (ω 0) + (M + (B - C)) / 2 := by linarith [hid]
      have hsq : (phi (ω t)) ^ 2 ≤ 4 * (phi (ω 0)) ^ 2 + M ^ 2 + B ^ 2 + C ^ 2 := by
        rw [hp]
        nlinarith [sq_nonneg (phi (ω 0) - M / 2), sq_nonneg (phi (ω 0) - B / 2),
          sq_nonneg (phi (ω 0) + C / 2), sq_nonneg (M / 2 - B / 2),
          sq_nonneg (M / 2 + C / 2), sq_nonneg (B / 2 + C / 2)]
      have hsplit : ENNReal.ofReal (4 * (phi (ω 0)) ^ 2 + M ^ 2 + B ^ 2 + C ^ 2)
          ≤ ENNReal.ofReal (4 * (phi (ω 0)) ^ 2) + ENNReal.ofReal (M ^ 2)
            + ENNReal.ofReal (B ^ 2) + ENNReal.ofReal (C ^ 2) := by
        calc ENNReal.ofReal (4 * (phi (ω 0)) ^ 2 + M ^ 2 + B ^ 2 + C ^ 2)
            ≤ ENNReal.ofReal (4 * (phi (ω 0)) ^ 2 + M ^ 2 + B ^ 2)
              + ENNReal.ofReal (C ^ 2) := ENNReal.ofReal_add_le
          _ ≤ (ENNReal.ofReal (4 * (phi (ω 0)) ^ 2 + M ^ 2) + ENNReal.ofReal (B ^ 2))
              + ENNReal.ofReal (C ^ 2) := by gcongr; exact ENNReal.ofReal_add_le
          _ ≤ ((ENNReal.ofReal (4 * (phi (ω 0)) ^ 2) + ENNReal.ofReal (M ^ 2))
              + ENNReal.ofReal (B ^ 2)) + ENNReal.ofReal (C ^ 2) := by
                gcongr; exact ENNReal.ofReal_add_le
      have hMle : ENNReal.ofReal (M ^ 2) ≤ SupM ω := by
        rw [hSupMdef]
        refine le_iSup_of_le t (le_iSup_of_le ht ?_)
        rw [hM]
      have hBle : ENNReal.ofReal (B ^ 2) ≤ SupMhat ω := by
        rw [hSupMhatdef]
        exact le_iSup_of_le (T - t) (le_iSup_of_le tsub_le_self le_rfl)
      have hCle : ENNReal.ofReal (C ^ 2) ≤ SupMhat ω := by
        rw [hSupMhatdef]
        exact le_iSup_of_le T (le_iSup_of_le le_rfl le_rfl)
      calc ENNReal.ofReal ((phi (ω t)) ^ 2)
          ≤ ENNReal.ofReal (4 * (phi (ω 0)) ^ 2 + M ^ 2 + B ^ 2 + C ^ 2) :=
            ENNReal.ofReal_le_ofReal hsq
        _ ≤ ENNReal.ofReal (4 * (phi (ω 0)) ^ 2) + ENNReal.ofReal (M ^ 2)
              + ENNReal.ofReal (B ^ 2) + ENNReal.ofReal (C ^ 2) := hsplit
        _ ≤ A0 ω + SupM ω + SupMhat ω + SupMhat ω := by gcongr
        _ = A0 ω + SupM ω + 2 * SupMhat ω := by ring
    -- integrate
    have hkerA0 : ∀ x : Vec d, (∫⁻ ω, A0 ω ∂(laplacianContinuousLaw d x))
        = ENNReal.ofReal (4 * (phi x) ^ 2) := fun x =>
      lintegral_path_eval_zero (G := fun z => ENNReal.ofReal (4 * (phi z) ^ 2))
        (measurable_const.mul ((hphi.continuous.measurable).pow_const 2)).ennreal_ofReal x
    have hxA0 : Measurable fun x : Vec d => ∫⁻ ω, A0 ω ∂(laplacianContinuousLaw d x) :=
      Measurable.lintegral_kernel_prod_right' (κ := laplacianContinuousLaw d)
        (hA0meas.comp measurable_snd)
    have hxM : Measurable fun x : Vec d => ∫⁻ ω, SupM ω ∂(laplacianContinuousLaw d x) :=
      Measurable.lintegral_kernel_prod_right' (κ := laplacianContinuousLaw d)
        (hSupMmeas.comp measurable_snd)
    have hfwd : (∫⁻ x, (∫⁻ ω, SupM ω ∂(laplacianContinuousLaw d x)) ∂volume)
        ≤ ENNReal.ofReal (8 * (T : ℝ) *
          (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)) := by
      have h := lintegral_x_iSup_sq_dynkin_increment_le f g hf2 hfsupp hgsupp hgdef hTr
      refine le_trans (le_of_eq ?_) h
      refine lintegral_congr fun x => lintegral_congr fun ω => ?_
      rw [hSupMdef]
      exact iSup_congr fun t => iSup_congr fun _ =>
        congrArg _ (congrArg (· ^ 2) (dynkin_increment_eq f g hf2 hfsupp hgdef t ω))
    have hrev : (∫⁻ x, (∫⁻ ω, SupMhat ω ∂(laplacianContinuousLaw d x)) ∂volume)
        ≤ ENNReal.ofReal (8 * (T : ℝ) *
          (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)) :=
      lintegral_x_iSup_sq_reversedDynkin_le hinv f g hf2 hfsupp hgsupp hgdef hTr
    have hphi2supp : HasCompactSupport fun x : Vec d => phi x ^ 2 := by
      refine hsupp.mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by simp [h0])
    have hphi2int : Integrable (fun x : Vec d => phi x ^ 2) volume :=
      (hphi.continuous.pow 2).integrable_of_hasCompactSupport hphi2supp
    have hA0val : (∫⁻ x, (∫⁻ ω, A0 ω ∂(laplacianContinuousLaw d x)) ∂volume)
        = ENNReal.ofReal (4 * ∫ x, phi x ^ 2 ∂volume) := by
      simp only [hkerA0]
      rw [← ofReal_integral_eq_lintegral_ofReal (hphi2int.const_mul 4)
        (Eventually.of_forall fun x => by positivity), integral_const_mul]
    calc (∫⁻ x, (∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
          ENNReal.ofReal ((phi (ω t)) ^ 2)) ∂(laplacianContinuousLaw d x)) ∂volume)
        ≤ ∫⁻ x, (∫⁻ ω, (A0 ω + SupM ω + 2 * SupMhat ω)
            ∂(laplacianContinuousLaw d x)) ∂volume :=
          lintegral_mono fun x => lintegral_mono hpt
      _ = ∫⁻ x, ((∫⁻ ω, A0 ω ∂(laplacianContinuousLaw d x))
            + (∫⁻ ω, SupM ω ∂(laplacianContinuousLaw d x))
            + 2 * ∫⁻ ω, SupMhat ω ∂(laplacianContinuousLaw d x)) ∂volume := by
          refine lintegral_congr fun x => ?_
          simp_rw [← Pi.add_apply]
          rw [lintegral_add_left (hA0meas.add hSupMmeas)]
          simp only [Pi.add_apply]
          rw [lintegral_add_left hA0meas, lintegral_const_mul' 2 _ (by norm_num)]
      _ = (∫⁻ x, (∫⁻ ω, A0 ω ∂(laplacianContinuousLaw d x)) ∂volume)
            + (∫⁻ x, (∫⁻ ω, SupM ω ∂(laplacianContinuousLaw d x)) ∂volume)
            + 2 * ∫⁻ x, (∫⁻ ω, SupMhat ω ∂(laplacianContinuousLaw d x)) ∂volume := by
          have hadd := lintegral_add_left (μ := (volume : Measure (Vec d))) (hxA0.add hxM)
            (fun x => 2 * ∫⁻ ω, SupMhat ω ∂(laplacianContinuousLaw d x))
          simp only [Pi.add_apply] at hadd
          rw [hadd, lintegral_add_left hxA0, lintegral_const_mul' 2 _ (by norm_num)]
      _ ≤ ENNReal.ofReal (4 * ∫ x, phi x ^ 2 ∂volume)
            + ENNReal.ofReal (8 * (T : ℝ) *
              (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume))
            + 2 * ENNReal.ofReal (8 * (T : ℝ) *
              (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)) := by
          rw [hA0val]
          gcongr
      _ ≤ ENNReal.ofReal (32 * ((∫ x, phi x ^ 2 ∂volume) + (T : ℝ) *
            ∫ x, ∑ i : Fin d, (fderiv ℝ phi x (Pi.single i 1)) ^ 2 ∂volume)) := by
          rw [hE, show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by simp,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← ENNReal.ofReal_add (by positivity) (by nlinarith [hEnn, hTr.le]),
            ← ENNReal.ofReal_add (by nlinarith [hNnn, hEnn, hTr.le])
              (by nlinarith [hEnn, hTr.le])]
          refine ENNReal.ofReal_le_ofReal ?_
          have hEq : (∫ x, ∑ i : Fin d, (fderiv ℝ phi x (Pi.single i 1)) ^ 2 ∂volume)
              = ∫ x, energyDensity phi x ∂volume := rfl
          rw [hEq]
          nlinarith [hNnn, hEnn, hTr.le]

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
