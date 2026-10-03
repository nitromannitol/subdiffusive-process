module

public import SubdiffusiveProcess.Paper.car_variational
public import SubdiffusiveProcess.Paper.Support.UniformResolventTraceLinearity
public import SubdiffusiveProcess.Analysis.LimitEnergyCoercivity

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Section9
open scoped ENNReal NNReal
noncomputable section
namespace Paper

theorem aux_mfd_prop_uniform_resolvent_trace_zero {d : ℕ} (hd : 2 ≤ d)
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {mu : Measure (SpatialCoordinates d)} {K C : ℝ}
    {T : CubeFractionalL2 (k := 1) hd z
        r hr halfFractionalOrder → Lp ℝ 2 mu}
    (hT : CubeTraceCharacterization hd z hr mu K C T)
    (w0 : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder) :
    ∃ z0 : CubeFractionalL2 (k := 1) hd z
        r hr halfFractionalOrder,
      z0.val 0 = w0.val 0 - w0.val 0 ∧ T z0 = 0 := by
  refine ⟨⟨fun i => w0.val i - w0.val i,
    cubeFractionalL2Seminorm_sub_lt_top hd z
      r hr halfFractionalOrder w0.val w0.val
      w0.property w0.property⟩, rfl, ?_⟩
  have hae0 : ((⟨fun i => w0.val i - w0.val i,
      cubeFractionalL2Seminorm_sub_lt_top hd z
        r hr halfFractionalOrder w0.val w0.val
        w0.property w0.property⟩ : CubeFractionalL2 (k := 1) hd z
          r hr halfFractionalOrder).val 0 :
      SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube
        z r hr :
        Set (SpatialCoordinates d))] (fun _ => (0 : ℝ)) := by
    show ((w0.val 0 - w0.val 0 : DomainL2 (centeredCube z
        r hr)) : SpatialCoordinates d → ℝ) =ᵐ[_]
        (fun _ => (0 : ℝ))
    rw [sub_self]
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (centeredCube
      z r hr :
      Set (SpatialCoordinates d)))] with x hx
    simpa using hx
  have hmemlp0 : MemLp (fun _ : SpatialCoordinates d => (0 : ℝ)) 2 mu := MemLp.zero'
  rw [hT.2.2 (fun _ => (0 : ℝ)) contDiff_const _ hae0 hmemlp0]
  exact hmemlp0.toLp_zero

/-- Bundles the three per-omega coercivity/interpolation constants (`Ccoer` from `aux_car_
variational_limit_coercive`, `Cbase` from `aux_car_variational_frac_bound`, `Cint` from `Interp.
interpolation_half`) into ONE call, so `aux_car_variational_Ktr_bound`'s own body only needs one
`obtain` instead of four separate large-signature calls (house elaboration-budget rule: this
alone was still enough for `aux_car_variational_Ktr_bound` to breach the 200000-heartbeat ceiling
even after the fractional-exponent algebra and `T 0 = 0` derivation were already extracted). -/

theorem aux_mfd_prop_uniform_resolvent_trace_bound_per_u
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z
        r hr) →L[ℝ]
      DomainL2 (centeredCube z
        r hr))
    (Ccoer Cbase Cint : ℝ) (hCcoer : 0 < Ccoer) (hCbase : 0 < Cbase) (hCint : 0 < Cint)
    (u : DomainL2 (centeredCube z
        r hr))
    (hu : (limitFormEnergy G u).toENNReal ≠ ⊤)
    (hcoer : ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal Ccoer * (limitFormEnergy G u).toENNReal)
    (hfrac : ∃ v3 : CubeFractionalL2 (k := 1) hd z
        r hr threeQuarterOrder,
      v3.val 0 = u ∧ (cubeFractionalL2Norm hd z
        r hr threeQuarterOrder v3) ^ 2 ≤
          Cbase * (limitFormEnergy G u).toReal)
    (hinterp : ∀ (wHalf : CubeFractionalL2 (k := 1) hd z
          r hr halfFractionalOrder)
        (wThree : CubeFractionalL2 (k := 1) hd z
          r hr threeQuarterOrder),
      wThree.val 0 = wHalf.val 0 →
        cubeFractionalL2Norm hd z
            r hr halfFractionalOrder wHalf ≤
          Cint * (‖wHalf.val 0‖ / Real.sqrt (volume.real (centeredCube
              z r hr :
              Set (SpatialCoordinates d)))) ^ (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd z
              r hr threeQuarterOrder wThree ^ (2 / 3 : ℝ))
    (i : (u' : DomainL2 (centeredCube z
          r hr)) →
        (limitFormEnergy G u').toENNReal ≠ ⊤ →
        CubeFractionalL2 (k := 1) hd z
          r hr halfFractionalOrder)
    (hi : (i u hu).val 0 = u)
    (mu : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z
        r hr halfFractionalOrder → Lp ℝ 2 mu)
    (hT : CubeTraceCharacterization hd z hr mu K C T) (hKnn : 0 ≤ K) (hCnn : 0 ≤ C)
    (J : DomainL2 (centeredCube z
        r hr) → SpatialCoordinates d → ℝ)
    (hJ : (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ)) :
    (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤
      ENNReal.ofReal (C * (K + (mu (closure ((centeredCube z r hr : Set (SpatialCoordinates d))))).toReal) *
        (Cint ^ 2 * (Ccoer / volume.real (centeredCube z
            r hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
          Cbase ^ (2/3:ℝ))) * (limitFormEnergy G u).toENNReal := by
  have hvol : 0 < volume.real (centeredCube z
      r hr : Set (SpatialCoordinates d)) :=
    SubdiffusiveProcess.centeredCube_volume_pos z hr
  obtain ⟨v3, hv3_eq, hv3_bound⟩ := hfrac
  set E := (limitFormEnergy G u).toReal with hEdef
  have hEnn : 0 ≤ E := EReal.toReal_nonneg (limitFormEnergy_nonneg G u)
  have hunorm : ‖u‖ ^ 2 ≤ Ccoer * E := by
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu) hcoer
    rwa [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hCcoer.le, EReal.toReal_toENNReal (limitFormEnergy_nonneg G u)] at h2
  have hv3norm : (cubeFractionalL2Norm hd z
      r hr threeQuarterOrder v3) ^ 2 ≤ Cbase * E := hv3_bound
  have hcombine := hinterp (i u hu) v3 (hv3_eq.trans hi.symm)
  rw [hi] at hcombine
  set A := ‖u‖ / Real.sqrt (volume.real (centeredCube z
      r hr : Set (SpatialCoordinates d))) with hAdef
  set B := cubeFractionalL2Norm hd z
    r hr threeQuarterOrder v3 with hBdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; unfold cubeFractionalL2Norm; positivity
  have hA2 : A ^ 2 ≤ (Ccoer / volume.real (centeredCube z
      r hr : Set (SpatialCoordinates d))) * E := by
    rw [hAdef, div_pow, Real.sq_sqrt hvol.le, div_le_iff₀ hvol, mul_right_comm,
      div_mul_cancel₀ Ccoer hvol.ne']
    exact hunorm
  have hB2 : B ^ 2 ≤ Cbase * E := hv3norm
  have hhalf_nonneg : (0:ℝ) ≤ cubeFractionalL2Norm hd z
      r hr halfFractionalOrder (i u hu) :=
    by unfold cubeFractionalL2Norm; positivity
  have hsq' : (cubeFractionalL2Norm hd z
      r hr halfFractionalOrder (i u hu)) ^ 2 ≤
      Cint ^ 2 * (Ccoer / volume.real (centeredCube z
        r hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
        Cbase ^ (2/3:ℝ) * E :=
    aux_car_variational_Ktr_real_combine hvol hCcoer.le hCbase hEnn hAnn hBnn hhalf_nonneg hA2 hB2
      hcombine
  obtain ⟨z0, hz0val, hz0T⟩ := aux_mfd_prop_uniform_resolvent_trace_zero hd hT (i u hu)
  have hTlip := hT.2.1 (i u hu) z0 (i u hu) (by rw [hz0val]; abel)
  rw [hz0T, sub_zero] at hTlip
  have hnormsq : ‖T (i u hu)‖ ^ 2 ≤
      C * (K + (mu (closure ((centeredCube z r hr : Set (SpatialCoordinates d))))).toReal) *
        (Cint ^ 2 * (Ccoer / volume.real (centeredCube z
            r hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
          Cbase ^ (2/3:ℝ) * E) := by
    refine hTlip.trans ?_
    apply mul_le_mul_of_nonneg_left hsq'
    have hKterm : 0 ≤ K + (mu (closure ((centeredCube z r hr : Set (SpatialCoordinates d))))).toReal :=
      add_nonneg hKnn ENNReal.toReal_nonneg
    positivity
  have hlintJ : (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) =
      ∫⁻ x, ENNReal.ofReal ((T (i u hu) x) ^ 2) ∂mu := by
    apply lintegral_congr_ae
    filter_upwards [hJ] with x hx
    rw [hx]
  rw [hlintJ, aux_car_variational_Ktr_lintegral_sq_eq_norm_sq]
  have hEeq : (limitFormEnergy G u).toENNReal = ENNReal.ofReal E := by
    rw [hEdef, ← EReal.toReal_toENNReal (limitFormEnergy_nonneg G u), ENNReal.ofReal_toReal hu]
  rw [hEeq, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [hnormsq])

/-- Produced fractional coercivity bounds the completed trace on the actual
finite-energy domain. -/
theorem aux_mfd_prop_uniform_resolvent_trace_energy_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Interp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (Cbase : ℝ) (hCbase : 0 < Cbase)
    (hfrac : ∀ u : DomainL2 (centeredCube z r hr),
      (limitFormEnergy G u).toENNReal ≠ ∞ →
      ∃ v : CubeFractionalL2 (k := 1) hd z r hr threeQuarterOrder,
        v.val 0 = u ∧ cubeFractionalL2Norm hd z r hr threeQuarterOrder v ^ 2 ≤
          Cbase * (limitFormEnergy G u).toReal)
    (mu : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder → Lp ℝ 2 mu)
    (hT : CubeTraceCharacterization hd z hr mu K C T) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (lift : (u : DomainL2 (centeredCube z r hr)) →
      (limitFormEnergy G u).toENNReal ≠ ∞ → CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    (hlift : ∀ u hu, (lift u hu).val 0 = u)
    (J : DomainL2 (centeredCube z r hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ u hu, J u =ᵐ[mu] (T (lift u hu) : SpatialCoordinates d → ℝ)) :
    ∃ Ktr : ℝ, 0 ≤ Ktr ∧ ∀ (u : DomainL2 (centeredCube z r hr))
      (_hu : (limitFormEnergy G u).toENNReal ≠ ∞),
      (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤ ENNReal.ofReal Ktr * (limitFormEnergy G u).toENNReal := by
  obtain ⟨Ccoer, hCcoer, hcoer⟩ := SubdiffusiveProcess.Analysis.limitEnergy_coercive (centeredCube z r hr) G
  obtain ⟨Cint, hCint, hinterp⟩ := Interp.interpolation_half z r hr threeQuarterOrder rfl
  refine ⟨C * (K + (mu (closure (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) *
    (Cint ^ 2 * (Ccoer / volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ^
      (1 / 3 : ℝ) * Cbase ^ (2 / 3 : ℝ)), by positivity, ?_⟩
  intro u hu
  exact aux_mfd_prop_uniform_resolvent_trace_bound_per_u hd z r hr G Ccoer Cbase Cint
    hCcoer hCbase hCint u hu (hcoer u) (hfrac u hu) hinterp lift (hlift u hu)
    mu K C T hT hK hC J (hJ u hu)

end Paper
