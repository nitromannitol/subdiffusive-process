module

public import SubdiffusiveProcess.Paper.Support.UniformResolventTraceLinearity

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Section9
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Paper
open Classical in
/-- The proved speed-resolvent minimization applies to every centred cube.
All data are internal supplied conclusions in the principal assembly. -/
theorem aux_mfd_prop_uniform_resolvent_minimizer {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr))
    (Elim : DomainL2 (centeredCube z r hr) → ℝ≥0∞)
    (hElim : ∀ u : DomainL2 (centeredCube z r hr),
      Elim u = (limitFormEnergy G u).toENNReal)
    (mu muFull : Measure (SpatialCoordinates d))
    (hmu : mu = muFull.restrict
      (closure (centeredCube z r hr :
        Set (SpatialCoordinates d))))
    (hmufin : mu univ < ∞) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z r hr
      halfFractionalOrder → Lp ℝ 2 mu)
    (hT : CubeTraceCharacterization hd z hr mu K C T)
    (i : (u : DomainL2 (centeredCube z r hr)) →
      Elim u ≠ ∞ →
      CubeFractionalL2 (k := 1) hd z r hr
        halfFractionalOrder)
    (hi : ∀ (u : DomainL2 (centeredCube z r hr))
      (hu : Elim u ≠ ∞), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube z r hr) →
      SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube z r hr))
      (hu : Elim u ≠ ∞), (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ))
    (hcoer : ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ w : DomainL2 (centeredCube z r hr),
        ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Ccoer * Elim w)
    (hE0 : Elim 0 = 0)
    (hclosed : ∀ (c : ℝ)
      (w1 w2 : DomainL2 (centeredCube z r hr)),
      Elim w1 ≠ ∞ → Elim w2 ≠ ∞ → Elim (c • w1 + w2) ≠ ∞)
    (hpara : ∀ (w1 w2 : DomainL2 (centeredCube z r hr)),
      Elim w1 ≠ ∞ → Elim w2 ≠ ∞ →
      (Elim (w1 + w2)).toReal + (Elim (w1 - w2)).toReal =
        2 * (Elim w1).toReal + 2 * (Elim w2).toReal)
    (hscale : ∀ (c : ℝ)
      (u : DomainL2 (centeredCube z r hr)),
      Elim u ≠ ∞ → Elim (c • u) = ENNReal.ofReal (c ^ 2) * Elim u)
    (Ktr : ℝ) (hKtr : 0 ≤ Ktr)
    (hJtr : ∀ (u : DomainL2 (centeredCube z r hr))
      (_hu : Elim u ≠ ∞),
      (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤ ENNReal.ofReal Ktr * Elim u)
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∃ ustar : DomainL2 (centeredCube z r hr),
      Elim ustar ≠ ∞ ∧
      (∀ w : DomainL2 (centeredCube z r hr),
        Elim w ≠ ∞ →
        (Elim ustar).toReal + lam * (∫ x, J ustar x ^ 2 ∂mu) -
            2 * ∫ x, f x * J ustar x ∂mu ≤
          (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
            2 * ∫ x, f x * J w x ∂mu) ∧
      (∀ w : DomainL2 (centeredCube z r hr),
        Elim w ≠ ∞ →
        (∀ v : DomainL2 (centeredCube z r hr),
          Elim v ≠ ∞ →
          (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
              2 * ∫ x, f x * J w x ∂mu ≤
            (Elim v).toReal + lam * (∫ x, J v x ^ 2 ∂mu) -
              2 * ∫ x, f x * J v x ∂mu) →
        w = ustar) := by
  haveI : IsFiniteMeasure mu := ⟨hmufin⟩
  have hsupp : mu (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 := by
    rw [hmu, Measure.restrict_apply isClosed_closure.measurableSet.compl,
      Set.compl_inter_self, measure_empty]
  have hfm : MemLp (fun x => f x) 2 mu :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  let A : DomainL2 (centeredCube z r hr) → Lp ℝ 2 mu :=
    fun w => if h : Elim w ≠ ⊤ then T (i w h) else 0
  have hAw : ∀ (w : DomainL2 (centeredCube z r hr))
      (hw : Elim w ≠ ∞), A w = T (i w hw) := fun w hw => dif_pos hw
  have hlsc : LowerSemicontinuous Elim := by
    have hE : Elim = fun u => (limitFormEnergy G u).toENNReal := funext hElim
    rw [hE]
    exact aux_prop_speed_resolvent_elim_lsc G
  have hAlin : ∀ (c : ℝ)
      (w1 w2 : DomainL2 (centeredCube z r hr)),
      Elim w1 ≠ ∞ → Elim w2 ≠ ∞ → A (c • w1 + w2) = c • A w1 + A w2 :=
    fun c w1 w2 h1 h2 =>
      aux_mfd_prop_uniform_resolvent_trace_energy_linear hd z r hr mu hsupp K C T hT Elim hclosed i hi c w1 w2 h1 h2
  have hAbd : ∀ w : DomainL2 (centeredCube z r hr),
      Elim w ≠ ∞ → ‖A w‖ ^ 2 ≤ Ktr * (Elim w).toReal := by
    intro w hw
    rw [hAw w hw]
    exact aux_prop_speed_resolvent_trace_bound (J w) _ (hJ w hw) Ktr hKtr _ hw (hJtr w hw)
  obtain ⟨ustar, hus, hmin, huniq⟩ :=
    aux_prop_speed_resolvent_abstract_min Elim A (hfm.toLp (fun x => f x)) lam hlam hlsc hE0
      hclosed hpara hscale hcoer hAlin Ktr hKtr hAbd
  have key : ∀ (w : DomainL2 (centeredCube z r hr))
      (hw : Elim w ≠ ∞),
      (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) - 2 * ∫ x, f x * J w x ∂mu =
        (Elim w).toReal + lam * ‖A w‖ ^ 2 -
          2 * ⟪hfm.toLp (fun x => f x), A w⟫_ℝ := by
    intro w hw
    have hJA : J w =ᵐ[mu] ⇑(A w) := by
      rw [hAw w hw]
      exact hJ w hw
    rw [aux_prop_speed_resolvent_sq_integral_congr (J w) (A w) hJA,
      aux_prop_speed_resolvent_f_integral_inner f hfm (J w) (A w) hJA]
  refine ⟨ustar, hus, fun w hw => ?_, fun w hw hwmin => ?_⟩
  · rw [key ustar hus, key w hw]
    exact hmin w hw
  · exact huniq w hw (fun v hv => by
      rw [← key w hw, ← key v hv]
      exact hwmin v hv)

end Paper
