import SubdiffusiveProcess.Paper.Support.UniformResolventTraceBound
import SubdiffusiveProcess.Paper.Support.UniformResolventMinimizer
import SubdiffusiveProcess.Paper.lem_19_trace_completion

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

/-- Construct the completed trace, represented finite-energy embedding, and
all actual resolvent minimizers on one sample and one arbitrary centred cube. -/
theorem aux_mfd_prop_uniform_resolvent_form_data
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Interp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hsym : ∀ x y, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (G x))
    (Cbase : ℝ) (hCbase : 0 < Cbase)
    (hfrac : ∀ u : DomainL2 (centeredCube z r hr),
      (limitFormEnergy G u).toENNReal ≠ ∞ →
      ∃ v : CubeFractionalL2 (k := 1) hd z r hr threeQuarterOrder,
        v.val 0 = u ∧ cubeFractionalL2Norm hd z r hr threeQuarterOrder v ^ 2 ≤
          Cbase * (limitFormEnergy G u).toReal)
    (lift : (u : DomainL2 (centeredCube z r hr)) →
      (limitFormEnergy G u).toENNReal ≠ ∞ → CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    (hlift : ∀ u hu, (lift u hu).val 0 = u)
    (muFull : Measure (SpatialCoordinates d))
    (hfin : muFull (closure (centeredCube z r hr : Set (SpatialCoordinates d))) < ∞)
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (hgrowth : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rho, 0 < rho → rho ≤ 1 → muFull (Metric.ball x rho) ≤ ENNReal.ofReal (K * rho ^ t)) :
    let mu := muFull.restrict (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
    let Elim := fun u => (limitFormEnergy G u).toENNReal
    ∃ (T : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder → Lp ℝ 2 mu)
      (C Ktr : ℝ) (J : DomainL2 (centeredCube z r hr) → SpatialCoordinates d → ℝ)
      (ustar : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        DomainL2 (centeredCube z r hr)),
      0 ≤ C ∧ 0 ≤ Ktr ∧ CubeTraceCharacterization hd z hr mu K C T ∧
      (∀ u hu, J u =ᵐ[mu] (T (lift u hu) : SpatialCoordinates d → ℝ)) ∧
      (∀ (u : DomainL2 (centeredCube z r hr)) (_hu : Elim u ≠ ∞),
        (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤ ENNReal.ofReal Ktr * Elim u) ∧
      ∀ lam, 0 < lam → ∀ f,
        Elim (ustar lam f) ≠ ∞ ∧
        let F := fun u => (Elim u).toReal + lam * (∫ x, J u x ^ 2 ∂mu) - 2 * ∫ x, f x * J u x ∂mu
        (∀ u, Elim u ≠ ∞ → Integrable (fun x => J u x ^ 2) mu ∧
          Integrable (fun x => f x * J u x) mu ∧ F (ustar lam f) ≤ F u) ∧
        ∀ u, Elim u ≠ ∞ → (∀ v, Elim v ≠ ∞ → F u ≤ F v) → u = ustar lam f := by
  classical
  intro mu Elim
  have hmufin : mu univ < ∞ := by rw [Measure.restrict_apply_univ]; exact hfin
  haveI : IsFiniteMeasure mu := ⟨hmufin⟩
  have hsupp : mu (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 := by
    rw [Measure.restrict_apply isClosed_closure.measurableSet.compl, compl_inter_self, measure_empty]
  obtain ⟨C, hC, htrace⟩ := lem_19_trace_completion d hd z r hr t ht
  obtain ⟨T, hT', -⟩ := htrace mu K hmufin hsupp hK
    (fun x hx rho hrho hrho1 => (Measure.restrict_apply_le _ _).trans (hgrowth x hx rho hrho hrho1))
  have hT : CubeTraceCharacterization hd z hr mu K C T := ⟨hT'.1, hT'.2.1, hT'.2.2.1⟩
  let J := fun u => if hu : Elim u ≠ ∞ then (T (lift u hu) : SpatialCoordinates d → ℝ) else fun _ => 0
  have hJ : ∀ u hu, J u =ᵐ[mu] (T (lift u hu) : SpatialCoordinates d → ℝ) := by
    intro u hu
    exact EventuallyEq.of_eq (dif_pos hu)
  obtain ⟨Ktr, hKtr, hJtr⟩ := aux_mfd_prop_uniform_resolvent_trace_energy_bound
    hd Interp z r hr G Cbase hCbase hfrac mu K C T hT hK hC lift hlift J hJ
  obtain ⟨hE0, -⟩ := aux_car_variational_energy_algebra z r hr G hsym hpos
  obtain ⟨hclosed, hpara, hscale⟩ := aux_car_variational_energy_properties z r hr G hsym hpos
  have hpara' : ∀ w1 w2 : DomainL2 (centeredCube z r hr), Elim w1 ≠ ∞ → Elim w2 ≠ ∞ →
      (Elim (w1 + w2)).toReal + (Elim (w1 - w2)).toReal =
        2 * (Elim w1).toReal + 2 * (Elim w2).toReal := by
    intro w1 w2 h1 h2
    simpa only [Elim, EReal.toReal_toENNReal (limitFormEnergy_nonneg G (w1 + w2)),
      EReal.toReal_toENNReal (limitFormEnergy_nonneg G (w1 - w2)),
      EReal.toReal_toENNReal (limitFormEnergy_nonneg G w1),
      EReal.toReal_toENNReal (limitFormEnergy_nonneg G w2)] using hpara w1 w2 h1 h2
  have hmin : ∀ (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ), ∃ u : DomainL2 (centeredCube z r hr), 0 < lam →
      Elim u ≠ ∞ ∧
      (∀ w, Elim w ≠ ∞ → (Elim u).toReal + lam * (∫ x, J u x ^ 2 ∂mu) - 2 * ∫ x, f x * J u x ∂mu ≤
        (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) - 2 * ∫ x, f x * J w x ∂mu) ∧
      (∀ w, Elim w ≠ ∞ → (∀ v, Elim v ≠ ∞ →
        (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) - 2 * ∫ x, f x * J w x ∂mu ≤
        (Elim v).toReal + lam * (∫ x, J v x ^ 2 ∂mu) - 2 * ∫ x, f x * J v x ∂mu) → w = u) := by
    intro lam f
    by_cases hl : 0 < lam
    · obtain ⟨u, hu⟩ := aux_mfd_prop_uniform_resolvent_minimizer hd z r hr G Elim (fun _ => rfl)
        mu muFull rfl hmufin K C T hT lift hlift J hJ
        (SubdiffusiveProcess.Analysis.limitEnergy_coercive (centeredCube z r hr) G) hE0 hclosed hpara' hscale
        Ktr hKtr hJtr lam hl f
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h => (hl h).elim⟩
  choose ustar hustar using hmin
  refine ⟨T, C, Ktr, J, ustar, hC, hKtr, hT, hJ, hJtr, ?_⟩
  intro lam hlam f
  obtain ⟨hufin, hminle, huniq⟩ := hustar lam f hlam
  refine ⟨hufin, fun u hu => ?_, huniq⟩
  have hJmem : MemLp (J u) 2 mu := (Lp.memLp (T (lift u hu))).ae_eq (hJ u hu).symm
  have hfmem : MemLp (fun x => f x) 2 mu := MemLp.of_bound f.continuous.aestronglyMeasurable
    ‖f‖ (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  exact ⟨hJmem.integrable_sq, aux_prop_uniform_resolvent_ident_integrable_mul hfmem hJmem,
    hminle u hu⟩

end Paper
