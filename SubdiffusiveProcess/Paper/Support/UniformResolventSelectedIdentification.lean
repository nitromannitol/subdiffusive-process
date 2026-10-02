import SubdiffusiveProcess.Paper.Support.UniformResolventIdentification
import SubdiffusiveProcess.Paper.Support.UniformResolventMosco

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

theorem aux_mfd_prop_uniform_resolvent_ident_selected_sample
    {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (z : SpatialCoordinates d) (rQ : ℝ) (hr : 0 < rQ)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (theta : ℕ → ℕ)
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)), Metric.ball x 1 ⊆ Region)
    (muFull : Measure (SpatialCoordinates d))
    (hmu : MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega (theta N)) muFull ∧
      muFull (frontier ((centeredCube z rQ hr) : Set (SpatialCoordinates d))) = 0 ∧ muFull (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))) < ∞)
    (Kmu : ℝ) (hKmu : 0 ≤ Kmu)
    (hgrowth : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull (Metric.ball x r) ≤ ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega (theta N) (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))
    (Elim : DomainL2 (centeredCube z rQ hr) → ℝ≥0∞)
    (hmosco : Lane3.MoscoLiminf (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube z rQ hr) //
          (v : SobolevData (centeredCube z rQ hr)).1 = u},
          ENNReal.ofReal (sobolevCoefficientForm
            (Lane4.cutoffPositiveCoefficient M H omega (theta N) z hr)
            (v.val : SobolevData (centeredCube z rQ hr)) (v.val : SobolevData (centeredCube z rQ hr)))) Elim ∧
      Lane3.MoscoRecovery (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube z rQ hr) //
          (v : SobolevData (centeredCube z rQ hr)).1 = u},
          ENNReal.ofReal (sobolevCoefficientForm
            (Lane4.cutoffPositiveCoefficient M H omega (theta N) z hr)
            (v.val : SobolevData (centeredCube z rQ hr)) (v.val : SobolevData (centeredCube z rQ hr)))) Elim)
    (T : CubeFractionalL2 (k := 1) hd z
        rQ hr halfFractionalOrder →
      Lp ℝ 2 (muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))))
    (Ktrace Ctrace : ℝ)
    (hT : 0 ≤ Ktrace ∧ 0 ≤ Ctrace ∧
      CubeTraceCharacterization hd z hr (muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))) Ktrace Ctrace T)
    (i : (u : DomainL2 (centeredCube z rQ hr)) → Elim u ≠ ∞ →
      CubeFractionalL2 (k := 1) hd z
        rQ hr halfFractionalOrder)
    (hival : ∀ (u : DomainL2 (centeredCube z rQ hr)) (hu : Elim u ≠ ∞), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube z rQ hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube z rQ hr)) (hu : Elim u ≠ ∞),
      (J u) =ᵐ[muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))] (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube z rQ hr))
    (hmin : Elim ustar ≠ ∞ ∧
      (∀ w : DomainL2 (centeredCube z rQ hr), Elim w ≠ ∞ →
        (Elim ustar).toReal + lam * (∫ x, (J ustar x) ^ 2 ∂(muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))))) -
            2 * (∫ x, f x * J ustar x ∂(muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))))) ≤
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))))) -
            2 * (∫ x, f x * J w x ∂(muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))))) ∧
      (∀ w : DomainL2 (centeredCube z rQ hr), Elim w ≠ ∞ →
        (∀ v : DomainL2 (centeredCube z rQ hr), Elim v ≠ ∞ →
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))))) -
              2 * (∫ x, f x * J w x ∂(muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))))) ≤
            (Elim v).toReal + lam * (∫ x, (J v x) ^ 2 ∂(muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))))) -
              2 * (∫ x, f x * J v x ∂(muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))))) →
        w = ustar))
    (u : ℕ → killedSobolevGraph (centeredCube z rQ hr)) (R : ℕ → SpatialCoordinates d → ℝ)
    (hfinite : ∀ N : ℕ,
      (R N =ᵐ[volume.restrict ((centeredCube z rQ hr) : Set (SpatialCoordinates d))] ((u N : SobolevData (centeredCube z rQ hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube z rQ hr),
        sobolevCoefficientForm
            (Lane4.cutoffPositiveCoefficient M H omega (theta N) z hr)
            (u N : SobolevData (centeredCube z rQ hr)) (w : SobolevData (centeredCube z rQ hr)) =
          ∫ x, (f x - lam * R N x) * (w : SobolevData (centeredCube z rQ hr)).1 x
            ∂((cutoffSpeedMeasure M H omega (theta N)).restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
          (Lane4.cutoffPositiveCoefficient M H omega (theta N) z hr)
          (u N : SobolevData (centeredCube z rQ hr)) (u N : SobolevData (centeredCube z rQ hr)) ≤
        ‖f‖ ^ 2 * ((cutoffSpeedMeasure M H omega (theta N)).restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))) ((centeredCube z rQ hr) : Set (SpatialCoordinates d))).toReal / lam)
    (Kc : ℕ → ℝ)
    (hcoer3 : ∀ N (v : killedSobolevGraph (centeredCube z rQ hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd z
          rQ hr Lane4.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube z rQ hr)).1 ∧
        (cubeFractionalL2Norm hd z
          rQ hr Lane4.threeQuarterOrder v3) ^ 2 ≤
          Kc N * sobolevCoefficientForm
            (Lane4.cutoffPositiveCoefficient M H omega (theta N) z hr)
            (v : SobolevData (centeredCube z rQ hr)) (v : SobolevData (centeredCube z rQ hr)))
    (SInterp : CubeFractionalInterpolationInput d hd)
    (g : C(SpatialCoordinates d, ℝ)) (Mb : ℝ) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hbd : ∀ k, Kc (σ k) ≤ Mb)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∀ x ∈ closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)), |R (σ k) x - g x| < eps) :
    (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube z rQ hr) : Set (SpatialCoordinates d))] (ustar : SpatialCoordinates d → ℝ) := by
  have hKc : IsCompact (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded z hr).isCompact_closure
  have hlt1 : epsilon < 1 := by
    refine hepsilon'.trans ?_
    rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have ht : (d : ℝ) - 1 < (d : ℝ) - epsilon := by linarith
  have hReg : ∀ x ∈ closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)), x ∈ Region := fun x hx =>
    hNeighborhood x hx (Metric.mem_ball_self one_pos)
  have hcth_cut : ∀ N, cutoffSpeedMeasure M H omega (theta N)
      (Metric.cthickening (1 / 2) (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))) < ⊤ := fun N =>
    aux_prop_uniform_resolvent_ident_cthickening_finite _ hr Region hNeighborhood _
      (fun x hx => ((hgrowth x hx 1 one_pos le_rfl).2 N).trans_lt ENNReal.ofReal_lt_top)
  have hcth_full : muFull (Metric.cthickening (1 / 2) (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))) < ⊤ :=
    aux_prop_uniform_resolvent_ident_cthickening_finite _ hr Region hNeighborhood _
      (fun x hx => ((hgrowth x hx 1 one_pos le_rfl).1).trans_lt ENNReal.ofReal_lt_top)
  have hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun N => ∫ x, h x ∂((cutoffSpeedMeasure M H omega (theta N)).restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))))
        atTop (𝓝 (∫ x, h x ∂(muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))))) := fun h hh =>
    aux_prop_uniform_resolvent_ident_restrict_tendsto (fun N => cutoffSpeedMeasure M H omega (theta N))
      muFull ((centeredCube z rQ hr) : Set (SpatialCoordinates d)) (centeredCube _ _ hr).isOpen hKc
      (aux_prop_uniform_resolvent_ident_cube_nonempty _ hr)
      (aux_prop_uniform_resolvent_ident_cube_compl_nonempty hd _ hr) (1 / 2) (by norm_num)
      hcth_cut hcth_full hmu.1 hmu.2.1 h hh
  haveI : IsFiniteMeasure (muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hmu.2.2⟩
  have hsupp : ∀ ν : Measure (SpatialCoordinates d), (ν.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))) (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))ᶜ = 0 := by
    intro ν
    rw [Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet, compl_inter_self,
      measure_empty]
  have hνfin : ∀ N, (cutoffSpeedMeasure M H omega (theta N)).restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))) univ < ⊤ := by
    intro N
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (Metric.self_subset_cthickening _)).trans_lt (hcth_cut N)
  obtain ⟨Mbar, hMbar⟩ := aux_prop_uniform_resolvent_ident_mass_bound
    (fun N => (cutoffSpeedMeasure M H omega (theta N)).restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))))
    (muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))) hW (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))) hνfin
  have hνgrowth : ∀ N, ∀ x ∈ closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
      (cutoffSpeedMeasure M H omega (theta N)).restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))) (Metric.ball x rr) ≤
        ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) := fun N x hx rr hrr hrr1 =>
    (Measure.restrict_apply_le _ _).trans ((hgrowth x (hReg x hx) rr hrr hrr1).2 N)
  have hg2 : MemLp (g : SpatialCoordinates d → ℝ) 2 (volume.restrict ((centeredCube z rQ hr) : Set (SpatialCoordinates d))) := by
    refine aux_prop_uniform_resolvent_ident_memLp_of_continuous _ (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))) hKc ?_ g
      g.continuous
    rw [Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
    exact measure_mono_null (fun x hx => hx.1 (subset_closure hx.2)) measure_empty
  have hconv : Tendsto (fun k => (u (σ k) : SobolevData (centeredCube z rQ hr)).1) atTop (𝓝 (hg2.toLp g)) :=
    aux_prop_uniform_resolvent_ident_L2_of_uniform _ hr (fun k => (u (σ k) : SobolevData (centeredCube z rQ hr)).1)
      (fun k => R (σ k)) g hg2 (fun k => (hfinite (σ k)).1) (fun ε hε => by
        obtain ⟨k0, hk0⟩ := hunif ε hε
        exact ⟨k0, fun k hk x hx => hk0 k hk x (subset_closure hx)⟩)
  have heq := aux_mfd_prop_uniform_resolvent_ident_deterministic hd z rQ hr SInterp
    ((d : ℝ) - epsilon) ht
    (fun N => Lane4.cutoffPositiveCoefficient M H omega (theta N) z hr)
    _ (fun N u => rfl) Elim hmosco.1 hmosco.2
    (fun N => (cutoffSpeedMeasure M H omega (theta N)).restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d))))
    (muFull.restrict (closure ((centeredCube z rQ hr) : Set (SpatialCoordinates d)))) (hsupp muFull) Kmu Mbar hKmu hνfin
    (fun N => hsupp _) hMbar hνgrowth
    (fun N => aux_prop_uniform_resolvent_ident_density_le M H omega (theta N) _ hr) hW
    T Ktrace Ctrace hT.1 hT.2.1 hT.2.2 i hival J hJ lam hlam f ustar hmin u R
    (fun N => (hfinite N).1) (fun N => (hfinite N).2.1) (fun N => (hfinite N).2.2) Kc hcoer3
    σ hσ Mb hbd (hg2.toLp g) hconv
  rw [← heq]
  exact (MemLp.coeFn_toLp hg2).symm


end Paper
