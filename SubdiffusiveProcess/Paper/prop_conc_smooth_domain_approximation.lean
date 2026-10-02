import SubdiffusiveProcess.Paper.prop_conc_mesh_bounded_holder
import SubdiffusiveProcess.Paper.prop_conc_mesh_compactness
import SubdiffusiveProcess.Paper.in_represented_mosco
import SubdiffusiveProcess.Sobolev.UniformCubeLimit
import SubdiffusiveProcess.Geometry.TriadicApproximation

/-! Actual continuous domain approximations in each supplied limiting energy.
Harmonic meshes converge uniformly after extraction; the free Mosco lower bound
puts their limit in the exact dual-energy domain. No local Gamma is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
namespace Paper
noncomputable section

/-- Every smooth compactly supported datum has a uniformly close continuous representative in the supplied limit domain. -/
theorem prop_conc_smooth_domain_approximation
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
          ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
        (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
        (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)),
      (∀ n f, GN n f =
        (responseSolution (killedResponseSpace hP)
          (cutoffPositiveCoefficient M H om (N n) z hr)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) → ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
        HasCompactSupport phi → tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ eps : ℝ, 0 < eps →
      ∃ u ∈ limitFormDomain G, ∃ uc : SpatialCoordinates d → ℝ,
        ContinuousOn uc (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        ((u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc) ∧
        ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          |uc x - phi x| ≤ eps := by
  obtain ⟨delta0, Cmesh, hdelta0, _, hs⟩ := prop_conc_mesh_bounded_holder d hd I Pin X W Cp Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hP N
  filter_upwards [hs M Rm Sreg It H hIR hdelta z r hr N] with om hom
  intro GN G hGN hG phi hphi hcompact hsupp eps heps
  obtain ⟨seq, hseq, hmeshes⟩ := hom
  let gradBound := sSup ((fun y => ‖fderiv ℝ phi y‖) ''
    closure (centeredCube z r hr : Set (SpatialCoordinates d)))
  obtain ⟨J, hside, herr⟩ := exists_triadic_side_error_lt r (Cmesh * gradBound) eps heps
  obtain ⟨w, Ebound, Hbound, _, hHbound, hw⟩ := hmeshes J hside phi hphi hcompact hsupp
  obtain ⟨tau, htau, g, hlim⟩ := prop_conc_mesh_compactness d hd z r hr J
    (fun n => (w n).toH1Function.toFun) (fun n => (hw n).2.1)
    (3 / 4) (by norm_num) (fun _ => Hbound) (fun _ => hHbound)
    (fun k n => ((hw n).2.2.1 k).1) (fun k n => ((hw n).2.2.1 k).2)
  obtain ⟨v, vc, hvc, hvrep, hvg⟩ := exists_cubeL2_of_continuous_closedCube z hr g
  let uN : ℕ → (killedResponseSpace hP).space := fun n =>
    ⟨sobolevDataOfH1 (w (tau n)).toH1Function, sobolevDataOfH1_mem_killed (w (tau n))⟩
  have hvlim : Tendsto (fun n => (uN n).val.1) atTop (𝓝 v) :=
    cube_tendsto_of_uniformly_on z hr (fun n => (w (tau n)).toH1Function.toFun)
      (fun n => (uN n).val.1) (fun n => sobolevDataOfH1_fst_coeFn (w (tau n)).toH1Function)
      vc v hvrep (by
        have hfun : (fun x : closure (centeredCube z r hr : Set (SpatialCoordinates d)) => vc x.val) =
            (fun x => g x) := funext fun x => hvg x.val x.property
        rw [hfun]
        exact hlim)
  obtain ⟨_, hlower, _⟩ := aux_in_represented_mosco_free d hd M H om z r hr
    (killedResponseSpace hP) G (fun n => N (seq (tau n))) (fun n => GN (seq (tau n)))
    (fun n f => hGN (seq (tau n)) f) (hG.comp (hseq.comp htau).tendsto_atTop)
  have he (n : ℕ) : responseForm (killedResponseSpace hP)
      (cutoffPositiveCoefficient M H om (N (seq (tau n))) z hr) (uN n) (uN n) ≤ Ebound := by
    have hc := (cutoffPositiveCoefficient_representative M H om (N (seq (tau n))) z hr).2.2.2
    change sobolevCoefficientForm _ (sobolevDataOfH1 (w (tau n)).toH1Function)
      (sobolevDataOfH1 (w (tau n)).toH1Function) ≤ Ebound
    rw [← energy_eq_sobolevCoefficientForm _ _ hc]
    exact (hw (tau n)).1
  have hlow := hlower uN v (fun f => tendsto_const_nhds.inner hvlim)
  have hfin : limitFormEnergy G v < ⊤ :=
    (hlow.trans (liminf_le_of_frequently_le'
      (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => EReal.coe_le_coe (he n))))).trans_lt
        (EReal.coe_lt_top Ebound)
  refine ⟨v, hfin, vc, hvc, hvrep, ?_⟩
  intro x hx
  have hn (n : ℕ) : |(w n).toH1Function.toFun x - phi x| ≤
      Cmesh * (r / (3 : ℝ) ^ J) * gradBound :=
    le_on_closure (hw n).2.2.2 (((hw n).2.1.sub hphi.continuous.continuousOn).abs)
      continuousOn_const hx
  have hpt := ((hlim.tendsto_at ⟨x, hx⟩).sub_const (phi x)).abs
  have hle := le_of_tendsto' hpt (fun n => hn (tau n))
  rw [hvg x hx]
  refine hle.trans ?_
  change Cmesh * (r / (3 : ℝ) ^ J) * gradBound ≤ eps
  nlinarith only [herr]

end
end Paper
