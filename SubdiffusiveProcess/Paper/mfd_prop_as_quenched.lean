module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.mfd_convergence
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A3. Native-model statement: one full-measure event for the full sequence and every compact starting set. The limit is produced and identified by in-probability convergence in the conclusion, rather than a free input kernel. -/
theorem mfd_prop_as_quenched
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∃ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N)),
        in_crossing M H PN KN ∧
        ∃ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
          (hK : IsMarkovKernel K),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            Continuous (fun x : SpatialCoordinates d =>
              jointPathProbabilityMeasure K hK omega x)) ∧
          (∀ B : Set (SpatialCoordinates d), IsCompact B →
            ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
              ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
                (chaosSampleLaw M).toMeasure
                  {omega : BilateralField d | ∃ x ∈ B, eps ≤
                    pathLevyProkhorovDist
                      (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                      (jointPathProbabilityMeasure K hK omega x)} ≤
                  ENNReal.ofReal rho) ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < eps) := by
  classical
  obtain ⟨Jc, Pc, Xc, Sf, W, Cp, D, hES, Step, Dbase, Interp, BD, BDQ,
    hcontract, hlife, _EM, δr, Cresp, hδr, _hCresp, hsup⟩ := inputs_simultaneous d hd
  let δ := aux_mfd_convergence_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase
    Interp BD BDQ hcontract
  have hδ : 0 < δ := aux_mfd_convergence_delta0_pos hd Jc Pc Xc Sf W Cp D hES
    Step Dbase Interp BD BDQ hcontract
  refine ⟨min δr δ, lt_min hδr hδ, ?_⟩
  intro M hM
  have hMr : M.delta ≤ δr := hM.trans (min_le_left _ _)
  have hMδ : M.delta ≤ δ := hM.trans (min_le_right _ _)
  obtain ⟨Rm, Sreg, _hRm, ⟨It⟩⟩ := hsup M M.shellPrefix.delta_pos hMr
  have hle := hMδ
  dsimp only [δ, aux_mfd_convergence_delta0] at hle
  have hle1 : M.delta ≤ Classical.choose (finiteDimensional_cutoff (d := d) hd) :=
    hle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle2 : M.delta ≤ Classical.choose (tight_prop (d := d) hd Jc Pc Xc Sf W Cp) :=
    hle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hle6 : M.delta ≤ Classical.choose (aux_mfd_convergence_resolvent hd Jc Pc Xc
      Sf W Cp D hES Step Dbase Interp BD BDQ hcontract) :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  have hFD := (Classical.choose_spec (finiteDimensional_cutoff (d := d) hd)).2
    M H hH hle1
  obtain ⟨PN, KN, hKN, hin, hinput⟩ := hlife M H hH hFD
  obtain ⟨L, hL, hLlocal, _hLstrong⟩ :=
    aux_cutoff_lifetime_package_local M H KN hinput
  have htightNew := (Classical.choose_spec (tight_prop (d := d) hd Jc Pc Xc Sf W Cp)).2
    M Rm Sreg It hle2 H hH PN KN hKN hin L hL hLlocal
  have htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
          ∀ N : ℕ, (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal epsilon := by
    intro B hB epsilon hepsilon
    obtain ⟨Kset, hKset, hmajorant, _⟩ := htightNew B hB epsilon hepsilon
    refine ⟨Kset, hKset, ?_⟩
    intro N
    obtain ⟨G, _, hG, hGint⟩ := hmajorant N
    exact (lintegral_mono fun omega => iSup_le fun x => iSup_le fun hx =>
      hG omega x hx).trans hGint
  have hbounds := tight_fixed_cutoff hd M H hH PN KN hKN hin L hL hLlocal
  have hstart := in_cutoff_start_continuity hd M H hH PN KN hKN hin hbounds
  obtain ⟨Rlim, hRmeas, hRae⟩ := (Classical.choose_spec
    (aux_mfd_convergence_resolvent hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
      BD BDQ hcontract)).2 M Rm Sreg It hle6 H hH PN KN hKN hin hinput
  have hcauchy := aux_mfd_convergence_path_cauchy hd M H hH PN KN hKN hin
    hinput hstart htight Rlim hRmeas (hRae.mono fun _ h => h.2.1)
  obtain ⟨P, hP, K, hK, hcontK, hlim, hconvP⟩ :=
    limit_kernel hd M H hH PN KN hKN hin hcauchy hstart hin.2.2
  have hle4 : M.delta ≤ Classical.choose (prop_chaos_growth (d := d) hd
      (aux_mfd_convergence_eps d) (aux_mfd_convergence_eps_unit d)
      (aux_mfd_convergence_p d) (aux_mfd_convergence_p_spec d)) :=
    hle.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨mu, _hmum, hmuae, _hbound⟩ := (Classical.choose_spec
    (prop_chaos_growth (d := d) hd (aux_mfd_convergence_eps d)
      (aux_mfd_convergence_eps_unit d) (aux_mfd_convergence_p d)
      (aux_mfd_convergence_p_spec d))).2 M H hH hle4
  have hmuC : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (mu omega) ∧
        IsLocallyFiniteMeasure (mu omega) := by
    filter_upwards [hmuae] with omega h
    have heq : (fun N => cutoffSpeedMeasure M H omega N) =
        fun N => weightedChaosCutoff M H N omega :=
      funext fun N => cutoffSpeedMeasure_eq_weightedChaosCutoff M H omega N
    rw [heq]
    exact ⟨h.1, h.2.1⟩
  have hconvT : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      Tendsto (fun N => (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)}) atTop (nhds 0) :=
    fun B hB eps heps => aux_mfd_convergence_tendsto_of_prob _ _ (hconvP B hB eps heps)
  have hPL := aux_prop_limit_properties_of_suppliers hd M H hH PN P hP KN hKN K hK hin hinput hlim hconvT
    (hmuC.mono fun _ h => ⟨mu _, h⟩)
  obtain ⟨hkilled, _hres⟩ := aux_mfd_convergence_killed hd M H hH PN KN hKN hin
    P hP K hK hcontK hlim hconvP Rlim hRae
  have hAS := prop_as_quenched hd M H hH PN KN hKN K hK hin hinput
    (fun n => Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
    (fun n => Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
    (aux_mfd_convergence_hr d) (aux_mfd_convergence_exhaust d) P hP hkilled
    (hPL.mono fun _ h => ⟨h.1, h.2.2.1⟩) hlim hstart
  exact ⟨H, hH, PN, KN, hKN, hin, K, hK, hcontK, hconvP, hAS⟩

end SubdiffusiveProcess.Paper
