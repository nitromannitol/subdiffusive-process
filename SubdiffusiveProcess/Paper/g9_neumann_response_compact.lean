module

public import SubdiffusiveProcess.Paper.g9_neumann_response_wrapper
public import SubdiffusiveProcess.Paper.g9_neumann_band_uniform
public import SubdiffusiveProcess.Paper.rem_bank_neumann_coercive_response_bound_uniform
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal ContDiff

noncomputable section
namespace Paper

/-- Per-model body of `aux_g9_neumann_response_compact_general`: given an abstract Neumann
response space `S`/load `L0`/`Response` wrapper `R` (related only via `heval`, `R`'s definitional
content never inspected further), a model-uniform band bound `hband1` and order-6 moment bound
`hymom6` for the affine inverse-Neumann response at a FIXED model `M`, produces `L²`-relative
compactness of that response family. Split out from the main assembly theorem purely to keep each
declaration's elaboration under the heartbeat budget (the combined proof measured 300-400k
heartbeats; this piece plus the setup piece each individually fit under 200k). -/
theorem aux_g9_neumann_response_compact_body
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]
    (S : ResponseSpace (unitNeumannCube d)) (L0 : S.space →L[ℝ] ℝ)
    (R : SubdiffusiveProcess.Lane3.Response (unitNeumannCube d))
    (heval : ∀ g, R.eval g = inverseResponse S (expPotentialCoefficient g) L0)
    (C aD Cmom6 : ℝ) (hC : 0 < C) (haD : 0 < aD) (hCmom6 : 0 ≤ Cmom6)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (hband1 : ∀ h N : ℕ,
      eLpNorm (fun om => inverseResponse S
          (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0 -
        (((chaosSampleLaw M).toMeasure)[fun om => inverseResponse S
            (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0 |
          bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) om)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (C * Real.sqrt M.delta * (3 : ℝ) ^ (-(aD * (h : ℝ)))))
    (hymom6 : ∀ N, MemLp (fun om => inverseResponse S
          (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0)
        (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => inverseResponse S
          (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0)
        (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cmom6) :
    ∃ hmem : ∀ N, MemLp (fun omega : BilateralField d =>
        inverseResponse S
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0)
      (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range (fun N => (hmem N).toLp (fun omega : BilateralField d =>
        inverseResponse S
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0)))) := by
  classical
  have hRTrue_eq : ∀ N : ℕ,
      aux_g9_neumann_response_wrapper_generic_RTrue
        (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos R M H N =
      (fun omega : BilateralField d => inverseResponse S
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0) := by
    intro N
    funext omega
    have hev := heval (aux_lem_local_normalizations_lnorm_proxy_pot (H omega) M N omega
      (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
    convert! hev using 1
    congr 1
    simpa using! (aux_lem_local_normalizations_lnorm_proxy_pot_eq_coefficient
      M H N omega (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
  have hRDmoment6 : ∀ N, MemLp
      (aux_g9_neumann_response_wrapper_generic_RTrue (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
        R M H N) (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure := by
    intro N
    rw [hRTrue_eq N]
    exact (hymom6 N).1
  have hRDband : ∀ (h N : ℕ),
      eLpNorm (fun omega =>
          aux_g9_neumann_response_wrapper_generic_RTrue (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
            R M H N omega -
          (((chaosSampleLaw M).toMeasure)[
            aux_g9_neumann_response_wrapper_generic_RTrue (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
              R M H N |
            bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (C * Real.sqrt M.delta * (3 : ℝ) ^ (-(aD * (h : ℝ)))) := by
    intro h N
    rw [hRTrue_eq N]
    exact hband1 h N
  have hRfmomAll : ∀ N, MemLp
      (aux_g9_neumann_response_wrapper_generic_Rf (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos R M N)
      (ENNReal.ofReal 6) (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ∧
      eLpNorm
        (aux_g9_neumann_response_wrapper_generic_Rf (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos R M N)
        (ENNReal.ofReal 6) (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ≤
      ENNReal.ofReal Cmom6 := fun N =>
    aux_g9_neumann_response_wrapper_generic_hmom (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos R M H hH
      (ENNReal.ofReal 6) N Cmom6 hCmom6 (hRDmoment6 N) (by rw [hRTrue_eq N]; exact (hymom6 N).2)
  have hpq : (ENNReal.ofReal (2 : ℝ)) < ENNReal.ofReal (6 : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 6)).mpr (by norm_num)
  obtain ⟨hcompactRf, -, -, -, -⟩ :=
    Paper.prop_response_compact d (aux_lem_local_normalizations_lnorm_regroup_Y d)
      (aux_lem_local_normalizations_lnorm_regroup_laws M) Unit Empty
      (fun _ N => aux_g9_neumann_response_wrapper_generic_Rf (fun _ : Fin d => (1 / 2 : ℝ)) 1
        one_pos R M N)
      (fun e _ _ => e.elim)
      (ENNReal.ofReal 2) (ENNReal.ofReal 6) hpq ENNReal.ofReal_ne_top
      aD (Real.sqrt M.delta) haD (Real.sqrt_pos.mpr M.shellPrefix.delta_pos)
      (fun _ => C) (fun _ => hC.le)
      (fun _ => ENNReal.ofReal Cmom6) (fun _ => ENNReal.ofReal_ne_top)
      (fun _ N => by exact (hRfmomAll N).1)
      (fun _ N => by exact (hRfmomAll N).2)
      (fun _ Hband N _ => by
        have hb := aux_g9_neumann_response_wrapper_generic_hband
          (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos R M H hH (Real.sqrt M.delta) C aD Cmom6
          hRDmoment6 hRDband Hband N
        simpa only [neg_mul] using hb)
      (fun _ Hband => by
        exact aux_g9_neumann_response_wrapper_generic_hsplit (fun _ : Fin d => (1 / 2 : ℝ)) 1
          one_pos R M Hband)
      (fun e => e.elim) (fun e => e.elim)
      (fun e _ _ => e.elim)
  have hRDmem2 : ∀ N, MemLp
      (aux_g9_neumann_response_wrapper_generic_RTrue (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
        R M H N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure :=
    fun N => (hRDmoment6 N).mono_exponent hpq.le
  have hRfmem2 : ∀ N, MemLp
      (aux_g9_neumann_response_wrapper_generic_Rf (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos R M N)
      (ENNReal.ofReal 2) (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) :=
    fun N => ((hRfmomAll N).1).mono_exponent hpq.le
  have hcompact2 : IsCompact (closure (Set.range (fun N =>
      (hRfmem2 N).toLp
        (aux_g9_neumann_response_wrapper_generic_Rf (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
          R M N)))) := by
    have hEq : (fun N => (hRfmem2 N).toLp
          (aux_g9_neumann_response_wrapper_generic_Rf (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
            R M N)) =
        (fun N => (((hRfmomAll N).1).mono_exponent hpq.le).toLp
          (aux_g9_neumann_response_wrapper_generic_Rf (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
            R M N)) := rfl
    rw [hEq]
    exact hcompactRf ()
  have hcompactRD := aux_g9_neumann_response_wrapper_generic_compact_transport
    (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos R M H hH (p := ENNReal.ofReal 2) hRDmem2 hRfmem2
    hcompact2
  refine ⟨fun N => by rw [← hRTrue_eq N]; exact hRDmem2 N, ?_⟩
  have hset : (fun N => (hRDmem2 N).toLp
      (aux_g9_neumann_response_wrapper_generic_RTrue (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
        R M H N)) =
      (fun N => ((by rw [← hRTrue_eq N]; exact hRDmem2 N :
          MemLp (fun omega : BilateralField d => inverseResponse S
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0)
            (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure)).toLp
        (fun omega : BilateralField d => inverseResponse S
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0)) := by
    funext N
    apply Lp.ext
    filter_upwards [(hRDmem2 N).coeFn_toLp,
      (show MemLp (fun omega : BilateralField d => inverseResponse S
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure by
        rw [← hRTrue_eq N]; exact hRDmem2 N).coeFn_toLp] with omega h1 h2
    rw [h1, h2, hRTrue_eq N]
  rw [← hset]
  exact hcompactRD



theorem aux_g9_neumann_response_compact_general
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]
    (E : Paper.in_J d) (P : Paper.in_poincare d hd E) (X : Paper.in_extension d hd E)
    (W : Lane4.SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (Sfi : Lane4.SobolevFoundationalInput d hd)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (t : ℝ) (ht0 : (d : ℝ) - 1 < t) (ht1 : t < (d : ℝ))
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ v : ℝ, 0 ≤ rho v)
    (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) (hrhoi : (∫ v, rho v) = 1)
    (pvec : Fin d → ℝ) (hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (fL2 : ℝ → DomainL2 (unitNeumannCube d))
    (hfL2 : ∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
      ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
        faceBump rho pvec eps)) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M),
        Rm.C ≤ Cresp →
        ∀ (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ N, MemLp (fun omega : BilateralField d =>
            inverseResponse (meanZeroResponseSpace hPn)
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N =>
          (hmem N).toLp (fun omega : BilateralField d =>
            inverseResponse (meanZeroResponseSpace hPn)
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))))) := by
  classical
  set S : ResponseSpace (unitNeumannCube d) := meanZeroResponseSpace hPn with hSdef
  set L0 : S.space →L[ℝ] ℝ :=
    (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))
    with hL0def
  set R : SubdiffusiveProcess.Lane3.Response (unitNeumannCube d) :=
    g9_neumann_response_wrapper S L0 with hRdef
  obtain ⟨delta0N, C, hdelta0N, hC, hmainN⟩ :=
    g9_neumann_band_uniform d hd E P X W D Sfi Cresp hCresp t ht0 ht1 rho hrho hrho0 hrhos hrhoi
      pvec hpvec hPn fL2 hfL2
  obtain ⟨delta0c, hdelta0c, Cmom6, hCmom6, hmc⟩ :=
    rem_bank_neumann_coercive_response_bound_uniform d hd E P Sfi (3 / 2 : ℝ) (by norm_num)
      rho hrho hrho0 hrhos hrhoi pvec hpvec hPn
  obtain ⟨ha0, ha1⟩ := aux_prop_16_exponent_facts d hd t ht0 ht1
  set a : ℝ := t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) with ha_def
  set aD : ℝ := a / 32 with haD_def
  have haD : 0 < aD := by rw [haD_def]; linarith
  refine ⟨min delta0N delta0c, lt_min hdelta0N hdelta0c, ?_⟩
  intro M Rm hRC Sreg It H hH hM
  have hMband : M.delta ≤ delta0N := hM.trans ((min_le_right 1 _).trans (min_le_left _ _))
  have hMcoerc : M.delta ≤ min 1 delta0c :=
    hM.trans (min_le_min_left 1 (min_le_right delta0N delta0c))
  obtain ⟨hband1, -⟩ := hmainN M hMband Rm hRC Sreg It H hH
  obtain ⟨Kcoerc, -, hKmem, hKnorm⟩ := hmc M Rm H hH hMcoerc
  have h4p6 : (4 : ℝ) * (3 / 2 : ℝ) = 6 := by norm_num
  have hymom6 : ∀ N, MemLp (fun om => inverseResponse S
        (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0)
      (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ∧
    eLpNorm (fun om => inverseResponse S
        (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) L0)
      (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cmom6 := by
    intro N
    have h1 := (hKmem N).2
    have h2 := (hKnorm N).2
    rw [h4p6] at h1 h2
    exact ⟨h1, h2⟩
  exact aux_g9_neumann_response_compact_body d hd S L0 R
    (fun g => aux_g9_neumann_response_wrapper_eval S L0 g) C aD Cmom6 hC haD hCmom6 M H hH
    hband1 hymom6



theorem g9_neumann_response_compact
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]
    (E : Paper.in_J d) (P : Paper.in_poincare d hd E) (X : Paper.in_extension d hd E)
    (W : Lane4.SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (Sfi : Lane4.SobolevFoundationalInput d hd)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (t : ℝ) (ht0 : (d : ℝ) - 1 < t) (ht1 : t < (d : ℝ))
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ v : ℝ, 0 ≤ rho v)
    (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) (hrhoi : (∫ v, rho v) = 1)
    (pvec : Fin d → ℝ) (hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (fL2 : ℝ → DomainL2 (unitNeumannCube d))
    (hfL2 : ∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
      ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
        faceBump rho pvec eps)) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M),
        Rm.C ≤ Cresp →
        ∀ (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ N, MemLp (fun omega : BilateralField d =>
            inverseResponse (meanZeroResponseSpace hPn)
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N =>
          (hmem N).toLp (fun omega : BilateralField d =>
            inverseResponse (meanZeroResponseSpace hPn)
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))))) := by
  exact aux_g9_neumann_response_compact_general d hd E P X W D Sfi Cresp hCresp t ht0 ht1 rho hrho hrho0
    hrhos hrhoi pvec hpvec hPn fL2 hfL2

end Paper
