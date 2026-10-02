import SubdiffusiveProcess.Paper.Support.UniformResolventInputs

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open scoped ENNReal NNReal
noncomputable section
namespace Paper

theorem aux_mfd_prop_uniform_resolvent_inputs
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo 0 1)
    (q : ℕ) (hq : (1 : ℝ) ≤ q) (hp : (d : ℝ) < q * epsilon) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), 0 < M.delta → M.delta ≤ delta0 →
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
        Nonempty (aux_mfd_prop_uniform_resolvent_Inputs d hd M H KN epsilon q) := by
  classical
  let E := Classical.choice (inputs_J_witness d hd)
  let Pc := Classical.choice (inputs_poincare_witness d hd E)
  let X := Classical.choice (inputs_extension_witness d hd E)
  let W := Classical.choice (inputs_W_witness d)
  let Cp := Classical.choice (inputs_Cp_witness d)
  let Sf := Classical.choice (inputs_Sf_witness d hd)
  let Interp := inputs_Interp_witness d hd
  have ht : (d : ℝ) - 1 < (d : ℝ) - epsilon := by linarith [hepsilon.2]
  have ht' : (d : ℝ) - epsilon < (d : ℝ) := by linarith [hepsilon.1]
  obtain ⟨deltaG, hdeltaG, hinverse⟩ := aux_mfd_prop_uniform_resolvent_inverse d hd
  obtain ⟨deltaMu, hdeltaMu, hmeasure⟩ := aux_mfd_prop_uniform_resolvent_measure d hd epsilon hepsilon q hp
  obtain ⟨deltaC, hdeltaC, hcoercivity⟩ := aux_mfd_prop_uniform_resolvent_coercivity_moments d hd E Pc Sf q hq
  obtain ⟨deltaH, hdeltaH, hholder⟩ := aux_mfd_prop_uniform_resolvent_holder_family d hd E Pc X W Cp Sf
    ((d : ℝ) - epsilon) ht ht' q hq
  obtain ⟨Cresp, deltaR, -, hdeltaR, hresponses⟩ := inputs_responses_witness d hd q hq
  let delta0 := min deltaG (min deltaMu (min deltaC (min deltaH deltaR)))
  have hdelta0 : 0 < delta0 := lt_min hdeltaG (lt_min hdeltaMu (lt_min hdeltaC (lt_min hdeltaH hdeltaR)))
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hMpos hMsmall H hH PN KN hKN hin
  have hMG : M.delta ≤ deltaG := hMsmall.trans (min_le_left _ _)
  have hMM : M.delta ≤ deltaMu := hMsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMC : M.delta ≤ deltaC := hMsmall.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hMH : M.delta ≤ deltaH := hMsmall.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hMR : M.delta ≤ deltaR := hMsmall.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨Rm, -, -⟩ := hresponses M hMR
  obtain ⟨G0, hG0m, hG0conv⟩ := hinverse M hMpos hMG H hH
  obtain ⟨muFull, hmuMeas, hmu, hregions⟩ := hmeasure M H hH hMM
  have hgeometry := fun i => SubdiffusiveProcess.Geometry.exists_enclosing_triadic_region
    (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
  choose Qroot Region hRegion hroot hrootRegion hNeighborhood using hgeometry
  have hgrowth0 := fun i => hregions (Region i) (hRegion i)
  choose Kmu hKmuMeas hKmuMom hgrowth0 using hgrowth0
  have hgrowth := ae_all_iff.mpr hgrowth0
  obtain ⟨Kraw, Cc, hCc, hKrawm, hKrawn, hKrawc, hKrawmom⟩ :=
    hcoercivity M Rm H hH hMC (rationalTriadicCenter d) (rationalTriadicSide d)
      (rationalTriadicSide_pos d) (SubdiffusiveProcess.Geometry.rationalTriadicSide_small_or_large d)
  have hcoRaw := fun i N => (hKrawc i N).mono fun omega h v => (h v).2
  have hfrac0 := aux_mfd_prop_uniform_resolvent_fractional_event d hd Sf M H G0 hG0conv
    Kraw Cc q hq hCc hKrawm hKrawn (fun i N => (hKrawmom i N).1)
    (fun i N => (hKrawmom i N).2) hcoRaw
  have hhalf0 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i u,
      (limitFormEnergy (G0 i omega) u).toENNReal ≠ ∞ →
      ∃ v : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) halfFractionalOrder, v.val 0 = u := by
    filter_upwards [hfrac0] with omega hf i u hu
    obtain ⟨Cbase, -, hfr⟩ := (hf i).2.2
    obtain ⟨v, hv, -⟩ := hfr u hu
    obtain ⟨w, hw⟩ := aux_mfd_prop_uniform_resolvent_half_lift hd (rationalTriadicCenter d i)
      (rationalTriadicSide d i) (rationalTriadicSide_pos d i) v
    exact ⟨w, hw.trans hv⟩
  obtain ⟨G, hGmeas, hGconv, hGae, hhalf⟩ := aux_mfd_prop_uniform_resolvent_masked_inverse
    d hd Sf M H G0 hG0m hG0conv hhalf0
  have hfrac : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
      (∀ x y : DomainL2 (determiningCube d i), inner ℝ (G i omega x) y = inner ℝ x (G i omega y)) ∧
      (∀ x : DomainL2 (determiningCube d i), 0 ≤ inner ℝ x (G i omega x)) ∧
      ∃ Cbase : ℝ, 0 < Cbase ∧ ∀ u : DomainL2 (determiningCube d i),
        (limitFormEnergy (G i omega) u).toENNReal ≠ ∞ →
        ∃ v : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) threeQuarterOrder, v.val 0 = u ∧
          cubeFractionalL2Norm hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
            (rationalTriadicSide_pos d i) threeQuarterOrder v ^ 2 ≤ Cbase * (limitFormEnergy (G i omega) u).toReal := by
    filter_upwards [hfrac0, hGae] with omega hf heq i
    rw [heq i]
    exact hf i
  have hmuLocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
      muFull omega (closure (determiningCube d i : Set (SpatialCoordinates d))) < ∞ ∧
      0 ≤ Kmu i omega ∧ ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
        ∀ rho, 0 < rho → rho ≤ 1 → muFull omega (Metric.ball x rho) ≤
          ENNReal.ofReal (Kmu i omega * rho ^ ((d : ℝ) - epsilon)) := by
    filter_upwards [hmu, hgrowth] with omega hm hgr i
    haveI := hm.2.1
    refine ⟨(centeredCube_isBounded (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)).isCompact_closure.measure_lt_top,
      (hgr i).1, ?_⟩
    intro x hx rho hrho hrho1
    exact (hgr i).2.2 x (hrootRegion i (hroot i hx)) rho hrho hrho1
  obtain ⟨lift, O, hlift, hForm⟩ := aux_mfd_prop_uniform_resolvent_form_objects d hd Interp
    (chaosSampleLaw M).toMeasure G muFull Kmu ((d : ℝ) - epsilon) ht hhalf hfrac hmuLocal
  have hscale := fun i => aux_mfd_prop_uniform_resolvent_coercivity_scale hd Sf
    (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
  choose D hD hscale using hscale
  let Kcoer := fun i N omega => D i * Kraw i N omega
  have hcoer : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i N (v : killedSobolevGraph (determiningCube d i)),
      (‖v.val.1‖ ^ 2 ≤ Kcoer i N omega * sobolevCoefficientForm
        (cutoffPositiveCoefficient M H omega N (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) v.val v.val) ∧
      (globalFractionalSqNorm (3 / 4) ((determiningCube d i : Set (SpatialCoordinates d)).indicator (fun x => v.val.1 x)) ≤
        ENNReal.ofReal (Kcoer i N omega * sobolevCoefficientForm
          (cutoffPositiveCoefficient M H omega N (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) v.val v.val)) ∧
      ∃ v3 : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
        (rationalTriadicSide_pos d i) threeQuarterOrder, v3.val 0 = v.val.1 ∧
        cubeFractionalL2Norm hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) threeQuarterOrder v3 ^ 2 ≤
            Kcoer i N omega * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N
              (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) v.val v.val := by
    filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hKrawc i)] with omega hco i N v
    exact hscale i _ _ (hKrawn i N omega) (fun v => (hco i N v).2) v
  have hHolder0 := fun i => hholder M Rm (inputs_regularity_witness d M)
    (inputs_iteration_witness d hd M E) H hH hMH (rationalTriadicCenter d i)
      (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
  choose Khol Ch hCh hKholMeas hKholN hKholMom hHolder0 using hHolder0
  have hHolder := ae_all_iff.mpr hHolder0
  obtain ⟨uN, hRNmeas, hRNbound, hfinite, hpoint⟩ :=
    aux_mfd_prop_uniform_resolvent_finite_family d hd M H hH PN KN hKN hin
  let Cbound := fun i => D i * Cc i + Ch i
  refine ⟨{
    G := G, muFull := muFull, hGmeas := hGmeas, hmuMeas := hmuMeas, hGconv := hGconv, hmu := hmu
    Kmu := Kmu, hKmuMeas := hKmuMeas, hKmuMom := fun i => ?_
    Qroot := Qroot, Region := Region, hRegion := hRegion, hroot := hroot, hrootRegion := hrootRegion
    hNeighborhood := hNeighborhood, hgrowth := hgrowth
    Kcoer := Kcoer, Khol := Khol, Cbound := Cbound
    hCbound := fun i => add_nonneg (mul_nonneg (hD i).le (hCc i)) (hCh i)
    hKmeas := fun i N => ⟨measurable_const.mul (hKrawm i N), hKholMeas i N⟩
    hKnonneg := fun i N omega => ⟨mul_nonneg (hD i).le (hKrawn i N omega), hKholN i N omega⟩
    hKmom := fun i N => ⟨(hKrawmom i N).1.const_mul (D i), (hKholMom i N).1⟩
    hKbound := ?_, hcoer := hcoer, hHolder := hHolder
    lift := lift, hlift := hlift, O := O, hForm := hForm
    uN := uN, hRNmeas := hRNmeas, hRNbound := hRNbound, hfinite := hfinite, hpoint := hpoint
  }⟩
  · simpa only [ENNReal.ofReal_natCast] using hKmuMom i
  · intro i N
    constructor
    · change eLpNorm ((D i) • Kraw i N) (ENNReal.ofReal (q : ℝ)) _ ≤ _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (hD i).le]
      refine (mul_le_mul_right (hKrawmom i N).2 _).trans ?_
      rw [← ENNReal.ofReal_mul (hD i).le]
      exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hCh i))
    · exact ((hKholMom i N).2).trans (ENNReal.ofReal_le_ofReal
        (le_add_of_nonneg_left (mul_nonneg (hD i).le (hCc i))))

end Paper
