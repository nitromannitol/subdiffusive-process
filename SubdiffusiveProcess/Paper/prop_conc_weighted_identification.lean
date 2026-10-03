module

public import SubdiffusiveProcess.Paper.prop_conc_setup
public import SubdiffusiveProcess.Paper.prop_conc_pair_data
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.ScaledLayerLaw
public import SubdiffusiveProcess.Paper.prop_conc_weighted_identification_side
public import SubdiffusiveProcess.Paper.prop_conc_weighted_identification_affine
public import SubdiffusiveProcess.Paper.prop_conc_weighted_identification_transfer
public import SubdiffusiveProcess.Paper.prop_conc_tight_control_bank
public import SubdiffusiveProcess.Paper.inputs_classical_countable_bounded_subsequence
public import SubdiffusiveProcess.Paper.prop_conc_resampled_layer_coefficient
public import Mathlib.Tactic

@[expose] public section

/-! Weighted identification at typical configurations: resampling a fine layer `j ≤ 0` of a typical
configuration `ω` multiplies the coefficient by `exp(y - ω_j)`, and the relative response of the new
typical configuration is the relative response of the `exp(y - ω_j)`-weighted pair of `ω`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section


/-- The conclusion of the slope-wise actual identification theorem at one configuration and one
cutoff sequence, on the padded cube of side `3 r` around the observation cell. -/
def aux_prop_conc_weighted_identification_pk {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ → ℕ) (om : BilateralField d) : Prop :=
  ∀ (S : ResponseSpace (centeredCube z (3 * r) h3r)),
      S.space = killedSobolevGraph (centeredCube z (3 * r) h3r) →
      ∀ (GN : ℕ → DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
          DomainL2 (centeredCube z (3 * r) h3r))
        (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
          DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ n f, GN n f =
        (responseSolution S (cutoffPositiveCoefficient M H om (N n) z h3r)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      ∃ E : _root_.DirichletForm
          (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))),
        (∀ v, E.energy v = limitFormEnergy G v) ∧
        (∃ C, DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C) ∧
        ∃ Gamma : DirichletForm.EnergyMeasure E.toClosedForm,
          ∀ (p : Fin d → ℝ) (L : ℝ),
            Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded z hr) hP
              (cutoffPositiveCoefficient M H om (N n) z hr) p /
              (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
              atTop (𝓝 L) →
            IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm
              Gamma (centeredCube z r hr : Set (SpatialCoordinates d))
              (fun x => ∑ i, p i * x i))
              ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * L)

/-- Deterministic assembly for one side: with the operator limit at the represented configuration,
the analytic controls along a subsequence, the coefficient factorization at the resampled
configuration, and the identification data at the resampled configuration, the weighted killed-class
infimum at every listed slope is the volume of the cell times the limit of the resampled responses. -/
theorem aux_prop_conc_weighted_identification_assembly
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (zcell : SpatialCoordinates d) (k : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
      ‖(u : SobolevData
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
    (h3r : 0 < 3 * ((3 : ℝ) ^ (-(k : ℝ))))
    (S : ResponseSpace (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (omega : BilateralField d) (y : C(SpatialCoordinates d, ℝ)) (j : ℤ)
    (G : DomainL2 (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r))
    (hG : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H omega (N n) zcell h3r)) atTop (𝓝 G))
    (hctrl : ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zcell
        (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r S
        (fun n => cutoffPositiveCoefficient model H omega (N (seq n)) zcell h3r)))
    (hcoef : ∀ N₀ : ℕ, j.natAbs ≤ N₀ →
      (cutoffPositiveCoefficient model H (Function.update omega j y) N₀ zcell h3r).val
        =ᵐ[volume.restrict (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r :
          Set (SpatialCoordinates d))]
        (fun x => Real.exp (y x - omega j x) *
          (cutoffPositiveCoefficient model H omega N₀ zcell h3r).val x))
    (Gp : DomainL2 (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r))
    (hGp : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H (Function.update omega j y) (N n) zcell h3r))
      atTop (𝓝 Gp))
    (hpk : aux_prop_conc_weighted_identification_pk model H zcell ((3 : ℝ) ^ (-(k : ℝ)))
      (by positivity) h3r hPk N (Function.update omega j y))
    (Sl : Set (Fin d → ℝ)) (Lf : (Fin d → ℝ) → ℝ)
    (hL : ∀ p ∈ Sl, Tendsto (fun n => aux_prop_conc_setup_resp model H zcell k hPk (N n)
      (Function.update omega j y) p) atTop (𝓝 (Lf p)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r :
        Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hEloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (D : Submodule ℝ (DomainL2 (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r)))
    (hD : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) : Set (SpatialCoordinates d)) D)
    (bd : (Fin d → ℝ) → DomainL2 (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r))
    (hbd : ∀ p, bd p ∈ E.domain)
    (haff : ∀ p, ∃ V : SpatialCoordinates d → ℝ,
      ContinuousOn V (closure (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r :
        Set (SpatialCoordinates d))) ∧
      (⇑(bd p) =ᵐ[volume.restrict (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r :
        Set (SpatialCoordinates d))] V) ∧
      ∀ x ∈ frontier (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) :
        Set (SpatialCoordinates d)), V x = ∑ i, p i * x i) :
    ∀ p ∈ Sl, sInf {e : ℝ | ∃ v ∈ E.domain, v - bd p ∈ D ∧
      e = (∫⁻ x in (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) :
          Set (SpatialCoordinates d)),
        ENNReal.ofReal (Real.exp (y x - omega j x)) ∂(Gamma.measure v)).toReal} =
      (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) :
        Set (SpatialCoordinates d))).toReal * Lf p := by
  classical
  obtain ⟨seq, hseq, ⟨A⟩⟩ := hctrl
  have hr0 : 0 < (3 : ℝ) ^ (-(k : ℝ)) := by positivity
  have hqQ : (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) h3r : Set (SpatialCoordinates d)) := by
    show Metric.ball zcell (((3 : ℝ) ^ (-(k : ℝ))) / 2) ⊆
      Metric.ball zcell ((3 * ((3 : ℝ) ^ (-(k : ℝ)))) / 2)
    exact Metric.ball_subset_ball (by linarith only [hr0])
  set n0 : ℕ := j.natAbs with hn0
  have hshift : StrictMono (fun n : ℕ => n + n0) := fun a b h => by
    simp only []
    omega
  have hseq' : StrictMono (fun n => seq (n + n0)) := hseq.comp hshift
  have hA := aux_prop_conc_controlled_forms_controls_reindex A (fun n => n + n0)
  intro p hp
  obtain ⟨E', hE', hcore', Gamma', hGam⟩ := hpk S hS
    (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H (Function.update omega j y) (N n) zcell h3r))
    Gp (fun n f => volumeResponseOperator_apply S _ f) hGp
  obtain ⟨V, hVc, hVrep, hVb⟩ := haff p
  refine prop_conc_weighted_identification_side d hd zcell zcell
    (3 * ((3 : ℝ) ^ (-(k : ℝ)))) ((3 : ℝ) ^ (-(k : ℝ))) h3r hr0 hqQ S hS
    (fun n => cutoffPositiveCoefficient model H omega (N (seq (n + n0))) zcell h3r)
    (fun n => cutoffPositiveCoefficient model H (Function.update omega j y)
      (N (seq (n + n0))) zcell h3r) hA
    (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H omega (N (seq (n + n0))) zcell h3r))
    (fun n => volumeResponseOperator S (cutoffPositiveCoefficient model H (Function.update omega j y)
      (N (seq (n + n0))) zcell h3r)) G Gp
    (fun n f => volumeResponseOperator_apply S _ f)
    (fun n f => volumeResponseOperator_apply S _ f)
    (hG.comp hseq'.tendsto_atTop) (hGp.comp hseq'.tendsto_atTop)
    E hE hcore Gamma hEloc D hD (fun x => y x - omega j x)
    (y.continuous.sub (omega j).continuous) ?_ E' Gamma' hE' hcore' (bd p) (hbd p) V hVc hVrep
    (fun x => ∑ i, p i * x i) hVb
    ((volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 : Set (SpatialCoordinates d))).toReal *
      Lf p) (hGam p (Lf p) (hL p hp))
  intro n
  apply hcoef
  have h1 : n + n0 ≤ seq (n + n0) := hseq.id_le (n + n0)
  have h2 : seq (n + n0) ≤ N (seq (n + n0)) := hN.id_le (seq (n + n0))
  omega




theorem aux_prop_conc_weighted_identification_main
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (hprob : IsProbabilityMeasure P) (hmeas : Measurable field)
    (hmap : Measure.map field P = (chaosSampleLaw model).toMeasure)
    (hIR : InfraredCharacterization model H)
    (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (zcell : SpatialCoordinates d) (k : ℕ) (hr0 : 0 < (3 : ℝ) ^ (-(k : ℝ)))
    (h3r : 0 < 3 * ((3 : ℝ) ^ (-(k : ℝ))))
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0),
      ‖(u : SobolevData
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0)) u‖)
    (hz : zQ = zcell) (hR : RQ = 3 * ((3 : ℝ) ^ (-(k : ℝ))))
    (S : ResponseSpace (centeredCube zQ RQ hRQ))
    (hS : S.space = killedSobolevGraph (centeredCube zQ RQ hRQ))
    (GNi : ℕ → Ω → DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (GEi GFi : Ω → DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
    (hGNdef : ∀ N ω f, GNi N ω f =
      (responseSolution S (cutoffPositiveCoefficient model H (field ω) N zQ hRQ)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => GNi (NE n) ω) atTop (𝓝 (GEi ω)) ∧
      Tendsto (fun n => GNi (NF n) ω) atTop (𝓝 (GFi ω)))
    (C0 m M : ℝ)
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
      Tendsto (fun j : ℕ => aux_prop_conc_setup_resp model H zcell k hPk (NE j) (field omega) pvec)
        atTop (𝓝 (pvec ⬝ᵥ (AE omega).mulVec pvec)))
    (hAF : ∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
      Tendsto (fun j : ℕ => aux_prop_conc_setup_resp model H zcell k hPk (NF j) (field omega) pvec)
        atTop (𝓝 (pvec ⬝ᵥ (AF omega).mulVec pvec)))
    {ι : Type} [Countable ι] (F : ι → ℕ → BilateralField d → ℝ) (Cb : ι → ℝ≥0)
    (hmem : ∀ i n, MemLp (F i n) 1 (chaosSampleLaw model).toMeasure)
    (hnorm : ∀ i n, eLpNorm (F i n) 1 (chaosSampleLaw model).toMeasure ≤ Cb i)
    (hcontrol : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      ∀ N : ℕ → ℕ, (∀ i, ∃ B : ℝ, ∀ n, |F i (N n) om| ≤ B) →
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
          (fun n => cutoffPositiveCoefficient model H om (N n) zQ hRQ)))
    (hPkE : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      aux_prop_conc_weighted_identification_pk model H zcell ((3 : ℝ) ^ (-(k : ℝ)))
        hr0 h3r hPk NE om)
    (hPkF : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      aux_prop_conc_weighted_identification_pk model H zcell ((3 : ℝ) ^ (-(k : ℝ)))
        hr0 h3r hPk NF om)
    (c : ℝ) (pvec : Fin d → ℝ) (f : BilateralField d → ℝ) (hf : Measurable f)
    (hfR : (fun omega => (pvec ⬝ᵥ (AF omega).mulVec pvec -
            c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) / Matrix.trace (AE omega)) =ᵐ[P] f ∘ field)
    (j : ℤ) (hj : j ≤ 0) :
    ∀ᵐ omega ∂P,
        ∀ Y : prop_conc_pair_data (centeredCube zQ RQ hRQ)
            zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 C0 m M,
          (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy (GEi omega) u) →
          (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy (GFi omega) u) →
          aux_prop_conc_pair_data_affine Y →
          ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
            f (Function.update (field omega) j y) =
              aux_prop_conc_pair_data_theta Y c pvec (fun x => y x - (field omega) j x) := by
  subst hz
  subst hR
  classical
  haveI : IsProbabilityMeasure P := hprob
  have hfmp : MeasurePreserving field P (chaosSampleLaw model).toMeasure := ⟨hmeas, hmap⟩
  have hΦ := prop_conc_weighted_identification_transfer model j P field hfmp
  have hH : Measurable H := hIR.1
  -- actual operators and responses as functions of an arbitrary field
  let Gop : (ℕ → ℕ) → ℕ → BilateralField d → DomainL2 (centeredCube zQ (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hRQ) →L[ℝ]
      DomainL2 (centeredCube zQ (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hRQ) :=
    fun N n om => volumeResponseOperator S (cutoffPositiveCoefficient model H om (N n) zQ hRQ)
  have hGopeq : ∀ (N : ℕ → ℕ) (n : ℕ) (ω : Ω), Gop N n (field ω) = GNi (N n) ω := by
    intro N n ω
    apply ContinuousLinearMap.ext
    intro f
    rw [hGNdef (N n) ω f]
    exact volumeResponseOperator_apply S _ f
  have hGopSM : ∀ N n, StronglyMeasurable (Gop N n) := fun N n =>
    aux_prop_conc_weighted_identification_transfer_operator_measurable model H hH (N n) zQ (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hRQ S
  have hrespM : ∀ (N : ℕ → ℕ) (n : ℕ) (p : Fin d → ℝ), Measurable (fun om : BilateralField d =>
      aux_prop_conc_setup_resp model H zQ k hPk (N n) om p) := by
    intro N n p
    exact (aux_prop_conc_weighted_identification_transfer_response_measurable model H hH (N n)
      zQ ((3 : ℝ) ^ (-(k : ℝ))) hr0 hPk p).div_const _
  let Sl : Finset (Fin d → ℝ) :=
    insert pvec (Finset.univ.image (fun i : Fin d => (Pi.single i (1 : ℝ) : Fin d → ℝ)))
  have hpvSl : pvec ∈ Sl := Finset.mem_insert_self _ _
  have heSl : ∀ i : Fin d, (Pi.single i (1 : ℝ) : Fin d → ℝ) ∈ Sl := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  let resp : (ℕ → ℕ) → ℕ → BilateralField d → (Fin d → ℝ) → ℝ :=
    fun N n om p => aux_prop_conc_setup_resp model H zQ k hPk (N n) om p
  let ell : (ℕ → ℕ) → (Fin d → ℝ) → BilateralField d → ℝ :=
    fun N p om => limUnder atTop (fun n => resp N n om p)
  let Rhat : BilateralField d → ℝ := fun om =>
    (ell NF pvec om - c * ell NE pvec om) / ∑ i : Fin d, ell NE (Pi.single i 1) om
  have hellM : ∀ N p, Measurable (ell N p) := fun N p =>
    (StronglyMeasurable.limUnder (l := atTop)
      (fun n => (hrespM N n p).stronglyMeasurable)).measurable
  have hRhatM : Measurable Rhat :=
    ((hellM NF pvec).sub ((hellM NE pvec).const_mul c)).div
      (Finset.measurable_sum _ (fun i _ => hellM NE _))
  let TypeSet : Set (BilateralField d) :=
    {x | (∃ G, Tendsto (fun n => Gop NE n x) atTop (𝓝 G)) ∧
      (∃ G, Tendsto (fun n => Gop NF n x) atTop (𝓝 G)) ∧
      (∀ p ∈ Sl, ∃ L, Tendsto (fun n => resp NE n x p) atTop (𝓝 L)) ∧
      (∀ p ∈ Sl, ∃ L, Tendsto (fun n => resp NF n x p) atTop (𝓝 L)) ∧ f x = Rhat x}
  have hTypeMeas : MeasurableSet TypeSet := by
    have h1 := aux_prop_conc_weighted_identification_transfer_operator_event _
      (fun n => Gop NE n) (hGopSM NE)
    have h2 := aux_prop_conc_weighted_identification_transfer_operator_event _
      (fun n => Gop NF n) (hGopSM NF)
    have h3 : MeasurableSet {x : BilateralField d |
        ∀ p ∈ Sl, ∃ L, Tendsto (fun n => resp NE n x p) atTop (𝓝 L)} := by
      have hEq : {x : BilateralField d |
          ∀ p ∈ Sl, ∃ L, Tendsto (fun n => resp NE n x p) atTop (𝓝 L)} =
          ⋂ p ∈ Sl, {x : BilateralField d | ∃ L, Tendsto (fun n => resp NE n x p) atTop (𝓝 L)} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [hEq]
      exact MeasurableSet.biInter Sl.countable_toSet
        (fun p _ => measurableSet_exists_tendsto (l := atTop) (fun n => hrespM NE n p))
    have h4 : MeasurableSet {x : BilateralField d |
        ∀ p ∈ Sl, ∃ L, Tendsto (fun n => resp NF n x p) atTop (𝓝 L)} := by
      have hEq : {x : BilateralField d |
          ∀ p ∈ Sl, ∃ L, Tendsto (fun n => resp NF n x p) atTop (𝓝 L)} =
          ⋂ p ∈ Sl, {x : BilateralField d | ∃ L, Tendsto (fun n => resp NF n x p) atTop (𝓝 L)} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [hEq]
      exact MeasurableSet.biInter Sl.countable_toSet
        (fun p _ => measurableSet_exists_tendsto (l := atTop) (fun n => hrespM NF n p))
    have h5 : MeasurableSet {x : BilateralField d | f x = Rhat x} := measurableSet_eq_fun hf hRhatM
    exact h1.inter (h2.inter (h3.inter (h4.inter h5)))
  have hmemTS : ∀ᵐ ω ∂P, field ω ∈ TypeSet := by
    filter_upwards [hlim, hAE, hAF, hfR] with ω hlimω hAEω hAFω hfRω
    refine ⟨⟨GEi ω, hlimω.1.congr (fun n => (hGopeq NE n ω).symm)⟩,
      ⟨GFi ω, hlimω.2.congr (fun n => (hGopeq NF n ω).symm)⟩,
      fun p _ => ⟨_, hAEω p⟩, fun p _ => ⟨_, hAFω p⟩, ?_⟩
    have hEl : ∀ p, ell NE p (field ω) = p ⬝ᵥ (AE ω).mulVec p := fun p => (hAEω p).limUnder_eq
    have hFl : ell NF pvec (field ω) = pvec ⬝ᵥ (AF ω).mulVec pvec := (hAFω pvec).limUnder_eq
    have htr : ∑ i : Fin d, ell NE (Pi.single i 1) (field ω) = Matrix.trace (AE ω) := by
      simp only [hEl, Matrix.trace, Matrix.diag, single_dotProduct, Matrix.mulVec_single_one]
      simp
    show f (field ω) = (ell NF pvec (field ω) - c * ell NE pvec (field ω)) /
      ∑ i : Fin d, ell NE (Pi.single i 1) (field ω)
    rw [htr, hFl, hEl pvec]
    exact hfRω.symm
  have hTyp : ∀ᵐ x ∂(chaosSampleLaw model).toMeasure, x ∈ TypeSet :=
    aux_prop_conc_weighted_identification_transfer_ae hfmp hTypeMeas hmemTS
  have hjoint := hΦ.quasiMeasurePreserving.ae (hTyp.and (hPkE.and hPkF))
  have hjoint' := Measure.ae_ae_of_ae_prod hjoint
  -- the coefficient factorization on the padded cell, for every cutoff containing the layer
  have hcoefJ : ∀ᵐ ω ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      ∀ N₀ : ℕ, j.natAbs ≤ N₀ →
        (cutoffPositiveCoefficient model H (Function.update (field ω) j y) N₀ zQ hRQ).val
          =ᵐ[volume.restrict (centeredCube zQ (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hRQ :
            Set (SpatialCoordinates d))]
          (fun x => Real.exp (y x - field ω j x) *
            (cutoffPositiveCoefficient model H (field ω) N₀ zQ hRQ).val x) := by
    have hc : ∀ N₀ : ℕ, ∀ᵐ ω ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
        (j.natAbs ≤ N₀ →
        (cutoffPositiveCoefficient model H (Function.update (field ω) j y) N₀ zQ hRQ).val
          =ᵐ[volume.restrict (centeredCube zQ (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hRQ :
            Set (SpatialCoordinates d))]
          (fun x => Real.exp (y x - field ω j x) *
            (cutoffPositiveCoefficient model H (field ω) N₀ zQ hRQ).val x)) := by
      intro N₀
      by_cases hN : j.natAbs ≤ N₀
      · filter_upwards [aux_prop_conc_resampled_layer_coefficient_positive_ae P model H hIR field
          hfmp j N₀ hj hN zQ hRQ] with ω hω
        filter_upwards [hω] with y hy
        exact fun _ => hy
      · exact Eventually.of_forall fun ω => Eventually.of_forall fun y h => absurd h hN
    filter_upwards [ae_all_iff.2 hc] with ω hω
    filter_upwards [ae_all_iff.2 hω] with y hy
    exact hy
  -- a tight bank bounded along a subsequence gives the analytic controls at the represented field
  have hmemP : ∀ i n, MemLp (fun ω => F i n (field ω)) 1 P := fun i n =>
    (hmem i n).comp_measurePreserving hfmp
  have hnormP : ∀ i n, eLpNorm (fun ω => F i n (field ω)) 1 P ≤ Cb i := fun i n => by
    have h := eLpNorm_comp_measurePreserving (p := 1) (hmem i n).aestronglyMeasurable hfmp
    exact h.trans_le (hnorm i n)
  have hbdE := inputs_classical_countable_bounded_subsequence P
    (fun i n ω => F i (NE n) (field ω)) Cb (fun i n => hmemP i (NE n)) (fun i n => hnormP i (NE n))
  have hbdF := inputs_classical_countable_bounded_subsequence P
    (fun i n ω => F i (NF n) (field ω)) Cb (fun i n => hmemP i (NF n)) (fun i n => hnormP i (NF n))
  have hcontrolP := hfmp.quasiMeasurePreserving.ae hcontrol
  filter_upwards [hlim, hjoint', hcoefJ, hbdE, hbdF, hcontrolP] with
    ω hlimω hjω hcω hbE hbF hcP
  intro Y hYE hYF haff
  filter_upwards [hjω, hcω] with y hjy hcy
  obtain ⟨⟨⟨GpE, hGpE⟩, ⟨GpF, hGpF⟩, hLE, hLF, hfR'⟩, hpkE', hpkF'⟩ := hjy
  obtain ⟨seqE, hseqE, hbE'⟩ := hbE
  obtain ⟨seqF, hseqF, hbF'⟩ := hbF
  have hctrlE : ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ
        (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hRQ S
        (fun n => cutoffPositiveCoefficient model H (field ω) (NE (seq n)) zQ hRQ)) :=
    ⟨seqE, hseqE, hcP (fun n => NE (seqE n)) (fun i => by
      obtain ⟨B, _, hB⟩ := hbE' i
      exact ⟨B, hB⟩)⟩
  have hctrlF : ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ
        (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hRQ S
        (fun n => cutoffPositiveCoefficient model H (field ω) (NF (seq n)) zQ hRQ)) :=
    ⟨seqF, hseqF, hcP (fun n => NF (seqF n)) (fun i => by
      obtain ⟨B, _, hB⟩ := hbF' i
      exact ⟨B, hB⟩)⟩
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.2 (by linarith [Y.hC0])) Y.hm
  have hDF := aux_prop_conc_weighted_identification_side_killed_transfer Y.E.toClosedForm
    Y.F.toClosedForm Y.P.domain_eq m M hmpos (le_trans hmpos.le Y.hmM) Y.horder _ Y.D Y.P.killed
  have hLEt : ∀ p ∈ (Sl : Set (Fin d → ℝ)), Tendsto (fun n =>
      aux_prop_conc_setup_resp model H zQ k hPk (NE n) (Function.update (field ω) j y) p) atTop
      (𝓝 (ell NE p (Function.update (field ω) j y))) :=
    fun p hp => tendsto_nhds_limUnder (hLE p (Finset.mem_coe.mp hp))
  have hLFt : ∀ p ∈ (Sl : Set (Fin d → ℝ)), Tendsto (fun n =>
      aux_prop_conc_setup_resp model H zQ k hPk (NF n) (Function.update (field ω) j y) p) atTop
      (𝓝 (ell NF p (Function.update (field ω) j y))) :=
    fun p hp => tendsto_nhds_limUnder (hLF p (Finset.mem_coe.mp hp))
  let bd : (Fin d → ℝ) → DomainL2 (centeredCube zQ (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hRQ) :=
    fun p => (Y.P.boundary p : DomainL2 (centeredCube zQ (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hRQ))
  have hbdE : ∀ p, bd p ∈ Y.E.domain := fun p => (Y.P.boundary p).property
  have hbdF : ∀ p, bd p ∈ Y.F.domain := fun p => Y.P.domain_eq ▸ (Y.P.boundary p).property
  have hWE := aux_prop_conc_weighted_identification_assembly d hd model H zQ k hPk hRQ S hS NE hNE
    (field ω) y j (GEi ω) (hlimω.1.congr (fun n => (hGopeq NE n ω).symm)) hctrlE hcy GpE hGpE hpkE'
    (Sl : Set (Fin d → ℝ)) (fun p => ell NE p (Function.update (field ω) j y)) hLEt
    Y.E hYE Y.hEc Y.GammaE Y.hEl Y.D Y.P.killed bd hbdE haff
  have hWF := aux_prop_conc_weighted_identification_assembly d hd model H zQ k hPk hRQ S hS NF hNF
    (field ω) y j (GFi ω) (hlimω.2.congr (fun n => (hGopeq NF n ω).symm)) hctrlF hcy GpF hGpF hpkF'
    (Sl : Set (Fin d → ℝ)) (fun p => ell NF p (Function.update (field ω) j y)) hLFt
    Y.F hYF Y.hFc Y.GammaF Y.hFl Y.D hDF bd hbdF haff
  have hE1 : ∀ p ∈ Sl, aux_prop_conc_pair_data_wInfE Y (fun x => y x - (field ω) j x) p =
      (volume (centeredCube zQ ((3 : ℝ) ^ (-(k : ℝ))) hr0 : Set (SpatialCoordinates d))).toReal *
        ell NE p (Function.update (field ω) j y) :=
    fun p hp => hWE p (Finset.mem_coe.mpr hp)
  have hF1 : ∀ p ∈ Sl, aux_prop_conc_pair_data_wInfF Y (fun x => y x - (field ω) j x) p =
      (volume (centeredCube zQ ((3 : ℝ) ^ (-(k : ℝ))) hr0 : Set (SpatialCoordinates d))).toReal *
        ell NF p (Function.update (field ω) j y) :=
    fun p hp => hWF p (Finset.mem_coe.mpr hp)
  have hvol : (volume (centeredCube zQ ((3 : ℝ) ^ (-(k : ℝ))) hr0 :
      Set (SpatialCoordinates d))).toReal ≠ 0 := (centeredCube_volume_pos zQ hr0).ne'
  have hfR'' : f (Function.update (field ω) j y) = Rhat (Function.update (field ω) j y) := hfR'
  have hθ : aux_prop_conc_pair_data_theta Y c pvec (fun x => y x - (field ω) j x) =
      (ell NF pvec (Function.update (field ω) j y) -
        c * ell NE pvec (Function.update (field ω) j y)) /
        ∑ i : Fin d, ell NE (Pi.single i 1) (Function.update (field ω) j y) := by
    unfold aux_prop_conc_pair_data_theta
    rw [hF1 pvec hpvSl, hE1 pvec hpvSl,
      Finset.sum_congr rfl (fun i _ => hE1 _ (heSl i)), ← Finset.mul_sum]
    rw [show ∀ vol a b : ℝ, vol * a - c * (vol * b) = vol * (a - c * b) from
      fun vol a b => by ring]
    exact mul_div_mul_left _ _ hvol
  rw [hθ]
  exact hfR''


/-- For a.e. `ω` and every pair `Y` of limiting forms realizing the operator limits at `ω` in an affine
trace class, a.e. resampling `y` of the layer `j ≤ 0` gives `f(ω[j ← y]) = θ_Y(y - ω_j)`. -/
theorem prop_conc_weighted_identification
    (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (_MeyersMorrey : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ccamp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ) (C0 m M : ℝ) (hC0 : 1 ≤ C0)
        (zcell : SpatialCoordinates d) (k : ℕ) (cellIdx paddedIdx : ℕ)
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
          zcell k cellIdx paddedIdx hPk AE AF),
      ∀ (c : ℝ) (pvec : Fin d → ℝ) (f : BilateralField d → ℝ), Measurable f →
        ((fun omega => (pvec ⬝ᵥ (AF omega).mulVec pvec -
            c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) / Matrix.trace (AE omega)) =ᵐ[P]
          f ∘ field) →
      ∀ j : ℤ, j ≤ 0 →
      ∀ᵐ omega ∂P,
        ∀ Y : prop_conc_pair_data
            (centeredCube (z paddedIdx) (r paddedIdx) (hr paddedIdx))
            zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) C0 m M,
          (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy (GE paddedIdx omega) u) →
          (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy (GF paddedIdx omega) u) →
          aux_prop_conc_pair_data_affine Y →
          ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
            f (Function.update (field omega) j y) =
              aux_prop_conc_pair_data_theta Y c pvec (fun x => y x - (field omega) j x) := by
  -- thresholds are chosen before the measurable structure; the Borel structure is unique
  letI instBorel : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  haveI : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨deltaB, hdeltaB, hB⟩ := prop_conc_tight_control_bank d hd I Pin _X _MeyersMorrey Ccamp _Sob
    Interp ((d : ℝ) - 1 / 2) (3 / 4) (by linarith only []) (by linarith only [])
    (by norm_num) (by norm_num)
  obtain ⟨deltaA, hdeltaA, hA⟩ := prop_conc_weighted_identification_affine d hd I Pin _X _MeyersMorrey
    Ccamp _Sob Interp
  refine ⟨min deltaB deltaA, lt_min hdeltaB hdeltaA, ?_⟩
  intro instM instB model hdelta Rm Sreg It H Ω _ P field z r hr Sspace GN GE GF NE NF C0 m M hC0
    zcell k cellIdx paddedIdx hPk AE AF hyps c pvec f hf hfR j hj
  obtain rfl := instB.measurable_eq
  obtain ⟨⟨hprob, hmeas, hmap, hIR, ⟨hNE, hNF⟩, hSall, hGNall, hlimall⟩, hCm, hord, hcellEq,
    hpadEq, hsymAE, hsymAF, hAE, hAF⟩ := hyps
  have hr0 : 0 < (3 : ℝ) ^ (-(k : ℝ)) := by positivity
  have h3r : 0 < 3 * ((3 : ℝ) ^ (-(k : ℝ))) := by positivity
  have hr1 : (3 : ℝ) ^ (-(k : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
  obtain ⟨F, Cb, hmem, hnorm, hcontrol⟩ := hB model Rm Sreg It H hIR
    (hdelta.trans (min_le_left _ _)) (z paddedIdx) (r paddedIdx) (hr paddedIdx) (Sspace paddedIdx)
    (hSall paddedIdx)
  have hPkE := hA model Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) zcell
    ((3 : ℝ) ^ (-(k : ℝ))) hr0 hr1 h3r hPk NE
  have hPkF := hA model Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) zcell
    ((3 : ℝ) ^ (-(k : ℝ))) hr0 hr1 h3r hPk NF
  exact aux_prop_conc_weighted_identification_main d hd model H Ω P field hprob hmeas hmap hIR
    (z paddedIdx) (r paddedIdx) (hr paddedIdx) zcell k hr0 h3r hPk hpadEq.1 hpadEq.2
    (Sspace paddedIdx) (hSall paddedIdx) (GN paddedIdx) (GE paddedIdx) (GF paddedIdx) NE NF hNE hNF
    (hGNall paddedIdx) (hlimall.mono fun ω h => h paddedIdx) C0 m M AE AF hAE hAF F Cb hmem hnorm
    (hcontrol.mono fun om h N hb => (h N hb).1) hPkE hPkF c pvec f hf hfR j hj

end
end Paper
