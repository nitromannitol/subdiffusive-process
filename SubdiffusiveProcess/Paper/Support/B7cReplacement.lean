import SubdiffusiveProcess.Paper.Support.B7cGluingStatement
import SubdiffusiveProcess.Paper.Support.B7cReplacementPatch
import SubdiffusiveProcess.Paper.Support.B7cReplacementGeometry
import SubdiffusiveProcess.Paper.Support.B7cTruncationSupport
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

theorem aux_mfd_prop_gluing_replacement
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hr : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (omega : Ω)
    (Gs : ∀ j, DomainL2 (centeredCube (z j) (rad j) (hr j)) →L[ℝ]
      DomainL2 (centeredCube (z j) (rad j) (hr j)))
    (Ls : ∀ j, aux_limit_form_package_limit_side d hd (z j) (rad j) (hr j) (S j) (Gs j)
      (fun n => Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j) (hr j))) :
  conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hr
    S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
    Index resp respLim constants G coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
    cellGrowthKey cellHolderKey Grid origin gridRoot gridKey → omega ∈ G →
  -- (i) Every trace on every catalogue cube has its extension and its actual energy limit.
  (∀ (iq iQ : J) (hz : z iQ = z iq) (hrad : rad iQ = 3 * rad iq),
    ∀ b : SpatialCoordinates d → ℝ,
      Lane4.IsHolderOn alpha
        (frontier (centeredCube (z iq) (rad iq) (hr iq) : Set (SpatialCoordinates d))) b →
      ∃ lam : ℝ, ∃ U : DomainL2 (centeredCube (z iQ) (rad iQ) (hr iQ)),
        ∃ Uc : SpatialCoordinates d → ℝ,
          aux_mfd_prop_gluing_trace_package d hd M H (fun n => env n omega) cutoff
            (z iq) (rad iq) (hr iq) (z iQ) (rad iQ) (hr iQ) hz hrad (S iQ)
            (Gs iQ) (Ls iQ) E Cext beta alpha b lam U Uc) →
  -- (ii), with (iii) as the additional conclusion under its paper hypothesis.
  (∀ (iQ : J) (m : ℕ) (iq iQcell : Fin m → J)
    (hz : ∀ i, z (iQcell i) = z (iq i))
    (hrad : ∀ i, rad (iQcell i) = 3 * rad (iq i))
    (hCell : ∀ i, closure (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d)))
    (hEnlarge : ∀ i, (centeredCube (z (iQcell i)) (rad (iQcell i)) (hr (iQcell i)) :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d)))
    (hDisjoint : Pairwise fun i j : Fin m => Disjoint
      (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))
      (centeredCube (z (iq j)) (rad (iq j)) (hr (iq j)) : Set (SpatialCoordinates d)))
    (V : DomainL2 (centeredCube (z iQ) (rad iQ) (hr iQ)))
    (hV : V ∈ (Ls iQ).form.domain) (Vc : SpatialCoordinates d → ℝ)
    (hVc : ContinuousOn Vc (closure (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))))
    (hVrep : (V : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))] Vc)
    (hTrace : ∀ i, Lane4.IsHolderOn alpha
      (frontier (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))) Vc),
    ∃ (Lam : Fin m → ℝ)
      (Ui : Fin m → SpatialCoordinates d → ℝ)
      (UiL2 : Fin m → DomainL2 (centeredCube (z iQ) (rad iQ) (hr iQ)))
      (Vprime : DomainL2 (centeredCube (z iQ) (rad iQ) (hr iQ))),
      let Vprimec := fun x => Vc x + ∑ i : Fin m,
        (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d)).indicator
          (fun y => Ui i y - Vc y) x
      (∀ i,
        ∃ U : DomainL2 (centeredCube (z (iQcell i)) (rad (iQcell i)) (hr (iQcell i))),
          aux_mfd_prop_gluing_trace_package d hd M H (fun n => env n omega) cutoff
            (z (iq i)) (rad (iq i)) (hr (iq i))
            (z (iQcell i)) (rad (iQcell i)) (hr (iQcell i))
            (hz i) (hrad i)
            (S (iQcell i)) (Gs (iQcell i)) (Ls (iQcell i))
            E Cext beta alpha Vc (Lam i) U (Ui i)) ∧
      (∀ i, UiL2 i ∈ (Ls iQ).form.domain ∧
        (UiL2 i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))]
          ((centeredCube (z (iQcell i)) (rad (iQcell i)) (hr (iQcell i)) : Set (SpatialCoordinates d)).indicator (Ui i))) ∧
      Vprime ∈ (Ls iQ).form.domain ∧
      ContinuousOn Vprimec (closure (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))) ∧
      (Vprime : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))] Vprimec ∧
      (Ls iQ).form.form Vprime Vprime = (Ls iQ).form.form V V - ∑ i : Fin m,
        (((Ls iQ).gamma.measure V
          (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))).toReal - Lam i) ∧
      (Ls iQ).form.form Vprime Vprime ≤ (Ls iQ).form.form V V ∧
      (∀ i, ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d)) →
        (Ls iQ).gamma.measure Vprime B = (Ls iQ).gamma.measure (UiL2 i) B) ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d)) \
          (⋃ i : Fin m, (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))) →
        (Ls iQ).gamma.measure Vprime B = (Ls iQ).gamma.measure V B) ∧
      (∀ (zprime : SpatialCoordinates d) (rprime : ℝ) (hrprime : 0 < rprime),
        closure (centeredCube zprime rprime hrprime : Set (SpatialCoordinates d)) =
          ⋃ i : Fin m, closure (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d)) →
        (∀ i, (Ls iQ).gamma.measure V
          (frontier (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))) = 0) →
        ((Ls iQ).gamma.measure Vprime
          (centeredCube zprime rprime hrprime : Set (SpatialCoordinates d))).toReal = ∑ i : Fin m, Lam i))
 := by
  classical
  intro hR _hgood htrace iQ m iq iQcell hz hrad hCell hEnlarge hDisjoint V hV Vc hVc hVrep hTrace
  let cubes : J → Opens (SpatialCoordinates d) := fun j => centeredCube (z j) (rad j) (hr j)
  let a : ∀ j, ℕ → PositiveCoefficient (cubes j) := fun j n =>
    Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j) (hr j)
  have hS : ∀ j, (S j).space = killedSobolevGraph (cubes j) := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcoeff (i j : J) (hij : cubes j ≤ cubes i) (n : ℕ) :
      ((a i n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (cubes j : Set (SpatialCoordinates d))]
          ((a j n).val : SpatialCoordinates d → ℝ) := by
    have hi := (Lane4.cutoffPositiveCoefficient_representative M H (env n omega) (cutoff n)
      (z i) (hr i)).2.2.2
    have hj := (Lane4.cutoffPositiveCoefficient_representative M H (env n omega) (cutoff n)
      (z j) (hr j)).2.2.2
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hij hi, hj] with x hix hjx
    exact hix.trans hjx.symm
  have hK (i j : J) (hij : cubes j ≤ cubes i) :=
    limit_form_killed_consistency d hd (z i) (z j) (rad i) (rad j) (hr i) (hr j)
      hij (S i) (S j) (hS i) (hS j) (a i) (a j) (hcoeff i j hij)
      (Gs i) (Gs j) (Ls i) (Ls j)
  have hclParent : ∀ i : Fin m, closure (cubes (iq i) : Set (SpatialCoordinates d)) ⊆
      (cubes (iQcell i) : Set (SpatialCoordinates d)) := by
    intro i
    change closure (Metric.ball (z (iq i)) (rad (iq i) / 2)) ⊆
      Metric.ball (z (iQcell i)) (rad (iQcell i) / 2)
    rw [hz i, hrad i, closure_ball _ (ne_of_gt (div_pos (hr (iq i)) (by norm_num) : 0 < rad (iq i) / 2))]
    exact Metric.closedBall_subset_ball (by linarith only [hr (iq i)])
  have hqParent : ∀ i : Fin m, cubes (iq i) ≤ cubes (iQcell i) :=
    fun i => subset_closure.trans (hclParent i)
  have hqAmbient : ∀ i : Fin m, cubes (iq i) ≤ cubes iQ :=
    fun i => subset_closure.trans (hCell i)
  choose Lam Ul Ui hU using fun i : Fin m =>
    htrace (iq i) (iQcell i) (hz i) (hrad i) Vc (hTrace i)
  have hData : ∀ i : Fin m,
      Ul i ∈ (Ls (iQcell i)).form.domain ∧
      ContinuousOn (Ui i) (closure (cubes (iQcell i) : Set (SpatialCoordinates d))) ∧
      (Ul i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (cubes (iQcell i) : Set (SpatialCoordinates d))] Ui i ∧
      (∀ x ∈ frontier (cubes (iQcell i) : Set (SpatialCoordinates d)), Ui i x = 0) ∧
      EqOn (Ui i) Vc (frontier (cubes (iq i) : Set (SpatialCoordinates d))) ∧
      (Ls (iQcell i)).gamma.measure (Ul i) (frontier (cubes (iq i) : Set (SpatialCoordinates d))) = 0 ∧
      (∀ phi ∈ (Ls (iQcell i)).form.toClosedForm.killedCoreClosure
        (cubes (iq i) : Set (SpatialCoordinates d)), (Ls (iQcell i)).form.form (Ul i) phi = 0) ∧
      ((Ls (iQcell i)).gamma.measure (Ul i) (cubes (iq i) : Set (SpatialCoordinates d))).toReal = Lam i := by
    intro i
    obtain ⟨B, UN, UNS, _hb, _hB, _hcpt, _hsupp, _hholder, _hBb, hUN,
      _hlam, _hbdd, _hlambound, hu, huc, hrep, huni, hboundary, hface, horth, henergy,
      _hmin⟩ := hU i
    have hzero := aux_mfd_prop_gluing_limit_frontier_zero (cubes (iQcell i))
      (fun n => (UN n).toFun) (Ui i) huni (fun n => (hUN n).2.2.1)
    exact ⟨hu, huc, hrep, hzero, hboundary, hface, horth, henergy⟩
  choose hUdom hUcont hUrep hUzero hUtrace hUface hUorth hUenergy using hData
  let UiL2 : Fin m → DomainL2 (cubes iQ) := fun i => zeroExtensionLp (hEnlarge i) (Ul i)
  let Uic : Fin m → SpatialCoordinates d → ℝ := fun i =>
    (cubes (iQcell i) : Set (SpatialCoordinates d)).indicator (Ui i)
  have htransport (i : Fin m) := aux_mfd_prop_gluing_killed_gamma d hd (z iQ) (z (iQcell i))
    (rad iQ) (rad (iQcell i)) (hr iQ) (hr (iQcell i)) (hEnlarge i)
    (S iQ) (S (iQcell i)) (hS iQ) (hS (iQcell i))
    (a iQ) (a (iQcell i)) (hcoeff iQ (iQcell i) (hEnlarge i))
    (Gs iQ) (Gs (iQcell i)) (Ls iQ) (Ls (iQcell i)) (Ul i) (hUdom i)
  have hUiDomain : ∀ i : Fin m, UiL2 i ∈ (Ls iQ).form.domain := fun i => (htransport i).1
  have hUiRep : ∀ i : Fin m, (UiL2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (cubes iQ : Set (SpatialCoordinates d))] Uic i := fun i =>
    aux_mfd_prop_gluing_zeroExtension_rep (hEnlarge i) (Ul i) (Ui i) (hUrep i)
  have hUicont : ∀ i : Fin m, ContinuousOn (Uic i) (closure (cubes iQ : Set (SpatialCoordinates d))) :=
    fun i => (aux_mfd_prop_gluing_indicator_continuous (cubes (iQcell i))
      (Ui i) (hUcont i) (hUzero i)).continuousOn
  have hUibdry : ∀ i : Fin m, ∀ x ∈ frontier (cubes (iq i) : Set (SpatialCoordinates d)),
      Uic i x = Vc x := by
    intro i x hx
    change (cubes (iQcell i) : Set (SpatialCoordinates d)).indicator (Ui i) x = _
    rw [Set.indicator_of_mem (hclParent i (frontier_subset_closure hx))]
    exact hUtrace i hx
  choose Dq hDq hDqImage _hDqExt _hDqForm using fun i : Fin m => hK iQ (iq i) (hqAmbient i)
  have hUiOrth : ∀ i : Fin m, ∀ phi ∈ Dq i, (Ls iQ).form.form (UiL2 i) phi = 0 := by
    intro i
    obtain ⟨Dpq, hDpq, hDpqImage, _, _⟩ := hK (iQcell i) (iq i) (hqParent i)
    obtain ⟨_, _, _, _, hform⟩ := hK iQ (iQcell i) (hEnlarge i)
    exact aux_mfd_prop_gluing_transfer_orthogonality (hqParent i) (hEnlarge i) (hqAmbient i)
      (Ls iQ).form.toClosedForm (Ls (iQcell i)).form.toClosedForm (Ls (iq i)).form.toClosedForm
      (Dq i) Dpq (hDqImage i) hDpq hDpqImage hform (Ul i) (hUdom i) (hUorth i)
  have hUiFace : ∀ i : Fin m, (Ls iQ).gamma.measure (UiL2 i)
      (frontier (cubes (iq i) : Set (SpatialCoordinates d))) = 0 := by
    intro i
    rw [(htransport i).2.2]
    exact hUface i
  have hUiEnergy : ∀ i : Fin m, ((Ls iQ).gamma.measure (UiL2 i)
      (cubes (iq i) : Set (SpatialCoordinates d))).toReal = Lam i := by
    intro i
    rw [(htransport i).2.2]
    exact hUenergy i
  have hZeroTrace (i : Fin m) := aux_mfd_prop_boundary_zero_trace d hd
    (z iQ) (z (iq i)) (rad iQ) (rad (iq i)) (hr iQ) (hr (iq i)) (hqAmbient i)
    (Ls iQ).form (Ls iQ).gamma (Ls iQ).core (Dq i) (hDq i)
  have hQcube : ∃ z0 : SpatialCoordinates d, ∃ r0 : ℝ, 0 < r0 ∧
      (cubes iQ : Set (SpatialCoordinates d)) = Metric.ball z0 (r0 / 2) :=
    ⟨z iQ, rad iQ, hr iQ, rfl⟩
  have hEnlarge' : ∀ i : Fin m, Metric.ball (z (iq i)) (3 * rad (iq i) / 2) ⊆
      (cubes iQ : Set (SpatialCoordinates d)) := by
    intro i
    simpa only [cubes, hz i, hrad i] using hEnlarge i
  have hcent : ∀ (i : Fin m) (k : Fin d), ∃ s : ℚ, z (iq i) k = (s : ℝ) :=
    fun i => hR.2.2.2.2.2.2.2.2.2.2.2.1 (iq i)
  have htri : ∀ i : Fin m, ∃ k : ℤ, rad (iq i) = (3 : ℝ) ^ k :=
    fun i => hR.2.2.2.2.2.2.2.2.2.2.2.2.1 (iq i)
  have halpha : 1 / 2 < alpha := lt_trans hR.2.2.1.1 hR.2.2.1.2
  obtain ⟨Vprime, hrep, hout, hin, hpatch⟩ := aux_mfd_prop_gluing_construct_replacement hd
    hQcube (Ls iQ).form.toClosedForm (Ls iQ).gamma alpha halpha hR.2.1.1
    m (fun i => z (iq i)) (fun i => rad (iq i)) (fun i => hr (iq i))
    hCell hEnlarge' hDisjoint hcent htri Dq hDq V hV Vc hVc hVrep hTrace
    Uic UiL2 hUiDomain hUiRep hUicont hUibdry hZeroTrace
  let Vprimec := fun x => Vc x + ∑ i : Fin m,
    (cubes (iq i) : Set (SpatialCoordinates d)).indicator (fun y => Uic i y - Vc y) x
  have hloc := prop_gluing_replacement_localization (Ls iQ).form.toClosedForm (Ls iQ).gamma
    m (fun i => z (iq i)) (fun i => rad (iq i)) (fun i => hr (iq i)) hCell hDisjoint
    Dq hDq V hV Vc hVc hVrep Uic UiL2 hUiDomain hUiRep hUicont hUibdry hUiFace
    hZeroTrace Vprime Vprimec hrep hout hin hpatch
  have henergy := (prop_gluing_replacement_energy (Ls iQ).form.toClosedForm (Ls iQ).gamma
    m (fun i => z (iq i)) (fun i => rad (iq i)) (fun i => hr (iq i)) hCell hDisjoint
    Dq hDq V hV Vc hVc hVrep Uic UiL2 hUiDomain hUiRep hUicont hUibdry hUiOrth
    Lam hUiEnergy hZeroTrace Vprime Vprimec hrep hout hin hpatch hloc).2
  have hformula : (fun x => Vc x + ∑ i : Fin m,
      (cubes (iq i) : Set (SpatialCoordinates d)).indicator (fun y => Ui i y - Vc y) x) =
      Vprimec := by
    funext x
    apply congrArg (fun s : ℝ => Vc x + s)
    apply Finset.sum_congr rfl
    intro i _
    by_cases hxi : x ∈ (cubes (iq i) : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hxi, Set.indicator_of_mem hxi]
      change Ui i x - Vc x = (cubes (iQcell i) : Set (SpatialCoordinates d)).indicator (Ui i) x - Vc x
      rw [Set.indicator_of_mem (hqParent i hxi)]
    · rw [Set.indicator_of_notMem hxi, Set.indicator_of_notMem hxi]
  refine ⟨Lam, Ui, UiL2, Vprime, ?_⟩
  change (∀ i, ∃ U, aux_mfd_prop_gluing_trace_package d hd M H (fun n => env n omega) cutoff
    (z (iq i)) (rad (iq i)) (hr (iq i)) (z (iQcell i)) (rad (iQcell i)) (hr (iQcell i))
    (hz i) (hrad i) (S (iQcell i)) (Gs (iQcell i)) (Ls (iQcell i)) E Cext beta alpha Vc (Lam i) U (Ui i)) ∧ _
  refine ⟨fun i => ⟨Ul i, hU i⟩, fun i => ⟨hUiDomain i, hUiRep i⟩,
    hpatch.1, ?_, ?_, henergy.1, henergy.2, hloc.1, hloc.2, ?_⟩
  · rw [hformula]
    exact hpatch.2
  · rw [hformula]
    exact hrep
  · intro zprime rprime hrprime hpartition hface
    obtain ⟨hQ'sub, hcellsub, hcover⟩ := aux_mfd_prop_gluing_partition_geometry d (cubes iQ)
      m (fun i => z (iq i)) (fun i => rad (iq i)) (fun i => hr (iq i)) hCell
      zprime rprime hrprime hpartition
    exact prop_gluing_face_mass d hd (cubes iQ) hQcube (Ls iQ).form.toClosedForm (Ls iQ).gamma
      beta alpha hR.2.2.1.1 hR.2.2.1.2 hR.2.1.1 m (fun i => z (iq i))
      (fun i => rad (iq i)) (fun i => hr (iq i)) hcent htri hCell hEnlarge' hDisjoint
      V hV Vc hVc hVrep hTrace Lam UiL2 Uic hUiDomain hUiRep hUicont hUibdry
      hUiEnergy hUiFace Dq hDq hUiOrth Vprime Vprimec hrep hout hin hpatch.1 hpatch.2
      hloc.1 hloc.2 hface (centeredCube zprime rprime hrprime)
      ⟨zprime, rprime, hrprime, rfl⟩ hQ'sub hcellsub hcover

end Paper
