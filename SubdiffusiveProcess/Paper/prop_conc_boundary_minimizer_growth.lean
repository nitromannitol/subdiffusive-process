import SubdiffusiveProcess.Paper.prop_conc_boundary_glb
import SubdiffusiveProcess.Paper.prop_conc_boundary_measure_growth

/-! Actual local boundary minimizers retaining an eventual finite-energy growth bound.
Only the observation-cell energy measure is bounded; the padded-cube total is not identified with it. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace Paper
noncomputable section

variable {d : ℕ} {hd : 2 ≤ d}
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

include BD BDQ EM hcontract

/-- A controlled boundary sequence has an actual local minimizer with the inherited growth bound. -/
theorem prop_conc_boundary_minimizer_growth
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (EQ : _root_.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure EQ.toClosedForm)
    (q : Set (SpatialCoordinates d))
    (hqcell : q = (centeredCube z r hr : Set (SpatialCoordinates d)))
    (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
    (hkilled : DirichletForm.IsKilledDomain EQ.toClosedForm q Dq)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ a n x ∧ a n x ≤ Lam)
    (b beta : SpatialCoordinates d → ℝ)
    (hbeta : ContDiff ℝ ∞ beta)
    (hbetasupp : HasCompactSupport beta)
    (hbetaQ : tsupport beta ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetab : ∀ x ∈ frontier q, beta x = b x)
    (betaQ : H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetaQfun : betaQ.toFun = beta)
    (betaq : H1Function q)
    (hbetaqfun : betaq.toFun = beta)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNtrace : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      HasZeroTraceDifferenceOn
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k))
        (betaQ.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNcellcont : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ContinuousOn (UN n).toFun
        (closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d))))
    (hUNcellb : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ frontier (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
        (UN n).toFun x = beta x)
    (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (hHcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Hcell k)
    (hCellEnergy : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      energy (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) ≤ Bcell k)
    (hCellGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (hCellHolder : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        ∀ y ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
          |(UN n).toFun x - (UN n).toFun y| ≤ Hcell k * dist x y ^ alpha) ∧
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        |(UN n).toFun x| ≤ Hcell k))
    (A : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z (3 * r) h3r S aC)
    (GN : ℕ → DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (aC n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (hE : ∀ v, EQ.energy v = limitFormEnergy G v)
    (hcore : ∃ C, DirichletForm.IsCoreOn EQ.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (L : ℝ)
    (hResponse : Tendsto (fun n => cellDirichletInfimum (a n) q betaq) atTop (𝓝 L))
    (Bg tg : ℝ)
    (hgrowth : ∀ x ∈ q, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ∀ᶠ n in atTop,
        ((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n).val.2 i y) ^ 2))) (Metric.ball x rho ∩ q) ≤
          ENNReal.ofReal (Bg * rho ^ tg)) :
    ∃ (U : DomainL2 (centeredCube z (3 * r) h3r)) (Uc : SpatialCoordinates d → ℝ),
      U ∈ EQ.toClosedForm.domain ∧
      ContinuousOn Uc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (U : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      (∀ x ∈ frontier q, Uc x = b x) ∧ Gamma.measure U (frontier q) = 0 ∧
      (∀ phi ∈ Dq, EQ.form U phi = 0) ∧
      (Gamma.measure U q).toReal = L ∧
      (∀ V ∈ EQ.toClosedForm.domain, ∀ Vc : SpatialCoordinates d → ℝ,
        ContinuousOn Vc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (V : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
        (∀ x ∈ frontier q, Vc x = b x) →
        (Gamma.measure U q).toReal ≤ (Gamma.measure V q).toReal) ∧
      ∀ x ∈ q, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        Gamma.measure U (Metric.ball x rho ∩ q) ≤ ENNReal.ofReal (Bg * rho ^ tg) := by
  subst hqcell
  obtain ⟨E0, hE0⟩ := aux_prop_boundary_energy_bound z r h3r S a aC hacont haC
    UN UNS hUNrep hcellsub Bcell hCellEnergy
  obtain ⟨sigma, uBar, hsigma, huBar⟩ := Paper.aux_prop_conc_boundary_glb_patch_compactness A UNS E0 hE0
  let A' := Paper.aux_prop_conc_controlled_forms_controls_reindex
    (Paper.aux_prop_conc_boundary_glb_controls_lower_exponent A (min A.t t)
      (lt_min A.t_lower ht) (min_le_left _ _)) sigma
  have hG' : Tendsto (fun n => GN (sigma n)) atTop (𝓝 G) :=
    hConv.comp hsigma.tendsto_atTop
  have hMosco := Paper.prop_conc_controlled_forms hS A' _ G
    (fun n => hGN (sigma n)) hG'
  have hMeasures := Paper.prop_conc_energy_measure_convergence BD BDQ EM hcontract hS A'
    _ G (fun n => hGN (sigma n)) hG' EQ hE hcore Gamma
  have hdom := aux_thm_prop_domain_eq_of_energy EQ.toClosedForm G hE
  have hKilled (k : OddGridIndex d (triadicHalf 1)) :
      ∃ D, DirichletForm.IsKilledDomain EQ.toClosedForm
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) D :=
    ⟨_, DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _⟩
  obtain ⟨U, Uc, hUdom, hUc, hUrep, hUunif, hUb, hUface, hUorth, hUlim, hUmin⟩ :=
    prop_boundary d hd z r hr h3r EQ Gamma _ rfl Dq hkilled S hS
      (fun n => a (sigma n)) (fun n => aC (sigma n))
      (fun n => hacont (sigma n)) (fun n => haC (sigma n)) (fun n => hell (sigma n))
      b beta hbeta hbetasupp hbetaQ hbetab betaQ hbetaQfun betaq hbetaqfun
      (fun n => UN (sigma n)) (fun n => UNS (sigma n)) (fun n => hUNrep (sigma n))
      uBar huBar hcellsub (fun n => hUNharm (sigma n)) (fun n => hUNtrace (sigma n))
      (fun n => hUNcellcont (sigma n)) (fun n => hUNcellb (sigma n))
      (min A.t t) alpha (lt_min A.t_lower ht) ((min_le_right _ _).trans_lt htd)
      halpha halpha1 Bcell Hcell hBcell hHcell (fun n => hCellEnergy (sigma n))
      (fun n k x hx rr hrr hrr1 => Paper.aux_prop_conc_boundary_glb_growth_lower_exponent (hBcell k)
        hrr hrr1 (min_le_right A.t t) (hCellGrowth (sigma n) k x hx rr hrr hrr1))
      (fun n => hCellHolder (sigma n))
      (by simpa only [hE] using hMosco.lower)
      (by simpa only [← hdom, ← hE] using hMosco.recovery)
      (fun _ => A'.K) (fun _ => A'.K_pos.le) A'.K (fun _ => le_rfl)
      (fun w => (A'.coercive 0 w).1) (fun n w => (A'.coercive n w).2)
      A'.interpolation A'.cutoffs hMeasures
      (fun zc rc hrc hsub D hD w hw wc hwc hrep hzero wq hwq =>
        Paper.prop_conc_boundary_truncation d hd z zc (3 * r) rc h3r hrc hsub
          EQ Gamma hcore D hD w hw wc hwc hrep hzero wq hwq)
      hKilled
  have hL : (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal = L :=
    tendsto_nhds_unique hUlim (hResponse.comp hsigma.tendsto_atTop)
  obtain ⟨bc, _hbc, hbarrep, hbarunif⟩ := aux_prop_boundary_uniform_limit z r h3r S
    (fun n => UN (sigma n)) (fun n => UNS (sigma n)) (fun n => hUNrep (sigma n))
    uBar huBar alpha (by linarith only [halpha]) Hcell (fun n => hCellHolder (sigma n))
  have hUbar : U = uBar := by
    apply Lp.ext
    filter_upwards [hUrep, hbarrep,
      ae_restrict_mem (centeredCube z (3 * r) h3r).isOpen.measurableSet] with x hxU hxbar hx
    rw [hxU, hxbar]
    exact tendsto_nhds_unique (hUunif.tendsto_at (subset_closure hx))
      (hbarunif.tendsto_at (subset_closure hx))
  subst U
  refine ⟨uBar, Uc, hUdom, hUc, hUrep, hUb, hUface, hUorth, hL, hUmin, ?_⟩
  let Test := {x : SpatialCoordinates d // x ∈ centeredCube z r hr} ×
    {rho : ℝ // 0 < rho ∧ rho ≤ 1}
  let tests : Test → Set (SpatialCoordinates d) :=
    fun b => Metric.ball b.1.val b.2.val ∩ (centeredCube z r hr : Set (SpatialCoordinates d))
  let muN : ℕ → Measure (SpatialCoordinates d) := fun n =>
    (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
        ∑ i : Fin d, ((UNS (sigma n)).val.2 i y) ^ 2))
  have hpass := prop_conc_boundary_measure_growth
    (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (lane2_isCompact_closure_centeredCube z h3r) muN (Gamma.measure uBar) E0
    (fun n => aux_prop_boundary_supp _ _)
    (fun n => by
      change _ ≤ ENNReal.ofReal E0
      rw [aux_prop_boundary_mass_univ S (aC (sigma n)) (UNS (sigma n))]
      exact ENNReal.ofReal_le_ofReal (hE0 (sigma n)))
    (fun mu sig hmfin hmsupp hsig hweak =>
      (hMeasures.2.1 uBar (fun n => UNS (sigma n)) E0 mu sig hmfin hmsupp hsig
        huBar (fun n => hE0 (sigma n)) hweak).2)
    tests (fun _ => Metric.isOpen_ball.inter (centeredCube z r hr).isOpen)
    (fun b => ENNReal.ofReal (Bg * b.2.val ^ tg))
    (fun b => hsigma.tendsto_atTop.eventually
      (hgrowth b.1.val b.1.property b.2.val b.2.property.1 b.2.property.2))
  intro x hx rho hrho hrho1
  exact hpass (⟨x, hx⟩, ⟨rho, hrho, hrho1⟩)

end
end Paper
