module

public import SubdiffusiveProcess.Paper.Support.B7cBoundaryCompactness
public import SubdiffusiveProcess.Paper.Support.B7cCutoffExponent

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Deterministic assembly from finite smooth interpolants and proved native bounds.
The public principal derives every one of the finite bounds from the actual catalogue. -/
theorem aux_mfd_prop_boundary_from_native_bounds
    (d : ℕ) (hd : 2 ≤ d) (zq : SpatialCoordinates d) (rq : ℝ)
    (hrq : 0 < rq) (h3rq : 0 < 3 * rq)
    (S0 : ResponseSpace (centeredCube zq (3 * rq) h3rq))
    (hS0 : S0.space = killedSobolevGraph (centeredCube zq (3 * rq) h3rq))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube zq (3 * rq) h3rq))
    (hCont : ∀ n, ContinuousOn (a n) (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))))
    (hAe : ∀ n, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))] a n)
    (hEll : ∀ n, ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)),
        lo ≤ a n x ∧ a n x ≤ hi)
    (Phi : SpatialCoordinates d → ℝ)
    (hSource : ContDiff ℝ ∞ Phi ∧ HasCompactSupport Phi ∧
      tsupport Phi ⊆ (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
    (betaQ : H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
    (hBeta : betaQ.toFun = Phi)
    (UN : ℕ → H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
    (UNS : ℕ → S0.space)
    (hUNrep : ∀ n, (UNS n).val = sobolevDataOfH1 (UN n))
    (hFinite : ∀ k : OddGridIndex d (triadicHalf 1),
      let W := oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k
      let hsub := oddGridCell_subset zq h3rq (triadicHalf 1) k
      ∀ n,
        IsWeaklyHarmonicOn (a n) (W : Set (SpatialCoordinates d)) ((UN n).restrict W.isOpen hsub) ∧
        HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d))
          ((UN n).restrict W.isOpen hsub) (betaQ.restrict W.isOpen hsub) ∧
        ContinuousOn (UN n).toFun (closure (W : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier (W : Set (SpatialCoordinates d)), (UN n).toFun x = Phi x))
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBH : ∀ k, 0 ≤ Bcell k ∧ 0 ≤ Hcell k)
    (hNative : ∀ k : OddGridIndex d (triadicHalf 1), ∀ n,
      energy (a n) (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k).isOpen
          (oddGridCell_subset zq h3rq (triadicHalf 1) k)) ≤ Bcell k ∧
      (∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
        ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
          ((volume.restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, ((UN n).grad y i) ^ 2)))
            (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t)) ∧
      (∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
          |(UN n).toFun x - (UN n).toFun y| ≤ Hcell k * dist x y ^ alpha) ∧
      (∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
        |(UN n).toFun x| ≤ Hcell k))
    (G0 : DomainL2 (centeredCube zq (3 * rq) h3rq) →L[ℝ] DomainL2 (centeredCube zq (3 * rq) h3rq))
    (L : aux_limit_form_package_limit_side d hd zq (3 * rq) h3rq S0 G0 aC) :
  ∃ (U : DomainL2 (centeredCube zq (3 * rq) h3rq)) (Uc : SpatialCoordinates d → ℝ),
    U ∈ L.form.domain ∧
    ContinuousOn Uc (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) ∧
    (U : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))] Uc ∧
    TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
      (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) ∧
    (∀ x ∈ frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d)), Uc x = Phi x) ∧
    L.gamma.measure U (frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d))) = 0 ∧
    (∀ phi : DomainL2 (centeredCube zq (3 * rq) h3rq),
      phi ∈ L.form.toClosedForm.killedCoreClosure
        (centeredCube zq rq hrq : Set (SpatialCoordinates d)) → L.form.form U phi = 0) ∧
    (∃ betaq : H1Function (centeredCube zq rq hrq : Set (SpatialCoordinates d)),
      betaq.toFun = Phi ∧
      Tendsto (fun n => cellDirichletInfimum
        (a n)
        (centeredCube zq rq hrq : Set (SpatialCoordinates d)) betaq) atTop
        (𝓝 ((L.gamma.measure U (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal))) ∧
    (∀ V ∈ L.form.domain, ∀ Vc : SpatialCoordinates d → ℝ,
      ContinuousOn Vc (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) →
      (V : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))] Vc →
      (∀ x ∈ frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d)), Vc x = Phi x) →
      (L.gamma.measure U (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal ≤
        (L.gamma.measure V (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal)
 := by
  classical
  let Q := centeredCube zq (3 * rq) h3rq
  let q := centeredCube zq rq hrq
  let hsub := fun k : OddGridIndex d (triadicHalf 1) =>
    oddGridCell_subset zq h3rq (triadicHalf 1) k
  have hHarm := fun n k => (hFinite k n).1
  have hTrace := fun n k => (hFinite k n).2.1
  have hCellCont := fun n k => (hFinite k n).2.2.1
  have hBdry := fun n k => (hFinite k n).2.2.2
  have hEnergy := fun n k => (hNative k n).1
  have hHolder := fun n k => (hNative k n).2.2
  have hAlpha : 0 < alpha := by linarith only [halpha]
  obtain ⟨uBar, Ubarc, huDom, huCont, huRep, huUniform, huL2⟩ :=
    aux_mfd_prop_boundary_solution_limit d hd zq rq h3rq S0 hS0 a aC hCont hAe UN UNS
      hUNrep hsub hHarm Phi hBdry alpha hAlpha Bcell Hcell hEnergy hHolder G0 L
  obtain ⟨A⟩ := aux_limit_form_package_controls_of_bounds hd zq (3 * rq) h3rq S0 G0 aC L.bounds
  have hMosco := limit_form_package_controls hS0 A L.response G0 L.response_eq L.response_tendsto
  have hLower : ∀ (vn : ℕ → S0.space) (v : DomainL2 Q),
      (∀ test, Tendsto (fun n => inner ℝ test (vn n).val.1) atTop (𝓝 (inner ℝ test v))) →
      L.form.energy v ≤ liminf (fun n => (responseForm S0 (aC n) (vn n) (vn n) : EReal)) atTop := by
    intro vn v hv
    rw [L.energy_eq]
    exact hMosco.lower vn v hv
  have hRecovery : ∀ v ∈ L.form.domain, ∃ vn : ℕ → S0.space,
      Tendsto (fun n => ((vn n).val.1,
        (responseForm S0 (aC n) (vn n) (vn n) : EReal))) atTop (𝓝 (v, L.form.energy v)) := by
    intro v hv
    have hv' : v ∈ limitFormDomain G0 := by
      rw [← aux_limit_form_package_domain_eq_of_energy _ G0 L.energy_eq]
      exact hv
    simpa only [L.energy_eq] using hMosco.recovery v hv'
  have hEM := aux_mfd_prop_boundary_energy_measures hd zq (3 * rq) h3rq S0 hS0 aC G0 A
    L.response L.response_eq L.response_tendsto L.form L.energy_eq L.core L.gamma
  let t0 := min t A.t
  have ht0 : (d : ℝ) - 1 < t0 := lt_min ht A.t_lower
  have ht0d : t0 < (d : ℝ) := (min_le_left _ _).trans_lt htd
  have hGrowth : ∀ n k,
      ∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
      ((volume.restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((UNS n).val.2 i y) ^ 2)))
        (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t0) := by
    intro n k x hx rr hrr hrr1
    have hData := congrArg Prod.snd (hUNrep n)
    have hgrad : ∀ i : Fin d, ((UNS n).val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fun y => (UN n).grad y i := by
      intro i
      rw [hData]
      exact sobolevDataOfH1_snd_coeFn (UN n) i
    have hden : (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((UNS n).val.2 i y) ^ 2))
        =ᵐ[volume.restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))]
        (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, ((UN n).grad y i) ^ 2)) := by
      have hg := ae_all_iff.mpr hgrad
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hsub k) (hAe n),
        ae_restrict_of_ae_restrict_of_subset (hsub k) hg] with y hy hgy
      simp only [hy, hgy]
    rw [withDensity_congr_ae hden]
    exact ((hNative k n).2.1 x hx rr hrr hrr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hrr hrr1 (min_le_left _ _)) (hBH k).1))
  have hCutoffs := aux_mfd_prop_boundary_cutoffs_lower_exponent hd zq rq h3rq S0 aC A
    t0 (min_le_right _ _)
  let Dq := L.form.toClosedForm.killedCoreClosure (q : Set (SpatialCoordinates d))
  have hDq := _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure
    L.form.toClosedForm (q : Set (SpatialCoordinates d))
  have hKilled : ∀ k : OddGridIndex d (triadicHalf 1),
      ∃ D : Submodule ℝ (DomainL2 Q), _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain L.form.toClosedForm
        (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)) D :=
    fun k => ⟨_, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _⟩
  have hqQ : (q : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith)
  let betaq := betaQ.restrict q.isOpen hqQ
  have hBetaq : betaq.toFun = Phi := hBeta
  obtain ⟨U, Uc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := prop_boundary d hd zq rq hrq h3rq
    L.form L.gamma (q : Set (SpatialCoordinates d)) rfl Dq hDq S0 hS0 a aC hCont hAe hEll
    (Phi) (Phi) hSource.1 hSource.2.1 hSource.2.2 (fun _ _ => rfl)
    betaQ hBeta betaq hBetaq UN UNS hUNrep uBar huL2 hsub hHarm hTrace hCellCont hBdry
    t0 alpha ht0 ht0d halpha halpha1 Bcell Hcell
    (fun k => (hBH k).1) (fun k => (hBH k).2) hEnergy hGrowth hHolder
    hLower hRecovery (fun _ => A.K) (fun _ => A.K_pos.le) A.K (fun _ => le_rfl)
    (fun w => (A.coercive 0 w).1) (fun n w => (A.coercive n w).2) A.interpolation hCutoffs hEM
    (fun zc rc hrc hqc D hD w hw wc hwc hwa h0 wq hwq =>
      aux_mfd_prop_boundary_zero_trace d hd zq zc (3 * rq) rc h3rq hrc hqc L.form L.gamma
        L.core D hD w hw wc hwc hwa h0 wq hwq) hKilled
  exact ⟨U, Uc, h1, h2, h3, h4, h5, h6, h7, ⟨betaq, hBetaq, h8⟩, h9⟩

end SubdiffusiveProcess.Paper
