module

public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Section9.FiniteCellHarmonicUniqueness
public import SubdiffusiveProcess.Compactness.UniqueUniformCluster
public import SubdiffusiveProcess.Compactness.CubeUniformExtraction
public import SubdiffusiveProcess.Paper.Support.B7cEnergyMeasureSupport
public import SubdiffusiveProcess.Paper.Support.B7cTruncationSupport

@[expose] public section





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Localized recovery passes harmonic orthogonality on any open cell to an
L2 cluster. This proof step will be consumed internally by the B7c principal. -/
theorem aux_mfd_prop_boundary_harmonic_core_on_open {d : ℕ} (hd : 2 ≤ d)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
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
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (W : Set (SpatialCoordinates d)) (hWo : IsOpen W)
    (hWQ : W ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ n : ℕ, IsWeaklyHarmonicOn (a n) W
      ((UN n).restrict hWo hWQ))
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (hLower : ∀ (vn : ℕ → S.space)
      (v : DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ f : DomainL2 (centeredCube z (3 * r) h3r),
        Tendsto (fun n => inner ℝ f (vn n).val.1) atTop
          (𝓝 (inner ℝ f v))) →
      EQ.toClosedForm.energy v ≤
        Filter.liminf (fun n =>
          (responseForm S (aC n) (vn n) (vn n) : EReal)) atTop)
    (hRecovery : ∀ v ∈ EQ.toClosedForm.domain, ∃ vn : ℕ → S.space,
      Tendsto (fun n => ((vn n).val.1,
        (responseForm S (aC n) (vn n) (vn n) : EReal))) atTop
        (𝓝 (v, EQ.toClosedForm.energy v)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 +
          volume.real (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
              (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        KN n * responseForm S (aC n) w w)
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (hC : ∀ (u v : DomainL2 (centeredCube z (3 * r) h3r))
          (uN vN : ℕ → S.space) (E0 : ℝ),
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        v ∈ EQ.toClosedForm.domain →
        Tendsto (fun n => ((vN n).val.1,
          (responseForm S (aC n) (vN n) (vN n) : EReal))) atTop
          (𝓝 (v, EQ.toClosedForm.energy v)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
              φ x * ((aC n).val x *
                ∑ i : Fin d,
                  ((uN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x) *
                  ((vN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x))) atTop
            (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ)))
    (E0 : ℝ) (hE0 : ∀ n : ℕ, responseForm S (aC n) (UNS n) (UNS n) ≤ E0)
    (hdom : uBar ∈ EQ.toClosedForm.domain) :
    ∀ w : DomainL2 (centeredCube z (3 * r) h3r),
      EQ.toClosedForm.MemCoreOn W w →
        EQ.form uBar w = 0 := by
  intro w hw
  have hw' := hw.2
  obtain ⟨f, -, hfcs, hfq, hwf⟩ := hw'
  have hwE : EQ.toClosedForm.energy w < ⊤ := by
    rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem _ hw.1]
    exact EReal.coe_lt_top _
  have hrec := hRecovery w hw.1
  obtain ⟨wN, hwN⟩ := hrec
  have hloc := aux_prop_boundary_local_recovery hd hInterp z (3 * r) h3r t ht S hS aC
    EQ.toClosedForm.energy hLower KN hKN Kstar hKstar hfrac hcoercive hcutoffs W hWo w
    (_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_nonneg _ w) hwE wN hwN f hfcs hfq (hfq.trans hWQ) hwf
  obtain ⟨vN, Kc, hKc, hKq, hKQ, hvN, hvan⟩ := hloc
  have hzero : ∀ n, responseForm S (aC n) (UNS n) (vN n) = 0 := by
    intro n
    refine aux_prop_boundary_orth_supported S hS (aC n) (UNS n) W hWo ?_ Kc hKc hKq hKQ (vN n)
      (hvan n).1 (hvan n).2
    intro ζ hζS hζ
    exact aux_prop_boundary_orth_smooth z r h3r S a aC hacont haC UN UNS hUNrep W
      hWo hWQ n (hUNharm n) ζ hζ hζS
  have hlim := hC uBar w UNS vN E0 hUNL2 hE0 hw.1 hvN (fun _ => 1) continuousOn_const
  have hlim' : Tendsto (fun n => responseForm S (aC n) (UNS n) (vN n)) atTop
      (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross uBar w) Set.univ (fun _ => 1))) :=
    hlim.congr fun n => aux_prop_boundary_resp_integral S (aC n) (UNS n) (vN n)
  have hlim0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross uBar w) Set.univ (fun _ => 1))) :=
    hlim'.congr hzero
  have hval := tendsto_nhds_unique hlim0 tendsto_const_nhds
  rw [aux_prop_boundary_signedIntegralOn_one, Gamma.cross_univ uBar hdom w hw.1] at hval
  exact hval

/-- Truncation on every cell decomposes a difference with common boundary
values into killed differences. Cellwise harmonicity and inverse coercivity
then identify two possible clusters. -/
theorem aux_mfd_prop_boundary_cluster_unique
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (hEQ : ∀ w, EQ.toClosedForm.energy w = limitFormEnergy G w)
    (D : OddGridIndex d (triadicHalf 1) → Submodule ℝ
      (DomainL2 (centeredCube z (3 * r) h3r)))
    (hD : ∀ k, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ.toClosedForm
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) (D k))
    (hTruncate : ∀ k, ∀ w ∈ EQ.toClosedForm.domain,
      ∀ wc : SpatialCoordinates d → ℝ,
      ContinuousOn wc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
      (w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] wc →
      (∀ x ∈ frontier (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)), wc x = 0) →
      ∀ wq : DomainL2 (centeredCube z (3 * r) h3r),
      (wq : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          (closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
            Set (SpatialCoordinates d))).indicator wc → wq ∈ D k)
    (beta Uc Vc : SpatialCoordinates d → ℝ)
    (U V : DomainL2 (centeredCube z (3 * r) h3r))
    (hU : U ∈ EQ.toClosedForm.domain) (hV : V ∈ EQ.toClosedForm.domain)
    (hUc : ContinuousOn Uc
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hVc : ContinuousOn Vc
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hUrep : (U : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc)
    (hVrep : (V : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc)
    (hUb : ∀ k, ∀ x ∈ frontier
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)), Uc x = beta x)
    (hVb : ∀ k, ∀ x ∈ frontier
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)), Vc x = beta x)
    (hUorth : ∀ k w, w ∈ D k → EQ.form U w = 0)
    (hVorth : ∀ k w, w ∈ D k → EQ.form V w = 0) : U = V := by
  classical
  let Q := centeredCube z (3 * r) h3r
  let cell : OddGridIndex d (triadicHalf 1) → Set (SpatialCoordinates d) := fun k =>
    (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
  let wc : SpatialCoordinates d → ℝ := fun x => Uc x - Vc x
  have hwrep : ((U - V : DomainL2 Q) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc := by
    filter_upwards [Lp.coeFn_sub U V, hUrep, hVrep] with x hx h1 h2
    simp only [hx, Pi.sub_apply, h1, h2, wc]
  have hwb : ∀ k, ∀ x ∈ frontier (cell k), wc x = 0 := by
    intro k x hx
    simp only [wc, hUb k x hx, hVb k x hx, sub_self]
  have hex : ∀ k, ∃ wq : DomainL2 Q,
      (wq : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (closure (cell k)).indicator wc :=
    fun k => aux_prop_boundary_indicator_toLp (closure (cell k))
      isClosed_closure.measurableSet (U - V) wc hwrep
  choose wi hwiclosed using hex
  have hwi : ∀ k, wi k ∈ D k := fun k =>
    hTruncate k (U - V) (EQ.domain.sub_mem hU hV) wc (hUc.sub hVc) hwrep (hwb k)
      (wi k) (hwiclosed k)
  have hwiopen : ∀ k, (wi k : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (cell k).indicator wc := by
    intro k
    refine (hwiclosed k).trans (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ cell k
    · rw [Set.indicator_of_mem (subset_closure hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      by_cases hxc : x ∈ closure (cell k)
      · rw [Set.indicator_of_mem hxc]
        apply hwb k x
        rw [frontier, (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen.interior_eq]
        exact ⟨hxc, hx⟩
      · exact Set.indicator_of_notMem hxc wc
  have hcover : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), ∃ k, x ∈ cell k := by
    filter_upwards [ae_restrict_of_ae (oddGrid_union_ae_eq z h3r (triadicHalf 1)),
      ae_restrict_mem Q.isOpen.measurableSet] with x hx hQx
    have hUnion : x ∈ ⋃ k, cell k := by
      change (⋃ k : OddGridIndex d (triadicHalf 1),
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))) x
      exact hx.mpr hQx
    exact Set.mem_iUnion.mp hUnion
  have hsub : U - V = ∑ k, wi k :=
    SubdiffusiveProcess.Section9.eq_sum_of_ae_indicator_partition cell
      (oddGridCell_pairwiseDisjoint z h3r (triadicHalf 1)) hcover (U - V) wc hwrep wi hwiopen
  exact SubdiffusiveProcess.Section9.eq_of_orthogonal_finite_decomposition EQ.toClosedForm G hEQ D
    (fun k => (hD k).le_domain) U V hU hV hUorth hVorth wi hwi hsub

/-- Compactness and cellwise harmonic uniqueness construct the full L2
limit. This auxiliary has no supplied limit, convergence or uniqueness premise. -/
theorem aux_mfd_prop_boundary_solution_limit
    (d : ℕ)
    (hd : 2 ≤ d)
    (z : SpatialCoordinates d)
    (r : ℝ)
    (h3r : 0 < 3 * r)
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
    (beta : SpatialCoordinates d → ℝ)
    (hUNcellb : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ frontier (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
        (UN n).toFun x = beta x)
    (alpha : ℝ) (halpha : 0 < alpha)
    (Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hCellEnergy : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      energy (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) ≤ Bcell k)
    (hCellHolder : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        ∀ y ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
          |(UN n).toFun x - (UN n).toFun y| ≤ Hcell k * dist x y ^ alpha) ∧
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        |(UN n).toFun x| ≤ Hcell k))
    (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (L : aux_limit_form_package_limit_side d hd z (3 * r) h3r S G aC) :
    ∃ (U : DomainL2 (centeredCube z (3 * r) h3r)) (Uc : SpatialCoordinates d → ℝ),
      U ∈ L.form.domain ∧
      ContinuousOn Uc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (U : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      Tendsto (fun n => (UNS n).val.1) atTop (𝓝 U) := by
  classical
  let Q := centeredCube z (3 * r) h3r
  let cell : OddGridIndex d (triadicHalf 1) → Set (SpatialCoordinates d) :=
    fun k => (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
  let D : OddGridIndex d (triadicHalf 1) → Submodule ℝ (DomainL2 Q) :=
    fun k => L.form.toClosedForm.killedCoreClosure (cell k)
  have hD : ∀ k, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain L.form.toClosedForm (cell k) (D k) :=
    fun k => _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _
  have hTruncate : ∀ k, ∀ w ∈ L.form.domain, ∀ wc : SpatialCoordinates d → ℝ,
      ContinuousOn wc (closure (Q : Set (SpatialCoordinates d))) →
      (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc →
      (∀ x ∈ frontier (cell k), wc x = 0) →
      ∀ wq : DomainL2 Q,
      (wq : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (closure (cell k)).indicator wc → wq ∈ D k := by
    intro k w hw wc hwc hrep hzero wq hwq
    exact (aux_mfd_prop_boundary_zero_trace d hd z
      (oddGridCenter z (3 * r) (triadicHalf 1) k)
      (3 * r) (3 * r / (2 * (triadicHalf 1 : ℝ) + 1)) h3r
      (div_pos h3r (by positivity)) (hcellsub k) L.form L.gamma L.core
      (D k) (hD k) w hw wc hwc hrep hzero wq hwq).1
  let F : ℕ → SpatialCoordinates d → ℝ := fun n => (UN n).toFun
  let C : OddGridIndex d (triadicHalf 1) → Set (SpatialCoordinates d) :=
    fun k => closure (cell k)
  have hcover : (⋃ k, C k) = closure (Q : Set (SpatialCoordinates d)) :=
    oddGridCell_closure_iUnion_eq_closure_centeredCube z h3r (triadicHalf 1)
  have hequi : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ eps > 0,
      ∃ delta > 0, ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
        dist y x < delta → ∀ n, |F n y - F n x| < eps := by
    intro x _ eps heps
    obtain ⟨delta, hdelta, h⟩ := aux_prop_boundary_equi_holder C
      (fun _ => isClosed_closure) F Hcell alpha halpha
      (fun n k => (hCellHolder n k).1) x eps heps
    exact ⟨delta, hdelta, fun y hy => h y (hcover ▸ hy)⟩
  have hbd : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ n,
      |F n x| ≤ ∑ k, |Hcell k| := by
    intro x hx n
    exact aux_prop_boundary_cover_bound C F Hcell
      (fun n k => (hCellHolder n k).2) x (hcover ▸ hx) n
  have hW : ∀ n, ((UNS n).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] F n := by
    intro n
    have h := congrArg Prod.fst (hUNrep n)
    change (UNS n).val.1 = (sobolevDataOfH1 (UN n)).1 at h
    rw [h]
    exact sobolevDataOfH1_fst_coeFn (UN n)
  obtain ⟨E0, hE0⟩ := aux_prop_boundary_energy_bound z r h3r S a aC hacont haC UN UNS
    hUNrep hcellsub Bcell hCellEnergy
  obtain ⟨A⟩ := aux_limit_form_package_controls_of_bounds hd z (3 * r) h3r S G aC L.bounds
  let P : (SpatialCoordinates d → ℝ) → Prop := fun gc =>
    ∃ u : DomainL2 Q, u ∈ L.form.domain ∧
      ContinuousOn gc (closure (Q : Set (SpatialCoordinates d))) ∧
      (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] gc ∧
      (∀ k, ∀ x ∈ frontier (cell k), gc x = beta x) ∧
      (∀ k w, w ∈ D k → L.form.form u w = 0)
  have hcompact : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ (ms : ℕ → ℕ) (gc : SpatialCoordinates d → ℝ), P gc ∧
        TendstoUniformlyOn (fun n => F (ns (ms n))) gc atTop
          (closure (Q : Set (SpatialCoordinates d))) := by
    intro ns hns
    obtain ⟨ms, u, gc, hms, hgc, hurep, hunif, huL2⟩ :=
      SubdiffusiveProcess.Compactness.exists_cube_uniform_l2_cluster z (3 * r) h3r F
        (fun n => (UNS n).val.1) hW _ hequi hbd ns
    let sigma : ℕ → ℕ := fun n => ns (ms n)
    have hsigma : Tendsto sigma atTop atTop := hns.comp hms.tendsto_atTop
    let As := aux_limit_form_package_controls_reindex A sigma
    have hM := limit_form_package_controls hS As (fun n => L.response (sigma n)) G
      (fun n => L.response_eq (sigma n)) (L.response_tendsto.comp hsigma)
    have hLower : ∀ (vn : ℕ → S.space) (v : DomainL2 Q),
        (∀ f, Tendsto (fun n => inner ℝ f (vn n).val.1) atTop (𝓝 (inner ℝ f v))) →
        L.form.energy v ≤ liminf (fun n =>
          (responseForm S (aC (sigma n)) (vn n) (vn n) : EReal)) atTop := by
      intro vn v hw
      rw [L.energy_eq]
      exact hM.lower vn v hw
    have hRecovery : ∀ v ∈ L.form.domain, ∃ vn : ℕ → S.space,
        Tendsto (fun n => ((vn n).val.1,
          (responseForm S (aC (sigma n)) (vn n) (vn n) : EReal))) atTop
          (𝓝 (v, L.form.energy v)) := by
      intro v hv
      have hv' : v ∈ limitFormDomain G := by
        rw [← aux_limit_form_package_domain_eq_of_energy _ G L.energy_eq]
        exact hv
      simpa only [L.energy_eq] using hM.recovery v hv'
    have hEM := aux_mfd_prop_boundary_energy_measures hd z (3 * r) h3r S hS
      (fun n => aC (sigma n)) G As (fun n => L.response (sigma n))
      (fun n => L.response_eq (sigma n)) (L.response_tendsto.comp hsigma)
      L.form L.energy_eq L.core L.gamma
    have hdom : u ∈ L.form.domain := aux_prop_boundary_limit_mem_domain
      L.form.toClosedForm S (fun n => aC (sigma n)) hLower
      (fun n => UNS (sigma n)) u huL2 E0 (fun n => hE0 (sigma n))
    have hboundary : ∀ k, ∀ x ∈ frontier (cell k), gc x = beta x := by
      intro k x hx
      have hxQ : x ∈ closure (Q : Set (SpatialCoordinates d)) :=
        closure_mono (hcellsub k) (frontier_subset_closure hx)
      have h1 := hunif.tendsto_at hxQ
      have h2 : Tendsto (fun _ : ℕ => beta x) atTop (𝓝 (gc x)) :=
        h1.congr (fun n => hUNcellb (sigma n) k x hx)
      exact tendsto_nhds_unique h2 tendsto_const_nhds
    have horth : ∀ k w, w ∈ D k → L.form.form u w = 0 := by
      intro k
      apply aux_prop_boundary_form_zero_of_core (hD k) hdom
      exact aux_mfd_prop_boundary_harmonic_core_on_open hd As.interpolation z r h3r
        L.form L.gamma S hS (fun n => a (sigma n)) (fun n => aC (sigma n))
        (fun n => hacont (sigma n)) (fun n => haC (sigma n))
        (fun n => UN (sigma n)) (fun n => UNS (sigma n))
        (fun n => hUNrep (sigma n)) u huL2 (cell k)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)
        (fun n => hUNharm (sigma n) k) As.t As.t_lower hLower hRecovery
        (fun _ => As.K) (fun _ => As.K_pos.le) As.K (fun _ => le_rfl)
        (fun w => (As.coercive 0 w).1) (fun n w => (As.coercive n w).2)
        As.cutoffs hEM.2.2 E0 (fun n => hE0 (sigma n)) hdom
    exact ⟨ms, gc, ⟨u, hdom, hgc, hurep, hboundary, horth⟩, hunif⟩
  have hunique : ∀ f g, P f → P g → Set.EqOn f g (closure (Q : Set (SpatialCoordinates d))) := by
    rintro f g ⟨u, hu, hf, huf, hub, huo⟩ ⟨v, hv, hg, hvg, hvb, hvo⟩
    have huv := aux_mfd_prop_boundary_cluster_unique z r h3r L.form G L.energy_eq
      D hD hTruncate beta f g u v hu hv hf hg huf hvg hub hvb huo hvo
    subst v
    exact aux_prop_boundary_eqOn_closure_of_ae z (3 * r) h3r f g hf hg (huf.symm.trans hvg)
  obtain ⟨gc, ⟨u, hu, hgc, hurep, -, -⟩, hunif⟩ :=
    SubdiffusiveProcess.Compactness.exists_tendstoUniformlyOn_of_unique_clusters F
      (closure (Q : Set (SpatialCoordinates d))) P hcompact hunique
  exact ⟨u, gc, hu, hgc, hurep, hunif,
    cube_tendsto_of_uniformly_on z h3r F (fun n => (UNS n).val.1) hW gc u hurep
      (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hunif)⟩

end SubdiffusiveProcess.Paper
