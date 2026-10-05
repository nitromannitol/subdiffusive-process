module

public import SubdiffusiveProcess.Paper.goodext_cutoff_trace_response
public import SubdiffusiveProcess.Paper.inputs_classical_elliptic_boundary_continuity_cube
public import SubdiffusiveProcess.Sobolev.HarmonicTraceCompactness
public import SubdiffusiveProcess.Sobolev.WeightedHarmonicityTransfer
public import SubdiffusiveProcess.Sobolev.GoodextHolderLimit
public import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A uniform closed-cube `C^alpha` bound makes each finite trace bank equicontinuous. -/
theorem aux_goodext_harmonic_trace_bank_equicontinuous
    {d : ℕ} (alpha : ℝ) (halpha : 0 < alpha) (C : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m)
    (S : Set (SpatialCoordinates d)) (hS : IsCompact S)
    (F : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (hcont : ∀ m n, ContinuousOn (F m n) S)
    (hreg : ∀ m n, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S (F m n) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S (F m n) ≤ C m) :
    ∀ m, Equicontinuous (fun n (x : S) => F m n x) := by
  intro m x
  have hCm : 0 ≤ C m := hC m
  apply Metric.equicontinuousAt_iff.mpr
  intro eps heps
  have hdiff : ∀ n, ∀ x' ∈ S, ∀ y' ∈ S,
      |F m n x' - F m n y'| ≤ C m *
        (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ alpha := by
    intro n x' hx' y' hy'
    have hp := aux_lem_goodext_pointwise_of_cAlpha alpha (C m) halpha S hS
      (F m n) (hcont m n) (hreg m n).1 (hreg m n).2
    exact hp.2.2 x' hx' y' hy'
  have hmetric : ∀ n, ∀ x' ∈ S, ∀ y' ∈ S,
      |F m n x' - F m n y'| ≤ C m * (Real.sqrt d * dist x' y') ^ alpha := by
    intro n x' hx' y' hy'
    have h := hdiff n x' hx' y' hy'
    have heucl := aux_lem_goodext_euclid_le x' y'
    have hrpow :
        (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ alpha ≤
          (Real.sqrt d * dist x' y') ^ alpha :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) heucl halpha.le
    exact h.trans (mul_le_mul_of_nonneg_left hrpow hCm)
  have h_inner_cont : ContinuousAt (fun t : ℝ => (Real.sqrt d : ℝ) * t) 0 := by
    have hc : ContinuousAt (fun _ : ℝ => (Real.sqrt d : ℝ)) 0 := continuous_const.continuousAt
    exact hc.mul continuousAt_id
  have h_inner : Tendsto (fun t : ℝ => Real.sqrt d * t) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using h_inner_cont.tendsto
  have h_power : Tendsto (fun t : ℝ => t ^ alpha) (𝓝 0) (𝓝 (0 ^ alpha)) :=
    (Real.continuousAt_rpow_const 0 alpha (Or.inr halpha.le)).tendsto
  have h_tendsto : Tendsto (fun t : ℝ => C m * (Real.sqrt d * t) ^ alpha)
      (𝓝 0) (𝓝 0) := by
    have hscaled := Tendsto.const_mul (C m) (h_power.comp h_inner)
    simpa only [Real.zero_rpow (ne_of_gt halpha), mul_zero] using! hscaled
  have h_event : ∀ᶠ t in 𝓝 (0 : ℝ), C m * (Real.sqrt d * t) ^ alpha < eps :=
    h_tendsto.eventually (gt_mem_nhds heps)
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp h_event
  refine ⟨delta, hdelta, ?_⟩
  intro y hy n
  have hdist : dist y x < delta := by simpa only [dist_comm] using hy
  have hmem : dist y x ∈ Metric.ball (0 : ℝ) delta := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_nonneg dist_nonneg] using! hdist
  have hsmall := hball hmem
  have hbound := hmetric n x x.property y y.property
  calc
    dist (F m n x) (F m n y) = |F m n x - F m n y| := Real.dist_eq _ _
    _ ≤ C m * (Real.sqrt d * dist x y) ^ alpha := hbound
    _ < eps := by simpa only [dist_comm] using! hsmall

/-- The actual Hölder trace has a finite-cutoff minimizer bank with exact boundary values, response bounds, and a uniformly convergent subsequence. -/
theorem goodext_harmonic_trace_bank
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (Sob : SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta alpha : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) (halpha : 0 < alpha)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : ℕ → SpatialCoordinates d → ℝ) (hA : ∀ n, ContDiff ℝ ∞ (A n))
    (haA : ∀ n, (a n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] A n)
    (lam Lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (hbounds : ∀ n x, x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) →
      lam n ≤ A n x ∧ A n x ≤ Lam n)
    (g : SpatialCoordinates d → ℝ)
    (hgc : ContinuousOn g (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hgh : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g)
    (breg : ℕ → weakSobolevGraph (centeredCube z r hr))
    (greg : ℕ → SpatialCoordinates d → ℝ)
    (hgreg : ∀ m, ContinuousOn (greg m)
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hbreg : ∀ m, ((breg m).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] greg m)
    (happrox : TendstoUniformlyOn greg g atTop
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))))
    (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hReg : ∀ m n, ∃ V : SpatialCoordinates d → ℝ,
      ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      ((dirichletMinimizer (killedResponseSpace hP) (a n) (breg m)).val.1 :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) V ∧
      cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) V ≤ C m)
    (Ebound : ℕ → ℝ)
    (hResponse : ∀ n (b : weakSobolevGraph (centeredCube z r hr))
        (B : SpatialCoordinates d → ℝ),
      ContinuousOn B (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
      ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] B) →
      EqOn B g (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) →
      dirichletResponse (killedResponseSpace hP) (a n) b ≤ Ebound n)
    :
    ∃ (b : weakSobolevGraph (centeredCube z r hr))
      (VN : ℕ → SpatialCoordinates d → ℝ) (V : SpatialCoordinates d → ℝ) (ns : ℕ → ℕ),
      StrictMono ns ∧
      ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = g x) ∧
      TendstoUniformlyOn (fun n => VN (ns n)) V atTop
        (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      ∀ n, ContinuousOn (VN n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (((dirichletMinimizer (killedResponseSpace hP) (a n) b).val.1 :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] VN n) ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), VN n x = g x) ∧
        dirichletResponse (killedResponseSpace hP) (a n) b ≤ Ebound n := by
  let W : Set (SpatialCoordinates d) := centeredCube z r hr
  have hWgeom : IsOpenBoundedConvexDomain W := by
    exact isOpenBoundedConvexDomain_centeredCube z hr
  have hWne : W.Nonempty := by
    refine ⟨z, ?_⟩
    change z ∈ Metric.ball z (r / 2)
    exact Metric.mem_ball_self (half_pos hr)
  have hKcompact : IsCompact (closure W) :=
    (centeredCube_isBounded z hr).isCompact_closure

  obtain ⟨b, B, hBcontinuous, hBae, hBtrace⟩ :=
    aux_candidate_holder_harmonic_extension_datum hd Sob beta hbeta z r hr g hgh
  have hBcont : ContinuousOn B (closure W) := by
    exact hBcontinuous.continuousOn

  have hTargetFrozen : ∀ n, ∃ U : SpatialCoordinates d → ℝ,
      ContinuousOn U (closure W) ∧
      (((dirichletMinimizer (killedResponseSpace hP) (a n) b).val.1 :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W] U) ∧
      ∀ x ∈ frontier W, U x = B x := by
    intro n
    exact inputs_classical_elliptic_boundary_continuity_cube hd z r hr rfl hP (a n) b (A n) B
      (hA n).continuous (haA n) ⟨lam n, hlam n, fun x hx => (hbounds n x hx).1⟩ hBcont hBae
  choose VN hVNcont hVNae hVNtrace using hTargetFrozen
  have hVNboundary : ∀ n x, x ∈ frontier W → VN n x = g x := by
    intro n x hx
    exact (hVNtrace n x hx).trans (hBtrace x hx)

  have hResponseBound : ∀ n,
      dirichletResponse (killedResponseSpace hP) (a n) b ≤ Ebound n := by
    intro n
    exact hResponse n b B hBcont hBae (fun x hx => hBtrace x hx)

  have hRegFrozen : ∀ m n, ∃ U : SpatialCoordinates d → ℝ,
      ContinuousOn U (closure W) ∧
      (((dirichletMinimizer (killedResponseSpace hP) (a n) (breg m)).val.1 :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W] U) ∧
      ∀ x ∈ frontier W, U x = greg m x := by
    intro m n
    exact inputs_classical_elliptic_boundary_continuity_cube hd z r hr rfl hP (a n) (breg m)
      (A n) (greg m) (hA n).continuous (haA n)
      ⟨lam n, hlam n, fun x hx => (hbounds n x hx).1⟩
      (hgreg m) (hbreg m)
  choose Wreg hWregcont hWregae hWregtrace using hRegFrozen

  choose R hRcont hRae hRholder hRnorm using hReg
  have hRegEq : ∀ m n, EqOn (R m n) (Wreg m n) (closure W) := by
    intro m n
    have hae : R m n =ᵐ[volume.restrict W] Wreg m n :=
      (hRae m n).symm.trans (hWregae m n)
    exact eqOn_closure_of_ae_eq_restrict
      (centeredCube z r hr).isOpen (hRcont m n) (hWregcont m n) hae
  have hRegboundary : ∀ m n x, x ∈ frontier W → R m n x = greg m x := by
    intro m n x hx
    exact (hRegEq m n (frontier_subset_closure hx)).trans (hWregtrace m n x hx)

  have hspace : (killedResponseSpace hP).space =
      killedSobolevGraph (centeredCube z r hr) := rfl
  have hEuler : ∀ n (bb : weakSobolevGraph (centeredCube z r hr))
      (psi : killedSobolevGraph (centeredCube z r hr)),
      sobolevCoefficientForm (a n)
        (dirichletMinimizer (killedResponseSpace hP) (a n) bb).val psi.val = 0 := by
    intro n bb psi
    have hmem : psi.val ∈ (killedResponseSpace hP).space := hspace.symm ▸ psi.property
    let psiS : (killedResponseSpace hP).space := ⟨psi.val, hmem⟩
    have he := dirichletMinimizer_euler (killedResponseSpace hP) (a n) bb psiS
    change sobolevCoefficientForm (a n)
      (dirichletMinimizer (killedResponseSpace hP) (a n) bb).val psi.val = 0 at he
    exact he

  have hTargetHarmonic : ∀ n, ∃ u : H1Function W,
      u.toFun = (fun x =>
        ((dirichletMinimizer (killedResponseSpace hP) (a n) b).val.1 :
          SpatialCoordinates d → ℝ) x) ∧
      IsWeaklyHarmonicOn (A n) W u := by
    intro n
    exact isWeaklyHarmonicOn_of_sobolevCoefficientForm_zero (a n) (A n) (haA n)
      (dirichletMinimizer (killedResponseSpace hP) (a n) b) (hEuler n b)
  choose u huval huharm using hTargetHarmonic
  have huRep : ∀ n, (u n).toFun =ᵐ[volume.restrict W] VN n := by
    intro n
    filter_upwards [hVNae n] with x hx
    exact (congrFun (huval n) x).trans hx

  have hRegHarmonic : ∀ m n, ∃ u : H1Function W,
      u.toFun = (fun x =>
        ((dirichletMinimizer (killedResponseSpace hP) (a n) (breg m)).val.1 :
          SpatialCoordinates d → ℝ) x) ∧
      IsWeaklyHarmonicOn (A n) W u := by
    intro m n
    exact isWeaklyHarmonicOn_of_sobolevCoefficientForm_zero (a n) (A n) (haA n)
      (dirichletMinimizer (killedResponseSpace hP) (a n) (breg m))
      (hEuler n (breg m))
  choose ureg huregval huregharm using hRegHarmonic
  have huregRep : ∀ m n, (ureg m n).toFun =ᵐ[volume.restrict W] R m n := by
    intro m n
    filter_upwards [hRae m n] with x hx
    exact (congrFun (huregval m n) x).trans hx

  have hEqui : ∀ m, Equicontinuous (fun n (x : closure W) => R m n x) :=
    aux_goodext_harmonic_trace_bank_equicontinuous alpha halpha C hC
      (closure W) hKcompact R hRcont (fun m n => ⟨hRholder m n, hRnorm m n⟩)

  obtain ⟨M, hMbound⟩ := hKcompact.exists_bound_of_continuousOn hgc
  have hM : ∀ x ∈ frontier W, |g x| ≤ M := by
    intro x hx
    simpa only [Real.norm_eq_abs] using hMbound x (frontier_subset_closure hx)
  have hAmeas : ∀ n, Measurable (A n) := fun n => (hA n).continuous.measurable
  have hboundsOpen : ∀ n x, x ∈ W → lam n ≤ A n x ∧ A n x ≤ Lam n := by
    intro n x hx
    exact hbounds n x (subset_closure hx)
  obtain ⟨V, ns, hns, hVc, hVuniform, hVtrace⟩ :=
    exists_uniform_harmonic_trace_subseq hWgeom hWne A hAmeas lam Lam hlam hboundsOpen
      u huharm VN hVNcont huRep g hVNboundary M hM greg happrox
      ureg huregharm R hRcont huregRep hRegboundary hEqui

  refine ⟨b, VN, V, ns, hns, hVc, hVtrace, hVuniform, ?_⟩
  intro n
  exact ⟨hVNcont n, hVNae n, hVNboundary n, hResponseBound n⟩
