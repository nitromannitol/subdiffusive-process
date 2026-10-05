module

public import SubdiffusiveProcess.Paper.goodext_harmonic_trace_bank
public import SubdiffusiveProcess.Paper.inputs_classical_elliptic_boundary_continuity_cube

@[expose] public section

/-! Exact Holder traces have uniformly precompact minimizer banks for continuous elliptic coefficients. Smooth-data growth remains an explicit hypothesis. -/

open Filter MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The fixed actual trace has one minimizer bank which remains uniformly precompact after every strictly increasing reindexing. -/
theorem goodext_harmonic_trace_compact_continuous
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (Sob : SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta alpha : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) (halpha : 0 < alpha)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : ℕ → SpatialCoordinates d → ℝ) (hA : ∀ n, Continuous (A n))
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
      (VN : ℕ → SpatialCoordinates d → ℝ),
      (∀ n, ContinuousOn (VN n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (((dirichletMinimizer (killedResponseSpace hP) (a n) b).val.1 :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] VN n) ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), VN n x = g x) ∧
        dirichletResponse (killedResponseSpace hP) (a n) b ≤ Ebound n) ∧
      ∀ sigma : ℕ → ℕ, StrictMono sigma →
        ∃ (tau : ℕ → ℕ) (V : SpatialCoordinates d → ℝ), StrictMono tau ∧
          ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          TendstoUniformlyOn (fun n => VN (sigma (tau n))) V atTop
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = g x := by
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
      (hA n) (haA n) ⟨lam n, hlam n, fun x hx => (hbounds n x hx).1⟩ hBcont hBae
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
      (A n) (greg m) (hA n) (haA n)
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
  have hAmeas : ∀ n, Measurable (A n) := fun n => (hA n).measurable
  have hboundsOpen : ∀ n x, x ∈ W → lam n ≤ A n x ∧ A n x ≤ Lam n := by
    intro n x hx
    exact hbounds n x (subset_closure hx)
  refine ⟨b, VN, ?_, ?_⟩
  · intro n
    exact ⟨hVNcont n, hVNae n, hVNboundary n, hResponseBound n⟩
  · intro sigma hSigma
    have hEquiSigma : ∀ m, Equicontinuous
        (fun n (x : closure W) => R m (sigma n) x) := by
      intro m
      exact (hEqui m).comp sigma
    have hAmeasSigma : ∀ n, Measurable (A (sigma n)) := by
      intro n
      exact hAmeas (sigma n)
    have hboundsOpenSigma : ∀ n x, x ∈ W →
        lam (sigma n) ≤ A (sigma n) x ∧ A (sigma n) x ≤ Lam (sigma n) := by
      intro n x hx
      exact hboundsOpen (sigma n) x hx
    obtain ⟨V, tau, htau, hVc, hVuniform, hVtrace⟩ :=
      exists_uniform_harmonic_trace_subseq hWgeom hWne
        (fun n => A (sigma n)) hAmeasSigma
        (fun n => lam (sigma n)) (fun n => Lam (sigma n))
        (fun n => hlam (sigma n)) hboundsOpenSigma
        (fun n => u (sigma n)) (fun n => huharm (sigma n))
        (fun n => VN (sigma n)) (fun n => hVNcont (sigma n))
        (fun n => huRep (sigma n)) g
        (fun n x hx => hVNboundary (sigma n) x hx)
        M hM greg happrox
        (fun m n => ureg m (sigma n))
        (fun m n => huregharm m (sigma n))
        (fun m n => R m (sigma n))
        (fun m n => hRcont m (sigma n))
        (fun m n => huregRep m (sigma n))
        (fun m n x hx => hRegboundary m (sigma n) x hx)
        hEquiSigma
    exact ⟨tau, V, htau, hVc, hVuniform, hVtrace⟩

end SubdiffusiveProcess.Paper
