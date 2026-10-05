module

public import SubdiffusiveProcess.Paper.goodext_local_grid_trace_response
public import SubdiffusiveProcess.Paper.goodext_harmonic_trace_of_smooth_growth
public import SubdiffusiveProcess.Sobolev.HolderBoundaryExtension
public import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison

@[expose] public section

/-! Smooth-cell regularity and actual Holder response bounds construct one
continuous limiting-form grid trace witness. No stochastic bounds are asserted. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Actual smooth-data estimates and local trace responses yield a global continuous form-domain witness on a contained finite grid. -/
theorem goodext_grid_trace_of_smooth_growth
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hcs : ∀ n, Continuous (c n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam)
    (hrep : ∀ n, (a n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c n)
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr c t alpha)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    [NeZero d]
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (hPsub : (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (J : ℕ)
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)), g x = 0)
    (aCell : ∀ _n : ℕ, ∀ k : OddGridIndex d (triadicHalf J),
      PositiveCoefficient (oddGridCell z0 r0 hr0 (triadicHalf J) k))
    (hab : ∀ n k, (a n).val =ᵐ[volume.restrict
      (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] (aCell n k).val)
    (Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hgc : ContinuousOn g (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hgh : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) g)
    (hP : ∀ k : OddGridIndex d (triadicHalf J), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z0 r0 hr0 (triadicHalf J) k), ‖u.val.1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z0 r0 hr0 (triadicHalf J) k)) u‖)
    (hReg : ∀ (k : OddGridIndex d (triadicHalf J)) (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph (oddGridCell z0 r0 hr0 (triadicHalf J) k)),
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] phi) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace (hP k)) (aCell n k) b).val.1 :
            SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) V ≤ C)
    (Ecell : OddGridIndex d (triadicHalf J) → ℝ) (hEc : ∀ k, 0 ≤ Ecell k)
    (hResponse : ∀ (k : OddGridIndex d (triadicHalf J)) n (b : weakSobolevGraph (oddGridCell z0 r0 hr0 (triadicHalf J) k))
        (B : SpatialCoordinates d → ℝ),
      ContinuousOn B (closure (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) →
      ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] B) →
      EqOn B g (frontier (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) →
      dirichletResponse (killedResponseSpace (hP k)) (aCell n k) b ≤ Ecell k)
    :
    ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      ∀ k, (∀ x ∈ frontier (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)),
        V x = g x) ∧
        (Gamma.measure v (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))).toReal ≤ Ecell k  := by
  classical
  have hEll := hell
  choose lam Lam hlam hb using hEll
  have hbounds : ∀ n x, x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) →
      lam n ≤ c n x ∧ c n x ≤ Lam n := by
    intro n x hx
    exact ⟨le_on_closure (fun y hy => (hb n y hy).1) continuousOn_const
      (hc n).continuousOn hx,
      le_on_closure (fun y hy => (hb n y hy).2) (hc n).continuousOn continuousOn_const hx⟩
  have hWsub (k : OddGridIndex d (triadicHalf J)) :
      (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (oddGridCell_subset z0 hr0 (triadicHalf J) k).trans hPsub
  have hCellRep (k : OddGridIndex d (triadicHalf J)) (n : ℕ) :
      (aCell n k).val =ᵐ[volume.restrict
        (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] c n :=
    (hab n k).symm.trans (ae_mono (Measure.restrict_mono (hWsub k) le_rfl) (hrep n))
  have hBank (k : OddGridIndex d (triadicHalf J)) :=
    goodext_harmonic_trace_of_smooth_growth hd Sob
      (oddGridCenter z0 r0 (triadicHalf J) k) (r0 / (2 * ((triadicHalf J : ℕ) : ℝ) + 1))
      (div_pos hr0 (by positivity)) beta alpha hbeta ha (hP k)
      (fun n => aCell n k) c hcs (hCellRep k) lam Lam hlam
      (fun n x hx => hbounds n x (closure_mono (hWsub k) hx))
      g (hgc.mono (closure_mono (oddGridCell_subset z0 hr0 (triadicHalf J) k)))
      (FiniteStopping.isHolderOn_mono
        (frontier_subset_closure.trans (closure_mono (oddGridCell_subset z0 hr0 (triadicHalf J) k)))
        beta g hgh) (hReg k) (fun _ => Ecell k) (hResponse k)
  choose datum VN hVN hCompact using hBank
  exact goodext_local_grid_trace_response hd z r hr S hS a A c hc hell hrep
    t alpha ha hcell GN G hGN hConv E hE hcont Gamma z0 r0 hr0 hPsub J g hg0
    aCell hab
    (fun k n => dirichletMinimizer (killedResponseSpace (hP k)) (aCell n k) (datum k)) VN
    (fun k n => (hVN k n).1) (fun k n => (hVN k n).2.1)
    (fun k n => (hVN k n).2.2.1)
    (fun k sigma hsigma => by
      obtain ⟨tau, V, htau, _, hlim, _⟩ := hCompact k sigma hsigma
      exact ⟨tau, htau, V, hlim⟩)
    Ecell hEc (fun k n => (hVN k n).2.2.2)

end SubdiffusiveProcess.Paper
