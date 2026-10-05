module

public import SubdiffusiveProcess.Paper.goodext_cutoff_local_trace_eventual
public import SubdiffusiveProcess.EllipticRegularity.CutoffCoefficientRepresentative

@[expose] public section

/-! Actual cutoff coefficients instantiate the local trace construction on a
concentric three-cell grid. All uniform controls remain explicit hypotheses. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Uniform actual cutoff controls supply an ambient continuous witness with the central-cell energy bound. -/
theorem goodext_cutoff_local_trace
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I) (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (env : ℕ → BilateralField d) (N : ℕ → ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (_hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (_A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
      (fun n => cutoffPositiveCoefficient M H (env n) (N n) z hr))
    (t alpha : ℝ) (_ha : 0 < alpha)
    (_hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => cutoffCoefficient M H (env n) (N n)) t alpha)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (_hGN : ∀ n f, GN n f =
      (responseSolution S (cutoffPositiveCoefficient M H (env n) (N n) z hr)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (_hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (_hE : ∀ u, E.energy u = limitFormEnergy G u)
    (_hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0) (h3r0 : 0 < 3 * r0)
    (_hPsub : (centeredCube z0 (3 * r0) h3r0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (_hReg : ∀ (j : OddGridIndex d (triadicHalf 1)) (phi : SpatialCoordinates d → ℝ),
      ContDiff ℝ ∞ phi →
      ∀ b : weakSobolevGraph (centeredCube (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0),
        (b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))] phi →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (centeredCube
            (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer
            (killedResponseSpace (centeredCube_killedPoincare
              (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hr0))
            (cutoffPositiveCoefficient M H (env n) (N n)
              (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hr0) b).val.1 :
                SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                  (centeredCube (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (centeredCube
            (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube
            (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))) V ≤ K)
    (_hr01 : r0 ≤ 1) (Lam : OddGridIndex d (triadicHalf 1) → ℝ)
    (_hLam0 : ∀ j, 0 ≤ Lam j)
    (_hLam : ∀ n j, I.Lam (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0
      (cutoffPositiveCoefficient M H (env n) (N n)
        (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hr0)
      (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 ((beta - 1 / 2) / 4) 2 ≤ Lam j)
    (b : SpatialCoordinates d → ℝ)
    (_hbc : ContinuousOn b (frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (_hbh : IsHolderOn beta (frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) b),
    ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)), V x = b x) ∧
      (Gamma.measure v (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal ≤
        C * Lam (fun _ => 1) * r0 ^ ((d : ℝ) - 2) *
          (r0 ^ beta * holderSeminorm beta (frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) b) ^ 2 := by
  obtain ⟨C, hC, hTrace⟩ := goodext_cutoff_local_trace_eventual d hd I X Sob beta hbeta
  refine ⟨C, hC, ?_⟩
  intro M H env N z r hr S hS A t alpha ha hcell GN G hGN hConv E hE hcont Gamma
    z0 r0 hr0 h3r0 hPsub hReg hr01 Lam hLam0 hLam b hbc hbh
  have hcenter : oddGridCenter z0 (3 * r0) (triadicHalf 1) (fun _ => 1) = z0 := by
    change oddGridCenter z0 (3 * r0) 1 (fun _ => (1 : Fin 3)) = z0
    funext i
    simp only [oddGridCenter, Fin.val_one, Nat.cast_one, sub_self, zero_mul, add_zero]
  have hCentral : ∀ᶠ n in atTop, I.Lam z0 r0 hr0
      (cutoffPositiveCoefficient M H (env n) (N n) z0 hr0)
      z0 r0 ((beta - 1 / 2) / 4) 2 ≤ Lam (fun _ => 1) := by
    apply Filter.Eventually.of_forall
    intro n
    have hvalue := congrArg (fun zz : SpatialCoordinates d =>
      I.Lam zz r0 hr0 (cutoffPositiveCoefficient M H (env n) (N n) zz hr0)
        zz r0 ((beta - 1 / 2) / 4) 2) hcenter
    exact hvalue ▸ hLam n (fun _ => 1)
  exact hTrace M H env N z r hr S hS A t alpha ha hcell GN G hGN hConv E hE hcont Gamma
    z0 r0 hr0 h3r0 hPsub hReg hr01 Lam hLam0 hLam
    (Lam (fun _ => 1)) (hLam0 _) hCentral b hbc hbh
end SubdiffusiveProcess.Paper
