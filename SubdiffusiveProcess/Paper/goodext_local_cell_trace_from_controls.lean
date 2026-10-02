import SubdiffusiveProcess.Paper.goodext_coefficient_grid_trace
import SubdiffusiveProcess.Sobolev.CentralGridTrace

/-!
# Controlled local-cell trace

This module derives the central-cell trace witness from supplied continuous
coefficient-grid controls and makes no additional existence claim.
-/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- The concentric coefficient-grid bounds yield the prescribed central-cell trace with its exact cost. -/
theorem goodext_local_cell_trace_from_controls
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I)
    (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
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
    (E : DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : DirichletForm.EnergyMeasure E)
    [NeZero d]
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0) (h3r0 : 0 < 3 * r0)
    (hPsub : (centeredCube z0 (3 * r0) h3r0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (aCell : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf 1),
      PositiveCoefficient (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k))
    (hab : ∀ n k, (a n).val =ᵐ[volume.restrict
      (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))] (aCell n k).val)
    (hP : ∀ k : OddGridIndex d (triadicHalf 1), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k), ‖u.val.1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k)) u‖)
    (hReg : ∀ (k : OddGridIndex d (triadicHalf 1)) (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k)),
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))] phi) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace (hP k)) (aCell n k) b).val.1 :
            SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))) V ≤ C)
    (hr01 : r0 ≤ 1)
    (Lam : OddGridIndex d (triadicHalf 1) → ℝ)
    (hLam0 : ∀ k, 0 ≤ Lam k)
    (hLam : ∀ n k, I.Lam
      (oddGridCenter z0 (3 * r0) (triadicHalf 1) k) ((3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) (div_pos h3r0 (by positivity))
      (aCell n k) (oddGridCenter z0 (3 * r0) (triadicHalf 1) k) ((3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) ((beta - 1 / 2) / 4) 2 ≤ Lam k)

    (b : SpatialCoordinates d → ℝ)
    (hbc : ContinuousOn b (frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hbh : IsHolderOn beta (frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) b),
    ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)), V x = b x) ∧
      (Gamma.measure v (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal ≤
        C * Lam (fun _ => 1) * r0 ^ ((d : ℝ) - 2) *
          (r0 ^ beta * holderSeminorm beta (frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) b) ^ 2 := by
  obtain ⟨C, hC, hScalar⟩ :=
    Paper.goodext_coefficient_grid_trace d hd I X Sob beta hbeta
  refine ⟨C, hC, ?_⟩
  intro z r hr S hS a A c hc hell hrep t alpha ha hcell GN G hGN hConv E hE hcont Gamma
    instNeZero z0 r0 hr0 h3r0 hPsub aCell hab hP hReg hr01 Lam hLam0 hLam b hbc hbh
  have hHalf : triadicHalf 1 = 1 := rfl
  have hchild :
      (3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1) = r0 := by
    rw [hHalf]
    norm_num
  have hgridSideLe :
      (3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [hchild]
    exact hr01
  have hGrid :
      ∀ g : SpatialCoordinates d → ℝ,
        ContinuousOn g
          (closure (centeredCube z0 (3 * r0) h3r0 : Set (SpatialCoordinates d))) →
        IsHolderOn beta
          (closure (centeredCube z0 (3 * r0) h3r0 : Set (SpatialCoordinates d))) g →
        (∀ x ∈ frontier (centeredCube z0 (3 * r0) h3r0 : Set (SpatialCoordinates d)), g x = 0) →
        ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
          v ∈ E.domain ∧
          ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
          ∀ k : OddGridIndex d (triadicHalf 1),
            (∀ x ∈ frontier
              (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d)),
              V x = g x) ∧
            (Gamma.measure v
              (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))).toReal ≤
              C * Lam k * r0 ^ ((d : ℝ) - 2) *
                (r0 ^ beta * holderSeminorm beta
                  (frontier (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k :
                    Set (SpatialCoordinates d))) g) ^ 2 := by
    intro g hgcont hgholder hgzero
    obtain ⟨v, V, hv, hVcont, hVae, hVcell⟩ :=
      hScalar z r hr S hS a A c hc hc hell hrep t alpha ha hcell GN G hGN hConv E hE hcont
        Gamma z0 (3 * r0) h3r0 hPsub 1 g hgzero aCell hab hgcont hgholder hP hReg
        hgridSideLe Lam hLam0 hLam
    have hVcell' :
        ∀ k : OddGridIndex d (triadicHalf 1),
          (∀ x ∈ frontier
            (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d)),
            V x = g x) ∧
          (Gamma.measure v
            (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))).toReal ≤
            C * Lam k * r0 ^ ((d : ℝ) - 2) *
              (r0 ^ beta * holderSeminorm beta
                (frontier (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k :
                  Set (SpatialCoordinates d))) g) ^ 2 := by
      intro k
      rcases hVcell k with ⟨htrace, hcost⟩
      refine ⟨htrace, ?_⟩
      simpa only [hchild] using hcost
    exact ⟨v, V, hv, hVcont, hVae, hVcell'⟩
  have hbetaPos : 0 < beta := by
    linarith only [hbeta.1]
  exact SubdiffusiveProcess.exists_local_trace_of_concentric_grid
    (Q := centeredCube z r hr) E Gamma z0 r0 hr0 beta hbetaPos (le_of_lt hbeta.2)
    C Lam hGrid b hbc hbh
