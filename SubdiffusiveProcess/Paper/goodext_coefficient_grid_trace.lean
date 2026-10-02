import SubdiffusiveProcess.Paper.goodext_dirichlet_response_bound
import SubdiffusiveProcess.Paper.goodext_grid_trace_of_smooth_growth
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- Uniform upper coefficients bound the separate cell energies of one continuous limiting-form grid witness. -/
theorem goodext_coefficient_grid_trace
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
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (hPsub : (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (J : ℕ)
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)), g x = 0)
    (aCell : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf J),
      PositiveCoefficient (oddGridCell z0 r0 hr0 (triadicHalf J) k))
    (hab : ∀ n k, (a n).val =ᵐ[volume.restrict
      (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] (aCell n k).val)
    (hgc : ContinuousOn g (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hgh : SubdiffusiveProcess.Lane4.IsHolderOn beta
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
    (hside : (r0 / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ≤ 1)
    (Lam : OddGridIndex d (triadicHalf J) → ℝ)
    (hLam0 : ∀ k, 0 ≤ Lam k)
    (hLam : ∀ n k, I.Lam
      (oddGridCenter z0 r0 (triadicHalf J) k) (r0 / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) (div_pos hr0 (by positivity))
      (aCell n k) (oddGridCenter z0 r0 (triadicHalf J) k) (r0 / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ((beta - 1 / 2) / 4) 2 ≤ Lam k)
    ,
    ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      ∀ k, (∀ x ∈ frontier (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)),
        V x = g x) ∧
        (Gamma.measure v (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))).toReal ≤ C * Lam k * (r0 / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ^ ((d : ℝ) - 2) * ((r0 / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ^ beta * holderSeminorm beta (frontier (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) g) ^ 2  := by
  classical
  obtain ⟨C, hC, hScalar⟩ :=
    Paper.goodext_dirichlet_response_bound d hd I X Sob beta hbeta
  refine ⟨C, hC, ?_⟩
  intro z r hr S hS a A c hc hcs hell hrep t alpha ha hcell GN G hGN hConv E hE hcont Gamma
    instNeZero z0 r0 hr0 hPsub J g hg0 aCell hab hgc hgh hP hReg hside Lam hLam0 hLam
  have hden : (0 : ℝ) < 2 * ((triadicHalf J : ℕ) : ℝ) + 1 := by
    have hcast : (0 : ℝ) ≤ ((triadicHalf J : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith only [hcast]
  have hsidePos0 : 0 < r0 / (2 * ((triadicHalf J : ℕ) : ℝ) + 1) :=
    div_pos hr0 hden
  let side : ℝ := r0 / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)
  have hsidePos : 0 < side := by
    simpa only [side] using hsidePos0
  have hsideLe : side ≤ 1 := by
    simpa only [side] using hside
  let Ecell : OddGridIndex d (triadicHalf J) → ℝ := fun k =>
    C * Lam k * side ^ ((d : ℝ) - 2) *
      (side ^ beta *
        holderSeminorm beta
          (frontier (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) g) ^ 2
  have hEc : ∀ k, 0 ≤ Ecell k := by
    have hsidePow : 0 ≤ side ^ ((d : ℝ) - 2) :=
      (Real.rpow_pos_of_pos hsidePos _).le
    intro k
    dsimp only [Ecell]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC.le (hLam0 k)) hsidePow)
      (sq_nonneg _)
  have hResponseGrid :
      ∀ (k : OddGridIndex d (triadicHalf J)) n
        (b : weakSobolevGraph (oddGridCell z0 r0 hr0 (triadicHalf J) k))
        (B : SpatialCoordinates d → ℝ),
        ContinuousOn B (closure (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) →
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] B) →
        EqOn B g (frontier (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) →
        dirichletResponse (killedResponseSpace (hP k)) (aCell n k) b ≤ Ecell k := by
    intro k n b B hBcont hBae hBtrace
    have hHolderCell : IsHolderOn beta
        (frontier (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) g :=
      FiniteStopping.isHolderOn_mono
        (frontier_subset_closure.trans
          (closure_mono (oddGridCell_subset z0 hr0 (triadicHalf J) k)))
        beta g hgh
    have hBound := hScalar
      (oddGridCenter z0 r0 (triadicHalf J) k) side hsidePos hsideLe
      (hP k) (aCell n k) g (Lam k) (hLam n k) hHolderCell
      b B hBcont hBae hBtrace
    change dirichletResponse (killedResponseSpace (hP k)) (aCell n k) b ≤
      C * Lam k * side ^ ((d : ℝ) - 2) *
        (side ^ beta * holderSeminorm beta
          (frontier (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))) g) ^ 2
    exact hBound
  exact Paper.goodext_grid_trace_of_smooth_growth
    hd z r hr S hS a A c hc hcs hell hrep t alpha ha hcell GN G hGN hConv E hE hcont Gamma
    z0 r0 hr0 hPsub J g hg0 aCell hab Sob beta hbeta hgc hgh hP hReg Ecell hEc hResponseGrid
end Paper
