import SubdiffusiveProcess.Paper.goodext_harmonic_trace_of_smooth_growth
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
import SubdiffusiveProcess.Compactness.CountableCompact




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- Countably many actual Holder-trace minimizer families have one common uniform subsequence. -/
theorem goodext_countable_harmonic_trace_bank
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    {I : Type*} [Countable I]
    (z : I → SpatialCoordinates d) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (beta alpha : ℝ) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1) (ha : 0 < alpha)
    (a : ∀ i, ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i)))
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hac : ∀ i n, (a i n).val =ᵐ[volume.restrict
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] c n)
    (lam Lam : I → ℕ → ℝ) (hlam : ∀ i n, 0 < lam i n)
    (hbounds : ∀ i n x, x ∈ closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) →
      lam i n ≤ c n x ∧ c n x ≤ Lam i n)
    (g : SpatialCoordinates d → ℝ)
    (hgc : ∀ i, ContinuousOn g (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))))
    (hgh : ∀ i, IsHolderOn beta (frontier (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) g)
    (hReg : ∀ i (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ b : weakSobolevGraph (centeredCube (z i) (r i) (hr i)),
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] phi) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace (centeredCube_killedPoincare (z i) (hr i)))
            (a i n) b).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) V ≤ C)
    (Ebound : I → ℕ → ℝ)
    (hResponse : ∀ i n (b : weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
        (B : SpatialCoordinates d → ℝ),
      ContinuousOn B (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) →
      ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] B) →
      EqOn B g (frontier (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) →
      dirichletResponse (killedResponseSpace (centeredCube_killedPoincare (z i) (hr i))) (a i n) b ≤ Ebound i n) :
    ∃ (b : ∀ i, weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
      (VN : I → ℕ → SpatialCoordinates d → ℝ)
      (rho : ℕ → ℕ) (V : I → SpatialCoordinates d → ℝ),
      StrictMono rho ∧
      (∀ i n, ContinuousOn (VN i n) (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) ∧
        ((dirichletMinimizer (killedResponseSpace (centeredCube_killedPoincare (z i) (hr i)))
          (a i n) (b i)).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] VN i n ∧
        (∀ x ∈ frontier (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)), VN i n x = g x) ∧
        dirichletResponse (killedResponseSpace (centeredCube_killedPoincare (z i) (hr i))) (a i n) (b i) ≤ Ebound i n) ∧
      ∀ i, ContinuousOn (V i) (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) ∧
        TendstoUniformlyOn (fun n => VN i (rho n)) (V i) atTop
          (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) ∧
        EqOn (V i) g (frontier (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) := by
  choose b VN hbank using fun i =>
    goodext_harmonic_trace_of_smooth_growth hd Sob (z i) (r i) (hr i) beta alpha hb ha
      (centeredCube_killedPoincare (z i) (hr i)) (a i) c hc (hac i)
      (lam i) (Lam i) (hlam i) (hbounds i) g (hgc i) (hgh i) (hReg i)
      (Ebound i) (hResponse i)
  let S : I → Set (SpatialCoordinates d) := fun i =>
    closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))
  have hS : ∀ i, IsCompact (S i) := by
    intro i
    change IsCompact (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    exact (centeredCube_isBounded (z i) (hr i)).isCompact_closure
  have hU : ∀ i n, ContinuousOn (VN i n) (S i) := by
    intro i n
    change ContinuousOn (VN i n)
      (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    exact ((hbank i).1 n).1
  have hcompact : ∀ i (sigma : ℕ → ℕ), StrictMono sigma →
      ∃ (tau : ℕ → ℕ) (V : SpatialCoordinates d → ℝ), StrictMono tau ∧ ContinuousOn V (S i) ∧
        TendstoUniformlyOn (fun n => VN i (sigma (tau n))) V atTop (S i) := by
    intro i sigma hsigma
    obtain ⟨tau, V, htau, hVc, hlim, _⟩ := (hbank i).2 sigma hsigma
    exact ⟨tau, V, htau, hVc, hlim⟩
  obtain ⟨rho, V, hrho, hlimit⟩ :=
    SubdiffusiveProcess.exists_joint_uniform_subseq_of_countable_compact
      S hS VN hU hcompact
  refine ⟨b, VN, rho, V, hrho, ?_, ?_⟩
  · intro i n
    exact (hbank i).1 n
  · intro i
    refine ⟨(hlimit i).1, (hlimit i).2, ?_⟩
    intro x hx
    have hpoint : Tendsto (fun n => VN i (rho n) x) atTop (𝓝 (V i x)) :=
      (hlimit i).2.tendsto_at (frontier_subset_closure hx)
    have hconstant : Tendsto (fun n => VN i (rho n) x) atTop (𝓝 (g x)) := by
      have hseq : (fun n => VN i (rho n) x) = fun _ : ℕ => g x := by
        funext n
        exact ((hbank i).1 (rho n)).2.2.1 x hx
      rw [hseq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hpoint hconstant
end Paper
