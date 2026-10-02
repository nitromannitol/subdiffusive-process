import SubdiffusiveProcess.Paper.lem_as_regularity_boundary_step_twelve
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.TruncatedIteration

/-! Deterministic Dirichlet iteration with arbitrary original-field good-scale masks.
The recurrence consumes the literal coefficient error, never a native stopping witness. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- A mask of controlled cutoff coefficient errors supplies the full truncated-cube iteration
(the cutoff field on the threshold-12 good events of the unmasked scales; no standing input). -/
theorem lem_as_regularity_dirichlet_iteration_twelve (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ A CI : ℝ, 0 < A ∧ 0 < CI ∧ ∀ k : ℕ, 6 ≤ k → ∃ B : ℝ, 0 < B ∧
    ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, 2048 * M.delta ^ 2 ≤ 1 →
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ ((1 / 4 : ℝ) / 8) * Real.log 3 / 16 →
    ∀ eta : ℝ, eta ∈ Icc (32 * M.delta ^ 2) 1 → ∀ theta : ℝ, theta ∈ Ioo (0 : ℝ) 1 →
      theta ^ k ∈ Ioo (0 : ℝ) (3/5) →
      A*(3:ℝ)^(-(k:ℝ)/2)+B*eta ≤ theta ^ k →
    ∀ L m n top : ℕ, n < top → top + 5 ≤ m →
    ∀ z ∈ cube d m, ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
    ∀ bad : Finset ℤ, bad ⊆ Finset.Icc (n:ℤ) (top:ℤ) →
      (∀ j ∈ Finset.Icc (n:ℤ) (top:ℤ), j ∉ bad →
        k ≤ j.toNat ∧
          ω ∈ Paper.product_threshold_good_scale d M 12 (some L) (j.toNat + 2) z eta (1 / 32)) →
    ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
      IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
      (∃ sOrder : FractionalOrder, sOrder.1 = (1/4:ℝ) ∧
        Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d m) sOrder FiniteLpExponent.two g) →
      MemHolder (cube d m) (1/2) g → MemHolder (cube d m) (1/2) h.grad →
    ∀ epsRow defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc (n:ℤ) (top:ℤ), 0 ≤ epsRow j ∧ 0 ≤ defect j) →
      (∀ j ∈ Finset.Icc (n:ℤ) (top:ℤ), j ∉ bad →
        B*section6HomogenizationError M (1 / 32) L (j.toNat + 2) ω z ≤ epsRow j ∧
        B*(section6HomogenizationError M (1 / 32) L (j.toNat + 2) ω z * vectorSupNormOn (cube d m) h.grad +
          (tailAverage M L (j.toNat + 2) ω (translatedCube d ((j.toNat : ℤ) + 2) z))⁻¹ *
            (3:ℝ)^((j:ℝ)/2)*holderSeminormOn (cube d m) (1/2) g +
          (3:ℝ)^((j:ℝ)/2)*holderSeminormOn (cube d m) (1/2) h.grad) ≤ defect j) →
      (3:ℝ)^(-(n:ℤ))*normalizedL2On (truncatedCube d m n z)
        (fun x => u.toFun x-averageOn (truncatedCube d m n z) u.toFun) ≤
      Real.exp (CI*(k+1)*(bad.card+1)+CI*∑ j ∈ Finset.Icc (n:ℤ) (top:ℤ),epsRow j) *
        ((3:ℝ)^(-(top:ℤ))*normalizedL2On (truncatedCube d m top z)
          (fun x => u.toFun x-averageOn (truncatedCube d m top z) u.toFun) +
          ∑ j ∈ Finset.Icc (n:ℤ) (top:ℤ),defect j) := by
  obtain ⟨A,hA,hstep⟩ := lem_as_regularity_boundary_step_twelve d hd
  obtain ⟨CI,hCI,hiter⟩ := Section6Holder.truncatedCube_iteration d
  refine ⟨A,CI,hA,hCI,?_⟩
  intro k hk
  obtain ⟨B,hB,hstep⟩ := hstep k hk
  refine ⟨B,hB,?_⟩
  intro M hM htau eta heta theta htheta hthetak hcontract L m n top hnt htm z hz ω bad hbad hgood
    u h g hsol hg hgh hhh epsRow defect hnonneg hrows
  have hrec : ∀ j ∈ Finset.Icc (n:ℤ) (top:ℤ), j ∉ bad →
      ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m j z) u.toFun →
      excess (j-k) (truncatedCube d m (j-k) z) u.toFun ≤
        theta ^ k * excess j (truncatedCube d m j z) u.toFun +
          epsRow j * Real.sqrt (vecNormSq ell.slope) + defect j := by
    intro j hj hjbad ell hell
    have hj0 : 0 ≤ j := (Int.natCast_nonneg n).trans (Finset.mem_Icc.mp hj).1
    have hjcast : (j.toNat:ℤ) = j := Int.toNat_of_nonneg hj0
    have hjtop : j.toNat ≤ top := by exact_mod_cast (hjcast ▸ (Finset.mem_Icc.mp hj).2)
    obtain ⟨hkj,herr⟩ := hgood j hj hjbad
    obtain ⟨hrow,hdef⟩ := hrows j hj hjbad
    have hself : z ∈ truncatedCube d m ((j.toNat:ℤ)-3) z := by
      refine ⟨?_, hz⟩
      rw [mem_translatedCube_iff, sub_self]
      exact zero_mem_cube d _
    have hs := hstep M hM htau eta heta L m j.toNat hkj (by omega) z z hz hz hself ω herr u h g hsol hg
      hgh hhh ell (by simpa only [hjcast] using hell)
    have hc := mul_le_mul_of_nonneg_right hcontract
      (excess_nonneg j (truncatedCube d m j z) u.toFun)
    have he := mul_le_mul_of_nonneg_right hrow (Real.sqrt_nonneg (vecNormSq ell.slope))
    have hcastreal : (j.toNat:ℝ) = (j:ℝ) := by exact_mod_cast hjcast
    simp only [hjcast,hcastreal] at hs
    simp only [hjcast] at he hdef
    linarith only [hs,hc,he,hdef]
  exact (hiter k (by omega) theta htheta hthetak m n top hnt (by omega) z hz u bad hbad
    epsRow defect hnonneg hrec).1

end Paper
