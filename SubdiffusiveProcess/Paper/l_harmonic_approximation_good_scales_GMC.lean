module

public import SubdiffusiveProcess.Analysis.SmoothDualBoundaryClauseSix

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Paper

/-- For `m ≤ L + 2` the cutoff good event `goodEvent M (some L) m` (responses `a_{min(n,L)}`) is the
uncutoff good event `goodEvent M none m` (responses `a_n`): every scale `n ≤ m - 2` is at most `L`. -/
theorem aux_l_harmonic_approximation_good_scales_GMC_goodEvent_some_eq_none {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {L m : ℕ} (hmL : m ≤ L + 2) (y : Vec d) (epsilon s : ℝ) :
    goodEvent M (some L) m y epsilon s = goodEvent M none m y epsilon s := by
  ext ω
  simp only [goodEvent, Set.mem_ofPred_eq, GoodResponse]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  refine forall_congr' fun j => forall_congr' fun n' => forall_congr' fun hj =>
    forall_congr' fun hn' => ?_
  have hn'L : n' ≤ L := by omega
  simp only [Option.getD_some, Option.getD_none, min_eq_left hn'L, min_self]



theorem l_harmonic_approximation_good_scales_GMC
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, m ≤ L → n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemFractionalOn (cube d m) s h.grad →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          (∃ v : H1Function (translatedCube d (n - 2) y),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
          (∀ v v' : H1Function (translatedCube d (n - 2) y),
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
            v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
              v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            indicatorValue (goodEvent M none (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-3 / 2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    (normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
                        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                    else 0)) +
                  C * s ^ (-15 / 2 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal else 0) := by
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension (by norm_num)⟩
  have : NeZero d := ⟨hdpos.ne'⟩
  obtain ⟨C, hC, hclause⟩ := SubdiffusiveProcess.Analysis.aux_b12bd_boundaryClause_six d
  refine ⟨C, hC, ?_⟩
  intro M s hs L m n hmL hnm z hz x hx ω u h g hdir hgex hh y hy hcov hloc uD hfval hfgrad
  have hev := aux_l_harmonic_approximation_good_scales_GMC_goodEvent_some_eq_none M
    (by omega : n + 2 ≤ L + 2) z 1 (s / 8)
  have := hclause M s hs L m n hnm z hz x hx ω u h g hdir hgex hh y hy hcov hloc uD hfval hfgrad
  rw [hev] at this
  exact this

end SubdiffusiveProcess.Paper
