module

public import SubdiffusiveProcess.Paper.inputs_deterministic_excess

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
theorem aux_l_excess_decay_good_scales_GMC_goodEvent_some_eq_none {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {L m : ℕ} (hmL : m ≤ L + 2) (y : Vec d) (epsilon s : ℝ) :
    goodEvent M (some L) m y epsilon s = goodEvent M none m y epsilon s := by
  ext ω
  simp only [goodEvent, Set.mem_ofPred_eq, GoodResponse]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  refine forall_congr' fun j => forall_congr' fun n' => forall_congr' fun hj =>
    forall_congr' fun hn' => ?_
  have hn'L : n' ≤ L := by omega
  simp only [Option.getD_some, Option.getD_none, min_eq_left hn'L, min_self]



theorem l_excess_decay_good_scales_GMC
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → m ≤ L → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M none (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0) := by
  by_cases hd : 2 ≤ d
  · have : NeZero d := ⟨by omega⟩
    obtain ⟨C, hC, hclause⟩ := _root_.SubdiffusiveProcess.Paper.inputs_deterministic_excess d hd
    refine ⟨C, hC, ?_⟩
    intro M s hs epsilon heps k hk L m n hkn hmL hnm x hx z hz hxz ω u h g hdir hgex hh ell hell
    have hev := aux_l_excess_decay_good_scales_GMC_goodEvent_some_eq_none M
      (by omega : n + 2 ≤ L + 2) z epsilon (s / 8)
    have := hclause M s hs epsilon heps k hk L m n hkn hnm x hx z hz hxz ω u h g hdir hgex hh
      ell hell
    rw [hev] at this
    exact this
  · refine ⟨1, one_pos, ?_⟩
    intro M
    exact absurd M.shellPrefix.dimension hd

end SubdiffusiveProcess.Paper
