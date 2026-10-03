module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodScaleIteration
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.AnchorBoundary
public import SubdiffusiveProcess.Providers.Section6.HarmonicApproximationGoodScales
public import SubdiffusiveProcess.Providers.Section6.GoodScaleMathcalE

@[expose] public section




namespace SubdiffusiveProcess.Providers.Section6

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The frozen right-hand side is monotone in its constant.**

Stated over abstract nonnegative reals in exactly the four-line shape of
`SubdiffusiveProcess.Frozen.Section6.excess_decay_good_scales`, so that the two branches of the
provider — which carry different constants — can be joined at their maximum. -/
theorem excessDecayRhs_le_of_le {C C' : ℝ} (hCC : C ≤ C')
    {p : Prop} [Decidable p]
    {a1 E b ss eps Err Sl J s15 Tinv qn Fg s3 pn Hh X : ℝ}
    (hE : 0 ≤ E) (ha1 : 0 ≤ a1) (hb : 0 ≤ b) (hss : 0 ≤ ss) (heps : 0 ≤ eps)
    (hErr : 0 ≤ Err) (hSl : 0 ≤ Sl) (hJ : 0 ≤ J) (hs15 : 0 ≤ s15) (hTinv : 0 ≤ Tinv)
    (hqn : 0 ≤ qn) (hFg : 0 ≤ Fg) (hs3 : 0 ≤ s3) (hpn : 0 ≤ pn) (hHh : 0 ≤ Hh)
    (hX : X ≤ C * (a1 + b * ss * eps) * E + C * b * ss * Err * (Sl + J)
      + C * s15 * b * Tinv * qn * Fg + (if p then C * s3 * b * pn * Hh else 0)) :
    X ≤ C' * (a1 + b * ss * eps) * E + C' * b * ss * Err * (Sl + J)
      + C' * s15 * b * Tinv * qn * Fg + (if p then C' * s3 * b * pn * Hh else 0) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_decay_rhs_mono (C := C) (C' := C') (hCC := hCC) (p := p) (a := a1) (E := E) (b := b) (ss := ss) (eps := eps) (Err := Err) (Sl := Sl) (J := J) (sourceWeight := s15) (Tinv := Tinv) (scaleWeight := qn) (Fg := Fg) (holderWeight := s3) (holderScale := pn) (Hh := Hh) (X := X) (hE := hE) (ha := ha1) (hb := hb) (hss := hss) (heps := heps) (hErr := hErr) (hSl := hSl) (hJ := hJ) (hsourceWeight := hs15) (hTinv := hTinv) (hscaleWeight := hqn) (hFg := hFg) (hholderWeight := hs3) (hholderScale := hpn) (hHh := hHh) (hX := hX)



theorem excess_decay_good_scales_of_anchors (d : ℕ)
    (hharm : HarmonicApproximationInput d) (hcap : MathcalECapInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → m ≤ L → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M none (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-8 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0) := by
  obtain ⟨C₁, hC₁pos, hint⟩ := excess_decay_good_scales_interior d hharm hcap
  obtain ⟨C₂, hC₂pos, hbdy⟩ := excess_decay_good_scales_boundary d hharm hcap
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁pos (le_max_left _ _), ?_⟩
  intro M s hs epsilon heps k hk L m n hkn hmL hnm x hx z hz hxz ω u h g hsol hgfrac
    hhold ell hell
  -- the nonnegativity of every atom of the display
  have hdel : 0 < M.delta := M.shellPrefix.delta_pos
  have hdel2 : (0 : ℝ) < M.delta ^ 2 := pow_pos hdel 2
  have hs0 : 0 < s := lt_of_lt_of_le (mul_pos (by norm_num) hdel2) hs.1
  have heps0 : 0 ≤ epsilon :=
    le_trans (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hs0.le)) hdel2.le) heps.1
  have hMemHW : MemHolder (truncatedCube d m n x) (1 / 2) h.grad :=
    memHolder_mono hhold (truncatedCube_subset_cube d m n x)
  have hE : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
  have ha1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hb : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := Real.rpow_nonneg (by norm_num) _
  have hss : (0 : ℝ) ≤ s ^ (-2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hssIn : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z := ENNReal.toReal_nonneg
  have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
  have hAh : 0 ≤ Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) :=
    Real.sqrt_nonneg _
  have hJ : (0 : ℝ) ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
      s ^ (-3 / 2 : ℝ) *
        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) else 0) := by
    split_ifs
    · exact mul_nonneg hssIn hAh
    · exact le_rfl
  have hs15 : (0 : ℝ) ≤ s ^ (-8 : ℝ) := Real.rpow_nonneg hs0.le _
  have hTinv : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
    inv_nonneg.2 (tailAverage_nonneg _ _ _ _ _)
  have hqn : (0 : ℝ) ≤ (3 : ℝ) ^ (s * n) := Real.rpow_nonneg (by norm_num) _
  have hFg : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    ENNReal.toReal_nonneg
  have hs3 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hpn : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hHh : 0 ≤ holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad :=
    holderSeminormOn_nonneg hMemHW
  by_cases hgate : translatedCube d ((n : ℤ) - 4) x ⊆ cube d m
  · exact excessDecayRhs_le_of_le (le_max_left C₁ C₂) hE ha1 hb hss heps0 hErr hSl hJ
      hs15 hTinv hqn hFg hs3 hpn hHh
      (hint M s hs epsilon heps k hk L m n hkn hmL hnm x hx z hz hxz hgate ω u h g hsol
        hgfrac hhold ell hell)
  · exact excessDecayRhs_le_of_le (le_max_right C₁ C₂) hE ha1 hb hss heps0 hErr hSl hJ
      hs15 hTinv hqn hFg hs3 hpn hHh
      (hbdy M s hs epsilon heps k hk L m n hkn hmL hnm x hx z hz hxz hgate ω u h g hsol
        hgfrac hhold ell hell)


/-- **The harmonic input, unconditionally.**

`HarmonicApproximationInput d` is the body of the frozen v6 block of
`l.harmonic.approximation.good.scales.GMC`, transcribed byte for byte, and that
block is sealed with provider
`SubdiffusiveProcess.Providers.Section6.harmonic_approximation_good_scales` (D-093).  The
provider carries the instance binder `[NeZero d]`, which the frozen
excess-decay block does not; for `d = 0` the model class
`SubdiffusiveProcess.Frozen.Assumptions.GMCModel 0` is empty, since every model carries
`2 ≤ d` through its shell-law prefix. -/
theorem harmonicApproximationInput_all (d : ℕ) :
    HarmonicApproximationInput d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `GMCModel 0` is empty: every model carries `2 ≤ d`.
    refine ⟨1, one_pos, ?_⟩
    intro M
    exact absurd M.shellPrefix.dimension (by norm_num)
  · haveI : NeZero d := ⟨hd.ne'⟩
    exact harmonic_approximation_good_scales d

/-- **The `𝓔` cap input, unconditionally**: the second conjunct of the
established provider `SubdiffusiveProcess.Providers.Section6.good_scale_mathcal_e`. -/
theorem mathcalECapInput_all (d : ℕ) : MathcalECapInput d := by
  obtain ⟨C, hCpos, hgood⟩ := good_scale_mathcal_e d
  refine ⟨C, hCpos, ?_⟩
  intro M s hs L m hmL ω epsilon heps hω
  exact (hgood M s hs L m hmL ω).2 epsilon heps hω



theorem excess_decay_good_scales
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → m ≤ L → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M none (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-8 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0)
    := excess_decay_good_scales_of_anchors d
      (harmonicApproximationInput_all d) (mathcalECapInput_all d)


end

end SubdiffusiveProcess.Providers.Section6
