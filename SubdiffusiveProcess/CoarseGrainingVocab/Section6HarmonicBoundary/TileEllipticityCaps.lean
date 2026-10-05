module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps

@[expose] public section

/-!
# The good-event coarse ellipticity cap on a translated cube of arbitrary scale

 §12.5 item 2 asks, besides
the descendant transfer (`TileCoarsePoincare.lean`), for "the good-event cap
for a tile doubled across `∂𝔠_m` — a variant of
`exists_localBoundaryEllipticityCaps_nextWindow` at scale `k − j`".

A tile straddling `∂𝔠_m` is *not* a triadic descendant of the projected parent
`Q = originCube d (n−2)`: the met face of `P_q` sits at a distance from `Q`'s
own faces which is not a multiple of any tile side (§11.4).  In GMC's
translated-sample formalism such a tile is nevertheless an honest triadic
cube: it is `originCube d k` read in the frame translated by its centre `p`,
with coefficient family `aCutoffFamily M L (translatePotentialSample p omega)`.
So what is needed is the ellipticity cap of
`Section6HarmonicApproximation.exists_localBoundaryEllipticityCaps_nextWindow`
with the *inner* cube scale left free.

Searching before proving: the whole chain that produces that cap is already
scale-generic except for one line.
`Section6HarmonicApproximation.localHomogenizationError_two_le_anchor_of_closedContainment`
fixes the inner cube to `originCube d ((n : ℤ) − 2)` only in order to evaluate
`(K.scale − P.scale).toNat = 4`; the tool it calls,
`LambdaStabilitySupport.offGridErrorFunctional_le_slot`, is already stated for
arbitrary `P` and `K`, and
`Section6HarmonicApproximation.localBoundaryEllipticityCaps_of_errorCap` is
already stated for an arbitrary cube.  This module therefore only re-runs that
one transport with the inner scale as a parameter, and reads off the `s/3`
lower cap.

The price of dropping the inner cube by `j` scales is the single factor
`3^{(s/8) j}` inside the error, hence `3^{(s/4) j}` inside `B` and
`3^{(s/8) j}` inside `√(B σ⁻¹)`.  At the frozen parameters `s ≤ 1/4`, so that
factor is at most `3^{j/32}`, while the tile gain of
`TileCoarsePoincare.aCutoff_cubeFluctuation_lpNorm_descendant_le_of_lambdaSCap`
is `3^{-(1−t) j}` with `1 − t ≥ 11/12`.  The tile depth therefore remains a
genuinely free parameter with a net geometric gain.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **Scale-generic local error transport.**  The good-scale error at the
anchor cube `z + 𝔠_{n+2}` controls the Chapter-2 homogenization error of the
translated cube `y + 𝔠_k` for *every* scale `k` whose translate is contained
in the anchor, with the single explicit loss `3^{(s/8)(n+2−k)}`.

This is `localHomogenizationError_two_le_anchor_of_closedContainment` with the
inner scale left free; its proof is the same off-grid stability slot. -/
theorem localHomogenizationError_two_le_anchor_atScale
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L n : ℕ) (hnL : n + 2 ≤ L) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (y z : Vec d)
    (hcontain : translateSet (y - z) (cubeSet (originCube d k)) ⊆
      cubeSet (originCube d ((n : ℤ) + 2)))
    (hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)) :
    Ch02.HomogenizationErrorOnCube (originCube d k) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  let P : TriadicCube d := originCube d k
  let K : TriadicCube d := originCube d ((n : ℤ) + 2)
  let w : Vec d := y - z
  let A := aCutoffFamily M L (translatePotentialSample z omega)
  let A' := aCutoffFamily M L (translatePotentialSample y omega)
  let a : CoeffField d :=
    scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega))
  let sigma : ℝ := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hrep : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = a := by
    intro Q
    rfl
  have hcompact : IsCompact (closure (cubeSet K)) :=
    (isBounded_cubeSet K).isCompact_closure
  have hnonempty : (closure (cubeSet K)).Nonempty :=
    ⟨cubeCenter K, subset_closure (cubeCenter_mem_cubeSet K)⟩
  let a0 := _root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega)
  have ha : Continuous a0 :=
    _root_.SubdiffusiveProcess.Model.continuous_aCutoff M L (translatePotentialSample z omega)
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty ha.continuousOn
  have hTmeas : MeasurableSet (translateSet w (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage (measurable_id.sub measurable_const)
  have hEll : IsEllipticFieldOn (a0 xmin) (a0 xmax)
      (translateSet w (cubeSet P)) a := by
    constructor
    · have hmatrix : Continuous fun p : Vec d => scalarCoeffField a0 p :=
        ha.smul continuous_const
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      have hentry : Measurable fun p : Vec d => scalarCoeffField a0 p i j :=
        (continuous_apply j).comp ((continuous_apply i).comp hmatrix) |>.measurable
      exact Measurable.ite hTmeas hentry measurable_const
    · intro p hp
      have hpK : p ∈ closure (cubeSet K) := subset_closure (hcontain hp)
      have hlow : a0 xmin ≤ a0 p := hmin hpK
      have hupp : a0 p ≤ a0 xmax := hmax hpK
      exact (isEllipticMatrix_scalarMatrix
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L (translatePotentialSample z omega) p)).mono
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L
            (translatePotentialSample z omega) xmin) hlow hupp
  have hstab := offGridErrorFunctional_le_slot
    (w := w) (P := P) (K := K) A (scalarMatrix (d := d) sigma)
      hs0 (hs.2.trans (by norm_num)) hrep hEll hcontain
  have hscale : (((K.scale - P.scale).toNat : ℕ) : ℝ) =
      ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) := rfl
  rw [hscale] at hstab
  have hframe := offGridErrorFunctional_eq_homogenizationErrorOnCube_translate
    w P (by linarith only [hs0] : 0 < s / 6) A' a
      (aCutoffFamily_coeffField_translate_sub M L omega y z)
      (scalarMatrix (d := d) sigma)
  have hparent := homogenizationErrorOnCube_aCutoff_le_section6_of_goodEvent
    M (s := s / 8) (L := L) (m := n + 2)
      (by linarith only [hs.1]) (by linarith only [hs.2]) hnL omega z hgood
  have hparent' : Ch02.HomogenizationErrorOnCube K (s / 8)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤
      section6HomogenizationError M (s / 8) L (n + 2) omega z := by
    simpa [K, A, sigma,
      Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] using! hparent
  rw [← hframe]
  exact hstab.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hparent' (Real.rpow_nonneg (by norm_num) _))
    (Real.sqrt_nonneg _))

/-- The dimension-only ellipticity constant of a tile whose scale is `jj`
levels below the anchor's inner cube: `2 d (E₀² + 1)` with the error budget
`E₀ = √(192 d) · 3^{(s/8) jj} · C`. -/
def tileEllipticityConst (d : ℕ) (C s jj : ℝ) : ℝ :=
  2 * (d : ℝ) *
    ((Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 8 * jj) * C)) ^ 2 + 1)

theorem tileEllipticityConst_pos (d : ℕ) [NeZero d] (C s jj : ℝ) :
    0 < tileEllipticityConst d C s jj := by
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  unfold tileEllipticityConst
  positivity

/-- **The good-event coarse ellipticity cap on a tile of arbitrary scale.**
For every translated cube `y + 𝔠_k` contained in the anchor `z + 𝔠_{n+2}`, the
frozen good event supplies the coarse lower-ellipticity cap

```text
(lambda_{s/3}(originCube d k ; A_y))⁻¹ ≤ tileEllipticityConst d C s (n+2−k) * σ⁻¹ ,
```

with `C` dimension-only.  This is the tile form of
`exists_localBoundaryEllipticityCaps_nextWindow`; feeding it to
`TileCoarsePoincare.aCutoff_cubeFluctuation_lpNorm_le_of_lambdaSCap` prices the
tile's `L²` oscillation with no pointwise `aCutoff/σ` ratio anywhere. -/
theorem exists_localTileEllipticityCap (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L → ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        (Ch02.lambdaS (originCube d k) (s / 3) A)⁻¹ ≤
          tileEllipticityConst d C s ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) * sigma⁻¹ := by
  obtain ⟨C, hC, hgoodCap⟩ := exists_section6HomogenizationError_le_of_goodEvent (d := d)
  refine ⟨3 * C, by positivity, ?_⟩
  intro M s hs L n hnL k omega y z hcontain hgood
  dsimp only
  set Q : TriadicCube d := originCube d k with hQ
  set A := aCutoffFamily M L (translatePotentialSample y omega) with hAdef
  set sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z) with hsig
  set jj : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) with hjj
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    rw [hsig]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using! h
  have hsection := hgoodCap M s hs L (n + 2) hnL omega z hgood
  have hlocal := localHomogenizationError_two_le_anchor_atScale M hs L n hnL k
    omega y z hcontain hgood
  have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
    ENNReal.toReal_nonneg
  have hE₀ : Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
      (scalarMatrix (d := d) sigma) ≤
        Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 8 * jj) * (3 * C)) := by
    refine hlocal.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    exact hsection.trans (by linarith only [hC])
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hE₀
  simpa [tileEllipticityConst] using! hcaps.2.2.2.1

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
