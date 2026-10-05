
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellCover
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsExponentBridge

@[expose] public section

/-!
# One coarse energy constant for the whole mesoscopic box

`exists_mesoscopic_coarseEnergyBoundOn_mesoCell`
(`WholeSpaceRowsCellCover.lean`, P-232 §2) produces the coarse energy bound on
one mesoscopic cell with the constant

`caccioppoliWithRHSPrefactor Ccacc (originCube d k) afam s t * Gam0`,

where `afam` is the coefficient family **of that cell** (the translate of the
ambient coefficient by the cell centre).  The energy leg
`coarseEnergyBoundOn_contraction_pair_of_mesoCells` needs a *single* `Gam` for
every cell of the index box, so the cell dependence has to be removed.

The only cell-dependent factor of `caccioppoliWithRHSPrefactor` is
`Ch02.ThetaRatio (originCube d k) s t afam`, which enters through a positive
`rpow` exponent `(1 - t) / (1 - s - t)`.  So a uniform *upper bound* `B` on that
ratio over the box gives a uniform constant, and that is all this file does:

* `coarseCaccioppoliUniformPrefactor` — the prefactor with the ratio replaced by
  a bound `B`;
* `caccioppoliWithRHSPrefactor_le_of_thetaRatio_le` — the monotonicity;
* `exists_uniform_mesoscopic_coarseEnergyBoundOn_mesoCell` — the uniform form of
  P-232's per-cell energy bound.

Where `B` comes from is a separate question, answered by the off-grid transfer
theorems (`WholeSpaceRowsOffGridEllipticity.lambdaSq_translated_inv_le`,
`LambdaSq_translated_le` and `WholeSpaceRowsExponentBridge.thetaRatio_translated_le`),
which bound the ratio of a *translate* of a triadic cube by the ratio of any
triadic cube containing it — in the application, a triadic cube containing the
contraction cube.  `thetaRatio_mesoCell_le` below is that specialization.

Argument: `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## 1. Monotonicity of the Caccioppoli prefactor in the ellipticity ratio -/

/-- The Caccioppoli-with-forcing prefactor of `Homogenization.Book.Ch03`, with
the coarse ellipticity ratio `Θ_{s,t}(Q;a)` replaced by an upper bound `B`.

By `caccioppoliWithRHSPrefactor_le_of_thetaRatio_le` this dominates
`caccioppoliWithRHSPrefactor C Q a s t` for every cube `Q` and family `a` whose
ratio is at most `B`; it depends only on `C`, `s`, `t` and `B`. -/
def coarseCaccioppoliUniformPrefactor (C s t B : ℝ) : ℝ :=
  Real.rpow (C / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
    Real.rpow s (-(2 * s / (1 - s - t))) *
    Real.rpow B ((1 - t) / (1 - s - t))

/-- The coarse ellipticity ratio is nonnegative. -/
theorem thetaRatio_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 ≤ Ch02.ThetaRatio Q s t a := by
  have hU0 : 0 ≤ Ch02.LambdaS Q s a :=
    Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num)
  have hL0 : 0 ≤ (Ch02.lambdaS Q t a)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num))
  rw [Ch02.ThetaRatio, div_eq_mul_inv]
  exact mul_nonneg hU0 hL0

/-- **Monotonicity of the Caccioppoli prefactor in the ellipticity ratio.**

`caccioppoliWithRHSPrefactor` is `(C/(1-s-t))^{2+4s/(1-s-t)} s^{-2s/(1-s-t)}`
times `Θ_{s,t}(Q;a)^{(1-t)/(1-s-t)}`, and the exponent of the ratio is
nonnegative in the admissible range `0 < s`, `0 < t < 1`, `s + t < 1`.  So an
upper bound on the ratio gives an upper bound on the prefactor with the same
`C`, `s`, `t`. -/
theorem caccioppoliWithRHSPrefactor_le_of_thetaRatio_le [NeZero d]
    {C B s t : ℝ} (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (hC0 : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hB : Ch02.ThetaRatio Q s t a ≤ B) :
    caccioppoliWithRHSPrefactor C Q a s t ≤
      coarseCaccioppoliUniformPrefactor C s t B := by
  have hden : 0 < 1 - s - t := by linarith
  have hexp : 0 ≤ (1 - t) / (1 - s - t) := div_nonneg (by linarith) hden.le
  have hratio := thetaRatio_nonneg Q a hs ht
  have hpow : Real.rpow (Ch02.ThetaRatio Q s t a) ((1 - t) / (1 - s - t)) ≤
      Real.rpow B ((1 - t) / (1 - s - t)) :=
    Real.rpow_le_rpow hratio hB hexp
  have hfront : 0 ≤ Real.rpow (C / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
      Real.rpow s (-(2 * s / (1 - s - t))) :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg hC0 hden.le) _) (Real.rpow_nonneg hs.le _)
  rw [caccioppoliWithRHSPrefactor, coarseCaccioppoliUniformPrefactor]
  exact mul_le_mul_of_nonneg_left hpow hfront

/-! ## 2. The uniform per-cell coarse energy bound -/

/-- **P-232's per-cell coarse energy bound with one constant for the whole
box.**

Identical to `exists_mesoscopic_coarseEnergyBoundOn_mesoCell` except that the
conclusion's constant is
`coarseCaccioppoliUniformPrefactor Ccacc s t B * Gam0`, which does not depend on
the cell: the cell only enters through the hypothesis
`Ch02.ThetaRatio (originCube d k) s t (afam n) ≤ B`.

This is the shape `coarseEnergyBoundOn_contraction_pair_of_mesoCells` consumes.
-/
theorem exists_uniform_mesoscopic_coarseEnergyBoundOn_mesoCell
    (d : ℕ) [NeZero d] {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    ∃ Ccacc Gam0 : ℝ, 0 < Ccacc ∧ 0 ≤ Gam0 ∧
      ∀ (k : ℤ) (a : Vec d → ℝ) (s T B : ℝ)
        (afam : (Fin d → ℤ) → CoeffFamily d)
        (u : ∀ n : Fin d → ℤ, H1Function (mesoCell d k n)),
        0 < s → s < 1 → s + t < 1 → 0 < T →
        ∀ n : Fin d → ℤ,
        (∀ y, ((afam n).coeffOn (originCube d k)).toCoeffField y =
          scalarCoeffField (fun p => a (p + mesoCentre d k n)) y) →
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (mesoCell d k n) (u n)
          (fun _ ↦ (0 : ℝ)) →
        (cubeScaleFactor (originCube d k)) ^ 2 ≤
          Ch02.lambdaS (originCube d k) t (afam n) * T →
        Ch02.lambdaS (originCube d k) t (afam n) * T ≤
          9 * (cubeScaleFactor (originCube d k)) ^ 2 →
        Ch02.ThetaRatio (originCube d k) s t (afam n) ≤ B →
        CoarseEnergyBoundOn a (mesoCell d k n) (mesoCore d k n) (u n).toFun
          (u n).grad T (coarseCaccioppoliUniformPrefactor Ccacc s t B * Gam0) := by
  obtain ⟨Ccacc, Gam0, hC, hG, hbound⟩ :=
    exists_mesoscopic_coarseEnergyBoundOn_mesoCell d ht ht2
  refine ⟨Ccacc, Gam0, hC, hG, ?_⟩
  intro k a s T B afam u hs hs1 hst hT n hA hu hlo hhi hTheta
  have hbase := hbound k n (afam n) a s T (u n) hA hu hs hs1 hst hT hlo hhi
  have hmono : caccioppoliWithRHSPrefactor Ccacc (originCube d k) (afam n) s t ≤
      coarseCaccioppoliUniformPrefactor Ccacc s t B :=
    caccioppoliWithRHSPrefactor_le_of_thetaRatio_le (originCube d k) (afam n)
      hC.le hs ht hst hTheta
  refine le_trans hbase ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmono hG)
    (setIntegral_nonneg (measurableSet_mesoCell k n) fun x _ ↦ sq_nonneg _)

/-! ## 3. Where the uniform bound `B` comes from

The off-grid transfer theorems bound the coarse ellipticities of a *translate*
of a triadic cube by those of any triadic cube containing the translate.  Applied
with `P = originCube d k`, `w = mesoCentre d k n` and `K` a triadic cube
containing the contraction cube, they give one `B` for the whole index box: the
right-hand side below does not mention `n`. -/

/-- The translate of a scalar coefficient field is the scalar field of the
translated representative. -/
theorem translateCoeffField_scalarCoeffField (z : Vec d) (a : Vec d → ℝ) :
    translateCoeffField z (scalarCoeffField a) =
      scalarCoeffField (fun p => a (p + z)) := by
  funext x
  simp [translateCoeffField, scalarCoeffField]
  rfl

/-- **A uniform ellipticity-ratio bound over the mesoscopic index box.**

`WholeSpaceRowsExponentBridge.thetaRatio_translated_le` at the origin cube of
scale `k`, with the cell centre as translation vector: the bound depends on the
enclosing triadic cube `K`, on `d, s, t, u` and on the scale gap
`K.scale - k`, but **not** on the cell `n`.  Feeding it into
`exists_uniform_mesoscopic_coarseEnergyBoundOn_mesoCell` gives one coarse energy
constant for the whole box. -/
theorem thetaRatio_mesoCell_le [NeZero d] {k : ℤ} {K : TriadicCube d}
    {a : Vec d → ℝ} {lam Lam s t u : ℝ}
    (A : CoeffFamily d) (Aw : (Fin d → ℤ) → CoeffFamily d)
    (hs0 : 0 < s) (ht0 : 0 < t) (hu0 : 0 < u) (hus : u < s / 2) (hut : u < t / 2)
    (hs : s / 2 ≤ 1 / 2) (ht : t / 2 ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = scalarCoeffField a)
    (hgw : ∀ (n : Fin d → ℤ) (S : TriadicCube d),
      ((Aw n).coeffOn S).toCoeffField =
        scalarCoeffField (fun p => a (p + mesoCentre d k n)))
    (hEll : ∀ n : Fin d → ℤ, IsEllipticFieldOn lam Lam
      (translateSet (mesoCentre d k n) (cubeSet (originCube d k)))
      (scalarCoeffField a))
    (hcontain : ∀ n : Fin d → ℤ,
      translateSet (mesoCentre d k n) (cubeSet (originCube d k)) ⊆ cubeSet K)
    (n : Fin d → ℤ) :
    Ch02.ThetaRatio (originCube d k) s t (Aw n) ≤
      (SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.offGridStabilityConst d (s / 2) u *
          SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.offGridStabilityConst d (t / 2) u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - k).toNat : ℕ) : ℝ)) *
            (3 : ℝ) ^ (2 * u * (((K.scale - k).toNat : ℕ) : ℝ)) *
          (Ch02.LambdaSq K u (.finite 2) A *
            (Ch02.lambdaSq K u (.finite 2) A)⁻¹)) := by
  have hgw' : ∀ S : TriadicCube d,
      ((Aw n).coeffOn S).toCoeffField =
        translateCoeffField (mesoCentre d k n) (scalarCoeffField a) := by
    intro S
    rw [hgw n S, translateCoeffField_scalarCoeffField]
  exact thetaRatio_translated_le (w := mesoCentre d k n) (P := originCube d k)
    (K := K) (g := scalarCoeffField a) (lam := lam) (Lam := Lam) A (Aw n)
    hs0 ht0 hu0 hus hut hs ht hg hgw' (hEll n) (hcontain n)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
