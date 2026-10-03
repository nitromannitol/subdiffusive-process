module

public import SubdiffusiveProcess.Analysis.SmoothDualInteriorLeg

@[expose] public section

/-!
# Event-generic smooth-dual interior leg

The interior harmonic chain reads its good event through raw-error finiteness
and the error cap at the anchor `(n + 2, z, s / 8)`. The generic result below
also recovers the threshold-6 cutoff-event instance.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.SmoothDualScratch

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualScratch
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section

section Generic

variable {d : ℕ} [NeZero d]

/-- Read 1 at an anchor `(m, z, s)`: the raw `ENNReal` paper error is finite, i.e. it is
the `ofReal` of `section6HomogenizationError`. -/
def aux_AnchorFinite (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) (z : Vec d)
    (s : ℝ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : Prop :=
  paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s
      .infinity (.finite 2)
      (aCutoffFamily M L (translatePotentialSample z omega))
      (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) =
    ENNReal.ofReal (section6HomogenizationError M s L m omega z)

/-! ### Local error transport from the finiteness read -/

/-- Cutoff companion of
`Section6HarmonicApproximation.homogenizationErrorOnCube_aCutoff_le_section6_of_goodEvent`,
with no relation between `L` and `m`. -/
theorem aux_gen_errorOnCube_le_section6
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (_hsUpper : s ≤ 1 / 2) (L m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hfin : aux_AnchorFinite M L m z s omega) :
    Ch02.HomogenizationErrorOnCube (originCube d (m : ℤ)) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (scalarMatrix (d := d)
          (tailCoefficientCubeAverage M L m (translatePotentialSample z omega))) ≤
      section6HomogenizationError M s L m omega z := by
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  have hsigma : 0 < tailCoefficientCubeAverage M L m
      (translatePotentialSample z omega) :=
    tailCoefficientCubeAverage_pos M L m (translatePotentialSample z omega)
  have hraw := ofReal_homogenizationErrorOnCube_infinity_two_le_paper
    (originCube d (m : ℤ))
    (aCutoffFamily M L (translatePotentialSample z omega))
    (fun R => (aCutoffTriadicData M L
      (translatePotentialSample z omega)).onCube R |>.isSymmetric)
    hs0 hsigma
  change ENNReal.ofReal _ ≤ paperHomogenizationError
    (originCube d (m : ℤ)) (m : ℤ) s .infinity (.finite 2)
      (aCutoffFamily M L (translatePotentialSample z omega))
      (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) at hraw
  have hfin' := hfin
  unfold aux_AnchorFinite at hfin'
  rw [hfin'] at hraw
  exact (ENNReal.ofReal_le_ofReal_iff
    (ENNReal.toReal_nonneg : 0 ≤ section6HomogenizationError M s L m omega z)).mp hraw

/-- **Cutoff local error transport.**  Companion of
`Section6HarmonicApproximation.localHomogenizationError_two_le_anchor_of_closedContainment`
on the cutoff good event, with the binder `n + 2 ≤ L` deleted. -/
theorem aux_gen_localError_two_le_anchor_of_closedContainment
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L n : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
    (hcontain : translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
      cubeSet (originCube d ((n : ℤ) + 2)))
    (hfin : aux_AnchorFinite M L (n + 2) z (s / 8) omega) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  let P : TriadicCube d := originCube d ((n : ℤ) - 2)
  let K : TriadicCube d := originCube d ((n : ℤ) + 2)
  let w : Vec d := y - z
  let A := aCutoffFamily M L (translatePotentialSample z omega)
  let A' := aCutoffFamily M L (translatePotentialSample y omega)
  let a : CoeffField d :=
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample z omega))
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
  let a0 := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample z omega)
  have ha : Continuous a0 :=
    SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L (translatePotentialSample z omega)
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
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L (translatePotentialSample z omega) p)).mono
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L
            (translatePotentialSample z omega) xmin) hlow hupp
  have hstab := offGridErrorFunctional_le_slot
    (w := w) (P := P) (K := K) A (scalarMatrix (d := d) sigma)
      hs0 (hs.2.trans (by norm_num)) hrep hEll hcontain
  have hscale : (((K.scale - P.scale).toNat : ℕ) : ℝ) = 4 := by
    change (((((n : ℤ) + 2) - ((n : ℤ) - 2)).toNat : ℕ) : ℝ) = 4
    rw [show ((n : ℤ) + 2) - ((n : ℤ) - 2) = 4 by ring]
    rfl
  rw [hscale] at hstab
  have hframe := offGridErrorFunctional_eq_homogenizationErrorOnCube_translate
    w P (by linarith only [hs0] : 0 < s / 6) A' a
      (aCutoffFamily_coeffField_translate_sub M L omega y z)
      (scalarMatrix (d := d) sigma)
  have hparent := aux_gen_errorOnCube_le_section6
    M (s := s / 8) (by linarith only [hs.1]) (by linarith only [hs.2]) L (n + 2)
      omega z hfin
  have hparent' : Ch02.HomogenizationErrorOnCube K (s / 8)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤
      section6HomogenizationError M (s / 8) L (n + 2) omega z := by
    simpa [K, A, sigma,
      Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] using hparent
  rw [← hframe]
  exact hstab.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hparent' (Real.rpow_nonneg (by norm_num) _))
    (Real.sqrt_nonneg _))

/-- The projected-cell variant of the cutoff transport: the comparison cube's
centre ranges over the next truncated window. -/
theorem aux_gen_localError_two_le_anchor_nextWindow
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L m n : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x y z : Vec d)
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hy : y ∈ truncatedCube d m n x)
    (hfin : aux_AnchorFinite M L (n + 2) z (s / 8) omega) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  apply aux_gen_localError_two_le_anchor_of_closedContainment M hs L n
    omega y z
  · exact closedOffGridCube_subset_originAnchorParent_of_mem_nextWindow hx hy
  · exact hfin
/-! ### Ellipticity caps from the two reads -/

/-- The `E₀`/`B` pair of the cutoff caps, and the error cap in the shape the
deterministic converter consumes. -/
theorem aux_gen_errorCapPair (d : ℕ) [NeZero d] (Cerr : ℝ) (hCerr : 0 < Cerr) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ,
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        x ∈ truncatedCube d m (n - 3) z →
        y ∈ truncatedCube d m n x →
aux_AnchorFinite M L (n + 2) z (s / 8) omega →
        section6HomogenizationError M (s / 8) L (n + 2) omega z ≤ Cerr →
        Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
            .infinity (.finite 2)
            (aCutoffFamily M L (translatePotentialSample y omega))
            (scalarMatrix (d := d)
              (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
          Real.sqrt (192 * (d : ℝ)) * (3 * C) := by
  refine ⟨Cerr, hCerr, ?_⟩
  intro M s hs L m n z x y omega hx hy hfin hcapE
  refine (aux_gen_localError_two_le_anchor_nextWindow
    M hs L m n omega x y z hx hy hfin).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hexp : s / 8 * (4 : ℝ) ≤ 1 := by linarith only [hs.2]
  have hpow : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 3 := by norm_num
  have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
    ENNReal.toReal_nonneg
  exact (mul_le_mul_of_nonneg_right hpow hsec0).trans
    (mul_le_mul_of_nonneg_left hcapE (by norm_num))

/-- **The finite-cutoff ellipticity caps.**  Companion of
`Section6HarmonicApproximation.exists_localBoundaryEllipticityCaps_nextWindow`
on the good event `𝒢^{(L)}_{n+2,z}`, with the binder `n + 2 ≤ L` deleted. -/
theorem aux_gen_localEllipticityCaps_nextWindow (d : ℕ) [NeZero d]
    (Cerr : ℝ) (hCerr : 0 < Cerr) :
    ∃ E₀ B : ℝ, 0 < E₀ ∧ 0 < B ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        y ∈ truncatedCube d m n x →
aux_AnchorFinite M L (n + 2) z (s / 8) omega →
        section6HomogenizationError M (s / 8) L (n + 2) omega z ≤ Cerr →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
              (scalarMatrix (d := d) sigma) ≤ E₀ ∧
          sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B ∧
          sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B ∧
          Ch02.LambdaS Q (1 / 2) A ≤ B * sigma ∧
          (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ ∧
          Ch02.lambdaS Q (s / 3) A ≤ B * sigma ∧
          Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ) := by
  obtain ⟨C, hC, hcap⟩ := aux_gen_errorCapPair d Cerr hCerr
  let E₀ : ℝ := Real.sqrt (192 * (d : ℝ)) * (3 * C)
  let B : ℝ := 2 * (d : ℝ) * (E₀ ^ 2 + 1)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hE₀ : 0 < E₀ := by
    dsimp [E₀]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨E₀, B, hE₀, hB, ?_⟩
  intro M s hs L m n z x y omega hx hy hfin hcapE
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have hlocalCap : Ch02.HomogenizationErrorOnCube Q (s / 6)
      .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E₀ :=
    hcap M s hs L m n z x y omega hx hy hfin hcapE
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hlocalCap
  simpa only [Q, A, sigma, B] using ⟨hlocalCap, hcaps⟩
/-! ### Interior cell energy from the two reads (verbatim re-run of `CutoffCellEnergy`) -/

theorem aux_gen_publicIsForcedEquation_neg_of_divForm
    {Q : TriadicCube d} {a : CoeffFamily d}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn
      (fun x => ((a.coeffOn Q).toCoeffField x) 0 0) (openCubeSet Q) u g)
    (hscalar : ∀ x, (a.coeffOn Q).toCoeffField x =
      scalarMatrix (d := d) (((a.coeffOn Q).toCoeffField x) 0 0)) :
    IsForcedEquation Q a u (fun x => -g x) := by
  intro phi
  have hflux : ∀ x,
      matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x) =
        (((a.coeffOn Q).toCoeffField x) 0 0) • u.grad x := by
    intro x
    have ha := congrArg (fun A => matVecMul A (u.grad x)) (hscalar x)
    exact ha.trans (matVecMul_scalarMatrix _ _)
  have hneg : (fun x => vecDot (-g x) (phi.toH1Function.grad x)) =
      fun x => -vecDot (g x) (phi.toH1Function.grad x) := by
    funext x
    exact vecDot_neg_left _ _
  simp only [Ch02.cubeDomain_coe]
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot ((((a.coeffOn Q).toCoeffField x) 0 0) • u.grad x)
          (phi.toH1Function.grad x) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          exact congrArg (fun z => vecDot z (phi.toH1Function.grad x)) (hflux x))
    _ = -∫ x in openCubeSet Q,
        vecDot (g x) (phi.toH1Function.grad x) ∂volume := h phi
    _ = ∫ x in openCubeSet Q,
        vecDot ((fun x => -g x) x) (phi.toH1Function.grad x) ∂volume := by
      rw [hneg, integral_neg]

noncomputable def aux_gen_wspFieldOfFull
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    CubeEuclideanWspField Q s FiniteLpExponent.two where
  toField := f
  euclideanMemLp := hf.1
  euclideanMemWsp := hf.2

omit [NeZero d] in
@[simp] theorem aux_gen_wspFieldOfFull_toField
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    (aux_gen_wspFieldOfFull hf).toField = f := rfl

theorem aux_gen_forceBesovRegularity_neg_of_interiorFull
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    ForceBesovRegularity Q s.1 (fun x => -f x) := by
  let F := negCubeEuclideanWspField (aux_gen_wspFieldOfFull hf)
  have hsob := cubeEuclideanWspField_forceSobolevRegularity s F
  simpa [F] using hsob.toForceBesovRegularity s.2.1 s.2.2.le

theorem aux_gen_projectedInteriorCellEnergy_readout
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
        (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d) (c0 : ℝ),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        sOrder.1 ≤ 1 / 4 → k ≤ (m : ℤ) → q ∈ cube d (m : ℤ) →
        openCubeAtScale
            (q - Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) (k - 1) ⊆
          openCubeSet (originCube d k) →
        ∃ g0 : Vec d → Vec d,
          ∃ u0 : H1Function (openCubeSet (originCube d k)),
            (∀ x, g0 x = g (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d k) sOrder
              FiniteLpExponent.two (fun x => g (x +
                Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            (∀ x, u0.toFun x = u.toFun (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            IsForcedEquation (originCube d k)
                (aCutoffFamily M L
                  (translatePotentialSample
                    (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                u0 (fun x => -g0 x) ∧
            ForceBesovRegularity (originCube d k) sOrder.1 (fun x => -g0 x) ∧
            normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
                (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                  vecNormSq (u.grad x)) ≤
              (81 : ℝ) ^ d *
                (caccioppoliWithRHSPrefactor C (originCube d k)
                    (aCutoffFamily M L
                      (translatePotentialSample
                        (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                    (1 / 2) (sOrder.1 / 2) *
                  (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                      (aCutoffFamily M L
                        (translatePotentialSample
                          (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)) *
                    Real.rpow (3 : ℝ) (-2 * (((originCube d k).scale : ℤ) : ℝ)) *
                    normalizedL2SqOnSet (openCubeSet (originCube d k))
                      (fun y => u0.toFun y - c0) +
                  Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                    Real.rpow
                      (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                        (aCutoffFamily M L
                          (translatePotentialSample
                            (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)))
                      (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo
                      (originCube d k) sOrder.1 (fun x => -g0 x) ^ 2)) := by
  obtain ⟨C, hC, hinterior⟩ := exists_interior_caccioppoli_quarter_subConst d
  refine ⟨C, hC, ?_⟩
  intro M L omega m k q sOrder u g c0 hweak hg hs4 hkm hq hpatch
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  have hP : translateSet c (openCubeSet Q) = translatedCube d k c := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  have hsub : translateSet c (openCubeSet Q) ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    rw [hP]
    exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkm
  have hPopen : IsOpen (translateSet c (openCubeSet Q)) :=
    ((isOpenBoundedConvexDomain_openCubeSet Q).translateSet c).isOpen
  let uP : H1Function (translateSet c (openCubeSet Q)) := u.restrict hPopen hsub
  let u0 : H1Function (openCubeSet Q) := H1Function.untranslate c uP
  let g0 : Vec d → Vec d := fun x => g (x + c)
  have hweak' : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (openCubeSet (originCube d (m : ℤ))) u g := by
    simpa [cube] using hweak
  have heqP : IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (translateSet c (openCubeSet Q)) uP g :=
    isDivFormWeakSolutionOn_restrict
      (isOpenBoundedConvexDomain_openCubeSet (originCube d (m : ℤ))).isOpen
      hPopen hsub hweak'
  have heq0 : IsDivFormWeakSolutionOn
      (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x + c))
      (openCubeSet Q) u0 g0 :=
    isDivFormWeakSolutionOn_untranslate c heqP
  have hcoeff : ∀ x, (A.coeffOn Q).toCoeffField x =
      scalarMatrix (d := d) (((A.coeffOn Q).toCoeffField x) 0 0) := by
    intro x
    simp [A, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField]
  have hfield : (fun x => ((A.coeffOn Q).toCoeffField x) 0 0) =
      fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x + c) := by
    funext x
    simp [A, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Section6Covariance.aCutoff_translatePotentialSample]
  have heqPublic : IsForcedEquation Q A u0 (fun x => -g0 x) := by
    apply aux_gen_publicIsForcedEquation_neg_of_divForm (a := A) (g := g0)
    · rw [hfield]
      exact heq0
    · exact hcoeff
  have hgLocal : Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
      FiniteLpExponent.two (fun x => g (x + c)) :=
    memCubeEuclideanFullWsp_translate_of_subset Q
      (originCube d (m : ℤ)) c sOrder FiniteLpExponent.two g hsub hg
  have hgReg : ForceBesovRegularity Q sOrder.1 (fun x => -g0 x) := by
    exact aux_gen_forceBesovRegularity_neg_of_interiorFull hgLocal
  have hbound := hinterior u0 c0 heqPublic
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by linarith only [sOrder.2.1] : 0 < sOrder.1 / 2)
    (by linarith only [hs4] : sOrder.1 / 2 ≤ 1 / 4)
    (by linarith only [sOrder.2.2] : (1 / 2 : ℝ) + sOrder.1 / 2 < 1)
    hpatch (by simpa [show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hgReg)
  have hu0val : ∀ x, u0.toFun x = u.toFun (x + c) := by
    intro x
    rw [H1Function.untranslate_toFun]
    rfl
  have hu0grad : ∀ x, u0.grad x = u.grad (x + c) := by
    intro x
    rw [H1Function.untranslate_grad]
    rfl
  have hread := normalizedCutoffEnergy_truncatedCube_le_projectedCore
    M L omega hq hkm u u0 hu0grad
  have hfactor : (0 : ℝ) ≤ (81 : ℝ) ^ d := by positivity
  have hfinal := hread.trans (mul_le_mul_of_nonneg_left hbound hfactor)
  refine ⟨g0, u0, ?_, hgLocal, hu0val, heqPublic, hgReg, ?_⟩
  · intro x
    rfl
  · simpa [Q, A, c, show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hfinal

theorem aux_gen_interiorCellEnergy_le_windowPrices
    (d : ℕ) [NeZero d] (Cerr : ℝ) (hCerr : 0 < Cerr) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
aux_AnchorFinite M L (n + 2) z (sOrder.1 / 8) omega →
        section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z ≤ Cerr →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let k : ℤ := (n : ℤ) - 2
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          (81 : ℝ) ^ d *
            ((4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) *
              (B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
                  ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  normalizedL2On U
                    (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
                Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                  (B * sigma⁻¹) *
                  (caccioppoliExactDatumConstant d *
                    cubeBesovScaleWeight (-sOrder.1) Q *
                    (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                      (Real.sqrt ((volume U).toReal /
                          (volume (translatedCube d k c)).toReal) *
                        (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2)) := by
  obtain ⟨C, hC, hinterior⟩ := aux_gen_projectedInteriorCellEnergy_readout d
  obtain ⟨_E, B, _hE, hB, hcaps⟩ :=
    aux_gen_localEllipticityCaps_nextWindow d Cerr hCerr
  refine ⟨C, B, hC, hB, ?_⟩
  intro M sOrder hs L m n hnm z x q omega hz hx hq hpatchPhysical hfin hcapE
    u g hweak hg
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  let U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hpatch : openCubeAtScale (q - c) (k - 1) ⊆ openCubeSet Q := by
    have hbase := openCubeAtScale_wellPlaced_pullback_subset_originCube
      (d := d) (m := (m : ℤ)) (k := k) (q := q) hkm
      (by simpa only [k, sub_sub, sub_self, sub_zero] using! hpatchPhysical)
    simpa only [c, Q] using hbase
  have hPsub : translatedCube d k c ⊆ U := by
    exact translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k, U] using hq) hkm
  have hcU : c ∈ U := hPsub (by
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    simpa using Section6ExcessDecay.zero_mem_cube d k)
  have hUsub : U ⊆ openCubeSet (originCube d (m : ℤ)) := by
    intro y hy
    exact hy.2
  have hUpos : 0 < (volume U).toReal :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos x hxDomain (by omega)
  have hPpos : 0 < (volume (translatedCube d k c)).toReal := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hU0 : volume U ≠ 0 := (ENNReal.toReal_ne_zero.mp hUpos.ne').1
  have hUtop : volume U ≠ ⊤ :=
    (Section6ExcessDecay.volume_truncatedCube_lt_top d (m : ℤ) (n : ℤ) x).ne
  have hPpair' : volume (translateSet c (openCubeSet Q)) ≠ 0 ∧
      volume (translateSet c (openCubeSet Q)) ≠ ⊤ := by
    rw [volume_translateSet_eq]
    constructor
    · intro hzero
      have hz := congrArg ENNReal.toReal hzero
      rw [volume_openCubeSet_toReal] at hz
      exact (cubeVolume_pos Q).ne' hz
    · exact (volume_openCubeSet_lt_top Q).ne
  have hgUfin : fractionalSeminormOn U sOrder.1 g ≠ ⊤ := by
    have hfrac : MemFractionalOn (cube d (m : ℤ)) sOrder.1 g := by
      change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ)))
        sOrder.1 g ≠ ⊤
      rw [fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable _ _ _ hg.2.aestronglyMeasurable]
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hg.2.eSeminorm_lt_top.ne
    exact memFractionalOn_truncatedCube_of_domain hxDomain (by omega) hfrac
  obtain ⟨g0, u0, hg0, hgLocal, hu0, _heq, _hgReg, hcell⟩ :=
    hinterior M L omega m k q sOrder u g (averageOn U u.toFun)
      hweak hg hs.2 hkm (by exact hq.2) hpatch
  have hparent := normalizedL2SqOnSet_projected_le_window u u0
    (averageOn U u.toFun) hu0 hPsub hUsub hUpos hPpos
  have hsource := projectedForceSeminorm_le_window Q c U sOrder g g0
    (by simpa [Q, c] using hgLocal) hg0 (by
      rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet] at hPsub
      exact hPsub) hPpair'.1 hPpair'.2 hU0 hUtop hgUfin
  have hvolP : volume (translateSet c (openCubeSet Q)) =
      volume (translatedCube d k c) := by
    congr 1
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  rw [hvolP] at hsource
  have hcap := hcaps M sOrder.1 hs L m n z x c omega hx hcU hfin hcapE
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hhalf := interiorHalfEllipticityCaps_of_sixth Q A hs0 hsigma
    hcap.2.2.2.1 hcap.2.2.1
  have hpref := caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Q) (A := A) hC hs0 hs.2 hhalf.2.2
  have hlam : Ch02.lambdaS Q (sOrder.1 / 2) A ≤ B * sigma := hhalf.2.1
  have hlamInv : Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
      B * sigma⁻¹ := by
    calc
      Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) =
          (Ch02.lambdaS Q (sOrder.1 / 2) A)⁻¹ := Real.rpow_neg_one _
      _ ≤ B * sigma⁻¹ := hhalf.1
  have hinner :
      Ch02.lambdaS Q (sOrder.1 / 2) A *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 ≤
        B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
              ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
            (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-sOrder.1) Q *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 := by
    have hscale : 0 ≤ Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hparent0 : 0 ≤ normalizedL2SqOnSet (openCubeSet Q)
        (fun y => u0.toFun y - averageOn U u.toFun) :=
      normalizedL2SqOnSet_nonneg (openCubeSet Q) _ (measurableSet_openCubeSet Q)
    have hcoef : Ch02.lambdaS Q (sOrder.1 / 2) A *
        Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) ≤
        B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hlam hscale
    have hfirst := mul_le_mul hcoef hparent hparent0
      (mul_nonneg (mul_nonneg hB.le hsigma.le) hscale)
    have hsource0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
        (fun x => -g0 x) :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (by simpa using _hgReg)
    have hsecondSq := pow_le_pow_left₀ hsource0 hsource 2
    let Sg : ℝ := caccioppoliExactDatumConstant d *
      cubeBesovScaleWeight (-sOrder.1) Q *
        (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal /
              (volume (translatedCube d k c)).toReal) *
            (fractionalSeminormOn U sOrder.1 g).toReal))
    have hcoefSecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) :=
      mul_le_mul_of_nonneg_left hlamInv
        (Real.rpow_nonneg (by linarith only [hs0] : 0 ≤ sOrder.1 / 2) _)
    have hcoefSecond0 : 0 ≤ Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        (B * sigma⁻¹) :=
      mul_nonneg (Real.rpow_nonneg (by linarith only [hs0] : 0 ≤ sOrder.1 / 2) _)
        (mul_nonneg hB.le (inv_nonneg.mpr hsigma.le))
    have hsecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
          Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
            (fun x => -g0 x) ^ 2 ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) * Sg ^ 2 :=
      mul_le_mul hcoefSecond (by simpa only [Sg] using hsecondSq)
        (sq_nonneg _) hcoefSecond0
    exact add_le_add (by simpa [mul_assoc] using hfirst)
      (by simpa only [Sg] using hsecond)
  have hrawInner0 : 0 ≤
      Ch02.lambdaS Q (sOrder.1 / 2) A *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 := by
    have hlam0 : 0 ≤ Ch02.lambdaS Q (sOrder.1 / 2) A := by
      rw [Ch02.lambdaS]
      exact Ch02.lambdaSq_finite_nonneg Q A (by linarith only [hs0]) (by norm_num)
    have hparent0 := normalizedL2SqOnSet_nonneg (openCubeSet Q)
      (fun y => u0.toFun y - averageOn U u.toFun) (measurableSet_openCubeSet Q)
    exact add_nonneg
      (mul_nonneg (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _)) hparent0)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by linarith only [hs0]) _)
          (Real.rpow_nonneg hlam0 _)) (sq_nonneg _))
  have hprefBound0 : 0 ≤
      (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) := by positivity
  have hmul := mul_le_mul hpref hinner hrawInner0 hprefBound0
  have hstep := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  have hfinal := hcell.trans (by simpa only [Q, A, c] using hstep)
  simpa only [Q, A, c, U, sigma] using hfinal

/-- Datum-free companion of `exists_interiorCellEnergy_le_manuscriptPrices`.
The interior estimate consumes only the weak equation and force regularity. -/
theorem aux_gen_interiorCellEnergy_le_manuscriptPrices
    (d : ℕ) [NeZero d] (Cerr : ℝ) (hCerr : 0 < Cerr) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
aux_AnchorFinite M L (n + 2) z (sOrder.1 / 8) omega →
        section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z ≤ Cerr →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let k : ℤ := (n : ℤ) - 2
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          K *
            (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U
                  (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
  obtain ⟨C, B, hC, hB, hraw⟩ := aux_gen_interiorCellEnergy_le_windowPrices d Cerr hCerr
  let P : ℝ := (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ)
  let Kparent : ℝ := 81 * B * (9 : ℝ) ^ d
  let Ksource : ℝ := B *
    ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 * (9 : ℝ) ^ d)
  let K : ℝ := (81 : ℝ) ^ d * P * max Kparent Ksource
  have hmaxC : 0 < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hKparent : 0 < Kparent := by
    dsimp [Kparent]
    positivity
  have hKsource : 0 < Ksource := by
    dsimp [Ksource]
    exact mul_pos hB (mul_pos
      (mul_pos (by positivity) (sq_pos_of_pos (caccioppoliExactDatumConstant_pos d)))
      (by positivity))
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hnm z x q omega hz hx hq hpatch hfin hcapE u g
    hweak hg
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hbase := hraw M sOrder hs L m n hnm z x q omega hz hx hq hpatch hfin hcapE
    u g hweak hg
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hPsub : translatedCube d k c ⊆ U :=
    translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k, U] using hq) hkm
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hratio := volume_ratio_truncatedCube_translated_predTwo_le
    (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (x := x) (c := c)
    hxDomain (by omega)
  have hratio0 : 0 ≤ (volume U).toReal /
      (volume (translatedCube d k c)).toReal := by positivity
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hX : 0 ≤ normalizedL2On U
      (fun y => u.toFun y - averageOn U u.toFun) := Real.sqrt_nonneg _
  have hG : 0 ≤ (fractionalSeminormOn U sOrder.1 g).toReal := ENNReal.toReal_nonneg
  have hparent := projected_parent_factor_le
    (d := d) (n := n) hB.le hsigma.le hratio
      (X := normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun))
  have hsource := projected_source_factor_le
    (d := d) (n := n) sOrder.2.1 (caccioppoliExactDatumConstant_pos d).le
      hratio0 hratio hG
  have hfirst :
      B * sigma * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 ≤
        Kparent *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
            normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) := by
    dsimp [U] at hparent
    dsimp [U, k, Kparent]
    simpa only [mul_assoc] using hparent
  have hsecond :
      Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
          (caccioppoliExactDatumConstant d *
            cubeBesovScaleWeight (-sOrder.1) Q *
            (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 ≤
        Ksource *
          (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
    rw [show cubeBesovScaleWeight (-sOrder.1) Q =
        Real.rpow (3 : ℝ)
          (sOrder.1 * (((n : ℤ) - 2 : ℤ) : ℝ)) by
      simpa [Q, k] using cubeBesovScaleWeight_neg_origin_predTwo
        (d := d) sOrder.1 n]
    have hm := mul_le_mul_of_nonneg_left hsource
      (mul_nonneg hB.le (inv_nonneg.mpr hsigma.le))
    calc
      _ = (B * sigma⁻¹) *
          (Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            (caccioppoliExactDatumConstant d *
              Real.rpow (3 : ℝ) (sOrder.1 * (((n : ℤ) - 2 : ℤ) : ℝ)) *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2) := by ring
      _ ≤ (B * sigma⁻¹) *
          ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 *
            (9 : ℝ) ^ d * Real.rpow sOrder.1 (-12 : ℝ) *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := hm
      _ = Ksource *
          (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
        dsimp [Ksource]
        ring
  have hsum :
      B * sigma * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
          (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-sOrder.1) Q *
            (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 ≤
        max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
    have hA0 : 0 ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 := by
      positivity
    have hD0 : 0 ≤ Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg sOrder.2.1.le _)
            (inv_nonneg.mpr hsigma.le))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    calc
      _ ≤ Kparent *
            (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) +
          Ksource *
            (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) :=
        add_le_add hfirst hsecond
      _ ≤ max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
        have h1 := mul_le_mul_of_nonneg_right (le_max_left Kparent Ksource) hA0
        have h2 := mul_le_mul_of_nonneg_right (le_max_right Kparent Ksource) hD0
        linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hP.le
  have hout := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  refine hbase.trans ?_
  calc
    _ ≤ (81 : ℝ) ^ d *
        (P * (max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) := by
      simpa only [k, Q, U, sigma, P] using hout
    _ = K *
        (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
          Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
      dsimp [K]
      ring


/-! ### Cover and weighted energy from the two reads -/

/-- **Datum-free interior cover energy display at a finite cutoff.**  Companion
of `Section6HarmonicInterior.exists_interiorCoverEnergy_le_manuscriptPrices_weak`
on the cutoff good event, with the binder `m ≤ L` deleted. -/
theorem aux_gen_interiorCoverEnergy_le_manuscriptPrices (d : ℕ) [NeZero d]
    (Cerr : ℝ) (hCerr : 0 < Cerr) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
aux_AnchorFinite M L (n + 2) z (sOrder.1 / 8) omega →
        section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z ≤ Cerr →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let D := translatedCube d ((n : ℤ) - 2) y
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage D (fun q ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega q * vecNormSq (u.grad q)) ≤
          K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U
                  (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
  obtain ⟨K, hK, hcell⟩ := aux_gen_interiorCellEnergy_le_manuscriptPrices d Cerr hCerr
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hnm z x y omega hz hx hD hnot hfin hcapE u g
    hweak hg
  let k : ℤ := (n : ℤ) - 2
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let B : ℝ := K *
    (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
      Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2)
  have htranslated : translateSet y (openCubeSet (originCube d k)) =
      translatedCube d k y := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  have hparent : translatedCube d k y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    have hp' : p ∈ translatedCube d ((n : ℤ) - 2) y := by
      simpa only [k] using hp
    exact (hD hp').2
  apply normalizedCutoffEnergy_translatedCube_le_of_depthTwo_cell_bounds
    M L omega u hparent B
  intro R hR
  let qR : Vec d := y + triadicCubeShift R
  have hDtranslate : translateSet y (openCubeSet (originCube d k)) ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x := by
    rw [htranslated]
    simpa only [k] using hD
  have hqR : qR ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x :=
    translated_descendantCentre_mem_of_parent_subset hR hDtranslate
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hpatch : openCubeAtScale qR ((n : ℤ) - 3) ⊆ cube d (m : ℤ) :=
    openCubeAtScale_predTwo_subset_domain_of_not_boundaryTouches
      hxDomain hqR hnot
  have hbound := hcell M sOrder hs L m n hnm z x qR omega hz hx hqR
    hpatch hfin hcapE u g hweak hg
  have hset : translateSet y (openCubeSet R) =
      truncatedCube d (m : ℤ) (k - 2) qR := by
    apply translate_descendant_openCubeSet_eq_truncatedCube hR
    rw [htranslated]
    simpa only [cube] using hparent
  rw [hset]
  simpa only [k, U, sigma, B] using hbound

/-- **The weighted-energy slot at a finite cutoff.** -/
theorem aux_gen_interiorWeightedEnergy_le_manuscriptPrices (d : ℕ) [NeZero d]
    (Cerr : ℝ) (hCerr : 0 < Cerr) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
aux_AnchorFinite M L (n + 2) z (sOrder.1 / 8) omega →
        section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z ≤ Cerr →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
      ∀ (u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2)))),
        (∀ p, u0.grad p = u.grad (p + y)) →
      ∀ (s1 smid : FractionalOrder), s1.1 < smid.1 →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        Ch03.ABK26.weightedLocalSymmetricEnergyLp (originCube d ((n : ℤ) - 2))
            ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
            ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
              (originCube d ((n : ℤ) - 2))) u0 s1 smid FiniteLpExponent.two ≤
          ENNReal.ofReal
            (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
              Real.sqrt (K *
                (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                    normalizedL2On U
                      (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
                  Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                    Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                    (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) := by
  obtain ⟨K, hK, hcover⟩ := aux_gen_interiorCoverEnergy_le_manuscriptPrices d Cerr hCerr
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hnm z x y omega hz hx hD hnot hfin hcapE u g hweak hg
    u0 hu0 s1 smid hgap
  dsimp only
  have henergy := hcover M sOrder hs L m n hnm z x y omega hz hx hD hnot
    hfin hcapE u g hweak hg
  simp only at henergy
  have hframe := cubeAverage_coefficientEnergyDensity_aCutoffFamily_eq_translatedCube
    M L omega ((n : ℤ) - 2) y u0 u.grad hu0
  have hroot := weightedLocalSymmetricEnergyLp_two_le_rootEnergyReadout
    (originCube d ((n : ℤ) - 2))
    ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
      (originCube d ((n : ℤ) - 2))) u0 s1 smid (by linarith)
  refine hroot.trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_
    (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
  rw [hframe]
  exact Real.sqrt_le_sqrt henergy
/-! ### The K-free loop from the finiteness read -/

/-- Cutoff good-event specialization of the smooth-dual local comparator estimate. -/
theorem aux_gen_cubeLpNorm_sub_le_cutoffBound_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hfin : aux_AnchorFinite M L (n + 2) z (s / 8) omega),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x => u.toFun x - v.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorSmoothManuscriptBound d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n omega y z hcontain hfin
  dsimp only
  intro g hg u v hu hv huv S D hS hD
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 (by norm_num)
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hE := aux_gen_localError_two_le_anchor_of_closedContainment
    M hs L n omega y z hcontain hfin
  have hres := hmain ((n : ℤ) - 2) s hs0 hs1 hs.2
    (aCutoffFamily M L (translatePotentialSample y omega))
    (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))
    (by
      rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
      rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
      exact tailCoefficientCubeAverage_pos M L (n + 2)
        (translatePotentialSample z omega)) g hg u v hu hv huv E S D
    (by simpa only [E] using hE)
    (by simpa [originCube] using hS) hD
  simpa only [E, show ((n : ℤ) - 2) - 1 = (n : ℤ) - 3 by ring] using hres

/-- Complete smooth-dual local comparator loop at a finite cutoff, including the
direct forcing comparison to the unit harmonic function. -/
theorem aux_gen_cubeLpNorm_sub_unitHarmonic_le_cutoff_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hfin : aux_AnchorFinite M L (n + 2) z (s / 8) omega),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v h : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
        IsUnitWeaklyHarmonicOn (openCubeSet Q) h →
        HasH10Difference Q u h →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x ↦ u.toFun x - h.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal +
          unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
            (d : ℝ) * sigma⁻¹ *
              (Real.sqrt (Fintype.card (Fin d) : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  obtain ⟨C, hCtop, hcoarse⟩ :=
    aux_gen_cubeLpNorm_sub_le_cutoffBound_smoothDual d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n omega y z hcontain hfin
  dsimp only
  intro g hg u v h hu hv huv hh huh S D hS hD
  let s1 : FractionalOrder := ⟨s / 3, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let smid : FractionalOrder := ⟨s / 2, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let s2 : FractionalOrder := ⟨s, by
    exact (mul_pos (by norm_num)
      (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
    by linarith [hs.2]⟩
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hcoarse' := hcoarse M s hs L n omega y z hcontain hfin
    g hg u v hu hv huv S D (by simpa [s1, smid] using hS) hD
  have hreg : ForceBesovRegularity (originCube d ((n : ℤ) - 2)) smid.1 g := by
    apply forceBesovRegularity_of_memCubeEuclideanFullWsp_lt hg
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    dsimp [smid, s2]
    linarith
  have hvh : HasH10Difference (originCube d ((n : ℤ) - 2)) v h :=
    hasH10Difference_trans (hasH10Difference_symm huv) huh
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hforce := cubeLpNorm_scalarForced_sub_unitHarmonic_le_positiveBesov
    ((n : ℤ) - 2) hsigma hreg hv hh hvh
  exact cubeLpNorm_sub_unitHarmonic_le_add
    (originCube d ((n : ℤ) - 2)) u v h
    (by simpa only [E, s1, smid, s2] using hcoarse')
    (by simpa only [smid] using hforce)

/-- Arbitrary translated-cube physical-frame smooth-dual loop at a finite cutoff. -/
theorem aux_gen_normalizedL2On_sub_flatComparator_le_loop_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hfin : aux_AnchorFinite M L (n + 2) z (s / 8) omega),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n sigma smid s1 s2
            E S D Q g := by
  obtain ⟨C, hCtop, hloop⟩ :=
    aux_gen_cubeLpNorm_sub_unitHarmonic_le_cutoff_smoothDual d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n omega y z hcontain hfin
  dsimp only
  intro g hg u0 hu0 uPhysical ubar hh ht hu0Physical S D hS hD
  have hgTwo : MemLp g 2 (normalizedCubeMeasure (originCube d ((n : ℤ) - 2))) :=
    MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hg
  have hgCube : MemVectorL2 (cubeSet (originCube d ((n : ℤ) - 2))) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure
      (originCube d ((n : ℤ) - 2)) hgTwo
  have hgOpen : MemVectorL2 (openCubeSet (originCube d ((n : ℤ) - 2))) g := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hgCube
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  let v0 := sourceForcedReplacement
    (scalarConstantCoeffMatrix (d := d) hsigma) u0 hgOpen
  have hv0 : IsScalarForcedEquation (originCube d ((n : ℤ) - 2))
      (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z)) v0 g :=
    isScalarForcedEquation_sourceForcedReplacement hsigma u0 hgOpen
  have huv0 : HasH10Difference (originCube d ((n : ℤ) - 2)) u0 v0 :=
    hasH10Difference_sourceForcedReplacement
      (scalarConstantCoeffMatrix (d := d) hsigma) u0 hgOpen
  obtain ⟨ubar0, hh0, hu0bar0, hnorm⟩ :=
    exists_recenteredFlatComparator (originCube d ((n : ℤ) - 2)) y
      u0 uPhysical ubar hh ht hu0Physical
  rw [hnorm]
  have hout := hloop M s hs L n omega y z hcontain hfin g hg u0 v0 ubar0
    hu0 hv0 huv0 hh0 hu0bar0 S D hS hD
  simpa only [flatComparatorSmoothGoodEventLoopBound] using hout

/-- The cutoff smooth-dual loop at the `[NeZero d]` signature of the Section 6
anchors. -/
theorem aux_gen_normalizedL2On_sub_flatComparator_le_loop_smoothDual_neZero
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hfin : aux_AnchorFinite M L (n + 2) z (s / 8) omega),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n sigma smid s1 s2
            E S D Q g := by
  classical
  by_cases hmodel : Nonempty (SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
  · let M0 : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d := Classical.choice hmodel
    exact aux_gen_normalizedL2On_sub_flatComparator_le_loop_smoothDual
      d M0.shellPrefix.dimension
  · refine ⟨0, ENNReal.zero_lt_top, ?_⟩
    intro M
    exact (hmodel ⟨M⟩).elim



/-! ### The interior comparison from the two reads -/

/-- Twin of `exists_interiorCutoffHarmonicComparison_le_sharpLoopBound` on the
K-free loop.  Only the loop input changes. -/
theorem aux_gen_interiorComparison_le_smoothLoopBound (d : ℕ) [NeZero d]
    (Cerr : ℝ) (hCerr : 0 < Cerr) :
    ∃ (C : ℝ≥0∞) (K Cd : ℝ), C < ∞ ∧ 0 < K ∧ 0 < Cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
aux_AnchorFinite M L (n + 2) z (s / 8) omega →
        section6HomogenizationError M (s / 8) L (n + 2) omega z ≤ Cerr →
      let Q := originCube d ((n : ℤ) - 2)
      let U := truncatedCube d (m : ℤ) (n : ℤ) x
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      let E := Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z)
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (cube d (m : ℤ)) u g →
        MemCubeEuclideanFullWsp (originCube d (m : ℤ)) s2
          FiniteLpExponent.two g →
      ∀ (v : H1Function (translatedCube d ((n : ℤ) - 2) y)),
        IsWeaklyHarmonicOn (fun _ => (1 : ℝ))
          (translatedCube d ((n : ℤ) - 2) y) v →
        MemH10 (translatedCube d ((n : ℤ) - 2) y)
          (fun p ↦ v.toFun p - u.toFun p) →
        normalizedL2On (translatedCube d ((n : ℤ) - 2) y)
            (fun p ↦ u.toFun p - v.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n sigma smid s1 s2 E
            (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
              Real.sqrt (K *
                (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                    normalizedL2On U
                      (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
                  Real.rpow s (-12 : ℝ) * sigma⁻¹ *
                    Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
                    (fractionalSeminormOn U s g).toReal ^ 2)))
            (Cd * Real.rpow s (-(1 / 2 : ℝ)) *
              (fractionalSeminormOn U s g).toReal)
            Q (fun p ↦ g (p + y)) := by
  obtain ⟨C, hCtop, hloop⟩ :=
    aux_gen_normalizedL2On_sub_flatComparator_le_loop_smoothDual_neZero d
  obtain ⟨K, hK, henergy⟩ :=
    aux_gen_interiorWeightedEnergy_le_manuscriptPrices d Cerr hCerr
  obtain ⟨Cd, hCd, hforce⟩ := exists_interiorForceOverlap_le_windowSeminorm d
  refine ⟨C, K, Cd, hCtop, hK, hCd, ?_⟩
  intro M s hs L m n hnm z x y omega hz hx hD hnot hfin hcapE
  dsimp only
  intro u g hweak hg
  have hDset : translatedCube d ((n : ℤ) - 2) y =
      translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))) := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  rw [hDset]
  intro v hharm htrace
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hsubOpen : translatedCube d ((n : ℤ) - 2) y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    exact (hD hp).2
  obtain ⟨g0, hg0, hg0eq, u0, v0, hu0forced, _hv0, _huv0, hu0val, hu0grad⟩ :=
    exists_localSourceComparisonDatum_weak_retained M L omega m ((n : ℤ) - 2) y
      ⟨s, (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
        by linarith [hs.2]⟩
      u g hweak hg hsubOpen
      (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z)) hsigma
  have hS := henergy M
    ⟨s, (mul_pos (by norm_num)
          (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
      by linarith [hs.2]⟩
    hs L m n hnm z x y omega hz hx hD hnot hfin hcapE u g hweak hg u0 hu0grad
    ⟨s / 3, by
      have hs0 : 0 < s :=
        (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
      positivity, by linarith [hs.2]⟩
    ⟨s / 2, by
      have hs0 : 0 < s :=
        (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
      positivity, by linarith [hs.2]⟩
    (by
      have hs0 : 0 < s :=
        (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
      dsimp only
      linarith)
  have hDforce := hforce
    ⟨s, (mul_pos (by norm_num)
          (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
      by linarith [hs.2]⟩
    m n hnm z x y hx hD g g0 hg hg0 hg0eq
  have hcontain : translateSet (y - z)
      (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
        cubeSet (originCube d ((n : ℤ) + 2)) :=
    closedOffGridCube_subset_originAnchorParent hx hD
  have hharm' : IsUnitWeaklyHarmonicOn
      (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2)))) v :=
    isUnitWeaklyHarmonicOn_iff.mpr hharm
  have hg0fun : (fun p ↦ g (p + y)) = g0 := (funext hg0eq).symm
  rw [hg0fun]
  exact hloop M s hs L n omega y z hcontain hfin g0 hg0 u0 hu0forced
    u.toFun v hharm' htrace hu0val _ _ hS hDforce



/-! ### The interior clause estimate from the two reads -/

/-- **Interior clause, event-generic.**  For a fixed error-cap level `Cerr`, the
interior harmonic-approximation estimate at the original powers holds for every
sample satisfying the two anchor reads.  The constant precedes the model. -/
theorem aux_gen_interiorClause (d : ℕ) [NeZero d] (Cerr : ℝ) (hCerr : 0 < Cerr) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ ω,
      aux_AnchorFinite M L (n + 2) z (s / 8) ω →
      section6HomogenizationError M (s / 8) L (n + 2) ω z ≤ Cerr →
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
          (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) →
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q) ≤
                C * s ^ (-3 / 2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                  C * s ^ (-15 / 2 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal := by
  classical
  obtain ⟨Cloop, Kslot, Cdslot, _hCloopTop, hKslot, hCdslot, hloop⟩ :=
    aux_gen_interiorComparison_le_smoothLoopBound d Cerr hCerr
  obtain ⟨Cb, hCb, hbesov⟩ := exists_interiorForceBesov_le_windowSeminorm d
  have hCX0 := aux_smoothInteriorConstX_nonneg d Cloop Kslot
  have hCF0 := aux_smoothInteriorConstF_nonneg d Cloop (Kslot := Kslot) hCdslot.le
    hCerr.le hCb.le
  refine ⟨(9 : ℝ) ^ d * (aux_smoothInteriorConstX d Cloop Kslot +
      aux_smoothInteriorConstF d Cloop Kslot Cdslot Cerr Cb + 1), by positivity, ?_⟩
  intro M s hs L m n hnm z hz x hx hbd ω hfin hErC u g hweak hgex y hy hcov hloc uD
    hfval v hharm htrace
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < s := (mul_pos (by norm_num) (pow_pos hdelta 2)).trans_le hs.1
  have hs4 : s ≤ 1 / 4 := hs.2
  have hslt : s < 1 := by linarith
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  set sigma : ℝ :=
    tailAverage M L (n + 2) ω (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set Er : ℝ := section6HomogenizationError M (s / 8) L (n + 2) ω z with hErdef
  set Wq : ℝ := normalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
    (fun q ↦ u.toFun q - averageOn (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun)
    with hWqdef
  set Gq : ℝ := (fractionalSeminormOn (truncatedCube d (m : ℤ) (n : ℤ) x) s g).toReal
    with hGqdef
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z ω)
  have hEr0 : 0 ≤ Er := ENNReal.toReal_nonneg
  have hWq0 : 0 ≤ Wq := Section6Iteration.normalizedL2On_nonneg _ _
  have hGq0 : 0 ≤ Gq := ENNReal.toReal_nonneg
  have hP1 : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) * Er * Wq :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) hEr0) hWq0
  have hP2 : (0 : ℝ) ≤ s ^ (-15 / 2 : ℝ) * sigma⁻¹ *
      (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (inv_nonneg.mpr hsigma.le)) (Real.rpow_nonneg (by norm_num) _)) hGq0
  obtain ⟨sOrder, hsval, hgWsp⟩ := hgex
  have hsO : sOrder = (⟨s, hs0, hslt⟩ : FractionalOrder) := Subtype.ext hsval
  rw [hsO] at hgWsp
  have hH10 : MemH10 (translatedCube d ((n : ℤ) - 2) y)
      (fun p ↦ v.toFun p - u.toFun p) :=
    Section6HarmonicApproximation.memH10_sub_physical_of_hasZeroTraceDifferenceOn
      htrace hfval
  have hL := hloop M s hs L m n hnm z x y ω hz hx hloc hbd hfin hErC u g hweak
    hgWsp v hharm hH10
  have hBv := hbesov (⟨s, hs0, hslt⟩ : FractionalOrder) m n hnm z x y hx hloc g hgWsp
    (s / 2) (by dsimp only; linarith)
  have hC := aux_smoothInterior_loopBound_le Cloop hKslot hCdslot hCb n hs0 hs4
    hsigma hEr0 hErC hWq0 hGq0 (⟨s / 2, by positivity, by linarith⟩ : FractionalOrder)
    (⟨s / 3, by positivity, by linarith⟩ : FractionalOrder)
    (⟨s, hs0, hslt⟩ : FractionalOrder) rfl rfl rfl (originCube d ((n : ℤ) - 2))
    (fun p ↦ g (p + y)) hBv
  have hshrink := aux_smoothInterior_windowShrink hnm hxDomain (uD := uD) (v := v)
    (u := u.toFun) hfval hcov
  set CX := aux_smoothInteriorConstX d Cloop Kslot with hCXdef
  set CF := aux_smoothInteriorConstF d Cloop Kslot Cdslot Cerr Cb with hCFdef
  have hmain := hshrink.trans (mul_le_mul_of_nonneg_left (hL.trans hC) (by positivity))
  refine hmain.trans ?_
  have hb1 : (9 : ℝ) ^ d * CX ≤ (9 : ℝ) ^ d * (CX + CF + 1) :=
    mul_le_mul_of_nonneg_left (by linarith only [hCF0]) (by positivity)
  have hb2 : (9 : ℝ) ^ d * CF ≤ (9 : ℝ) ^ d * (CX + CF + 1) :=
    mul_le_mul_of_nonneg_left (by linarith only [hCX0]) (by positivity)
  calc (9 : ℝ) ^ d * (CX * s ^ (-3 / 2 : ℝ) * Er * Wq +
        CF * s ^ (-15 / 2 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq)
      = ((9 : ℝ) ^ d * CX) * (s ^ (-3 / 2 : ℝ) * Er * Wq) +
        ((9 : ℝ) ^ d * CF) *
          (s ^ (-15 / 2 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq) := by
        ring
    _ ≤ ((9 : ℝ) ^ d * (CX + CF + 1)) * (s ^ (-3 / 2 : ℝ) * Er * Wq) +
        ((9 : ℝ) ^ d * (CX + CF + 1)) *
          (s ^ (-15 / 2 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq) :=
        add_le_add (mul_le_mul_of_nonneg_right hb1 hP1)
          (mul_le_mul_of_nonneg_right hb2 hP2)
    _ = (9 : ℝ) ^ d * (CX + CF + 1) * s ^ (-3 / 2 : ℝ) * Er * Wq +
        (9 : ℝ) ^ d * (CX + CF + 1) * s ^ (-15 / 2 : ℝ) * sigma⁻¹ *
          (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq := by ring

omit [NeZero d] in
/-- Nonnegativity of the interior right-hand side (for the indicator split). -/
theorem aux_interiorRHS_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hs0 : 0 < s) (L n : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    {C : ℝ} (hC : 0 ≤ C) (U : Set (Vec d)) (f : Vec d → ℝ) (g : Vec d → Vec d) :
    0 ≤ C * s ^ (-3 / 2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
          normalizedL2On U f +
        C * s ^ (-15 / 2 : ℝ) *
          (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
          (3 : ℝ) ^ ((1 + s) * n) * (fractionalSeminormOn U s g).toReal := by
  have hsigma : 0 < tailAverage M L (n + 2) ω (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z ω)
  have hE : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z :=
    ENNReal.toReal_nonneg
  have hW : 0 ≤ normalizedL2On U f := Section6Iteration.normalizedL2On_nonneg _ _
  have hG : 0 ≤ (fractionalSeminormOn U s g).toReal := ENNReal.toReal_nonneg
  have h1 : 0 ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have h2 : 0 ≤ s ^ (-15 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have h3 : 0 ≤ (3 : ℝ) ^ ((1 + s) * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have h4 : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d ((n : ℤ) + 2) z))⁻¹ :=
    inv_nonneg.mpr hsigma.le
  exact add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hC h1) hE) hW)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC h2) h4) h3) hG)

end Generic

/-! ### Threshold-6 instance (cross-check of `InteriorLegSmoothDual`) -/

/-- The two reads on the threshold-6 cutoff event give back
`InteriorCutoffHarmonicApproximationInput d (-3/2) (-15/2)`. -/
theorem interiorCutoffHarmonicApproximationInput_smoothDual_viaReads (d : ℕ) [NeZero d] :
    InteriorCutoffHarmonicApproximationInput d (-3 / 2 : ℝ) (-15 / 2 : ℝ) := by
  obtain ⟨Cerr, hCerr, herr⟩ :=
    exists_section6HomogenizationError_le_of_cutoffGoodEvent (d := d)
  obtain ⟨C, hC, hmain⟩ := aux_gen_interiorClause d Cerr hCerr
  refine ⟨C, hC, ?_⟩
  intro M s hs L m n hnm z hz x hx hbd ω u g hweak hgex y hy hcov hloc uD hfval _hfgrad
  refine ⟨(Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).1,
    (Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).2, ?_⟩
  intro v hharm htrace
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  refine Section6HarmonicApproximation.indicatorValue_le_of_mem_imp _ _ _
    (aux_interiorRHS_nonneg M hs0 L n ω z hC.le _ _ g) ?_
  intro hgood
  have hfin : aux_AnchorFinite M L (n + 2) z (s / 8) ω :=
    Section6ThetaLadder.paperHomogenizationError_eq_ofReal_cutoffGoodEvent M
      (by linarith [hs.1]) (by linarith [hs.2]) L (n + 2) ω z zero_le_one le_rfl hgood
  exact hmain M s hs L m n hnm z hz x hx hbd ω hfin (herr M s hs L (n + 2) ω z hgood)
    u g hweak hgex y hy hcov hloc uD hfval v hharm htrace

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.SmoothDualScratch
