module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsMesoscopicLift
public import Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge
public import Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergyPoincare
public import SubdiffusiveProcess.Providers.Section2.CoarseGrainedPoincare

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## From the forced equation to the library's weak-solution predicate -/

/-- The `Ch03` forced equation on the open cube is the library's `H¹`
divergence-datum weak equation on the half-open cube: the two realizations of a
triadic cube differ by a Lebesgue-null boundary, and `H10Function.toOpenCubeSet`
transports the test class. -/
theorem isH1DirichletRhsWeakSolutionOn_toCubeSet_of_isForcedEquation [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hforced : Ch03.IsForcedEquation Q afam u g) :
    IsH1DirichletRhsWeakSolutionOn ((afam.coeffOn Q).toCoeffField) (cubeSet Q)
      u.toCubeSet g := by
  intro φ
  have h := hforced φ.toOpenCubeSet
  have hgrad : ∀ x, φ.toOpenCubeSet.toH1Function.grad x = φ.toH1Function.grad x := by
    intro x
    exact congrFun (H10Function.toOpenCubeSet_toH1Function_grad φ) x
  have hleft :
      ∫ x in cubeSet Q,
          vecDot (matVecMul ((afam.coeffOn Q).toCoeffField x) (u.toCubeSet.grad x))
            (φ.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x))
            (φ.toOpenCubeSet.toH1Function.grad x) ∂volume := by
    simp only [H1Function.grad_toCubeSet, hgrad]
    exact setIntegral_cubeSet_eq_setIntegral_openCubeSet
  have hright :
      ∫ x in cubeSet Q, vecDot (g x) (φ.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (g x) (φ.toOpenCubeSet.toH1Function.grad x) ∂volume := by
    simp only [hgrad]
    exact setIntegral_cubeSet_eq_setIntegral_openCubeSet
  rw [hleft, hright]
  exact h

/-- Solenoidality transfers from the half-open triadic cube to its open
realization: the two differ by a Lebesgue-null boundary and
`H10Function.toCubeSet` transports the test class. -/
theorem isSolenoidalOn_openCubeSet_of_cubeSet [NeZero d]
    {Q : TriadicCube d} {F : Vec d → Vec d}
    (h : IsSolenoidalOn (cubeSet Q) F) : IsSolenoidalOn (openCubeSet Q) F := by
  intro φ
  have hgrad : ∀ x, φ.toCubeSet.toH1Function.grad x = φ.toH1Function.grad x := by
    intro x
    exact congrFun (H10Function.toCubeSet_toH1Function_grad φ) x
  have hcube := h φ.toCubeSet
  have htransfer :
      ∫ x in cubeSet Q, vecDot (F x) (φ.toCubeSet.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q, vecDot (F x) (φ.toH1Function.grad x) ∂volume := by
    simp only [hgrad]
    exact setIntegral_cubeSet_eq_setIntegral_openCubeSet
  rw [htransfer] at hcube
  exact hcube

/-! ## The Hodge-type decomposition -/

/-- **The Hodge-type decomposition of the flux on a triadic cube.**

For a solution of the forced equation `−∇·(a∇u) = ∇·g` on `Q` there are

* the **mean-zero Neumann corrector** `ω` of the centered datum
  `g − ⟨g⟩_Q` — produced by Lax–Milgram on the mean-zero subspace of `H¹(Q)`
  (`meanZeroNeumannCorrectorDataOf_h1CoerciveEstimate` with the cube's own
  coercive estimate `h1CoerciveEstimate_cubeSet`), and
* an **`a`-harmonic remainder** `w`,

with `∇u = ∇w + ∇ω` on `Q`.  The flux `a∇w` of the remainder is solenoidal, so
it is the field clause 2 of `SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare`
accepts, and `a∇u = a∇w + a∇ω` splits the flux into a solenoidal part and the
corrector flux of the datum, whose coarse energy is priced by
`coefficientEnergy_average_le_force_scale_noteConstants_expanded`.

This is the decomposition P-222 §9 item 1 named; the bookkeeping it fixes is
that the **corrector flux `a∇ω`, not the datum `g`, is what is subtracted**:
subtracting `g` also leaves a solenoidal field, but its `a⁻¹`-energy is
`⟨a⁻¹|g|²⟩`, which only the *pointwise* ellipticity controls, whereas
`⟨a|∇ω|²⟩` is controlled by the *coarse* `λ_{s,q}`. -/
theorem exists_hodge_decomposition_of_isForcedEquation [NeZero d] {lam Lam : ℝ}
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    (hg : MemVectorL2 (cubeSet Q) g)
    (hforced : Ch03.IsForcedEquation Q afam u g) :
    ∃ ω : MeanZeroNeumannCorrectorData Q ((afam.coeffOn Q).toCoeffField)
        (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction ((afam.coeffOn Q).toCoeffField) (cubeSet Q),
        (∀ x ∈ cubeSet Q,
            u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
          IsSolenoidalOn (openCubeSet Q)
            (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (w.toH1.grad x)) := by
  obtain ⟨ω, w, hsplit⟩ :=
    exists_centeredNeumannCorrector_aHarmonicRemainder_of_h1DirichletRhsWeakSolutionOn
      (Q := Q) (a := (afam.coeffOn Q).toCoeffField) (g := g) (u := u.toCubeSet)
      hEll (isH1DirichletRhsWeakSolutionOn_toCubeSet_of_isForcedEquation hforced)
      hg (h1CoerciveEstimate_cubeSet Q)
  refine ⟨ω, w, ?_, isSolenoidalOn_openCubeSet_of_cubeSet w.isHarmonic.2⟩
  intro x hx
  simpa using hsplit x hx

/-! ## The corrector energy at the mesoscopic scale -/

/-- **The mesoscopic Hodge decomposition of the flux of a massive solution.**

Combining `exists_mesoscopic_forced_datum` (the datum of the massive equation on
an arbitrary triadic cube, with the mesoscopic factor `side(Q)`),
`exists_hodge_decomposition_of_isForcedEquation` (the splitting) and the
library's corrector-energy estimate
`coefficientEnergy_average_le_force_scale_noteConstants_expanded` (the *coarse*
`λ⁻¹` price of the datum), the flux of a solution of `mu u − ∇·(a∇u) = 0` splits
on `Q` as

```
a∇u = a∇w + a∇ω ,     ∇·(a∇w) = 0 weakly on Q ,
⟨a|∇ω|²⟩_Q ≤ C(d,s) · λ_{s/2,2}(Q;a)⁻¹ · (side(Q) · |mu| · ‖u‖_{L̲²(Q)})² .
```

At `mu = T⁻¹` and the balanced mesoscopic scale `side(Q)² ≤ λ T` the right-hand
side is `C(d,s) T⁻¹‖u‖²_{L̲²(Q)}`, i.e. the `Sc · t⁻¹ M` of
`MesoscopicCrossPriceEnergyOn` with a **dimension-only** `Sc`
(`mesoscopic_corrector_energy_le_of_balanced_scale`). -/
theorem exists_mesoscopic_hodge_decomposition (d : ℕ) [NeZero d] {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1) :
    ∃ Csc : ℝ, 0 ≤ Csc ∧
      ∀ (Q : TriadicCube d) (afam : Ch03.CoeffFamily d) (a : Vec d → ℝ)
        (lam Lam mu : ℝ) (u : H1Function (openCubeSet Q)),
        (∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y) →
        IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField) →
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu (openCubeSet Q) u
          (fun _ ↦ (0 : ℝ)) →
        ∃ (g : Vec d → Vec d)
          (ω : MeanZeroNeumannCorrectorData Q ((afam.coeffOn Q).toCoeffField)
              (fun x => g x - cubeAverageVec Q g))
          (w : AHarmonicFunction ((afam.coeffOn Q).toCoeffField) (cubeSet Q)),
          (∀ x ∈ cubeSet Q,
              u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
            IsSolenoidalOn (openCubeSet Q)
              (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (w.toH1.grad x)) ∧
            cubeAverage Q
                (coefficientEnergyDensity ((afam.coeffOn Q).toCoeffField)
                  (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
              Csc * (lambdaSq Q (s / 2) (.finite 2)
                    ((afam.coeffOn Q).toCoeffField))⁻¹ *
                (cubeScaleFactor Q * (|mu| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)) ^ 2 := by
  classical
  obtain ⟨Clift, hClift0, hlift⟩ := exists_mesoscopic_forced_datum d hs
  refine ⟨500 * (s⁻¹) ^ 2 * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
    Clift ^ 2, by positivity, ?_⟩
  intro Q afam a lam Lam mu u hA hEll hu
  obtain ⟨g, hforced, hreg, hgbound⟩ := hlift Q afam a hA mu u hu
  have hgmem : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hreg.memLp
  obtain ⟨ω, w, hsplit, hsol⟩ :=
    exists_hodge_decomposition_of_isForcedEquation hEll hgmem hforced
  refine ⟨g, ω, w, hsplit, hsol, ?_⟩
  have henergy :=
    ω.coefficientEnergy_average_le_force_scale_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam) hs0 hs.le hEll hreg.memLp
      hreg.partialSeminorms_bddAbove
  have hgnonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hreg
  have hbound_nonneg :
      0 ≤ Clift * (cubeScaleFactor Q * (|mu| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)) :=
    le_trans hgnonneg hgbound
  have hsq :
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        Clift ^ 2 * (cubeScaleFactor Q * (|mu| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)) ^ 2 := by
    have := mul_self_le_mul_self hgnonneg hgbound
    nlinarith [this]
  have hlaminv : 0 ≤ (lambdaSq Q (s / 2) (.finite 2)
      ((afam.coeffOn Q).toCoeffField))⁻¹ := by
    refine inv_nonneg.mpr ?_
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2
      ((afam.coeffOn Q).toCoeffField) (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  refine henergy.trans ?_
  have hconst : 0 ≤ 500 * (s⁻¹) ^ 2 *
      (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ *
      ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 := by positivity
  calc
    500 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2
        ≤ 500 * (s⁻¹) ^ 2 *
            (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (Clift ^ 2 *
              (cubeScaleFactor Q * (|mu| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hconst
    _ = (500 * (s⁻¹) ^ 2 * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            Clift ^ 2) *
          (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ *
          (cubeScaleFactor Q * (|mu| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)) ^ 2 := by
          ring

/-! ## The `a⁻¹`-energy of the solenoidal part -/

/-- `|p − q|² ≤ 2|p|² + 2|q|²`. -/
private theorem vecNormSq_sub_le_two_add_two (p q : Vec d) :
    vecNormSq (p - q) ≤ 2 * vecNormSq p + 2 * vecNormSq q := by
  have hsplit : 2 * vecNormSq p + 2 * vecNormSq q =
      ∑ i : Fin d, (2 * (p i * p i) + 2 * (q i * q i)) := by
    simp [vecNormSq, vecDot, Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsplit]
  have hleft : vecNormSq (p - q) = ∑ i : Fin d, (p i - q i) * (p i - q i) := by
    simp [vecNormSq, vecDot]
  rw [hleft]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [sq_nonneg (p i + q i)]

/-- With a scalar coefficient the `a⁻¹`-energy density of a flux is the
`a`-energy density of the underlying gradient: `a⁻¹|a v|² = a|v|²`. -/
theorem vecDot_inv_scalarMatrix_matVecMul {c : ℝ} (hc : 0 < c) (v : Vec d) :
    vecDot (matVecMul (scalarMatrix (d := d) c) v)
        (matVecMul ((scalarMatrix (d := d) c))⁻¹
          (matVecMul (scalarMatrix (d := d) c) v)) =
      c * vecNormSq v := by
  have hInv : ((scalarMatrix (d := d) c)⁻¹ : Mat d) = c⁻¹ • (1 : Mat d) := by
    rw [scalarMatrix, nonsing_inv_smul c (ne_of_gt hc) (by simp)]
    simp
  have hInv' : ((scalarMatrix (d := d) c)⁻¹ : Mat d) = scalarMatrix (d := d) c⁻¹ := hInv
  rw [matVecMul_scalarMatrix, hInv', matVecMul_scalarMatrix, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hc), one_smul, vecDot_smul_left]
  rfl

/-- With a scalar coefficient the coefficient energy density is `a|v|²`. -/
theorem coefficientEnergyDensity_scalar {A : CoeffField d} {a : Vec d → ℝ}
    (hA : ∀ y, A y = scalarCoeffField a y) (v : Vec d → Vec d) (x : Vec d) :
    coefficientEnergyDensity A v x = a x * vecNormSq (v x) := by
  have hsymm : symmPart (A x) = scalarMatrix (a x) := by
    rw [hA x]
    have hsp : symmPart (scalarMatrix (d := d) (a x)) = scalarMatrix (d := d) (a x) := by
      ext i j
      simp only [symmPart, scalarMatrix, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij; norm_num
      · rw [if_neg hij, if_neg (Ne.symm hij)]; norm_num
    simpa [scalarCoeffField] using hsp
  rw [coefficientEnergyDensity, hsymm, matVecMul_scalarMatrix, vecDot_smul_right]
  rfl

/-- **The `a⁻¹`-energy of the solenoidal part, pointwise.**

`a⁻¹|a∇w|² = a|∇u − ∇ω|² ≤ 2 a|∇u|² + 2 a|∇ω|²`.  This is the step that makes
the corrector, and not the datum, the right object to subtract: the left-hand
side is the quantity clause 2 of the frozen coarse Poincaré prices, and the
right-hand side is *coarse* — no pointwise `λ⁻¹` appears. -/
theorem inverseEnergyDensity_solenoidalPart_le
    {A : CoeffField d} {a : Vec d → ℝ} (hA : ∀ y, A y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y) {gu gw gom : Vec d → Vec d}
    {S : Set (Vec d)} (hsplit : ∀ x ∈ S, gu x = gw x + gom x) (x : Vec d)
    (hx : x ∈ S) :
    vecDot (matVecMul (A x) (gw x)) (matVecMul (A x)⁻¹ (matVecMul (A x) (gw x))) ≤
      2 * coefficientEnergyDensity A gu x + 2 * coefficientEnergyDensity A gom x := by
  have hw : gw x = gu x - gom x := by
    rw [hsplit x hx]; abel
  have hleft :
      vecDot (matVecMul (A x) (gw x))
          (matVecMul (A x)⁻¹ (matVecMul (A x) (gw x))) =
        a x * vecNormSq (gw x) := by
    rw [hA x]
    exact vecDot_inv_scalarMatrix_matVecMul (hapos x) (gw x)
  rw [hleft, hw, coefficientEnergyDensity_scalar hA, coefficientEnergyDensity_scalar hA]
  have hbound := vecNormSq_sub_le_two_add_two (gu x) (gom x)
  nlinarith [(hapos x).le, hbound]

/-! ## The coarse conversion of the solenoidal part -/

/-- With a scalar coefficient, `x ↦ a x |v x|²` is integrable on the cube. -/
private theorem integrableOn_scalarEnergy {Q : TriadicCube d} {A : CoeffField d}
    {a : Vec d → ℝ} {lam Lam : ℝ}
    (hA : ∀ y, A y = scalarCoeffField a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) A)
    {v : Vec d → Vec d} (hv : MemVectorL2 (cubeSet Q) v) :
    IntegrableOn (fun x => a x * vecNormSq (v x)) (cubeSet Q) volume := by
  have hflux : MemVectorL2 (cubeSet Q) (fun x => matVecMul (A x) (v x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hv
  have hint : IntegrableOn (fun x => vecDot (v x) (matVecMul (A x) (v x)))
      (cubeSet Q) volume := integrableOn_vecDot_of_memVectorL2 hv hflux
  have heq : (fun x => vecDot (v x) (matVecMul (A x) (v x))) =
      fun x => a x * vecNormSq (v x) := by
    funext x
    rw [hA x]
    simp [scalarCoeffField, matVecMul_scalarMatrix, vecDot_smul_right, vecNormSq]
  rwa [heq] at hint

/-- **The `a⁻¹`-energy of the solenoidal part is coarse.**

The cube average of the `a⁻¹`-energy of `a∇w` — the quantity clause 2 of
`SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare` prices — is at most twice the
`a`-energy of `∇u` plus twice that of the corrector.  No pointwise `λ⁻¹`
enters. -/
theorem cubeAverage_inverseEnergy_solenoidalPart_le {Q : TriadicCube d}
    {A : CoeffField d} {a : Vec d → ℝ} {lam Lam : ℝ}
    (hA : ∀ y, A y = scalarCoeffField a y) (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) A)
    {gu gw gom : Vec d → Vec d}
    (hgu : MemVectorL2 (cubeSet Q) gu) (hgw : MemVectorL2 (cubeSet Q) gw)
    (hgom : MemVectorL2 (cubeSet Q) gom)
    (hsplit : ∀ x ∈ cubeSet Q, gu x = gw x + gom x) :
    cubeAverage Q (fun x =>
        vecDot (matVecMul (A x) (gw x))
          (matVecMul (A x)⁻¹ (matVecMul (A x) (gw x)))) ≤
      2 * cubeAverage Q (fun x => a x * vecNormSq (gu x)) +
        2 * cubeAverage Q (fun x => a x * vecNormSq (gom x)) := by
  have hleft : (fun x =>
        vecDot (matVecMul (A x) (gw x))
          (matVecMul (A x)⁻¹ (matVecMul (A x) (gw x)))) =
      fun x => a x * vecNormSq (gw x) := by
    funext x
    rw [hA x]
    exact vecDot_inv_scalarMatrix_matVecMul (hapos x) (gw x)
  rw [hleft]
  have hintw := integrableOn_scalarEnergy hA hEll hgw
  have hintu := integrableOn_scalarEnergy hA hEll hgu
  have hintom := integrableOn_scalarEnergy hA hEll hgom
  have hsum : IntegrableOn
      (fun x => 2 * (a x * vecNormSq (gu x)) + 2 * (a x * vecNormSq (gom x)))
      (cubeSet Q) volume := (hintu.const_mul 2).add (hintom.const_mul 2)
  have hpt : ∀ x ∈ cubeSet Q, a x * vecNormSq (gw x) ≤
      2 * (a x * vecNormSq (gu x)) + 2 * (a x * vecNormSq (gom x)) := by
    intro x hx
    have hw : gw x = gu x - gom x := by rw [hsplit x hx]; abel
    have hbound := vecNormSq_sub_le_two_add_two (gu x) (gom x)
    rw [hw]
    nlinarith [(hapos x).le, hbound]
  have hmono := cubeAverage_le_cubeAverage_of_le_on Q hintw hsum hpt
  have hsplit_avg :
      cubeAverage Q
          (fun x => 2 * (a x * vecNormSq (gu x)) + 2 * (a x * vecNormSq (gom x))) =
        2 * cubeAverage Q (fun x => a x * vecNormSq (gu x)) +
          2 * cubeAverage Q (fun x => a x * vecNormSq (gom x)) := by
    unfold cubeAverage
    rw [MeasureTheory.integral_add (hintu.const_mul 2) (hintom.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  rw [hsplit_avg] at hmono
  exact hmono

/-- **Clause 2 of the coarse Poincaré inequality, applied to the solenoidal part
of the flux.**

The negative Besov norm of the solenoidal part `a∇w` of the flux of a massive
solution is bounded by `Λ_{s,q}^{1/2} √(2 Ea + 2 Eω)` — the conversion
`Σ_i ‖flux_i‖_{B^{-s}} ≤ cL √(Ea + Sc t⁻¹ M)` that
`abs_cubeAverage_vecDot_cutoffProduct_mesoscopic_le_of_coarse_conversions`
consumes, for the **solenoidal part only**.

The engine is `SubdiffusiveProcess.Providers.Section2.coarsePoincareRaw`, the arbitrary-cube
form of the already proved translation-covariant engine behind the frozen anchor
`SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare` (whose own statement is restricted
to origin cubes). -/
theorem negativeBesovNorm_solenoidalPart_le [NeZero d]
    {Q : TriadicCube d} {afam : Ch02.TriadicCoeffFamily d} {a : Vec d → ℝ}
    {lam Lam : ℝ}
    (haSymm : ∀ R, Ch02.CoeffOn.IsSymmetric (afam.coeffOn R))
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    {s : ℝ} (hs : 0 < s) {q : Ch02.MultiscaleExponent} (hq : q.IsAdmissible)
    (u : H1Function (openCubeSet Q)) {gw gom : Vec d → Vec d}
    (hgw : MemVectorL2 (cubeSet Q) gw) (hgom : MemVectorL2 (cubeSet Q) gom)
    (hfluxMem : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (gw x)))
    (hsol : IsSolenoidalOn (openCubeSet Q)
      (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (gw x)))
    (hsplit : ∀ x ∈ cubeSet Q, u.grad x = gw x + gom x) :
    Ch03.scaleNormalizedNegativeBesovVectorNorm Q s q
        (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (gw x)) ≤
      Ch03.poincareDiscountFactor s q * Ch03.poincareUpperEllipticityFactor Q afam s q *
        Real.sqrt (2 * cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
          2 * cubeAverage Q (fun x => a x * vecNormSq (gom x))) := by
  have hguCube : MemVectorL2 (cubeSet Q) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using u.grad_memVectorL2
  have hraw :=
    (SubdiffusiveProcess.Providers.Section2.coarsePoincareRaw Q afam haSymm s hs q hq u
      (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (gw x)) hfluxMem hsol).2
  refine hraw.trans ?_
  have hDisc : 0 ≤ Ch03.poincareDiscountFactor s q := by
    cases q with
    | finite qq =>
        have hqq : (1 : ℝ) ≤ qq := by simpa using hq
        exact Real.rpow_nonneg
          (Ch02.book_geometricDiscount_nonneg (by nlinarith : (0 : ℝ) ≤ s * qq)) _
    | infinity => simp [Ch03.poincareDiscountFactor]
  have hUpper : 0 ≤ Ch03.poincareUpperEllipticityFactor Q afam s q :=
    Real.rpow_nonneg (Ch02.LambdaSq_nonneg Q afam hs hq) _
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hDisc hUpper)
  refine Real.sqrt_le_sqrt ?_
  have hint :
      ∫ x, vecDot (matVecMul ((afam.coeffOn Q).toCoeffField x) (gw x))
          (matVecMul ((afam.coeffOn Q).toCoeffField x)⁻¹
            (matVecMul ((afam.coeffOn Q).toCoeffField x) (gw x)))
          ∂normalizedCubeMeasure Q =
        cubeAverage Q (fun x =>
          vecDot (matVecMul ((afam.coeffOn Q).toCoeffField x) (gw x))
            (matVecMul ((afam.coeffOn Q).toCoeffField x)⁻¹
              (matVecMul ((afam.coeffOn Q).toCoeffField x) (gw x)))) :=
    (cubeAverage_eq_integral_normalizedCubeMeasure Q _).symm
  rw [hint]
  exact cubeAverage_inverseEnergy_solenoidalPart_le hA hapos hEll hguCube hgw hgom hsplit

/-! ## The balanced mesoscopic scale, and why the leftover must carry `beta` -/

/-- **At the balanced mesoscopic scale the corrector energy is `Sc · t⁻¹ M` with a
dimension-only `Sc`.**

If the cube's side obeys `side² ≤ λ T` — the balance
`exists_triadic_scale_balancing` realizes — then the datum bound
`C λ⁻¹ (side · T⁻¹ · ‖u‖)²` of `exists_mesoscopic_hodge_decomposition` collapses
to `C T⁻¹ ‖u‖²`, i.e. exactly the `Sc · t⁻¹ M` term of
`MesoscopicCrossPriceEnergyOn`, with `Sc` depending only on `d` and the Besov
index.  At the *top* scale of the contraction the same expression is larger by
the factor `side²/(λ T) ≫ 1`, which is why the lift has to be mesoscopic. -/
theorem corrector_energy_le_of_balanced_scale {Csc lamq T ell N E : ℝ}
    (hCsc : 0 ≤ Csc) (hT : 0 < T) (hlam : 0 < lamq)
    (hbal : ell ^ 2 ≤ lamq * T)
    (hE : E ≤ Csc * lamq⁻¹ * (ell * (|T⁻¹| * N)) ^ 2) :
    E ≤ Csc * (T⁻¹ * N ^ 2) := by
  have habs : |T⁻¹| = T⁻¹ := abs_of_pos (inv_pos.mpr hT)
  rw [habs] at hE
  refine hE.trans ?_
  have hstep : (ell * (T⁻¹ * N)) ^ 2 ≤ (lamq * T) * (T⁻¹ * N) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hbal (sq_nonneg (T⁻¹ * N))
    nlinarith [this]
  have hpos : 0 ≤ Csc * lamq⁻¹ := mul_nonneg hCsc (inv_nonneg.mpr hlam.le)
  refine (mul_le_mul_of_nonneg_left hstep hpos).trans ?_
  have hcollapse : Csc * lamq⁻¹ * ((lamq * T) * (T⁻¹ * N) ^ 2) =
      Csc * (T⁻¹ * N ^ 2) := by
    field_simp
  exact le_of_eq hcollapse

/-- **A `beta`-free mass term in the cross-term price destroys the
contraction.**

This is the quantitative reason the leftover pairing `⟨a∇ω, u ξ⟩` of the Hodge
decomposition may *not* be estimated by Cauchy–Schwarz into a term
`Sc · t⁻¹ M`: however small `t` is and whatever the smallness condition, a price
carrying such a term with a `beta`-independent constant `Sc` allows data
satisfying both the price and the coarse energy bound and violating
`m + t e ≤ eta M` for every `eta < Sc`.  (`MesoscopicCrossPriceOn`'s own
`S`-term is `beta · S · t⁻¹ M`, and `MesoscopicCrossPriceEnergyOn` carries the
datum inside the energy; both are `beta`-graded.  The companion refutation for
the `beta = 1` whole-cube price is
`whole_cube_price_insufficient` in `WholeSpaceRowsMesoscopic.lean`.) -/
theorem bare_mass_term_price_insufficient {t Sc eta P R Gam : ℝ}
    (_ht : 0 < t) (hSc : 0 < Sc) (hGam : 0 ≤ Gam) (heta : eta < Sc) :
    ∃ m e E M : ℝ, 0 ≤ m ∧ 0 ≤ e ∧ 0 ≤ E ∧ 0 ≤ M ∧
      (∀ beta : ℝ, 0 < beta → beta ≤ 1 →
        t⁻¹ * m + e ≤
          beta * P * E + beta⁻¹ * R * Real.sqrt E * Real.sqrt M +
            Sc * (t⁻¹ * M)) ∧
      t * E ≤ Gam * M ∧
      ¬ (m + t * e ≤ eta * M) := by
  refine ⟨Sc, 0, 0, 1, hSc.le, le_rfl, le_rfl, zero_le_one, ?_, by simpa using hGam, ?_⟩
  · intro beta _ _
    simp [mul_comm]
  · simpa using heta

/-! ## The package: the solenoidal part of a massive solution's flux -/

/-- **The mesoscopic Hodge package for the flux of a massive solution.**

On a triadic cube whose side is balanced against the resolvent time,
`side(Q)² ≤ λ T`, the flux of a solution of `T⁻¹u − ∇·(a∇u) = 0` splits as
`a∇u = G + a∇ω` with

* `G` **solenoidal** on `Q`, and
* the negative Besov norm of `G` bounded by the *coarse* conversion

```
‖G‖_{B^{-s}(Q)} ≤ C_disc Λ_{s,q}^{1/2} √( 2 ⟨a|∇u|²⟩_Q + 2 Sc T⁻¹ ‖u‖²_{L̲²(Q)} ) ,
```

with `Sc = Sc(d, s₀)` **dimension-only**.  This is items 3 and 4 of P-222 §6
(`ledger/reports/provider-77-whole-space-provider.md`): the flux factor of the
mesoscopic duality price, in the shape
`Σ_i ‖flux_i‖_{B^{-s}} ≤ cL √(Ea + Sc t⁻¹ M)` that
`MesoscopicCrossPriceEnergyOn` is built around — **for the solenoidal part
only**.  What is *not* supplied here, and has no statement in the tree, is the
same bound for the corrector flux `a∇ω`; see the file docstring. -/
theorem exists_mesoscopic_hodge_flux_conversion (d : ℕ) [NeZero d] {s0 : ℝ}
    (hs00 : 0 < s0) (hs0 : s0 < 1) :
    ∃ Sc : ℝ, 0 ≤ Sc ∧
      ∀ (Q : TriadicCube d) (afam : Ch03.CoeffFamily d) (a : Vec d → ℝ)
        (lam Lam T s : ℝ) (q : Ch02.MultiscaleExponent)
        (u : H1Function (openCubeSet Q)),
        (∀ R, Ch02.CoeffOn.IsSymmetric (afam.coeffOn R)) →
        (∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y) →
        (∀ y, 0 < a y) →
        IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField) →
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (openCubeSet Q) u
          (fun _ ↦ (0 : ℝ)) →
        0 < T → 0 < s → q.IsAdmissible →
        0 < lambdaSq Q (s0 / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField) →
        cubeScaleFactor Q ^ 2 ≤
          lambdaSq Q (s0 / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField) * T →
        ∃ G corr : Vec d → Vec d,
          (∀ x ∈ cubeSet Q,
              matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x) = G x + corr x) ∧
            IsSolenoidalOn (openCubeSet Q) G ∧
            Ch03.scaleNormalizedNegativeBesovVectorNorm Q s q G ≤
              Ch03.poincareDiscountFactor s q *
                  Ch03.poincareUpperEllipticityFactor Q afam s q *
                Real.sqrt
                  (2 * cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
                    2 * (Sc * (T⁻¹ * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun ^ 2))) := by
  classical
  obtain ⟨Csc, hCsc, hdec⟩ := exists_mesoscopic_hodge_decomposition d hs00 hs0
  refine ⟨Csc, hCsc, ?_⟩
  intro Q afam a lam Lam T s q u haSymm hA hapos hEll hu hT hs hq hlam hbal
  obtain ⟨g, ω, w, hsplit, hsol, henergy⟩ := hdec Q afam a lam Lam T⁻¹ u hA hEll hu
  have hgwCube : MemVectorL2 (cubeSet Q) w.toH1.grad := w.toH1.grad_memVectorL2
  have hgomCube : MemVectorL2 (cubeSet Q) ω.toH1MeanZero.toH1Function.grad :=
    ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q)
      ((afam.coeffOn Q).toCoeffField) :=
    IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hgwOpen : MemVectorL2 (openCubeSet Q) w.toH1.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hgwCube
  have hfluxMem : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (w.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllOpen hgwOpen
  refine ⟨fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (w.toH1.grad x),
    fun x => matVecMul ((afam.coeffOn Q).toCoeffField x)
      (ω.toH1MeanZero.toH1Function.grad x), ?_, hsol, ?_⟩
  · intro x hx
    rw [hsplit x hx, matVecMul_add]
  · have hconv :=
      negativeBesovNorm_solenoidalPart_le haSymm hA hapos hEll hs hq u hgwCube hgomCube
        hfluxMem hsol hsplit
    refine hconv.trans ?_
    have hDisc : 0 ≤ Ch03.poincareDiscountFactor s q := by
      cases q with
      | finite qq =>
          have hqq : (1 : ℝ) ≤ qq := by simpa using hq
          exact Real.rpow_nonneg
            (Ch02.book_geometricDiscount_nonneg (by nlinarith : (0 : ℝ) ≤ s * qq)) _
      | infinity => simp [Ch03.poincareDiscountFactor]
    have hUpper : 0 ≤ Ch03.poincareUpperEllipticityFactor Q afam s q :=
      Real.rpow_nonneg (Ch02.LambdaSq_nonneg Q afam hs hq) _
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (mul_nonneg hDisc hUpper)
    have hdensity :
        cubeAverage Q (fun x => a x * vecNormSq (ω.toH1MeanZero.toH1Function.grad x)) =
          cubeAverage Q (coefficientEnergyDensity ((afam.coeffOn Q).toCoeffField)
            (fun x => ω.toH1MeanZero.toH1Function.grad x)) := by
      refine congrArg (cubeAverage Q) ?_
      funext x
      rw [coefficientEnergyDensity_scalar hA]
    have hom :
        cubeAverage Q (fun x => a x * vecNormSq (ω.toH1MeanZero.toH1Function.grad x)) ≤
          Csc * (T⁻¹ * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun ^ 2) := by
      rw [hdensity]
      refine corrector_energy_le_of_balanced_scale (ell := cubeScaleFactor Q)
        (N := cubeLpNorm Q (2 : ℝ≥0∞) u.toFun) hCsc hT hlam hbal ?_
      simpa [mul_pow] using henergy
    linarith [hom]

/-- **The balanced mesoscopic cube cannot itself be the cube of the
contraction.**

`exists_mesoscopic_coarseEnergyBoundOn` (P-222) proves `CoarseEnergyBoundOn` on
a cube whose side is balanced against the resolvent time,
`side² ≤ λ T ≤ 9 side²`, and the natural reading is to feed that cube straight
into `massive_local_l2_coarse_contraction_of_energy_price_on`.  That reading is
vacuous: the contraction's smallness hypothesis
`81 (P(Gam+Sc))² R² (Gam+Sc) t ≤ eta⁴` already fails on size grounds, because
the price's `R ≍ Λ^{1/2} side⁻¹` (P-221 §2.3) gives `R² t ≥ Λ/λ ≥ 1` as soon as
`side² ≤ λ t`, while `P, Gam ≥ 1` and `eta ≤ 1`.

Equivalently: the manuscript's condition `t ℓ⁻² Λ¹²λ⁻¹¹ ≤ C⁻¹η^{15/2}` forces
`t ℓ⁻² ≤ λ⁻¹`, i.e. the mesoscopic scale `(λt)^{1/2}` is *strictly* below the
contraction scale `ℓ`.  So the coarse energy bound has to be transported from
the mesoscopic descendants up to the contraction cube (P-221 §6 item 2, the
descendant summation), which P-222 §3.2 recorded as unnecessary.  Nothing here
contradicts P-222's theorem — only the way it can be consumed. -/
theorem balanced_scale_incompatible_with_contraction_smallness
    {t ell lamq Lam P Gam Sc R eta : ℝ}
    (ht : 0 < t) (hell : 0 < ell) (hlam : 0 < lamq) (hlamLam : lamq ≤ Lam)
    (hbal : ell ^ 2 ≤ lamq * t)
    (hR : Lam * (ell ^ 2)⁻¹ ≤ R ^ 2)
    (hP : 1 ≤ P) (hGam : 1 ≤ Gam) (hSc : 0 ≤ Sc) (heta : eta ≤ 1) (heta0 : 0 < eta) :
    ¬ (81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) * t ≤ eta ^ 4) := by
  intro hle
  have hell2 : 0 < ell ^ 2 := by positivity
  have hratio : (lamq)⁻¹ ≤ t * (ell ^ 2)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hlam, mul_comm]
    have := mul_le_mul_of_nonneg_right hbal (inv_nonneg.mpr hell2.le)
    rw [mul_inv_cancel₀ hell2.ne'] at this
    calc (1 : ℝ) ≤ lamq * t * (ell ^ 2)⁻¹ := this
      _ = lamq * (t * (ell ^ 2)⁻¹) := by ring
  have hRt : 1 ≤ R ^ 2 * t := by
    have h1 : Lam * (ell ^ 2)⁻¹ * t ≤ R ^ 2 * t :=
      mul_le_mul_of_nonneg_right hR ht.le
    have h2 : (1 : ℝ) ≤ Lam * (ell ^ 2)⁻¹ * t := by
      have hlamq : lamq * (lamq)⁻¹ = 1 := mul_inv_cancel₀ hlam.ne'
      have hstep : lamq * ((lamq)⁻¹) ≤ Lam * (t * (ell ^ 2)⁻¹) := by
        refine mul_le_mul hlamLam hratio (by positivity) (by linarith)
      calc (1 : ℝ) = lamq * (lamq)⁻¹ := hlamq.symm
        _ ≤ Lam * (t * (ell ^ 2)⁻¹) := hstep
        _ = Lam * (ell ^ 2)⁻¹ * t := by ring
    linarith
  have hPG : 1 ≤ (P * (Gam + Sc)) ^ 2 := by
    have : 1 ≤ P * (Gam + Sc) := by nlinarith
    nlinarith
  have hG : 1 ≤ Gam + Sc := by linarith
  have heta4 : eta ^ 4 ≤ 1 := pow_le_one₀ heta0.le heta
  have hA : (1 : ℝ) ≤ (P * (Gam + Sc)) ^ 2 * (R ^ 2 * t) := by
    have hmul := mul_le_mul hPG hRt (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    simpa using hmul
  have hB : (1 : ℝ) ≤ (P * (Gam + Sc)) ^ 2 * (R ^ 2 * t) * (Gam + Sc) := by
    have hmul := mul_le_mul hA hG (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (0 : ℝ) ≤ (P * (Gam + Sc)) ^ 2 * (R ^ 2 * t))
    simpa using hmul
  have hbig : (81 : ℝ) ≤ 81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) * t := by
    have hmul := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 81)
    calc (81 : ℝ) = 81 * 1 := by ring
      _ ≤ 81 * ((P * (Gam + Sc)) ^ 2 * (R ^ 2 * t) * (Gam + Sc)) := hmul
      _ = 81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) * t := by ring
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
