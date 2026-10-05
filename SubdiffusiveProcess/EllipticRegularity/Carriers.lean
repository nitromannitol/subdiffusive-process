/-
Elliptic regularity carriers -- Part A of `mfd:sec-local`.

These carriers have explicit definition bodies; none introduces an assumption.
-/
module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.Geometry.CoordinateFold

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.EllipticRegularity

/-- `[f]²_{H̲^s(Q)}`: the normalized Gagliardo seminorm squared of a vector `L²` class on a
cube.  This is `cubeFractionalL2Seminorm` read as a real number; it is the carrier for the
paper's bracketed seminorm `[g]_{H̲^s}`, which appears alone — without any `L²` term — in
the source summand. -/
def cubeFractionalVecSeminormSq {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr)) : ℝ :=
  ((cubeFractionalL2Seminorm hd z r hr s f).toReal) ^ 2

/-- `‖f‖²_{H̲^s(Q)}`: the inhomogeneous normalized `H^s` norm squared of a vector `L²` class
on a cube — the normalized Gagliardo seminorm squared plus the **normalized** `L²` norm
squared.

Both summands are volume-normalized, as the paper's underlined norms are.  The previous
version added the un-normalized `‖f‖²`, mixing normalizations: against a normalized left
side that inserts a spurious factor of order `3^{md/2}` on a cube of side `3^{-m}`. -/
def cubeFractionalVecSqNorm {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr)) : ℝ :=
  cubeFractionalVecSeminormSq hd z r hr s f +
    (∑ i : Fin k, ‖f i‖ ^ 2) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d))

/-- The scalar case of `cubeFractionalVecSqNorm`: the inhomogeneous normalized `H^s` norm
squared of a scalar `L²` class on a cube.  Used for the `H^{3/4}(Q)` norm of `eq:mfd-1`
-/
def cubeFractionalSqNorm {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr)) : ℝ :=
  cubeFractionalVecSqNorm (k := 1) hd z r hr s (fun _ => v)

/-- The exponent `3/4` of `eq:mfd-1`. -/
def threeQuarterOrder : Set.Ioo (0 : ℝ) 1 := ⟨3 / 4, by norm_num, by norm_num⟩

/-- The mean of an `L²` class over a finite-volume domain (the `v_Q` of `eq:mfd-1`). -/
def domainMean {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (v : DomainL2 Ω) : ℝ :=
  (volume.real (Ω : Set (SpatialCoordinates d)))⁻¹ *
    ∫ x in (Ω : Set (SpatialCoordinates d)), v x


/-- `‖a^{1/2}∇u‖_{\underline L²(s)}`: the volume-normalized coefficient energy norm. -/
def normalizedEnergyNorm {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (g : HilbertGradient Ω) : ℝ :=
  Real.sqrt (localGradientEnergy a hs g / volume.real s)

/-- `[g]_{W^{1/2,∞}(S)}`: the Euclidean Hölder-`1/2` seminorm of a vector field on `S`. -/
def halfHolderSeminorm {d k : ℕ} (S : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → Fin k → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧
    v = Real.sqrt (∑ i : Fin k, (g x i - g y i) ^ 2) /
      Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))}

/-- `‖g‖_{\underline W^{1/2,∞}(S)}` at scale `r`: sup norm plus `r^{1/2}` times the seminorm. -/
def halfHolderNorm {d k : ℕ} (r : ℝ) (S : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → Fin k → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x ∈ S, v = Real.sqrt (∑ i : Fin k, (g x i) ^ 2)} +
    Real.sqrt r * halfHolderSeminorm S g

/-- `E(u,U) = 3^{-j} min_ℓ ‖u-ℓ‖_{\underline L²(U)}`, the excess of `e.excess.def`:
the scale factor `3^{-j}` and the volume normalization are both retained. -/
def affineExcess {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (j : ℤ)
    (u : DomainL2 Ω) : ℝ :=
  (3 : ℝ) ^ (-j) * (⨅ pc : (Fin d → ℝ) × ℝ, ‖u - affineL2 hΩ pc.1 pc.2‖) /
    Real.sqrt (volume.real (Ω : Set (SpatialCoordinates d)))

/-- `A_N` of `eq:mfd-normalization`  as a continuous map
on the compact cube `closedCube z r hr`. -/
def cutoffCoefficientCM {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) : C(closedCube z r hr, ℝ) :=
  ⟨fun x => cutoffCoefficient M H omega N (x : SpatialCoordinates d), by
    have hcont : Continuous (cutoffCoefficient M H omega N) := by
      refine continuous_const.mul (Real.continuous_exp.comp ?_)
      exact Continuous.sub
        (Continuous.add (H omega).continuous
          (continuous_finsetSum _ fun j _ => (omega (-(Int.ofNat j))).continuous))
        continuous_const
    exact hcont.comp continuous_subtype_val⟩

theorem cutoffCoefficientCM_pos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ x, 0 < cutoffCoefficientCM M H omega N z hr x := by
  intro x
  exact mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

/-- `A_N` restricted to the open cube, as the project's positive bounded coefficient. -/
def cutoffPositiveCoefficient {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    PositiveCoefficient (centeredCube z r hr) :=
  @normalizedContinuousPositiveCoefficient d (centeredCube z r hr) (closedCube z r hr)
    ⟨centeredCube_subset_closedCube z hr⟩
    (cutoffCoefficientCM M H omega N z hr) (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos


/-- The set of Hölder difference quotients `|G x - G y| / |x - y| ^ beta` over distinct
points of `S`.  `holderSeminorm` is its supremum. -/
def holderRatioSet {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (G : SpatialCoordinates d → ℝ) : Set ℝ :=
  {v : ℝ | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧
    v = |G x - G y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta}

/-- `[G]_{C^β(S)}`: the Hölder-`β` seminorm of a scalar function on `S`. -/
def holderSeminorm {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (G : SpatialCoordinates d → ℝ) : ℝ :=
  sSup (holderRatioSet beta S G)

/-- `G ∈ C^β(S)` in the only sense that makes `holderSeminorm` a genuine seminorm rather
than `sSup`'s junk default: the difference quotients are bounded above.  Without this
hypothesis `holderSeminorm beta S G = 0` for functions that are *not* `β`-Hölder (the
supremum of an unbounded set is `0` by mathlib's convention), so any estimate whose right
side is a multiple of `holderSeminorm` is refutable — see the comment on
`lem_extension`.  Every consumer of `holderSeminorm` as an upper bound must carry it. -/
def IsHolderOn {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (G : SpatialCoordinates d → ℝ) : Prop :=
  BddAbove (holderRatioSet beta S G)

/-- The `C²(S)` norm of a scalar function. -/
def c2Norm {d : ℕ} (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x ∈ S, v = |f x|} +
    sSup {v : ℝ | ∃ x ∈ S, v = ‖fderiv ℝ f x‖} +
    sSup {v : ℝ | ∃ x ∈ S, v = ‖fderiv ℝ (fderiv ℝ f) x‖}

/-- The `C^α(S)` norm of a scalar function. -/
def cAlphaNorm {d : ℕ} (alpha : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + holderSeminorm alpha S f

/-- `u` solves `-∇·(a∇u) = F` weakly in `Ω` with Dirichlet datum `b`. -/
def SolvesDirichlet {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (F : SpatialCoordinates d → ℝ)
    (b u : weakSobolevGraph Ω) : Prop :=
  ((u : SobolevData Ω) - (b : SobolevData Ω)) ∈ killedSobolevGraph Ω ∧
    ∀ ψ : killedSobolevGraph Ω,
      sobolevCoefficientForm a (u : SobolevData Ω) (ψ : SobolevData Ω) =
        ∫ x in (Ω : Set (SpatialCoordinates d)), F x * (ψ : SobolevData Ω).1 x

/-- `u` solves `-∇·(a∇u) = F` weakly in `Ω` with zero conormal derivative on every face
(the mean-zero Neumann problem of `eq:mfd-bump`). -/
def SolvesNeumann {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (a : PositiveCoefficient Ω) (F : SpatialCoordinates d → ℝ)
    (u : meanZeroSobolevGraph Ω) : Prop :=
  ∀ ψ : weakSobolevGraph Ω,
    sobolevCoefficientForm a (u : SobolevData Ω) (ψ : SobolevData Ω) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), F x * (ψ : SobolevData Ω).1 x

/-- The unit cube `Q = (0,1)^d` of the smoothed Neumann problem. -/
def unitNeumannCube (d : ℕ) : Opens (SpatialCoordinates d) :=
  centeredCube (fun _ => (1 / 2 : ℝ)) 1 one_pos

instance instIsFiniteMeasureUnitNeumannCube (d : ℕ) :
    IsFiniteMeasure (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  unfold unitNeumannCube
  infer_instance

/-- The face-bump source `f_ε` of `eq:mfd-bump`. -/
def faceBump {d : ℕ} (rho : ℝ → ℝ) (p : Fin d → ℝ) (eps : ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  ∑ i : Fin d, p i * (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps))

/-- The centre of the reflection planes for the active faces `I` of `centeredCube w r hr`,
with the face selected in each active coordinate by the sign set `P`:
`coordinateReflectionSign P j = -1` for `j ∈ P`, so the plane is then the upper face. -/
def foldedCubeCenter {d : ℕ} (w : SpatialCoordinates d) (r : ℝ) (I P : Finset (Fin d)) :
    SpatialCoordinates d :=
  fun j => if j ∈ I then (if j ∈ P then w j + r / 2 else w j - r / 2) else w j

/-- The union `Ũ` of `U = centeredCube w r hr` with its reflections in the active faces
`I`: the cube doubled in each active coordinate, on the side opposite to the fold
direction selected by `P`. -/
def foldedCube {d : ℕ} (w : SpatialCoordinates d) (r : ℝ) (_hr : 0 < r)
    (I P : Finset (Fin d)) : Opens (SpatialCoordinates d) :=
  ⟨Set.pi Set.univ (fun j =>
      if j ∈ I then
        (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
          else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
      else Set.Ioo (w j - r / 2) (w j + r / 2)),
    isOpen_set_pi Set.finite_univ (fun j _ => by
      by_cases hj : j ∈ I
      · by_cases hP : j ∈ P <;>
          simp only [hj, hP, ite_true, ite_false] <;> exact isOpen_Ioo
      · simp only [hj, ite_false]; exact isOpen_Ioo)⟩


/-- `(⨍_s |∇u|^{p_1})^{1/p_1}`: the volume-normalized `L^{p_1}` norm of the Euclidean
length of an `L²` gradient on a measurable subset. -/
def normalizedGradientLpNorm {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (p1 : ℝ≥0∞)
    (s : Set (SpatialCoordinates d)) (g : HilbertGradient Ω) : ℝ :=
  (eLpNorm (fun y => Real.sqrt (∑ i : Fin d, (g i y) ^ 2)) p1
      ((volume.restrict (Ω : Set (SpatialCoordinates d))).restrict s)).toReal /
    (volume.real s) ^ (1 / p1.toReal)


/-- The Gagliardo `H^s(ℝ^d)` squared norm of a global scalar function: the `L²(ℝ^d)`
norm squared plus the Gagliardo double integral, in the same kernel normalization as
`cubeFractionalL2Seminorm`. -/
def globalFractionalSqNorm {d : ℕ} (s : ℝ) (v : SpatialCoordinates d → ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal ((v x) ^ 2)) +
    ∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
      ENNReal.ofReal ((v q.1 - v q.2) ^ 2) /
        ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * s)

/-- The average of an `L²` class over a measurable set of positive volume. -/
def setAverage {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : Set (SpatialCoordinates d)) (u : DomainL2 Ω) : ℝ :=
  (volume.real S)⁻¹ * ∫ y in S, u y ∂volume.restrict (Ω : Set (SpatialCoordinates d))

/-- **Killed solution with a bounded Lebesgue source** (for
`Speed.uniform_resolvent`).  `u` is a zero-trace weak solution of `-∇·(a∇u) = F` in `Ω`
whose source `F` is essentially bounded by `K`.  This is `SolvesDirichlet` with boundary
datum `0`, together with the `L^∞(Ω)` bound on the source; it is the hypothesis class of
the Part A Hölder input `eq:mfd-5` at `α = 1/2`. -/
def KilledSolvesBoundedSource {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (K : ℝ) (F : SpatialCoordinates d → ℝ)
    (u : weakSobolevGraph Ω) : Prop :=
  SolvesDirichlet a F 0 u ∧
    AEStronglyMeasurable F (volume.restrict (Ω : Set (SpatialCoordinates d))) ∧
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |F x| ≤ K

/-- The solution of `KilledSolvesBoundedSource` has zero trace. -/
theorem killedSobolevGraph_of_killedSolvesBoundedSource {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} {a : PositiveCoefficient Ω} {K : ℝ}
    {F : SpatialCoordinates d → ℝ} {u : weakSobolevGraph Ω}
    (h : KilledSolvesBoundedSource a K F u) :
    (u : SobolevData Ω) ∈ killedSobolevGraph Ω := by
  have h0 := h.1.1
  simpa using h0

/-- The weak formulation carried by `KilledSolvesBoundedSource`. -/
theorem weakForm_of_killedSolvesBoundedSource {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} {a : PositiveCoefficient Ω} {K : ℝ}
    {F : SpatialCoordinates d → ℝ} {u : weakSobolevGraph Ω}
    (h : KilledSolvesBoundedSource a K F u) (ψ : killedSobolevGraph Ω) :
    sobolevCoefficientForm a (u : SobolevData Ω) (ψ : SobolevData Ω) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), F x * (ψ : SobolevData Ω).1 x :=
  h.1.2 ψ

/-- Every killed solution with a bounded source is inhabited by the trivial one:
`u = 0` with `F = 0` and any `0 ≤ K`.  This is the
inhabitation witness for the carrier. -/
theorem killedSolvesBoundedSource_zero {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {K : ℝ} (hK : 0 ≤ K) :
    KilledSolvesBoundedSource a K (fun _ => (0 : ℝ)) 0 := by
  refine ⟨⟨?_, ?_⟩, aestronglyMeasurable_const, ?_⟩
  · simp
  · intro ψ
    simp
  · filter_upwards with x
    simpa using hK

/-- On the whole domain the local gradient energy is the coefficient form of the datum
with itself. -/
theorem localGradientEnergy_domain_eq_sobolevCoefficientForm {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (u : SobolevData Ω) :
    localGradientEnergy a Ω.isOpen.measurableSet (sobolevGradient u) =
      sobolevCoefficientForm a u u := by
  rw [localGradientEnergy_eq_integral, sobolevCoefficientForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ((sobolevGradient u).ofLp i) = u.2 i := rfl
  simp only [h1, Measure.restrict_restrict Ω.isOpen.measurableSet, Set.inter_self, pow_two]

/-- The unit cube has volume one. -/
theorem centeredCube_one_volume_real {d : ℕ} (z : SpatialCoordinates d)
    (hr : (0 : ℝ) < 1) :
    volume.real (centeredCube z 1 hr : Set (SpatialCoordinates d)) = 1 := by
  rw [centeredCube_volume_real]
  exact one_pow d

end SubdiffusiveProcess.EllipticRegularity
