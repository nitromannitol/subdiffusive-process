module

public import SubdiffusiveProcess.Sobolev.PotentialPerturbation
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import SubdiffusiveProcess.Algebra.StripExponents
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section




open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

variable {d : ℕ}

/-- The bounded potentials on a cube: the carrier consumed by
`expPotentialCoefficient`.  Its norm is the essential supremum. -/
abbrev Potential (Q : Opens (SpatialCoordinates d)) :=
  Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))

/-- A *response* in the sense of the paper, lines 1247-1254: a nonnegative
functional `eval g` of the potential together with the energy measure `mass g`
of its minimizer.  The fields are exactly the properties proved in
`Sobolev/PotentialPerturbation` and `Sobolev/PotentialResponses`; nothing that
the paper proves later is assumed here. -/
structure Response (Q : Opens (SpatialCoordinates d)) where
  /-- The response `𝓡(g)` computed with the coefficient `e ^ g`. -/
  eval : Potential Q → ℝ
  /-- The energy measure `Γ(u^g)(B)` of the corresponding minimizer. -/
  mass : Potential Q → Set (SpatialCoordinates d) → ℝ
  eval_nonneg : ∀ g, 0 ≤ eval g
  mass_nonneg : ∀ g s, 0 ≤ mass g s
  mass_mono : ∀ g s t, MeasurableSet s → MeasurableSet t → s ⊆ t →
    mass g s ≤ mass g t
  /-- The total energy of the minimizer is the response, paper line 1465. -/
  mass_univ : ∀ g, mass g Set.univ = eval g
  /-- `eq:mfd-mult`, paper lines 1310-1314. -/
  exp_comparison : ∀ g h, eval g ≤ Real.exp ‖g - h‖ * eval h
  /-- The response bound in `eq:mfd-14`, paper line 1305. -/
  response_perturbation : ∀ (h g : Potential Q) (s : Set (SpatialCoordinates d)),
    MeasurableSet s →
    (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), x ∉ s → g x = 0) →
    |eval (h + g) - eval h| ≤ 2 * ‖g‖ * Real.exp (4 * ‖g‖) * mass h s
  /-- The local-energy bound in `eq:mfd-14`, paper line 1304, with the constant
  supplied by `boundary_responses_potential_stability` and
  `source_responses_potential_stability`: `δ = ‖g‖ e^{‖g‖}`, `c = e^{-‖g‖}`,
  `M = e^{‖g‖}`, so `2 M (1 + δ²/c²) = 2 e^{‖g‖} (1 + ‖g‖² e^{4‖g‖})`.  Like the
  paper's `4 e^{S}` it is of the form `C e^{C S}` with an extra factor `S²`,
  which the moment bank of paper lines 1512-1522 absorbs (it only adds powers
  of the disorder). -/
  mass_perturbation : ∀ (h g : Potential Q) (s : Set (SpatialCoordinates d)),
    MeasurableSet s →
    (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), x ∉ s → g x = 0) →
    mass (h + g) s ≤
      2 * Real.exp ‖g‖ * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) * mass h s

namespace Response

variable {Q : Opens (SpatialCoordinates d)}

/-- The two-sided form of `eq:mfd-mult`. -/
theorem exp_comparison' (R : Response Q) (g h : Potential Q) :
    Real.exp (-‖g - h‖) * eval R h ≤ eval R g := by
  have hgh : ‖h - g‖ = ‖g - h‖ := by
    rw [← norm_neg (h - g), neg_sub]
  have h₁ : eval R h ≤ Real.exp ‖g - h‖ * eval R g := by
    simpa only [hgh] using R.exp_comparison h g
  have h₂ : Real.exp (-‖g - h‖) * eval R h ≤
      Real.exp (-‖g - h‖) * (Real.exp ‖g - h‖ * eval R g) :=
    mul_le_mul_of_nonneg_left h₁ (Real.exp_nonneg _)
  calc Real.exp (-‖g - h‖) * eval R h
      ≤ Real.exp (-‖g - h‖) * (Real.exp ‖g - h‖ * eval R g) := h₂
    _ = eval R g := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Response

/-- The Efron--Stein moment inequality, `eq:mfd-ES`, paper lines 1380-1392;
Theorem 2 of BBLM 2005.  Foundational input, stated as an explicit
`Prop`-valued hypothesis structure and never as an axiom.  `X i` is the
`i`-th independent input, `Function.update x i y` replaces it by an
independent copy, and the right-hand side is the `L^p` norm of the square root
of the summed conditional squared increments. -/
structure EfronSteinMomentInequality : Prop where
  exists_const : ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (S : Fin m → Type) (_ : ∀ i, MeasurableSpace (S i))
      (μ : (i : Fin m) → Measure (S i)) (_ : ∀ i, IsProbabilityMeasure (μ i))
      (X : ((i : Fin m) → S i) → ℝ),
      MemLp X (ENNReal.ofReal p) (Measure.pi μ) →
      eLpNorm (fun x => X x - ∫ z, X z ∂(Measure.pi μ)) (ENNReal.ofReal p)
          (Measure.pi μ) ≤
        ENNReal.ofReal C *
          eLpNorm (fun x => Real.sqrt
            (∑ i : Fin m, ∫ y, (X x - X (Function.update x i y)) ^ 2 ∂(μ i)))
            (ENNReal.ofReal p) (Measure.pi μ)



structure LayerNormBank {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (Cb : ℝ → ℕ → ℝ → ℝ → ℝ) (S : ℤ → Omega → ℝ) (disorder : ℝ) : Prop where
  nonneg : ∀ j ω, 0 ≤ S j ω
  measurable : ∀ j, Measurable (S j)
  const_pos : ∀ q k lam gam, 0 < Cb q k lam gam
  moment : ∀ q : ℝ, 1 ≤ q → ∀ k : ℕ, ∀ lam : ℝ, 0 ≤ lam → ∀ gam : ℝ, 0 < gam →
    ∀ j : ℕ,
      eLpNorm (fun ω => S (-(j : ℤ)) ω ^ k * Real.exp (lam * S (-(j : ℤ)) ω))
          (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (Cb q k lam gam * disorder ^ k *
          (3 : ℝ) ^ (gam * (j : ℝ)))


/-- The band sigma-field `𝓑_H = σ(g_{-j} : -H ≤ j ≤ H)` of
Proposition `mfd:prop-16`, paper line 1573, on the integer-indexed layer
product. -/
def bandSigma (Y : ℤ → Type) [∀ j, MeasurableSpace (Y j)] (H : ℕ) :
    MeasurableSpace ((j : ℤ) → Y j) :=
  ⨆ j ∈ Set.Icc (-(H : ℤ)) (H : ℤ),
    (inferInstance : MeasurableSpace (Y j)).comap (fun ω : (j : ℤ) → Y j => ω j)



def coarseUpdate {Y : ℤ → Type} (H : ℕ) (ω ω' : (j : ℤ) → Y j) :
    (j : ℤ) → Y j :=
  fun j => if j < -(H : ℤ) then ω' j else ω j

/-- Replace the coordinates `H < j` of `ω` by those of an independent copy.
See the coordinate convention on `coarseUpdate`. -/
def fineUpdate {Y : ℤ → Type} (H : ℕ) (ω ω' : (j : ℤ) → Y j) :
    (j : ℤ) → Y j :=
  fun j => if (H : ℤ) < j then ω' j else ω j

/-- The paper's **coarse** block copy of Proposition `mfd:prop-16`, paper
line 1596: the layers `g_{-j}` with `j < -H`, i.e. the coordinates `> H`. -/
def coarseBlockUpdate {Y : ℤ → Type} (H : ℕ) (ω ω' : (j : ℤ) → Y j) :
    (j : ℤ) → Y j :=
  fun j => if (H : ℤ) < j then ω' j else ω j

/-- The paper's **fine** block copy of Proposition `mfd:prop-16`, paper
line 1588: the layers `g_{-j}` with `j > H`, i.e. the coordinates `< -H`. -/
def fineBlockUpdate {Y : ℤ → Type} (H : ℕ) (ω ω' : (j : ℤ) → Y j) :
    (j : ℤ) → Y j :=
  fun j => if j < -(H : ℤ) then ω' j else ω j

/-- The complete hypothesis bundle of Lemma `mfd:lem-15` (Fine-layer
influence), paper lines 1394-1406: the layer environment, the response, the
all-radii growth constants `K N` of `eq:mfd-4`, and the finite moment bank.
Every constant (`t`, the moment order `p`, the two suprema `B`, the bank
constants `Cb`) is a parameter fixed *before* `disorder`.  Nothing proved
later in the paper occurs here. -/
structure ResamplingData (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (Y : ℤ → Type) [∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j)) [∀ j, IsProbabilityMeasure (laws j)]
    (t p B : ℝ) (Cb : ℝ → ℕ → ℝ → ℝ → ℝ) (disorder : ℝ) where
  /-- The response of paper lines 1247-1254. -/
  R : Response Q
  /-- `h N` is the potential `h_N - log κ_N` at ultraviolet cutoff `N`. -/
  h : ℕ → ((j : ℤ) → Y j) → Potential Q
  /-- `K N` is the constant of `eq:mfd-4` for the minimizer at cutoff `N`. -/
  K : ℕ → ((j : ℤ) → Y j) → ℝ
  /-- `S j` is the layer sup norm `‖g_{-j}‖_{L^∞(Q)}`. -/
  S : ℤ → ((j : ℤ) → Y j) → ℝ
  t_lower : (d : ℝ) - 1 < t
  t_upper : t < (d : ℝ)
  p_ge : 2 ≤ p
  B_nonneg : 0 ≤ B
  disorder_pos : 0 < disorder
  disorder_le_one : disorder ≤ 1
  bank : LayerNormBank (Measure.infinitePi laws) Cb S disorder
  /-- `eq:mfd-4` on `Q` with constant `K N`, paper line 1400. -/
  growth : ∀ (N : ℕ) (ω : (j : ℤ) → Y j) (x : SpatialCoordinates d) (r : ℝ),
    0 < r → r ≤ 1 → R.mass (h N ω) (Metric.ball x r) ≤ K N ω * r ^ t
  K_nonneg : ∀ N ω, 0 ≤ K N ω
  K_measurable : ∀ N, Measurable (K N)
  response_measurable : ∀ N, Measurable (fun ω => R.eval (h N ω))
  /-- `sup_N ‖K_N‖_{L^{3p}} ≤ B`, paper line 1402. -/
  K_moment : ∀ N, eLpNorm (K N) (ENNReal.ofReal (3 * p))
    (Measure.infinitePi laws) ≤ ENNReal.ofReal B
  /-- `sup_N ‖𝓡_N‖_{L^{3p}} ≤ B`, paper line 1402. -/
  response_moment : ∀ N, eLpNorm (fun ω => R.eval (h N ω)) (ENNReal.ofReal (3 * p))
    (Measure.infinitePi laws) ≤ ENNReal.ofReal B

/-- The decay exponent `a = b / (8 log 3)` of `eq:mfd-15`, paper line 1404,
with `b = stripMassExponent d t` from Lemma `mfd:lem-strips`.  It depends on
`d` and `t` only, never on the moment order `p` or on the disorder. -/
def influenceExponent (d t : ℝ) : ℝ := stripMassExponent d t / (8 * Real.log 3)

theorem influenceExponent_pos {d t : ℝ} (hd : 1 ≤ d) (ht : d - 1 < t) :
    0 < influenceExponent d t := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  exact div_pos (strip_mass_exponent_pos hd ht) (by linarith)

end Lane3
end SubdiffusiveProcess
