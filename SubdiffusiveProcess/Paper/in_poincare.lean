module

public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.CoarseGrainingVocab.Norms
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Homogenization.Besov.Positive.ExactOverlap
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Paper.in_J

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



structure in_poincare (d : ℕ) (hd : 2 ≤ d) (E : in_J d) where
  /-- `[∇u]_{B^{-s}_{2,q}(Q)}`: the Besov seminorm of the gradient, at order `-s` and
  integrability parameter `q ∈ [1,∞]`. -/
  besovGradSeminorm : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    SobolevData (centeredCube z r hr) → ℝ → ℝ≥0∞ → ℝ
  besovGradSeminorm_nonneg : ∀ z r hr u s q, 0 ≤ besovGradSeminorm z r hr u s q
  /-- `[u]_{B^{1-s}_{2,∞}(Q)}`. -/
  besovSeminorm : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    DomainL2 (centeredCube z r hr) → ℝ → ℝ
  besovSeminorm_nonneg : ∀ z r hr u s, 0 ≤ besovSeminorm z r hr u s
  /-- The paper's normalizing factor `cs(s,q)^{-1/q}`, taken as a single positive object
  because `-1/q` is not a real exponent at `q = ∞`. -/
  cssPow : ℝ → ℝ≥0∞ → ℝ
  cssPow_pos : ∀ s q, 0 < cssPow s q
  C : ℝ
  C_pos : 0 < C
  /-- `cssPow` is the paper's geometric factor on the admissible domain `0 < s ≤ 1`,
  `1 ≤ q`: the normalized `1 - 3^{-s*q}` factor with the `q = ∞` case giving factor `1`. -/
  cssPow_eq : ∀ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ (q : ℝ≥0∞), 1 ≤ q →
    cssPow s q = SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor s
      (if q = ⊤ then .infinity else .finite q.toReal)
  /-- The gradient Besov seminorm is the paper's scale-normalized negative Besov vector
  norm of the transported physical gradient `fun x i => u.2 i (T x)` on the source cube
  `Q0 = originCube d 0`, scaled by `r^s`; `T x = fun i => z i + r * x i`. -/
  besovGradSeminorm_eq : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (u : SobolevData (centeredCube z r hr)) (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (q : ℝ≥0∞), 1 ≤ q →
    besovGradSeminorm z r hr u s q =
      r ^ s * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        (Homogenization.originCube d 0) s
        (if q = ⊤ then .infinity else .finite q.toReal)
        (fun x i => u.2 i (fun j => z j + r * x j))
  /-- The finite partial norms of the negative aggregation form a bounded real family. -/
  negativeBesovVectorPartialNormFinite_bddAbove :
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (u : SobolevData (centeredCube z r hr)) (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (q : ℝ), 1 ≤ q →
    BddAbove (Set.range (fun N : ℕ =>
      Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite
        (Homogenization.originCube d 0) s q N
        (fun x i => u.2 i (fun j => z j + r * x j))))
  /-- The negative Besov depth seminorms form a bounded real family. -/
  negativeBesovVectorDepthSeminorm_bddAbove :
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (u : SobolevData (centeredCube z r hr)) (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
    BddAbove (Set.range (fun j : ℕ =>
      Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm
        (Homogenization.originCube d 0) s
        (fun x i => u.2 i (fun j => z j + r * x j)) j))
  

  positive_integrable : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (v : DomainL2 (centeredCube z r hr)),
    Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0)
      (fun x => v (fun j => z j + r * x j))
  /-- The Besov seminorm is `r^(s-1)` times the exact-overlap depth `iSup` of order `1-s`,
  on the admissible domain `0 < s ≤ 1`. -/
  besovSeminorm_eq : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (v : DomainL2 (centeredCube z r hr)) (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
    besovSeminorm z r hr v s =
      r ^ (s - 1) *
        (iSup (fun j : ℕ =>
          Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
            (fun x => v (fun j => z j + r * x j))
            (positive_integrable z r hr v) j)).toReal
  /-- Finite-sup guard on the finite Sobolev domain: the depth `iSup` is finite for the
  value of every weak Sobolev graph. -/
  besovSeminorm_finite : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ u : weakSobolevGraph (centeredCube z r hr),
    (iSup (fun j : ℕ =>
      Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
        (fun x => (u : SobolevData (centeredCube z r hr)).1 (fun j => z j + r * x j))
        (positive_integrable z r hr (u : SobolevData (centeredCube z r hr)).1) j)) < ⊤
  /-- The explicit centering construction for the mean-subtracted branch: for every `H¹`
  function `u` there is `w` in the mean-zero graph whose value is a.e. the mean-subtracted
  value of `u` and whose gradient is unchanged. -/
  centered_representative : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ u : weakSobolevGraph (centeredCube z r hr),
    ∃ w : meanZeroSobolevGraph (centeredCube z r hr),
      ((w : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => (u : SobolevData (centeredCube z r hr)).1 x -
          SubdiffusiveProcess.Lane4.setAverage
            (centeredCube z r hr : Set (SpatialCoordinates d))
            (u : SobolevData (centeredCube z r hr)).1) ∧
      sobolevGradient (w : SobolevData (centeredCube z r hr)) =
        sobolevGradient (u : SobolevData (centeredCube z r hr))
  /-- `e.besov.grad.poincare`, the first display: for `s ∈ (0,1]`, `q ∈ [1,∞]`, `m ∈ ℤ`
  and `u ∈ H¹(Q_m)`,
  `3^{-sm}[∇u]_{B^{-s}_{2,q}} ≤ cs(s,q)^{-1/q} λ_{s,q}^{-1/2} ‖a^{1/2}∇u‖_{L̲²}`. -/
  besov_grad_poincare : ∀ (z : SpatialCoordinates d) (m : ℤ) (hr : (0 : ℝ) < 3 ^ m)
      (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hr))
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ q : ℝ≥0∞, 1 ≤ q →
    ∀ u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr),
      (3 : ℝ) ^ (-(s * (m : ℝ))) *
          besovGradSeminorm z ((3 : ℝ) ^ m) hr (u : SobolevData _) s q ≤
        cssPow s q * (E.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) s q) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a
            (centeredCube z ((3 : ℝ) ^ m) hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))
  /-- `e.nabla.u.detach`, the second display, on the unit cube:
  `[u]_{B^{1-s}_{2,∞}} ≤ C [∇u]_{B^{-s}_{2,1}}`. -/
  detach : ∀ (z : SpatialCoordinates d) (hr : (0 : ℝ) < 1)
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
    ∀ u : weakSobolevGraph (centeredCube z 1 hr),
      besovSeminorm z 1 hr (u : SobolevData (centeredCube z 1 hr)).1 s ≤
        C * besovGradSeminorm z 1 hr (u : SobolevData _) s 1
  /-- `e.CG.Poincare.trace.zero`, mean-zero half:
  `‖u - (u)_{Q_0}‖_{L̲²} ≤ C λ_{1,1}^{-1/2} ‖a^{1/2}∇u‖_{L̲²}` for `u ∈ H¹(Q_0)`.
  The difference `u - (u)_{Q_0}` is carried by `meanZeroSobolevGraph` (DEV-003). -/
  poincare_meanZero : ∀ (z : SpatialCoordinates d) (hr : (0 : ℝ) < 1)
      (a : PositiveCoefficient (centeredCube z 1 hr))
      (u : meanZeroSobolevGraph (centeredCube z 1 hr)),
      ‖(u : SobolevData (centeredCube z 1 hr)).1‖ /
          Real.sqrt (volume.real (centeredCube z 1 hr : Set (SpatialCoordinates d))) ≤
        C * (E.lam z 1 hr a z 1 1 1) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))
  /-- `e.CG.Poincare.trace.zero`, zero-trace half:
  `‖u‖_{L̲²} ≤ C λ_{1,1}^{-1/2} ‖a^{1/2}∇u‖_{L̲²}` for `u ∈ H¹_0(Q_0)`. -/
  poincare_killed : ∀ (z : SpatialCoordinates d) (hr : (0 : ℝ) < 1)
      (a : PositiveCoefficient (centeredCube z 1 hr))
      (u : killedSobolevGraph (centeredCube z 1 hr)),
      ‖(u : SobolevData (centeredCube z 1 hr)).1‖ /
          Real.sqrt (volume.real (centeredCube z 1 hr : Set (SpatialCoordinates d))) ≤
        C * (E.lam z 1 hr a z 1 1 1) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))
  /-- `e.besov.grad.poincare` for all translations/dilations: arbitrary positive radius. -/
  besov_grad_poincare_all_radii : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ (q : ℝ≥0∞), 1 ≤ q →
    ∀ u : weakSobolevGraph (centeredCube z r hr),
      r ^ (-s) * besovGradSeminorm z r hr (u : SobolevData _) s q ≤
        cssPow s q * (E.lam z r hr a z r s q) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))
  /-- `e.nabla.u.detach` for all translations/dilations: arbitrary positive radius. -/
  detach_all_radii : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
    ∀ u : weakSobolevGraph (centeredCube z r hr),
      besovSeminorm z r hr (u : SobolevData (centeredCube z r hr)).1 s ≤
        C * besovGradSeminorm z r hr (u : SobolevData _) s 1
  /-- `e.CG.Poincare.trace.zero`, mean-zero half, all radii: arbitrary `r > 0` with the
  extra radius factor `C * r`. -/
  poincare_meanZero_all_radii : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (u : meanZeroSobolevGraph (centeredCube z r hr)),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        C * r * (E.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))
  /-- `e.CG.Poincare.trace.zero`, zero-trace half, all radii: arbitrary `r > 0` with the
  extra radius factor `C * r`. -/
  poincare_killed_all_radii : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (u : killedSobolevGraph (centeredCube z r hr)),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        C * r * (E.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))

end Paper
