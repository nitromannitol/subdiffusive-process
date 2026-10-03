module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszShellTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFixedSpheres

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A countable sum of an indicator supported on the injective image of a
finite index set collapses to the finite sum. -/
theorem tsum_ite_eq_finset_sum_comp {A B : Type*} [Countable A] [DecidableEq A]
    (S : Finset B) (e : B → A) (he : Function.Injective e)
    (P : A → Prop) [DecidablePred P]
    (hP : ∀ a, P a ↔ ∃ b ∈ S, e b = a)
    (f : A → ℝ≥0∞) :
    ∑' a : A, (if P a then f a else 0) = ∑ b ∈ S, f (e b) := by
  have hzero : ∀ a ∉ S.image e, (if P a then f a else 0) = 0 := by
    intro a ha
    refine if_neg ?_
    intro hPa
    obtain ⟨b, hb, hbe⟩ := (hP a).mp hPa
    exact ha (Finset.mem_image.mpr ⟨b, hb, hbe⟩)
  rw [tsum_eq_sum hzero,
    Finset.sum_image (fun x _ y _ hxy ↦ he hxy)]
  refine Finset.sum_congr rfl ?_
  intro b hb
  exact if_pos ((hP (e b)).mpr ⟨b, hb, rfl⟩)

variable {d : ℕ} [NeZero d] {base : ℤ}
variable {failure : TriadicCube d → Set (PotentialSample d)}
variable {omega : PotentialSample d}

/-- **The exact repaired shell over the fixed code.**  With the local weights
transported along the code map, the fixed-code shell sum is the literal raw
shell of `FluxRowRieszShellSummation`. -/
theorem fixedRepairedShellSum_eq_ofReal_repairedFluxRowRieszRawShell
    (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega P))
    (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
      cubeSet P.1)
    (x0 : Vec d) {R : ℝ} (hR : 0 < R)
    (hsource : (repairedStoppingSourceCells hinitial hrepair x0 R).Nonempty)
    (W : RepairedStoppingCellCode d → PotentialSample d → ℝ≥0∞)
    (weight : RefinedStoppingCell failure omega base → ℝ)
    (hweight : ∀ q, 0 ≤ weight q)
    (hW : ∀ q, W (repairedStoppingCellCode q) omega = ENNReal.ofReal (weight q))
    (j : ℕ) :
    fixedRepairedShellSum failure base x0 R W j omega =
      ENNReal.ofReal (repairedFluxRowRieszRawShell
        (repairedStoppingSourceCells hinitial hrepair x0 R) hsource R weight j) := by
  have hstep : fixedRepairedShellSum failure base x0 R W j omega =
      ∑ q ∈ stoppingGraphLevelCells repairedStoppingGraph
          (repairedStoppingSourceCells hinitial hrepair x0 R) hsource j,
        ENNReal.ofReal
            ((((3 : ℝ) ^ repairedStoppingCellCodeScale
              (repairedStoppingCellCode q)) / R) ^ (d + 6)) *
          W (repairedStoppingCellCode q) omega := by
    exact tsum_ite_eq_finset_sum_comp _ _ repairedStoppingCellCode_injective _
      (fun c ↦ isExactRepairedStoppingCodeSphere_iff hinitial hrepair x0 R
        hsource j c) _
  rw [hstep, repairedFluxRowRieszRawShell,
    ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl ?_
    intro q _hq
    rw [hW q, repairedStoppingCellCodeScale_apply,
      ← ENNReal.ofReal_mul (by positivity)]
  · intro q _hq
    exact mul_nonneg (pow_nonneg (div_nonneg (by positivity) hR.le) _) (hweight q)

/-- The real measurable shell field agrees samplewise with the raw shell. -/
theorem fixedRepairedShell_eq_repairedFluxRowRieszRawShell
    (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega P))
    (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
      cubeSet P.1)
    (x0 : Vec d) {R : ℝ} (hR : 0 < R)
    (hsource : (repairedStoppingSourceCells hinitial hrepair x0 R).Nonempty)
    (W : RepairedStoppingCellCode d → PotentialSample d → ℝ≥0∞)
    (weight : RefinedStoppingCell failure omega base → ℝ)
    (hweight : ∀ q, 0 ≤ weight q)
    (hW : ∀ q, W (repairedStoppingCellCode q) omega = ENNReal.ofReal (weight q))
    (j : ℕ) :
    fixedRepairedShell failure base x0 R W j omega =
      repairedFluxRowRieszRawShell
        (repairedStoppingSourceCells hinitial hrepair x0 R) hsource R weight j := by
  rw [fixedRepairedShell,
    fixedRepairedShellSum_eq_ofReal_repairedFluxRowRieszRawShell
      hinitial hrepair x0 hR hsource W weight hweight hW j,
    ENNReal.toReal_ofReal
      (repairedFluxRowRieszRawShell_nonneg _ hsource hR hweight j)]

/-- **The almost-sure shell majorant.**  On the full-measure event carrying the
two local-finiteness certificates and the transported local weights, the
measurable fixed-code shell field agrees with the sample-dependent raw shell of
`FluxRowRieszShellSummation` at every level. -/
theorem ae_fixedRepairedShell_eq_repairedFluxRowRieszRawShell
    (mu : Measure (PotentialSample d))
    (failure : TriadicCube d → Set (PotentialSample d))
    (x0 : Vec d) {R : ℝ} (hR : 0 < R)
    (W : RepairedStoppingCellCode d → PotentialSample d → ℝ≥0∞)
    (weight : ∀ omega : PotentialSample d,
      RefinedStoppingCell failure omega base → ℝ)
    (hgood : ∀ᵐ omega ∂mu,
      ∃ (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
          cubeSet (triadicStoppingCandidate failure omega P))
        (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
          cubeSet P.1)
        (_hsource : (repairedStoppingSourceCells hinitial hrepair x0 R).Nonempty),
        (∀ q, 0 ≤ weight omega q) ∧
          ∀ q, W (repairedStoppingCellCode q) omega =
            ENNReal.ofReal (weight omega q)) :
    ∀ᵐ omega ∂mu,
      ∃ (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
          cubeSet (triadicStoppingCandidate failure omega P))
        (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
          cubeSet P.1)
        (hsource : (repairedStoppingSourceCells hinitial hrepair x0 R).Nonempty),
        ∀ j, fixedRepairedShell failure base x0 R W j omega =
          repairedFluxRowRieszRawShell
            (repairedStoppingSourceCells hinitial hrepair x0 R) hsource R
            (weight omega) j := by
  filter_upwards [hgood] with omega homega
  obtain ⟨hinitial, hrepair, hsource, hweight, hW⟩ := homega
  refine ⟨hinitial, hrepair, hsource, fun j ↦ ?_⟩
  exact fixedRepairedShell_eq_repairedFluxRowRieszRawShell hinitial hrepair x0 hR
    hsource W (weight omega) hweight hW j

omit [NeZero d] in


theorem fluxRowRieszShellMomentInput_fixedRepairedShell
    {mu : Measure (PotentialSample d)}
    (failure : TriadicCube d → Set (PotentialSample d))
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ)
    (W : RepairedStoppingCellCode d → PotentialSample d → ℝ≥0∞)
    (hW : ∀ c, Measurable (W c))
    {beta : ℝ} (hbeta : 0 ≤ beta) {p : ℕ} {K C A : ℝ}
    (hsummable : ∀ omega, Summable fun j ↦
      beta ^ j * fixedRepairedShell failure base x0 R W j omega)
    (hp : 0 < p) (hK : 1 ≤ K) (hlogK : Real.log K ≤ C) (hA : (p : ℝ)⁻¹ ≤ A)
    (hintegrable : Integrable
      (fun omega ↦ wholeSpaceFluxPartitionFactor beta
        (fixedRepairedShell failure base x0 R W) omega ^ p) mu)
    (hmoment : ∫ omega, wholeSpaceFluxPartitionFactor beta
        (fixedRepairedShell failure base x0 R W) omega ^ p ∂mu ≤ K ^ p) :
    FluxRowRieszShellMomentInput mu beta
      (fixedRepairedShell failure base x0 R W) p K C A :=
  fluxRowRieszShellMomentInput_of_measurable_shell hbeta
    (fun j omega ↦ fixedRepairedShell_nonneg failure base x0 R W j omega)
    hsummable
    (fun j ↦ measurable_fixedRepairedShell failure hfailure x0 R W hW j)
    hp hK hlogK hA hintegrable hmoment

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
