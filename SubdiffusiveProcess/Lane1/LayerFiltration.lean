import SubdiffusiveProcess.Lane1.TailFunctional
import SubdiffusiveProcess.Probability.LayerProductBlocks
import SubdiffusiveProcess.Main.ChaosSampleLaw

/-!
# The layer filtration and its tail

The environment is an independent family indexed by the integers.  The head
block at stage `k` is the set of indices the first `k+1` generations read
together with everything above them; its complement is the tail block, and the
two are independent because disjoint coordinate restrictions of a product
measure are.  The head blocks increase to the whole index set, so the head
sigma-fields form a filtration generating everything -- exactly the input
Levy's upward theorem needs.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The indices the first `k+1` generations read, together with everything
above them. -/
def headIndices (k : ℕ) : Set ℤ := (tailIndices (k + 1))ᶜ

theorem monotone_headIndices : Monotone headIndices := by
  intro k l hkl j hj
  simp only [headIndices, tailIndices, Set.mem_compl_iff, Set.mem_setOf_eq] at hj ⊢
  omega

/-- The sigma-field of the tail block at stage `k`. -/
def tailSigma (k : ℕ) : MeasurableSpace (BilateralField d) :=
  MeasurableSpace.comap ((tailIndices (k + 1)).restrict)
    (inferInstance : MeasurableSpace ((i : tailIndices (k + 1)) →
      C(SpatialCoordinates d, ℝ)))

/-- The sigma-field of the head block at stage `k`. -/
def headSigma (k : ℕ) : MeasurableSpace (BilateralField d) :=
  MeasurableSpace.comap ((headIndices k).restrict)
    (inferInstance : MeasurableSpace ((i : headIndices k) →
      C(SpatialCoordinates d, ℝ)))

theorem tailSigma_le (k : ℕ) :
    tailSigma (d := d) k ≤ (inferInstance : MeasurableSpace (BilateralField d)) :=
  (Set.measurable_restrict _).comap_le

theorem headSigma_le (k : ℕ) :
    headSigma (d := d) k ≤ (inferInstance : MeasurableSpace (BilateralField d)) :=
  (Set.measurable_restrict _).comap_le

theorem monotone_headSigma : Monotone (headSigma (d := d)) := by
  intro k l hkl
  rw [headSigma, headSigma, comap_restrict_eq_iSup, comap_restrict_eq_iSup]
  exact iSup₂_mono' fun i hi => ⟨i, monotone_headIndices hkl hi, le_rfl⟩

/-- The head sigma-fields generate everything. -/
theorem le_iSup_headSigma :
    (inferInstance : MeasurableSpace (BilateralField d))
      ≤ ⨆ k : ℕ, headSigma (d := d) k := by
  have hpi : (inferInstance : MeasurableSpace (BilateralField d))
      = ⨆ i : ℤ, (inferInstance :
        MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
          (fun x : BilateralField d => x i) := rfl
  rw [hpi]
  refine iSup_le fun i => ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, i ∈ headIndices k := by
    refine ⟨(-i).toNat, ?_⟩
    simp only [headIndices, tailIndices, Set.mem_compl_iff, Set.mem_setOf_eq]
    omega
  refine le_trans ?_ (le_iSup (fun k : ℕ => headSigma (d := d) k) k)
  rw [headSigma, comap_restrict_eq_iSup]
  exact le_iSup₂ (f := fun i (_ : i ∈ headIndices k) =>
    (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
      (fun x : BilateralField d => x i)) i hk

/-- The layer filtration. -/
def layerFiltration : Filtration ℕ (inferInstance : MeasurableSpace (BilateralField d)) :=
  ⟨headSigma, monotone_headSigma, headSigma_le⟩

/-- Head and tail blocks are independent. -/
theorem indep_tailSigma_headSigma (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) :
    Indep (tailSigma (d := d) k) (headSigma (d := d) k)
      (chaosSampleLaw M).toMeasure := by
  have hmeasure : (chaosSampleLaw M).toMeasure
      = Measure.infinitePi (fun j : ℤ =>
        (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure) := rfl
  have hdisj : Disjoint (tailIndices (k + 1)) (headIndices k) :=
    disjoint_compl_right
  have hbase := indepFun_restrict_infinitePi
    (fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure)
    (tailIndices (k + 1)) (headIndices k) hdisj
  rw [IndepFun_iff_Indep] at hbase
  rw [hmeasure]
  exact hbase

end SubdiffusiveProcess
