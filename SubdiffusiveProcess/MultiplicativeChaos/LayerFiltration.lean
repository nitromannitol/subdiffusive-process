module

public import SubdiffusiveProcess.MultiplicativeChaos.TailFunctional
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import SubdiffusiveProcess.Main.ChaosSampleLaw

@[expose] public section

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
  simp only [headIndices, tailIndices, Set.mem_compl_iff, Set.mem_ofPred_eq] at hj ⊢
  omega

/-- The sigma-field of the tail block at stage `k`. -/
@[instance_reducible]
def tailSigma (k : ℕ) : MeasurableSpace (BilateralField d) :=
  MeasurableSpace.comap ((tailIndices (k + 1)).domRestrict)
    (inferInstance : MeasurableSpace ((i : tailIndices (k + 1)) →
      C(SpatialCoordinates d, ℝ)))

/-- The sigma-field of the head block at stage `k`. -/
@[instance_reducible]
def headSigma (k : ℕ) : MeasurableSpace (BilateralField d) :=
  MeasurableSpace.comap ((headIndices k).domRestrict)
    (inferInstance : MeasurableSpace ((i : headIndices k) →
      C(SpatialCoordinates d, ℝ)))

omit [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem tailSigma_le [_instPreserved0 : BorelSpace C(SpatialCoordinates d, ℝ)] (k : ℕ) :
    tailSigma (d := d) k ≤ (inferInstance : MeasurableSpace (BilateralField d)) :=
  (Set.measurable_restrict _).comap_le

omit [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem headSigma_le [_instPreserved0 : BorelSpace C(SpatialCoordinates d, ℝ)] (k : ℕ) :
    headSigma (d := d) k ≤ (inferInstance : MeasurableSpace (BilateralField d)) :=
  (Set.measurable_restrict _).comap_le

omit [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem monotone_headSigma [_instPreserved0 : BorelSpace C(SpatialCoordinates d, ℝ)] : Monotone (headSigma (d := d)) := by
  intro k l hkl
  have hhead (n : ℕ) : headSigma (d := d) n =
      ⨆ i, ⨆ (_ : i ∈ headIndices n),
        MeasurableSpace.comap (fun x : BilateralField d => x i)
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) := by
    simpa only [headSigma] using! comap_restrict_eq_iSup
      (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (headIndices n)
  rw [hhead k, hhead l]
  exact iSup₂_mono' fun i hi => ⟨i, monotone_headIndices hkl hi, le_rfl⟩

omit [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- The head sigma-fields generate everything. -/
theorem le_iSup_headSigma [_instPreserved0 : BorelSpace C(SpatialCoordinates d, ℝ)] :
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
    simp only [headIndices, tailIndices, Set.mem_compl_iff, Set.mem_ofPred_eq]
    omega
  refine le_trans ?_ (le_iSup (fun k : ℕ => headSigma (d := d) k) k)
  have hhead : headSigma (d := d) k =
      ⨆ i, ⨆ (_ : i ∈ headIndices k),
        MeasurableSpace.comap (fun x : BilateralField d => x i)
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) := by
    simpa only [headSigma] using! comap_restrict_eq_iSup
      (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (headIndices k)
  rw [hhead]
  exact le_iSup₂ (f := fun i (_ : i ∈ headIndices k) =>
    (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
      (fun x : BilateralField d => x i)) i hk

/-- The layer filtration. -/
def layerFiltration : Filtration ℕ (inferInstance : MeasurableSpace (BilateralField d)) :=
  ⟨headSigma, monotone_headSigma, headSigma_le⟩

/-- Head and tail blocks are independent. -/
theorem indep_tailSigma_headSigma (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) :
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
