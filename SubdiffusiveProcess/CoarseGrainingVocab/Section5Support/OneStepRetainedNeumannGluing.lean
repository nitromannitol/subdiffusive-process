module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLocalizedFiniteSplit

@[expose] public section




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A finite sum of zero-extended residuals over an arbitrary retained
subfamily of descendants. -/
def oneStepRetainedNeumannResidual {d : ℕ} (s : Finset (TriadicCube d))
    (residual : TriadicCube d → Vec d → Vec d) : Vec d → Vec d :=
  fun x ↦ ∑ R ∈ s, (openCubeSet R).indicator (residual R) x

/-- Open region covered by the retained cells. -/
def oneStepRetainedOpenSet {d : ℕ} (s : Finset (TriadicCube d)) :
    Set (Vec d) :=
  ⋃ R ∈ (s : Set (TriadicCube d)), openCubeSet R

theorem measurableSet_oneStepRetainedOpenSet {d : ℕ}
    (s : Finset (TriadicCube d)) :
    MeasurableSet (oneStepRetainedOpenSet s) := by
  exact Finset.measurableSet_biUnion s fun R _hR ↦
    measurableSet_openCubeSet R

theorem oneStepRetainedOpenSet_subset_openCubeSet {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {s : Finset (TriadicCube d)}
    (hs : s ⊆ descendantsAtDepth Q j) :
    oneStepRetainedOpenSet s ⊆ openCubeSet Q := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨R, hxR⟩
  rcases Set.mem_iUnion.mp hxR with ⟨hR, hxR⟩
  exact openCubeSet_subset_of_mem_descendantsAtDepth (hs (by simpa using hR)) hxR

/-- The integral over the retained region is the literal finite sum of the
cell integrals.  Pairwise disjointness comes from the ambient descendant
partition. -/
theorem integral_oneStepRetainedOpenSet_eq_sum {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {s : Finset (TriadicCube d)}
    (hs : s ⊆ descendantsAtDepth Q j) (f : Vec d → ℝ)
    (hf : IntegrableOn f (openCubeSet Q)) :
    ∫ x in oneStepRetainedOpenSet s, f x ∂volume =
      ∑ R ∈ s, ∫ x in openCubeSet R, f x ∂volume := by
  unfold oneStepRetainedOpenSet
  apply integral_biUnion_finset
  · intro R _hR
    exact measurableSet_openCubeSet R
  · intro R hR S hS hRS
    exact pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j
      (hs (by simpa using hR)) (hs (by simpa using hS)) hRS
  · intro R hR
    exact hf.mono_set
      (openCubeSet_subset_of_mem_descendantsAtDepth (hs hR))

/-- Exact retained-interior plus boundary-complement split of any integrable
parent-domain energy density. -/
theorem integral_openCubeSet_eq_retained_add_complement {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {s : Finset (TriadicCube d)}
    (hs : s ⊆ descendantsAtDepth Q j) (f : Vec d → ℝ)
    (hf : IntegrableOn f (openCubeSet Q)) :
    ∫ x in openCubeSet Q, f x ∂volume =
      (∫ x in oneStepRetainedOpenSet s, f x ∂volume) +
        ∫ x in openCubeSet Q \ oneStepRetainedOpenSet s, f x ∂volume := by
  have hdiff := integral_diff
    (measurableSet_oneStepRetainedOpenSet s) hf
    (oneStepRetainedOpenSet_subset_openCubeSet hs)
  linarith

/-- `volumeAverage` form of the exact retained-interior/boundary split. -/
theorem volumeAverage_openCubeSet_eq_retained_add_complement {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {s : Finset (TriadicCube d)}
    (hs : s ⊆ descendantsAtDepth Q j) (f : Vec d → ℝ)
    (hf : IntegrableOn f (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) f =
      (cubeVolume Q)⁻¹ *
          ∫ x in oneStepRetainedOpenSet s, f x ∂volume +
        (cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q \ oneStepRetainedOpenSet s, f x ∂volume := by
  rw [volumeAverage, volume_openCubeSet_toReal,
    integral_openCubeSet_eq_retained_add_complement hs f hf]
  ring

/-- The parent-normalized retained integral is bounded by the normalized
average of its cellwise volume averages.  The missing volume fraction is at
most one because the retained family is a subfamily of the full descendant
partition. -/
theorem inv_cubeVolume_mul_integral_retained_le_normalized_cellAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    {s : Finset (TriadicCube d)} (hs : s ⊆ descendantsAtDepth Q j)
    (hsne : s.Nonempty) (f : Vec d → ℝ)
    (hf : IntegrableOn f (openCubeSet Q))
    (hf0 : ∀ R ∈ s, 0 ≤ volumeAverage (openCubeSet R) f) :
    (cubeVolume Q)⁻¹ *
        ∫ x in oneStepRetainedOpenSet s, f x ∂volume ≤
      ((s.card : ℝ)⁻¹) *
        ∑ R ∈ s, volumeAverage (openCubeSet R) f := by
  classical
  obtain ⟨R0, hR0⟩ := hsne
  have hR0full : R0 ∈ descendantsAtDepth Q j := hs hR0
  have hvolR0 : 0 < cubeVolume R0 := cubeVolume_pos R0
  have hcardS : 0 < (s.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨R0, hR0⟩)
  have hcardD : 0 < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j))
  have hcardLe : s.card ≤ (descendantsAtDepth Q j).card :=
    Finset.card_le_card hs
  have hcellVolume : ∀ R ∈ s, cubeVolume R = cubeVolume R0 := by
    intro R hR
    exact cubeVolume_eq_of_mem_descendantsAtDepth (hs hR) hR0full
  have hintegralCell : ∀ R ∈ s,
      ∫ x in openCubeSet R, f x ∂volume =
        cubeVolume R * volumeAverage (openCubeSet R) f := by
    intro R hR
    unfold volumeAverage
    rw [volume_openCubeSet_toReal]
    have hvolR : 0 < cubeVolume R := cubeVolume_pos R
    field_simp
  have hsum0 : 0 ≤ ∑ R ∈ s, volumeAverage (openCubeSet R) f := by
    exact Finset.sum_nonneg fun R hR ↦ hf0 R hR
  have hcoef : (cubeVolume Q)⁻¹ * cubeVolume R0 ≤ (s.card : ℝ)⁻¹ := by
    have hvolPartition :=
      cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR0full
    rw [hvolPartition]
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ hvolR0.ne', mul_one]
    exact (inv_le_inv₀ hcardD hcardS).2 (by exact_mod_cast hcardLe)
  rw [integral_oneStepRetainedOpenSet_eq_sum hs f hf]
  have hsum :
      ∑ R ∈ s, ∫ x in openCubeSet R, f x ∂volume =
        cubeVolume R0 * ∑ R ∈ s, volumeAverage (openCubeSet R) f := by
    calc
      _ = ∑ R ∈ s,
          cubeVolume R * volumeAverage (openCubeSet R) f := by
            apply Finset.sum_congr rfl
            intro R hR
            exact hintegralCell R hR
      _ = ∑ R ∈ s,
          cubeVolume R0 * volumeAverage (openCubeSet R) f := by
            apply Finset.sum_congr rfl
            intro R hR
            rw [hcellVolume R hR]
      _ = cubeVolume R0 *
          ∑ R ∈ s, volumeAverage (openCubeSet R) f :=
            (Finset.mul_sum _ _ _).symm
  rw [hsum, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hcoef hsum0

/-- Retaining only a subfamily of descendants preserves vector `L²`
membership on the parent cube. -/
theorem oneStepRetainedNeumannResidual_memVectorL2 {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (s : Finset (TriadicCube d))
    (residual : TriadicCube d → Vec d → Vec d)
    (hs : s ⊆ descendantsAtDepth Q j)
    (hL2 : ∀ R ∈ s, MemVectorL2 (openCubeSet R) (residual R)) :
    MemVectorL2 (openCubeSet Q)
      (oneStepRetainedNeumannResidual s residual) := by
  unfold oneStepRetainedNeumannResidual
  apply oneStep_memVectorL2_finsetSum
  intro R hR
  exact oneStep_memVectorL2_indicator_of_subset
    (measurableSet_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth (hs hR)) (hL2 R hR)

/-- Retaining only a subfamily of descendant residuals preserves the
zero-normal-trace constraint on the parent cube. -/
theorem oneStepRetainedNeumannResidual_zeroNormalTrace {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (s : Finset (TriadicCube d))
    (residual : TriadicCube d → Vec d → Vec d)
    (hs : s ⊆ descendantsAtDepth Q j)
    (hL2 : ∀ R ∈ s, MemVectorL2 (openCubeSet R) (residual R))
    (hSol : ∀ R ∈ s,
      IsSolenoidalZeroNormalTraceOn (openCubeSet R) (residual R)) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (oneStepRetainedNeumannResidual s residual) := by
  unfold oneStepRetainedNeumannResidual
  apply oneStep_isSolenoidalZeroNormalTraceOn_finsetSum
  · intro R hR
    exact oneStep_memVectorL2_indicator_of_subset
      (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth (hs hR)) (hL2 R hR)
  · intro R hR
    exact oneStep_isSolenoidalZeroNormalTraceOn_indicator_of_subset
      (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth (hs hR)) (hSol R hR)

/-- At a point in one retained cell, the retained residual sum is exactly
that cell's residual. -/
theorem oneStepRetainedNeumannResidual_eq_of_mem {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} {s : Finset (TriadicCube d)}
    (residual : TriadicCube d → Vec d → Vec d)
    (hs : s ⊆ descendantsAtDepth Q j) (hR : R ∈ s)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    oneStepRetainedNeumannResidual s residual x = residual R x := by
  classical
  unfold oneStepRetainedNeumannResidual
  rw [Finset.sum_eq_single R]
  · exact Set.indicator_of_mem hx _
  · intro S hS hSR
    refine Set.indicator_of_notMem (fun hxS ↦ ?_) _
    exact Set.disjoint_left.mp
      (pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j
        (hs hS) (hs hR) hSR) hxS hx
  · intro h
    exact (h hR).elim

/-- Away from every retained cell, the retained residual sum vanishes. -/
theorem oneStepRetainedNeumannResidual_eq_zero_of_not_mem {d : ℕ}
    {s : Finset (TriadicCube d)}
    (residual : TriadicCube d → Vec d → Vec d) {x : Vec d}
    (hx : ∀ R ∈ s, x ∉ openCubeSet R) :
    oneStepRetainedNeumannResidual s residual x = 0 := by
  classical
  unfold oneStepRetainedNeumannResidual
  apply Finset.sum_eq_zero
  intro R hR
  simp only [Set.indicator_of_notMem (hx R hR)]

/-- The two selected Neumann residual families, glued only over the retained
descendants and added to the ambient background flux. -/
def oneStepSelectedRetainedGluedNeumannTwoFlux {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (s : Finset (TriadicCube d))
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    (background : Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R)) : Vec d → Vec d :=
  background +
    oneStepRetainedNeumannResidual s
      (oneStepSelectedNeumannResidualFamily a P hEll hP) +
    oneStepRetainedNeumannResidual s
      (oneStepSelectedNeumannResidualFamily a F hEll hF)

theorem oneStepSelectedRetainedGluedNeumannTwoFlux_memVectorL2 {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (s : Finset (TriadicCube d))
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    (background : Vec d → Vec d) {lam Lam : ℝ}
    (hs : s ⊆ descendantsAtDepth Q j)
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R))
    (hBackground : MemVectorL2 (openCubeSet Q) background) :
    MemVectorL2 (openCubeSet Q)
      (oneStepSelectedRetainedGluedNeumannTwoFlux
        Q j s a P F background hEll hP hF) := by
  refine (hBackground.add ?_).add ?_
  · apply oneStepRetainedNeumannResidual_memVectorL2 Q j s _ hs
    intro R hR
    rw [oneStepSelectedNeumannResidualFamily_eq a P hEll hP (hs hR)]
    exact (oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux_memVectorL2
      (hEll R (hs hR)) |>.sub (hP R (hs hR))
  · apply oneStepRetainedNeumannResidual_memVectorL2 Q j s _ hs
    intro R hR
    rw [oneStepSelectedNeumannResidualFamily_eq a F hEll hF (hs hR)]
    exact (oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux_memVectorL2
      (hEll R (hs hR)) |>.sub (hF R (hs hR))

/-- The retained two-family glue stays in the affine zero-normal-trace class
prescribed by the ambient background flux. -/
theorem oneStepSelectedRetainedGluedNeumannTwoFlux_sub_const_zeroNormalTrace
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (s : Finset (TriadicCube d))
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    (background : Vec d → Vec d) (q : Vec d) {lam Lam : ℝ}
    (hs : s ⊆ descendantsAtDepth Q j)
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R))
    (hBackgroundL2 : MemVectorL2 (openCubeSet Q) background)
    (hBackground : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x ↦ background x - q)) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x ↦ oneStepSelectedRetainedGluedNeumannTwoFlux
        Q j s a P F background hEll hP hF x - q) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let pResidual := oneStepRetainedNeumannResidual s
    (oneStepSelectedNeumannResidualFamily a P hEll hP)
  let fResidual := oneStepRetainedNeumannResidual s
    (oneStepSelectedNeumannResidualFamily a F hEll hF)
  have hbaseL2 : MemVectorL2 (openCubeSet Q) (fun x ↦ background x - q) :=
    hBackgroundL2.sub (MeasureTheory.memLp_const q)
  have hpL2 : MemVectorL2 (openCubeSet Q) pResidual := by
    apply oneStepRetainedNeumannResidual_memVectorL2 Q j s _ hs
    intro R hR
    rw [oneStepSelectedNeumannResidualFamily_eq a P hEll hP (hs hR)]
    exact (oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux_memVectorL2
      (hEll R (hs hR)) |>.sub (hP R (hs hR))
  have hfL2 : MemVectorL2 (openCubeSet Q) fResidual := by
    apply oneStepRetainedNeumannResidual_memVectorL2 Q j s _ hs
    intro R hR
    rw [oneStepSelectedNeumannResidualFamily_eq a F hEll hF (hs hR)]
    exact (oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux_memVectorL2
      (hEll R (hs hR)) |>.sub (hF R (hs hR))
  have hpSol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) pResidual := by
    apply oneStepRetainedNeumannResidual_zeroNormalTrace Q j s _ hs
    · intro R hR
      rw [oneStepSelectedNeumannResidualFamily_eq a P hEll hP (hs hR)]
      exact (oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux_memVectorL2
        (hEll R (hs hR)) |>.sub (hP R (hs hR))
    · intro R hR
      rw [oneStepSelectedNeumannResidualFamily_eq a P hEll hP (hs hR)]
      exact (oneStepSelectedNeumannCell a P hEll hP R (hs hR)).residual_zeroNormalTrace
        (hEll R (hs hR)) (hP R (hs hR))
  have hfSol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) fResidual := by
    apply oneStepRetainedNeumannResidual_zeroNormalTrace Q j s _ hs
    · intro R hR
      rw [oneStepSelectedNeumannResidualFamily_eq a F hEll hF (hs hR)]
      exact (oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux_memVectorL2
        (hEll R (hs hR)) |>.sub (hF R (hs hR))
    · intro R hR
      rw [oneStepSelectedNeumannResidualFamily_eq a F hEll hF (hs hR)]
      exact (oneStepSelectedNeumannCell a F hEll hF R (hs hR)).residual_zeroNormalTrace
        (hEll R (hs hR)) (hF R (hs hR))
  have hfirst := isSolenoidalZeroNormalTraceOn_add_of_memVectorL2
    hbaseL2 hpL2 hBackground hpSol
  have htotal := isSolenoidalZeroNormalTraceOn_add_of_memVectorL2
    (hbaseL2.add hpL2) hfL2 hfirst hfSol
  convert htotal using 1
  funext x
  simp only [oneStepSelectedRetainedGluedNeumannTwoFlux, Pi.add_apply]
  abel

/-- On a retained descendant the glued flux is exactly the sum of the two
selected cell minimizer fluxes. -/
theorem oneStepSelectedRetainedGluedNeumannTwoFlux_eq_of_mem {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} {s : Finset (TriadicCube d)}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    (background : Vec d → Vec d) {lam Lam : ℝ}
    (hs : s ⊆ descendantsAtDepth Q j)
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ s) {x : Vec d} (hx : x ∈ openCubeSet R)
    (hbackground : background x = P R x + F R x) :
    oneStepSelectedRetainedGluedNeumannTwoFlux
      Q j s a P F background hEll hP hF x =
      (oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux x +
      (oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux x := by
  change background x +
      oneStepRetainedNeumannResidual s
        (oneStepSelectedNeumannResidualFamily a P hEll hP) x +
      oneStepRetainedNeumannResidual s
        (oneStepSelectedNeumannResidualFamily a F hEll hF) x = _
  rw [
    oneStepRetainedNeumannResidual_eq_of_mem
      (residual := oneStepSelectedNeumannResidualFamily a P hEll hP) hs hR hx,
    oneStepSelectedNeumannResidualFamily_eq a P hEll hP (hs hR),
    oneStepRetainedNeumannResidual_eq_of_mem
      (residual := oneStepSelectedNeumannResidualFamily a F hEll hF) hs hR hx,
    oneStepSelectedNeumannResidualFamily_eq a F hEll hF (hs hR),
    hbackground]
  unfold OneStepNeumannCellMinimizer.residual
  abel

/-- On a retained cell, the glued inverse energy has exactly the manuscript's
half-principal plus mixed plus half-oscillatory decomposition. -/
theorem oneStepSelectedRetainedGluedNeumannTwoFlux_half_energy_eq_of_mem
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    {s : Finset (TriadicCube d)}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    (background : Vec d → Vec d) {lam Lam : ℝ}
    (hs : s ⊆ descendantsAtDepth Q j)
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ s) {x : Vec d} (hx : x ∈ openCubeSet R)
    (hbackground : background x = P R x + F R x) :
    let principal := oneStepSelectedNeumannCell a P hEll hP R (hs hR)
    let oscillatory := oneStepSelectedNeumannCell a F hEll hF R (hs hR)
    let Ainv := (blockMatrixOfCoeff (a x)).lowerRight
    let glued := oneStepSelectedRetainedGluedNeumannTwoFlux
      Q j s a P F background hEll hP hF x
    (1 / 2 : ℝ) * vecDot glued (matVecMul Ainv glued) =
      (1 / 2 : ℝ) * vecDot (principal.flux x)
          (matVecMul Ainv (principal.flux x)) +
        vecDot (principal.flux x)
          (matVecMul Ainv (oscillatory.flux x)) +
        (1 / 2 : ℝ) * vecDot (oscillatory.flux x)
          (matVecMul Ainv (oscillatory.flux x)) := by
  rw [oneStepSelectedRetainedGluedNeumannTwoFlux_eq_of_mem
    a P F background hs hEll hP hF hR hx hbackground]
  exact oneStepSelectedNeumannTwoCell_half_energy_eq
    a P F hEll hP hF (hs hR) x

/-- Outside the retained cells the glued competitor is exactly the ambient
background flux, which is the boundary-layer term in the manuscript. -/
theorem oneStepSelectedRetainedGluedNeumannTwoFlux_eq_background_of_not_mem
    {d : ℕ} {Q : TriadicCube d} {j : ℕ} {s : Finset (TriadicCube d)}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    (background : Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    {x : Vec d} (hx : ∀ R ∈ s, x ∉ openCubeSet R) :
    oneStepSelectedRetainedGluedNeumannTwoFlux
      Q j s a P F background hEll hP hF x = background x := by
  change background x +
      oneStepRetainedNeumannResidual s
        (oneStepSelectedNeumannResidualFamily a P hEll hP) x +
      oneStepRetainedNeumannResidual s
        (oneStepSelectedNeumannResidualFamily a F hEll hF) x = background x
  rw [oneStepRetainedNeumannResidual_eq_zero_of_not_mem _ hx,
    oneStepRetainedNeumannResidual_eq_zero_of_not_mem _ hx]
  simp

/-- Insert the retained-cell two-family flux into the parent starred
variational problem.  This is the deterministic boundary-discard carrier:
the background field remains untouched outside the retained cells. -/
theorem vecDot_sigmaStarInvCoarse_le_selectedRetainedGluedNeumannTwoFluxEnergy
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (s : Finset (TriadicCube d))
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    (background : Vec d → Vec d) (q : Vec d) {lam Lam : ℝ}
    (hs : s ⊆ descendantsAtDepth Q j)
    (hEllParent : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R))
    (hBackgroundL2 : MemVectorL2 (openCubeSet Q) background)
    (hBackground : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x ↦ background x - q))
    (hex : ∃ Abar : BlockMat d,
      IsCoarseBlockMatrix (openCubeSet Q) a Abar)
    (hMuResp : ∀ r : Vec d,
      Mu (openCubeSet Q) (0, r) a = ResponseJ (openCubeSet Q) 0 r a) :
    vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q) ≤
      volumeAverage (openCubeSet Q) (fun x ↦
        let flux := oneStepSelectedRetainedGluedNeumannTwoFlux
          Q j s a P F background hEll hP hF x
        vecDot flux
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) flux)) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hvol : (volume (openCubeSet Q)).toReal ≠ 0 := by
    simpa [volume_openCubeSet_toReal] using (cubeVolume_pos Q).ne'
  apply vecDot_sigmaStarInvCoarse_le_volumeAverage_lowerRight_energy
    (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain
    hEllParent hex hvol hMuResp
  · exact oneStepSelectedRetainedGluedNeumannTwoFlux_memVectorL2
      Q j s a P F background hs hEll hP hF hBackgroundL2
  · exact oneStepSelectedRetainedGluedNeumannTwoFlux_sub_const_zeroNormalTrace
      Q j s a P F background q hs hEll hP hF hBackgroundL2 hBackground

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
