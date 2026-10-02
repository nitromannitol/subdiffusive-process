import SubdiffusiveProcess.Section10.RetainedPrefixConsumer




namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (aMatrix)
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

variable {d : ℕ}

/-- The actual normalized continuum energy of the retained-prefix field. -/
def retainedPrefixEnergy (M : GMCModel d) (ell R N : ℕ) (T : KuhnCell d)
    (omega : PotentialSample d) (p : Vec d) : ℝ :=
  (volume T.openCarrier).toReal⁻¹ *
    dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p

/-- The induction bound on all translated/permuted cells at the retained scale. -/
def RetainedPrefixSparseBound (M : GMCModel d) (ell R N : ℕ) (kap : ℝ) : Prop :=
  ∀ (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) (p : Vec d),
    ∫ omega, retainedPrefixEnergy M ell R N (dilatedCell (ell + N * R) c pi)
      omega p ∂M.P.toMeasure ≤ kap * vecNormSq p

theorem retainedPrefixEnergy_smul (M : GMCModel d) (ell R N : ℕ) (T : KuhnCell d)
    (omega : PotentialSample d) (t : ℝ) (p : Vec d) :
    retainedPrefixEnergy M ell R N T omega (t • p) =
      t ^ 2 * retainedPrefixEnergy M ell R N T omega p := by
  let ha := scalarCoeffOnDataOfContinuousPos
    (continuous_retainedPrefixCoefficient M ell R N omega)
    (retainedPrefixCoefficient_pos M ell R N omega) (kuhnCellDomain T)
  have hid (q : Vec d) :
      vecDot q (matVecMul (aMatrix (kuhnCellDomain T) ha.toCoeffOn) q) =
        retainedPrefixEnergy M ell R N T omega q :=
    vecDot_aMatrix_eq_dirichletInfOn ha
      (fun x => (retainedPrefixCoefficient_pos M ell R N omega x).le) q
  rw [← hid, vecDot_matVecMul_smul, hid]

theorem integrable_retainedPrefixEnergy (M : GMCModel d) (ell R N : ℕ)
    (T : KuhnCell d) (p : Vec d) :
    Integrable (fun omega => retainedPrefixEnergy M ell R N T omega p) M.P.toMeasure :=
  (integrable_retainedPrefix_dirichletInfOn M ell R N T p).const_mul _

/-- Generic MeshGluing applied to the actual successor factorization on a
sample-independent transported mesh. No new minimizer or geometry is needed. -/
theorem retainedPrefixEnergy_succ_le (M : GMCModel d) (ell : ℕ) {R : ℕ}
    (hR : 0 < R) (N : ℕ) (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d))
    (p : Vec d) (omega : PotentialSample d)
    (comp : KuhnCompetitor (dilatedCell (ell + (N + 1) * R) c pi).openCarrier
      (dilatedSubMesh (ell + (N + 1) * R) R c pi)) :
    retainedPrefixEnergy M ell R (N + 1) (dilatedCell (ell + (N + 1) * R) c pi)
        omega p ≤
      ∑ T ∈ dilatedSubMesh (ell + (N + 1) * R) R c pi,
        (volume T.openCarrier).toReal /
            (volume (dilatedCell (ell + (N + 1) * R) c pi).openCarrier).toReal *
          (cellSup (shellFactor M (ell + (N + 1) * R) omega) T *
            retainedPrefixEnergy M ell R N T omega (p + comp.slope T)) := by
  let k := ell + (N + 1) * R
  let A := retainedPrefixCoefficient M ell R N omega
  let B := shellFactor M k omega
  have hA : Continuous A := continuous_retainedPrefixCoefficient M ell R N omega
  have hApos : ∀ x, 0 < A x := retainedPrefixCoefficient_pos M ell R N omega
  have hB : Continuous B := continuous_shellFactor M k omega
  have hBpos : ∀ x, 0 < B x := shellFactor_pos M k omega
  let hBA := scalarCoeffOnDataOfContinuousPos (hB.mul hA)
    (fun x => mul_pos (hBpos x) (hApos x)) (kuhnCellDomain (dilatedCell k c pi))
  let hAV := fun T : KuhnCell d =>
    scalarCoeffOnDataOfContinuousPos hA hApos (kuhnCellDomain T)
  have hmain := vecDot_aMatrix_le_sum_cellSup_vecDot_aMatrix
    (A := A) (B := B) (S := dilatedSubMesh k R c pi) (s := (k : ℤ) - (R : ℤ))
    (p := p) (U := kuhnCellDomain (dilatedCell k c pi))
    (V := fun T => kuhnCellDomain T)
    hA (fun x => (hApos x).le) hB (fun x => (hBpos x).le)
    (fun T hT => scale_of_mem_dilatedSubMesh hT) (fun _ _ => rfl)
    (fun T hT => openCarrier_subset_of_mem_dilatedSubMesh hT)
    (openCarrier_dilatedCell_subset_iUnion k R c pi) comp hBA hAV
  have hleft :
      vecDot p (matVecMul (aMatrix (kuhnCellDomain (dilatedCell k c pi)) hBA.toCoeffOn) p) =
        retainedPrefixEnergy M ell R (N + 1) (dilatedCell k c pi) omega p := by
    rw [vecDot_aMatrix_eq_dirichletInfOn hBA
      (fun x => mul_nonneg (hBpos x).le (hApos x).le) p]
    change (volume (dilatedCell k c pi).openCarrier).toReal⁻¹ *
        dirichletInfOn (fun x => B x * A x) (dilatedCell k c pi).openCarrier p = _
    rw [← retainedPrefixCoefficient_succ M ell hR N omega]
    rfl
  have hright (T : KuhnCell d) (q : Vec d) :
      vecDot q (matVecMul (aMatrix (kuhnCellDomain T) (hAV T).toCoeffOn) q) =
        retainedPrefixEnergy M ell R N T omega q :=
    vecDot_aMatrix_eq_dirichletInfOn (hAV T) (fun x => (hApos x).le) q
  simpa only [hleft, hright] using hmain

end

end SubdiffusiveProcess.Section10
