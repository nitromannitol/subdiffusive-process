module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeshGluing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.SimplexMesh
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SimplexGapStrict

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory Set
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The deterministic display -/



theorem exists_triadicSubMesh_vecDot_aMatrix_le {A B : Vec d → ℝ}
    (U : KuhnCell d) (R : ℕ) (hA : Continuous A) (hA0 : ∀ x, 0 ≤ A x)
    (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d)
    (hBA : ScalarCoeffOnData (kuhnCellDomain U) (fun x => B x * A x))
    (hAV : ∀ T : KuhnCell d, ScalarCoeffOnData (kuhnCellDomain T) A) :
    ∃ S : Finset (KuhnCell d),
      (∀ T ∈ S, T.supportCube.scale = U.supportCube.scale - (R : ℤ)) ∧
      (∀ T ∈ S, T.openCarrier ⊆ U.openCarrier) ∧
      ∀ c : KuhnCompetitor U.openCarrier S,
        vecDot p (matVecMul (aMatrix (kuhnCellDomain U) hBA.toCoeffOn) p) ≤
          ∑ T ∈ S, (volume T.openCarrier).toReal / (volume U.openCarrier).toReal *
            (cellSup B T *
              vecDot (p + c.slope T)
                (matVecMul (aMatrix (kuhnCellDomain T) (hAV T).toCoeffOn)
                  (p + c.slope T))) := by
  obtain ⟨S, hscale, hsub, hcover⟩ := exists_triadicSubMesh U R
  refine ⟨S, hscale, hsub, fun c => ?_⟩
  exact vecDot_aMatrix_le_sum_cellSup_vecDot_aMatrix
    (A := A) (B := B) (S := S) (s := U.supportCube.scale - (R : ℤ)) (p := p)
    (U := kuhnCellDomain U) (V := fun T => kuhnCellDomain T)
    hA hA0 hB hB0 hscale (fun _ _ => rfl) hsub hcover c hBA hAV

/-! ## The same display at the GMC layers -/



theorem sparseLayerCoefficient_succ (M : GMCModel d) (R N : ℕ)
    (omega : PotentialSample d) :
    sparseLayerCoefficient M R (N + 1) omega =
      fun x => shellFactor M ((N + 1) * R) omega x *
        sparseLayerCoefficient M R N omega x := by
  funext x
  simp [sparseLayerCoefficient, Finset.prod_range_succ, mul_comm]



theorem exists_triadicSubMesh_vecDot_randomSparseMatrix_le (M : GMCModel d)
    (R N depth : ℕ) (U : KuhnCell d) (p : Vec d) (omega : PotentialSample d) :
    ∃ S : Finset (KuhnCell d),
      (∀ T ∈ S, T.supportCube.scale = U.supportCube.scale - (depth : ℤ)) ∧
      (∀ T ∈ S, T.openCarrier ⊆ U.openCarrier) ∧
      ∀ c : KuhnCompetitor U.openCarrier S,
        vecDot p (matVecMul (randomSparseMatrix M R (N + 1) (kuhnCellDomain U) omega) p) ≤
          ∑ T ∈ S, (volume T.openCarrier).toReal / (volume U.openCarrier).toReal *
            (cellSup (shellFactor M ((N + 1) * R) omega) T *
              vecDot (p + c.slope T)
                (matVecMul (randomSparseMatrix M R N (kuhnCellDomain T) omega)
                  (p + c.slope T))) := by
  set B : Vec d → ℝ := shellFactor M ((N + 1) * R) omega with hBdef
  set A : Vec d → ℝ := sparseLayerCoefficient M R N omega with hAdef
  have hA : Continuous A := continuous_sparseLayerCoefficient M R N omega
  have hA0 : ∀ x, 0 ≤ A x := fun x => (sparseLayerCoefficient_pos M R N omega x).le
  have hB : Continuous B := continuous_shellFactor M ((N + 1) * R) omega
  have hB0 : ∀ x, 0 ≤ B x := fun _ => (Real.exp_pos _).le
  have hprod : Continuous fun x => B x * A x := hB.mul hA
  have hprodpos : ∀ x, 0 < B x * A x := fun x =>
    mul_pos (Real.exp_pos _) (sparseLayerCoefficient_pos M R N omega x)
  set hBA : ScalarCoeffOnData (kuhnCellDomain U) (fun x => B x * A x) :=
    scalarCoeffOnDataOfContinuousPos hprod hprodpos (kuhnCellDomain U) with hBAdef
  set hAV : ∀ T : KuhnCell d, ScalarCoeffOnData (kuhnCellDomain T) A :=
    fun T => sparseLayerCoeffOnData M R N omega (kuhnCellDomain T) with hAVdef
  obtain ⟨S, hscale, hsub, hmain⟩ :=
    exists_triadicSubMesh_vecDot_aMatrix_le (A := A) (B := B) U depth hA hA0 hB hB0 p
      hBA hAV
  refine ⟨S, hscale, hsub, fun c => ?_⟩
  have hlhs :
      vecDot p (matVecMul (randomSparseMatrix M R (N + 1) (kuhnCellDomain U) omega) p) =
        vecDot p (matVecMul (aMatrix (kuhnCellDomain U) hBA.toCoeffOn) p) := by
    rw [randomSparseMatrix,
      vecDot_aMatrix_eq_dirichletInfOn (sparseLayerCoeffOnData M R (N + 1) omega
        (kuhnCellDomain U))
        (fun x => (sparseLayerCoefficient_pos M R (N + 1) omega x).le) p,
      vecDot_aMatrix_eq_dirichletInfOn hBA (fun x => (hprodpos x).le) p,
      sparseLayerCoefficient_succ M R N omega]
  rw [hlhs]
  exact hmain c

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
