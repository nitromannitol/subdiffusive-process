import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalDirichletCarrier
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PositiveFractionalDatum
import Homogenization.Book.Ch03.ABK26.FinitePToLegacyQTwo




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section



theorem memCubeEuclideanFullWsp_centeredCubeScaledVectorDilation
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    ABK26.MemCubeEuclideanFullWsp (originCube d m) s
      FiniteLpExponent.two
      (centeredCubeScaledVectorDilation alpha m F).toField := by
  let G := centeredCubeScaledVectorDilationWspField alpha m s F
  exact ⟨G.euclideanMemLp, G.euclideanMemWsp⟩

/-- At every strictly lower order, the negative physical forcing has exactly
the regularity stored by the public Chapter 3 Dirichlet solution. -/
theorem forceBesovRegularity_neg_centeredCubeScaledVectorDilation_of_lt
    {d : ℕ} [NeZero d] (alpha : ℝ) (m : ℤ)
    (s s2 : FractionalOrder) (hss2 : s.1 < s2.1)
    (F : CubeVectorH1Function (originCube d 0)) :
    ForceBesovRegularity (originCube d m) s.1
      (fun x ↦ -(centeredCubeScaledVectorDilation alpha m F).toField x) := by
  exact (memCubeEuclideanFullWsp_centeredCubeScaledVectorDilation
    alpha m s2 F).toCubeVectorBesovHRegularity_neg_of_lt (by norm_num) hss2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
