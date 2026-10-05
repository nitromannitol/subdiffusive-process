module

public import SubdiffusiveProcess.Frozen.Section2.CoarseGrainedPoincare

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem p_coarse_grained_poincare {d : ℕ}
    (hd : 2 ≤ d)
    (a : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 →
      ∀ q : Ch02.MultiscaleExponent, q.IsAdmissible →
        ∀ m : ℤ,
          ∀ u : Homogenization.H1Function
              (Homogenization.openCubeSet (Homogenization.originCube d m)),
            ∀ h : Vec d → Vec d,
              Homogenization.MemVectorL2
                (Homogenization.openCubeSet (Homogenization.originCube d m)) h →
              Homogenization.IsSolenoidalOn
                (Homogenization.openCubeSet (Homogenization.originCube d m)) h →
              paperScaleNormalizedNegativeBesovVectorNorm
                    (Homogenization.originCube d m) s q u.grad ≤
                  paperPoincareGeometricFactor s q *
                    Real.rpow (lambda (Homogenization.originCube d m) s q a) (-1 / 2) *
                      coefficientEnergyNorm (Homogenization.originCube d m) a u.grad ∧
                paperScaleNormalizedNegativeBesovVectorNorm
                    (Homogenization.originCube d m) s q h ≤
                  paperPoincareGeometricFactor s q *
                    Real.rpow (Lambda (Homogenization.originCube d m) s q a) (1 / 2) *
                      inverseCoefficientEnergyNorm
                        (Homogenization.originCube d m) a h :=
  SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare hd a haSymm

end SubdiffusiveProcess.Paper
