module

public import Homogenization.Book.Ch02.MultiscaleEllipticity

@[expose] public section




open Homogenization
open Homogenization.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Coarse-grained ellipticity constants** `(Λ_{s,q}(Q; a), λ_{s,q}(Q; a))` of the definition
`(e.coarse.grained.ellipticity)`/`(e.coarse.grained.ellipticity.infty)`. -/
def d_coarse_grained_ellipticity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d) : ℝ × ℝ :=
  (Ch02.LambdaSq Q s q a, Ch02.lambdaSq Q s q a)

/-- Finite `q`: `Λ_{s,q} = ((1-3^{-sq}) ∑_{n ≥ 0} 3^{-sqn} max_{z ∈ 3^{m-n}ℤ^d ∩ cu_m} |𝐚(z + cu_{m-n})|^{q/2})^{2/q}` and
`λ_{s,q} = ((1-3^{-sq}) ∑_{n ≥ 0} 3^{-sqn} max_z |𝐚_*^{-1}(z + cu_{m-n})|^{q/2})^{-2/q}`. -/
theorem aux_d_coarse_grained_ellipticity_finite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : Ch02.TriadicCoeffFamily d) :
    d_coarse_grained_ellipticity Q s (.finite q) a =
      (((∑' n : ℕ, ((1 - Real.rpow 3 (-s * q)) * Real.rpow 3 (-s * q * (n : ℝ))) *
          Real.rpow (Ch02.finsetSupReal (descendantsAtScale Q (Q.scale - (n : ℤ)))
            fun R => Ch02.coarseBMatrixNorm R a) (q / 2)) ^ (2 / q)),
       ((∑' n : ℕ, ((1 - Real.rpow 3 (-s * q)) * Real.rpow 3 (-s * q * (n : ℝ))) *
          Real.rpow (Ch02.finsetSupReal (descendantsAtScale Q (Q.scale - (n : ℤ)))
            fun R => Ch02.coarseSigmaStarInvMatrixNorm R a) (q / 2)) ^ (-(2 / q)))) := by
  rfl

/-- `q = ∞`: `Λ_{s,∞} = sup_{n ≥ 0} 3^{-2sn} max_z |𝐚(z + cu_{m-n})|` and
`λ_{s,∞} = (sup_{n ≥ 0} 3^{-2sn} max_z |𝐚_*^{-1}(z + cu_{m-n})|)^{-1}`. -/
theorem aux_d_coarse_grained_ellipticity_infinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : Ch02.TriadicCoeffFamily d) :
    d_coarse_grained_ellipticity Q s .infinity a =
      (sSup {M : ℝ | ∃ n : ℕ, M = Real.rpow 3 (-2 * s * (n : ℝ)) *
          Ch02.finsetSupReal (descendantsAtScale Q (Q.scale - (n : ℤ)))
            fun R => Ch02.coarseBMatrixNorm R a},
       (sSup {M : ℝ | ∃ n : ℕ, M = Real.rpow 3 (-2 * s * (n : ℝ)) *
          Ch02.finsetSupReal (descendantsAtScale Q (Q.scale - (n : ℤ)))
            fun R => Ch02.coarseSigmaStarInvMatrixNorm R a})⁻¹) := by
  rfl

/-- The default exponent: `Λ_s = Λ_{s,1}`, `λ_s = λ_{s,1}`. -/
theorem aux_d_coarse_grained_ellipticity_default {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : Ch02.TriadicCoeffFamily d) :
    d_coarse_grained_ellipticity Q s (.finite 1) a = (Ch02.LambdaS Q s a, Ch02.lambdaS Q s a) := by
  rfl

end SubdiffusiveProcess.Paper
