module

public import SubdiffusiveProcess.EllipticRegularity.HolderSobolevBridge

@[expose] public section

/-! The native vector supremum and half Holder norm agree with the translated cube norms.
These are carrier identities, with no PDE estimate. -/
open _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
namespace SubdiffusiveProcess

/-- Translation of a cube preserves the vector supremum norm. -/
theorem vectorSupNormOn_cube_translate (d m : ℕ) (z : SpatialCoordinates d)
    (hR : (0:ℝ) < 3^m) (g : SpatialCoordinates d → Fin d → ℝ) :
    vectorSupNormOn (cube d m) (fun x => g (x+z)) =
      sSup {v : ℝ | ∃ x ∈ (centeredCube z ((3:ℝ)^m) hR : Set (SpatialCoordinates d)),
        v = Real.sqrt (∑ i : Fin d,(g x i)^2)} := by
  unfold vectorSupNormOn
  congr 1
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x+z,(mem_cube_iff_add_mem_centeredCube m z hR x).mp hx,
      euclideanNorm_eq_sqrt_sum_sq _⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x-z,?_,?_⟩
    · rw [mem_cube_iff_add_mem_centeredCube m z hR,sub_add_cancel]
      exact hx
    · change Real.sqrt (∑ i : Fin d,(g x i)^2) = euclideanNorm (g (x-z+z))
      rw [sub_add_cancel,euclideanNorm_eq_sqrt_sum_sq]

/-- The translated native supremum plus half-scale seminorm is the physical half Holder norm. -/
theorem halfHolderNorm_cube_translate (d m : ℕ) (z : SpatialCoordinates d)
    (hR : (0:ℝ) < 3^m) (g : SpatialCoordinates d → Fin d → ℝ) :
    vectorSupNormOn (cube d m) (fun x => g (x+z)) +
      (3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) (fun x => g (x+z)) =
      halfHolderNorm ((3:ℝ)^m) (centeredCube z ((3:ℝ)^m) hR : Set (SpatialCoordinates d)) g := by
  rw [vectorSupNormOn_cube_translate d m z hR g,folded_source_holderSeminormOn_eq m z hR g]
  unfold halfHolderNorm
  congr 2
  rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  congr 1
  ring

end SubdiffusiveProcess
