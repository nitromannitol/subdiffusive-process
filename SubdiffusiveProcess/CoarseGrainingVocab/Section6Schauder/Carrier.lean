import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Windows
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.TaylorCompetitor
import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Support/Dirichlet.lean
-- Adapted from Algsuperdiff/Section4/Support/Dirichlet.lean




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

open MeasureTheory
open Homogenization (euclideanNorm)

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- **The sup-norm Hölder-seminorm bound** `[f]_{C^{0,α}(U)} ≤ K`, written
against the ambient (sup) norm of `Vec d`. -/
def supHolderBoundOn (U : Set (Vec d)) (alpha K : ℝ) (f : Vec d → E) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ alpha

theorem supHolderBoundOn_def {U : Set (Vec d)} {alpha K : ℝ} {f : Vec d → E} :
    supHolderBoundOn U alpha K f ↔
      ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ alpha :=
  Iff.rfl

theorem supHolderBoundOn.mono_set {U V : Set (Vec d)} {alpha K : ℝ} {f : Vec d → E}
    (hf : supHolderBoundOn U alpha K f) (hVU : V ⊆ U) : supHolderBoundOn V alpha K f :=
  fun x hx y hy => hf x (hVU hx) y (hVU hy)

theorem supHolderBoundOn.mono_const {U : Set (Vec d)} {alpha K K' : ℝ} {f : Vec d → E}
    (hf : supHolderBoundOn U alpha K f) (hKK : K ≤ K') :
    supHolderBoundOn U alpha K' f := by
  intro x hx y hy
  refine (hf x hx y hy).trans (mul_le_mul_of_nonneg_right hKK ?_)
  exact Real.rpow_nonneg (norm_nonneg _) _

/-! ### The exit: from the sup norm to the Euclidean magnitude -/



theorem holderSeminormBoundOn_of_supHolderBoundOn {U : Set (Vec d)} {alpha K : ℝ}
    {f : Vec d → Vec d} (hK : 0 ≤ K) (halpha : 0 ≤ alpha)
    (hf : supHolderBoundOn U alpha K f) :
    HolderSeminormBoundOn U alpha ((d : ℝ) * K) f := by
  intro x hx y hy
  have h1 : euclideanNorm (f x - f y) ≤ (d : ℝ) * ‖f x - f y‖ :=
    Homogenization.euclideanNorm_le_dimension_mul_norm _
  have h2 : ‖f x - f y‖ ≤ K * ‖x - y‖ ^ alpha := hf x hx y hy
  have h3 : ‖x - y‖ ^ alpha ≤ euclideanNorm (x - y) ^ alpha :=
    Real.rpow_le_rpow (norm_nonneg _) (Homogenization.norm_le_euclideanNorm _) halpha
  have h4 : K * ‖x - y‖ ^ alpha ≤ K * euclideanNorm (x - y) ^ alpha :=
    mul_le_mul_of_nonneg_left h3 hK
  calc euclideanNorm (f x - f y)
      ≤ (d : ℝ) * ‖f x - f y‖ := h1
    _ ≤ (d : ℝ) * (K * ‖x - y‖ ^ alpha) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d)
    _ ≤ (d : ℝ) * (K * euclideanNorm (x - y) ^ alpha) :=
        mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg d)
    _ = (d : ℝ) * K * euclideanNorm (x - y) ^ alpha := by ring

/-! ### Variational harmonicity at unit coefficient -/



def IsUnitWeaklyHarmonicOn (W : Set (Vec d)) (v : Homogenization.H1Function W) : Prop :=
  ∀ φ : Homogenization.H10Function W,
    ∫ x in W, Homogenization.vecDot (v.grad x) (φ.toH1Function.grad x) ∂volume = 0

/-- The two spellings of variational harmonicity agree at coefficient `1`. -/
theorem isUnitWeaklyHarmonicOn_iff {W : Set (Vec d)} {v : Homogenization.H1Function W} :
    IsUnitWeaklyHarmonicOn W v ↔ IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) W v := by
  constructor
  · intro h phi
    simpa using h phi
  · intro h phi
    simpa using h phi

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
