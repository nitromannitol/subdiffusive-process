module

public import SubdiffusiveProcess.FractionalSup.Iteration
public import SubdiffusiveProcess.FractionalSup.Truncation
public import SubdiffusiveProcess.FractionalSup.LevelSets
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.MultiplicativeChaos.ChaosBasic

@[expose] public section

/-!
# Stampacchia's supremum bound from a fractional Sobolev embedding

Given (i) the fractional Sobolev embedding on the cube with constant `CS` (as a hypothesis), (ii) the
fractional coercivity `‖v‖²_{H^s} ≤ K E_a(v,v)` on the killed space, (iii) finiteness of the
fractional seminorm of killed elements, the upper Stampacchia bound holds: `u ≤ M + δ` almost
everywhere, for every `δ > 0` above `δ₀ = CS·K·K_f·|Q|^{(p-2)/p}·2^{(p-1)/(p-2)}`, `p = 2d/(d-2s)`.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.FractionalSup

variable {d : ℕ}

/-- The critical exponent `2d/(d-2s)`. -/
def critExp (d : ℕ) (s : ℝ) : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 2 * s)

theorem critExp_gt_two {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    2 < critExp d s := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : 0 < (d : ℝ) - 2 * s := by linarith
  unfold critExp
  rw [lt_div_iff₀ hpos]
  nlinarith

open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

/-- The energy of a truncation of a Dirichlet solution equals its source pairing. -/
theorem fractionalSup_energy_identity {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (F : SpatialCoordinates d → ℝ) (b u : weakSobolevGraph Ω)
    (hsol : SolvesDirichlet a F b u) (Ψ : SobolevData Ω) (hΨk : Ψ ∈ killedSobolevGraph Ω)
    (c : ℝ)
    (hΨ2 : ∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      Ψ.2 i x = if c < u.val.1 x then u.val.2 i x else 0) :
    sobolevCoefficientForm a Ψ Ψ = ∫ x in (Ω : Set (SpatialCoordinates d)), F x * Ψ.1 x := by
  have h1 := hsol.2 ⟨Ψ, hΨk⟩
  have h2 : sobolevCoefficientForm a Ψ Ψ = sobolevCoefficientForm a u.val Ψ := by
    rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine integral_congr_ae ?_
    filter_upwards [hΨ2 i] with x hx
    rw [hx]
    by_cases hc : c < u.val.1 x
    · simp [hc]
    · simp [hc]
  exact h2.trans h1

/-- A bounded source pairs with a nonnegative integrable function. -/
theorem integral_mul_le_of_bound {μ : Measure (SpatialCoordinates d)} [IsFiniteMeasure μ]
    {F f g : SpatialCoordinates d → ℝ} {Kf : ℝ}
    (hFm : AEMeasurable F μ) (hFb : ∀ᵐ x ∂μ, |F x| ≤ Kf)
    (hf0 : 0 ≤ᵐ[μ] f) (hfL1 : Integrable f μ) (hg : g =ᵐ[μ] f) :
    ∫ x, F x * g x ∂μ ≤ Kf * ∫ x, f x ∂μ := by
  have hFint : Integrable (fun x => F x * f x) μ := by
    have := hfL1.bdd_mul (c := Kf) hFm.aestronglyMeasurable hFb
    simpa [mul_comm] using this
  have : ∫ x, F x * g x ∂μ = ∫ x, F x * f x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
  rw [this, ← integral_const_mul]
  refine integral_mono_ae hFint (hfL1.const_mul Kf) ?_
  filter_upwards [hFb, hf0] with x h1 h2
  have := (le_abs_self (F x)).trans h1
  simpa using mul_le_mul_of_nonneg_right this h2

/-- The energy--embedding chain for a single truncation. -/
theorem fractionalSup_energy_chain [NeZero d] (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) {CS : ℝ} (hCS : 0 < CS)
    (hemb : ∀ v : DomainL2 (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
      MemLp (v : SpatialCoordinates d → ℝ) (ENNReal.ofReal (critExp d s))
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            |v x| ^ (critExp d s)) ^ (((d : ℝ) - 2 * (s : ℝ)) / (d : ℝ)) ≤
          CS * cubeFractionalSqNorm hd z r hr s v)
    {K : ℝ} (hK : 0 < K) {Kf : ℝ} (_hKf : 0 ≤ Kf)
    (Ψ : DomainL2 (centeredCube z r hr)) {E : ℝ}
    (hsem : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => Ψ) < ⊤)
    (hcoer : cubeFractionalSqNorm hd z r hr s Ψ ≤ K * E)
    (f : SpatialCoordinates d → ℝ)
    (hf0 : 0 ≤ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (hΨf : (Ψ : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (hEF : E ≤ Kf * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x) :
    MemLp f (ENNReal.ofReal (critExp d s))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x ^ (critExp d s)) ^
          (2 / critExp d s) ≤
        (CS * K * Kf) * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 * (s : ℝ) := by linarith [s.2.2]
  obtain ⟨hmem, hbound⟩ := hemb Ψ hsem
  refine ⟨hmem.ae_eq hΨf, ?_⟩
  have hint_pow : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      |Ψ x| ^ (critExp d s)) = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        f x ^ (critExp d s) := by
    refine integral_congr_ae ?_
    filter_upwards [hΨf, hf0] with x h1 h2
    rw [h1, abs_of_nonneg h2]
  have hexp : ((d : ℝ) - 2 * (s : ℝ)) / (d : ℝ) = 2 / critExp d s := by
    rw [critExp]; field_simp
  rw [hint_pow, hexp] at hbound
  calc _ ≤ CS * cubeFractionalSqNorm hd z r hr s Ψ := hbound
    _ ≤ CS * (K * E) := mul_le_mul_of_nonneg_left hcoer hCS.le
    _ ≤ CS * (K * (Kf * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEF hK.le) hCS.le
    _ = _ := by ring

end SubdiffusiveProcess.FractionalSup
