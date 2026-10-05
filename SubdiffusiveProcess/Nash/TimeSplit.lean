module

public import SubdiffusiveProcess.Nash.DomainExtension
public import SubdiffusiveProcess.Nash.L2Dual

@[expose] public section

open MeasureTheory MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- Half-time composition gives the L1-to-L∞ estimate on L1 ∩ L2. -/
theorem semigroup_L1_top_bound {X : Type*} [MeasurableSpace X] (mu : Measure X) [SigmaFinite mu]
    (P : SubMarkovKernelSemigroup X) (S : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hsub : P.IsSubInvariant mu)
    (hcompat : ∀ (t : ℝ≥0) (f : Lp ℝ 2 mu), (S t f : X → ℝ) =ᵐ[mu] kernelIntegral (P t) f)
    (hsym : ∀ (t : ℝ≥0) (f g : Lp ℝ 2 mu), ⟪S t f, g⟫ = ⟪f, S t g⟫)
    (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 0 < K)
    (hsob : ∀ f : S.generatorDomain,
      eLpNorm (f : X → ℝ) (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))) mu ^ (2 : ℕ) ≤
        ENNReal.ofReal K * ENNReal.ofReal (-⟪S.generator f, (f : Lp ℝ 2 mu)⟫))
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 mu) (hf : Integrable (f : X → ℝ) mu) :
    eLpNorm (S t f : X → ℝ) ∞ mu ≤ ENNReal.ofReal (((d : ℝ) * K / (t : ℝ)) ^ d) *
      eLpNorm (f : X → ℝ) 1 mu := by
  let s : ℝ≥0 := t / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hss : s + s = t := by dsimp [s]; ring
  let R : ℝ := ((d : ℝ) * K / (2 * (s : ℝ))) ^ d
  let M : ℝ := Real.sqrt R
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have h12 : ∀ g : Lp ℝ 2 mu, Integrable (g : X → ℝ) mu →
      ‖S s g‖ ≤ M * (eLpNorm (g : X → ℝ) 1 mu).toReal :=
    semigroup_L1_L2_bound mu P S hsub hcompat d hd K hK hsob s hs
  have htop := symmetric_L2_top_bound mu (S s) M (hsym s) h12 (S s f)
  have hfin : eLpNorm (f : X → ℝ) 1 mu ≠ ∞ := (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top.ne
  calc
    _ = eLpNorm (S s (S s f) : X → ℝ) ∞ mu := by rw [← hss, S.add_apply]
    _ ≤ ENNReal.ofReal (M * ‖S s f‖) := htop
    _ ≤ ENNReal.ofReal (M * (M * (eLpNorm (f : X → ℝ) 1 mu).toReal)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (h12 f hf) hM)
    _ = ENNReal.ofReal R * eLpNorm (f : X → ℝ) 1 mu := by
      rw [← mul_assoc, ← sq, Real.sq_sqrt hR, ENNReal.ofReal_mul hR, ENNReal.ofReal_toReal hfin]
    _ = _ := by
      congr 2
      dsimp [R, s]
      congr 1
      ring

end SubdiffusiveProcess.Nash
