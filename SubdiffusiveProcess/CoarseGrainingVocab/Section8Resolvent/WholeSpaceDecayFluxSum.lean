module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayRandomRadius

@[expose] public section

/-!
# Weighted shell sum for the whole-space resolvent flux

The local coarse-graining estimate in the flux half of the whole-space
resolvent argument is summed with a geometric graph-distance weight.  This
file records that deterministic summation and the resulting factor, separately
from the still-missing stopping-partition and local analytic inputs.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section

variable {Omega : Type*}

/-- The graph-distance weighted sum of the local flux prices.  In the source,
`beta` is the square root of the discrete contraction factor and `shell j`
already includes the size power and the local random weight `W_Q` summed over
the `j`-th graph sphere.
-/
def wholeSpaceFluxWeightedSum (beta : ℝ) (shell : ℕ → Omega → ℝ) :
    Omega → ℝ :=
  fun omega ↦ ∑' j : ℕ, beta ^ j * shell j omega

/-- The positive random factor used to multiply the deterministic flux
scale in the final estimate.
-/
def wholeSpaceFluxPartitionFactor (beta : ℝ)
    (shell : ℕ → Omega → ℝ) : Omega → ℝ :=
  fun omega ↦ 1 + wholeSpaceFluxWeightedSum beta shell omega

/-- Exponential shell growth is summable against a stronger geometric
contraction.  This is the deterministic choice
`vartheta^(1/2) * C(d) * 9^(d+6) < 1` in the source proof.
-/
theorem summable_wholeSpaceFluxWeightedSum
    {beta D K : ℝ} (hbeta : 0 ≤ beta) (hD : 0 ≤ D)
    (hcontract : beta * D < 1) {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j omega, 0 ≤ shell j omega)
    (hgrowth : ∀ j omega, shell j omega ≤ K * D ^ j) (omega : Omega) :
    Summable (fun j : ℕ ↦ beta ^ j * shell j omega) := by
  have hratio : 0 ≤ beta * D := mul_nonneg hbeta hD
  have hgeom : Summable (fun j : ℕ ↦ K * (beta * D) ^ j) :=
    (summable_geometric_of_lt_one hratio hcontract).mul_left K
  apply hgeom.of_nonneg_of_le
  · intro j
    exact mul_nonneg (pow_nonneg hbeta j) (hshell j omega)
  · intro j
    calc
      beta ^ j * shell j omega ≤ beta ^ j * (K * D ^ j) :=
        mul_le_mul_of_nonneg_left (hgrowth j omega) (pow_nonneg hbeta j)
      _ = K * (beta * D) ^ j := by rw [mul_pow]; ring

/-- The weighted local prices are nonnegative once every shell price and the
contraction factor are nonnegative.
-/
theorem wholeSpaceFluxWeightedSum_nonneg
    {beta : ℝ} (hbeta : 0 ≤ beta) {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j omega, 0 ≤ shell j omega)
    (omega : Omega) :
    0 ≤ wholeSpaceFluxWeightedSum beta shell omega := by
  unfold wholeSpaceFluxWeightedSum
  exact tsum_nonneg fun j ↦
    mul_nonneg (pow_nonneg hbeta j) (hshell j omega)

/-- Consequently the assembled flux factor is at least one, as required by
the frozen whole-space estimate.
-/
theorem one_le_wholeSpaceFluxPartitionFactor
    {beta : ℝ} (hbeta : 0 ≤ beta) {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j omega, 0 ≤ shell j omega)
    (omega : Omega) :
    1 ≤ wholeSpaceFluxPartitionFactor beta shell omega := by
  unfold wholeSpaceFluxPartitionFactor
  exact le_add_of_nonneg_right
    (wholeSpaceFluxWeightedSum_nonneg hbeta hshell omega)

/-- Explicit geometric upper bound for the weighted shell sum.
-/
theorem wholeSpaceFluxWeightedSum_le_geometric
    {beta D K : ℝ} (hbeta : 0 ≤ beta) (hD : 0 ≤ D)
    (hcontract : beta * D < 1) {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j omega, 0 ≤ shell j omega)
    (hgrowth : ∀ j omega, shell j omega ≤ K * D ^ j) (omega : Omega) :
    wholeSpaceFluxWeightedSum beta shell omega ≤ K * (1 - beta * D)⁻¹ := by
  have hsum := summable_wholeSpaceFluxWeightedSum
    hbeta hD hcontract hshell hgrowth omega
  have hratio : 0 ≤ beta * D := mul_nonneg hbeta hD
  have hgeom : Summable (fun j : ℕ ↦ K * (beta * D) ^ j) :=
    (summable_geometric_of_lt_one hratio hcontract).mul_left K
  unfold wholeSpaceFluxWeightedSum
  calc
    (∑' j : ℕ, beta ^ j * shell j omega) ≤
        ∑' j : ℕ, K * (beta * D) ^ j := by
      apply hsum.tsum_le_tsum _ hgeom
      intro j
      calc
        beta ^ j * shell j omega ≤ beta ^ j * (K * D ^ j) :=
          mul_le_mul_of_nonneg_left (hgrowth j omega) (pow_nonneg hbeta j)
        _ = K * (beta * D) ^ j := by rw [mul_pow]; ring
    _ = K * ∑' j : ℕ, (beta * D) ^ j := by rw [tsum_mul_left]
    _ = K * (1 - beta * D)⁻¹ := by
      rw [tsum_geometric_of_lt_one hratio hcontract]

/-- Once the local coarse-graining and deterministic localization steps bound
the global squared flux norm by the weighted shell sum, adjoining the leading
one gives exactly the source's random factor.
-/
theorem wholeSpaceFluxEstimate_le_partitionFactor
    {beta B H : ℝ} (hB : 0 ≤ B) {shell : ℕ → Omega → ℝ}
    {omega : Omega}
    (hshellSum : H ≤ B * wholeSpaceFluxWeightedSum beta shell omega) :
    H ≤ B * wholeSpaceFluxPartitionFactor beta shell omega := by
  apply hshellSum.trans
  unfold wholeSpaceFluxPartitionFactor
  gcongr
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
