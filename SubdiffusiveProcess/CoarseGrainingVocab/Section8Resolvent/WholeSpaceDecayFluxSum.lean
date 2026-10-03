module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayRandomRadius

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section

variable {Omega : Type*}



def wholeSpaceFluxWeightedSum (beta : ℝ) (shell : ℕ → Omega → ℝ) :
    Omega → ℝ :=
  fun omega ↦ ∑' j : ℕ, beta ^ j * shell j omega



def wholeSpaceFluxPartitionFactor (beta : ℝ)
    (shell : ℕ → Omega → ℝ) : Omega → ℝ :=
  fun omega ↦ 1 + wholeSpaceFluxWeightedSum beta shell omega



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



theorem wholeSpaceFluxWeightedSum_nonneg
    {beta : ℝ} (hbeta : 0 ≤ beta) {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j omega, 0 ≤ shell j omega)
    (omega : Omega) :
    0 ≤ wholeSpaceFluxWeightedSum beta shell omega := by
  unfold wholeSpaceFluxWeightedSum
  exact tsum_nonneg fun j ↦
    mul_nonneg (pow_nonneg hbeta j) (hshell j omega)



theorem one_le_wholeSpaceFluxPartitionFactor
    {beta : ℝ} (hbeta : 0 ≤ beta) {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j omega, 0 ≤ shell j omega)
    (omega : Omega) :
    1 ≤ wholeSpaceFluxPartitionFactor beta shell omega := by
  unfold wholeSpaceFluxPartitionFactor
  exact le_add_of_nonneg_right
    (wholeSpaceFluxWeightedSum_nonneg hbeta hshell omega)



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
