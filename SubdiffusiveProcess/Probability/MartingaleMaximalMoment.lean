module

public import SubdiffusiveProcess.Probability.MartingalePowers
public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.DoobL2

@[expose] public section

open scoped ENNReal MeasureTheory ProbabilityTheory

open MeasureTheory


namespace SubdiffusiveProcess

theorem lintegral_iSup_evenPow_le_of_nonneg_martingale
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (X : ℕ → Omega → ℝ) (hX : Martingale X F mu)
    (hnonneg : ∀ n omega, 0 ≤ X n omega) (p : ℕ) (hp : 1 ≤ p)
    (hint : ∀ n, Integrable (fun omega => (X n omega)^p) mu)
    (B : ℝ≥0∞) (hB : ∀ n, (∫⁻ omega, ENNReal.ofReal ((X n omega)^(2*p)) ∂mu) ≤ B) :
    (∫⁻ omega, ⨆ n : ℕ, ENNReal.ofReal ((X n omega)^(2*p)) ∂mu) ≤ 4 * B := by
  have hsub : Submartingale (fun n w => (X n w)^p) F mu :=
    submartingale_natPow_of_nonneg_martingale mu F X hX
      (fun n => Filter.Eventually.of_forall (hnonneg n)) p hp hint
  have hpownn : 0 ≤ (fun n w => (X n w)^p) :=
    fun n w => pow_nonneg (hnonneg n w) p
  let S : ℕ → Omega → ℝ := fun n ω =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => (X k ω)^p)
  have hgrid : ∀ n, (∫⁻ ω, ENNReal.ofReal ((S n ω)^2) ∂mu) ≤ 4 * B := by
    intro n
    have h := _root_.SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.lintegral_sq_gridSup_le
      hsub hpownn n
    have hrewrite : ∀ ω, ((X n ω)^p)^2 = (X n ω)^(2*p) := by
      intro ω
      rw [← pow_mul, Nat.mul_comm]
    calc
      (∫⁻ ω, ENNReal.ofReal ((S n ω)^2) ∂mu) ≤
          4 * (∫⁻ ω, ENNReal.ofReal (((X n ω)^p)^2) ∂mu) := by
        simpa only [S] using h
      _ = 4 * (∫⁻ ω, ENNReal.ofReal ((X n ω)^(2*p)) ∂mu) := by
        congr 1
        apply lintegral_congr
        exact fun ω => by rw [hrewrite ω]
      _ ≤ 4 * B := mul_le_mul_right (hB n) 4
  have hpoint : ∀ ω, (⨆ n : ℕ, ENNReal.ofReal ((X n ω)^(2*p))) ≤
      ⨆ n : ℕ, ENNReal.ofReal ((S n ω)^2) := by
    intro ω
    apply iSup_mono
    intro n
    apply ENNReal.ofReal_le_ofReal
    have hle : (X n ω)^p ≤ S n ω := by
      dsimp [S]
      exact Finset.le_sup' (fun k => (X k ω)^p) (by simp)
    calc
      (X n ω)^(2*p) = ((X n ω)^p)^2 := by
        rw [← pow_mul, Nat.mul_comm]
      _ ≤ (S n ω)^2 := pow_le_pow_left₀ (pow_nonneg (hnonneg n ω) p) hle 2
  have hmeas : ∀ n : ℕ, Measurable (fun ω => ENNReal.ofReal ((S n ω)^2)) := by
    intro n
    have hS : Measurable (fun ω => S n ω) := by
      dsimp [S]
      apply Finset.measurable_range_sup''
      intro k hk
      exact ((hsub.stronglyMeasurable k).mono (F.le k)).measurable
    exact (hS.pow_const 2).ennreal_ofReal
  have hmono : Monotone (fun n : ℕ => fun ω => ENNReal.ofReal ((S n ω)^2)) := by
    intro n m hnm ω
    apply ENNReal.ofReal_le_ofReal
    have hsup : S n ω ≤ S m ω := by
      dsimp [S]
      exact Finset.sup'_mono (fun k => (X k ω)^p)
        (Finset.range_mono (Nat.succ_le_succ hnm))
        Finset.nonempty_range_add_one
    have hsn : 0 ≤ S n ω := (le_trans (pow_nonneg (hnonneg n ω) p) (by
      dsimp [S]
      exact Finset.le_sup' (fun k => (X k ω)^p) (by simp)))
    exact pow_le_pow_left₀ hsn hsup 2
  calc
    (∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal ((X n ω)^(2*p)) ∂mu) ≤
        ∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal ((S n ω)^2) ∂mu :=
      lintegral_mono hpoint
    _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal ((S n ω)^2) ∂mu :=
      lintegral_iSup hmeas hmono
    _ ≤ 4 * B := by
      apply iSup_le
      intro n
      exact hgrid n

end SubdiffusiveProcess
