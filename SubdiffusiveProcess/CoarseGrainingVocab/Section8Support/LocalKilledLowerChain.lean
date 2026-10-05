module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerDiagonal

@[expose] public section

/-!
# Harmonic propagation and chaining for the local lower bound

`s.fixed.coefficient` and `mfd:sec-speed`.

`KilledKernelOscillation` is the one external analytic input of the bundle: the
manuscript's spectral time-derivative bound `|∂_t p_t^U| ≤ C/(FM)`, the
zero-boundary Poisson correction on a prescribed pair `B' ⋐ B` and the maximum
principle, whose joint conclusion at `s.fixed.coefficient` and `mfd:sec-speed` is that `p_t^U(x,·)` has
oscillation at most `Cε/M` on `B'` for `t` comparable to `F`.  Everything else
here is proved: `compose_lower` is the Chapman–Kolmogorov integration over a
positive-mass overlap, and `chain_lower` is the induction along the `N` pairs of
the hypothesis.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}
  {p : ℝ → Vec d → Vec d → ℝ}

/-- **External input** (`s.fixed.coefficient` and `mfd:sec-speed`).  For a local diffusion whose
killed semigroup has a jointly continuous density obeying the diagonal upper bound of
the basic assumptions of the local killed lower bound, the spectral bound `|∂_t p_t^U(x,y)| ≤ C/(FM)` on
times comparable to `F`, the zero-boundary solution of
`-∇·(c∇v) = -ρ ∂_t p_t^U(x,·)` on a prescribed pair `B' ⋐ B` with `sup_B e_B ≤ εF`, and the
maximum principle together bound the oscillation of `p_t^U(x,·)` on `B'` by `Cε/M`, with `C`
depending only on `κ, A, γ`. -/
def KilledKernelOscillation (kappa A gamma : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ, 2 ≤ d → ∀ c rho : Vec d → ℝ, ∀ law : Kernel (Vec d) (Path d),
      LocalDiffusion c rho law → ∀ U : Set (Vec d), IsOpen U → Bornology.IsBounded U →
      CoefficientC11On U c → CoefficientC11On U rho →
      ∀ F : ℝ, 0 < F → ∀ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p →
      ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U) →
      0 < ((weightedMeasure rho) U).toReal →
      (∀ z ∈ U, meanExit law U z ≤ ENNReal.ofReal (A * F)) →
      (∀ t : ℝ, 0 < t → ∀ z ∈ U,
        p t z z ≤ A / ((weightedMeasure rho) U).toReal * (1 + F / t) ^ gamma) →
      ∀ epsilon : ℝ, 0 < epsilon → ∀ inner outer : Set (Vec d),
        IsOpen outer → IsCompact (closure inner) → closure inner ⊆ outer → outer ⊆ U →
        (∀ z ∈ outer, meanExit law outer z ≤ ENNReal.ofReal (epsilon * F)) →
        (∀ h : Vec d → ℝ, WeakHarmonic c outer h →
          oscillation inner h ≤ ENNReal.ofReal epsilon * oscillation outer h) →
        ∀ t : ℝ, kappa * F / 8 ≤ t → t ≤ kappa * F / 4 → ∀ x ∈ U,
          oscillation inner (fun y => p t x y)
            ≤ ENNReal.ofReal (C * epsilon / ((weightedMeasure rho) U).toReal)

/-- A bounded oscillation bounds every difference. -/
theorem sub_le_of_oscillation_le {S : Set (Vec d)} {h : Vec d → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hosc : oscillation S h ≤ ENNReal.ofReal b) {x y : Vec d} (hx : x ∈ S) (hy : y ∈ S) :
    h x - h y ≤ b := by
  have h1 : ENNReal.ofReal |h x - h y| ≤ oscillation S h := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.oscillation
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
  exact (le_abs_self _).trans ((ENNReal.ofReal_le_ofReal_iff hb).mp (h1.trans hosc))

/-- Chapman–Kolmogorov through a set of positive mass composes two lower bounds. -/
theorem compose_lower (hD : LocalDiffusion c rho law) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U)
    (hp : IsKilledDensity law rho U p)
    (hpc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    {alpha beta M m0 t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hm0 : 0 < m0) (hM : 0 < M)
    {S : Set (Vec d)} (hSmeas : MeasurableSet S) (hSU : S ⊆ U)
    (hmass : ENNReal.ofReal (m0 * M) ≤ (weightedMeasure rho) S)
    {z w : Vec d} (hz : z ∈ U) (hw : w ∈ U)
    (h₁ : ∀ y ∈ S, alpha / M ≤ p t₁ z y) (h₂ : ∀ y ∈ S, beta / M ≤ p t₂ y w) :
    alpha * beta * m0 / M ≤ p (t₁ + t₂) z w := by
  set mu := (weightedMeasure rho).restrict U with hmu
  have hSmu : mu S = (weightedMeasure rho) S := by
    rw [hmu, Measure.restrict_apply hSmeas, inter_eq_left.mpr hSU]
  have hpoint : ∀ y ∈ S, ENNReal.ofReal (alpha / M) * ENNReal.ofReal (beta / M)
      ≤ ENNReal.ofReal (p t₁ z y) * ENNReal.ofReal (p t₂ y w) := by
    intro y hy
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (h₁ y hy)) (ENNReal.ofReal_le_ofReal (h₂ y hy))
  have hkey : ENNReal.ofReal (alpha / M) * ENNReal.ofReal (beta / M) * ENNReal.ofReal (m0 * M)
      ≤ ENNReal.ofReal (p (t₁ + t₂) z w) := by
    refine le_trans ?_ (ofReal_density_lintegral_le hD hU hUb hp hpc ht₁ ht₂ hz hw)
    calc ENNReal.ofReal (alpha / M) * ENNReal.ofReal (beta / M) * ENNReal.ofReal (m0 * M)
        ≤ ENNReal.ofReal (alpha / M) * ENNReal.ofReal (beta / M) * mu S := by
          rw [hSmu]; exact mul_le_mul' le_rfl hmass
      _ = ∫⁻ _y in S, ENNReal.ofReal (alpha / M) * ENNReal.ofReal (beta / M) ∂mu :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ y in S, ENNReal.ofReal (p t₁ z y) * ENNReal.ofReal (p t₂ y w) ∂mu :=
          setLIntegral_mono ((measurable_density hp ht₁ z).mul
            (measurable_density_left hp ht₂ w)) hpoint
      _ ≤ ∫⁻ y, ENNReal.ofReal (p t₁ z y) * ENNReal.ofReal (p t₂ y w) ∂mu :=
          setLIntegral_le_lintegral _ _
  have hnn : 0 ≤ p (t₁ + t₂) z w := hp.2.1 (t₁ + t₂) (by linarith) z hz w hw
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at hkey
  have hle := (ENNReal.ofReal_le_ofReal_iff hnn).mp hkey
  have harith : alpha / M * (beta / M) * (m0 * M) = alpha * beta * m0 / M := by
    field_simp
  rwa [harith] at hle

/-- The lower bound propagates along the chain of pairs. -/
theorem chain_lower (hD : LocalDiffusion c rho law) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U)
    (hp : IsKilledDensity law rho U p)
    (hpc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    {V : Set (Vec d)} (hVU : V ⊆ U)
    {a m0 M tau : ℝ} (ha : 0 < a) (hm0 : 0 < m0) (hM : 0 < M) (htau : 0 < tau)
    {N k : ℕ} {inner : Fin k → Set (Vec d)} {chain : Fin N → Fin k}
    (hinnerU : ∀ i : Fin k, inner i ⊆ U)
    (hstep : ∀ i : Fin k, ∀ x ∈ V, x ∈ inner i → ∀ y ∈ inner i, a / M ≤ p tau x y)
    (hoverlap : ∀ i j : Fin N, j.val = i.val + 1 →
      ∃ overlap : Set (Vec d), MeasurableSet overlap ∧
        overlap ⊆ inner (chain i) ∩ inner (chain j) ∩ V ∧
        ENNReal.ofReal (m0 * M) ≤ (weightedMeasure rho) overlap)
    {z : Vec d} (hzV : z ∈ V) (hz0 : ∀ h0 : 0 < N, z ∈ inner (chain ⟨0, h0⟩)) :
    ∀ j : ℕ, ∀ hj : j < N, ∀ y ∈ inner (chain ⟨j, hj⟩),
      a ^ (j + 1) * m0 ^ j / M ≤ p (((j : ℝ) + 1) * tau) z y := by
  intro j
  induction j with
  | zero =>
    intro hj y hy
    have := hstep (chain ⟨0, hj⟩) z hzV (hz0 hj) y hy
    simpa using this
  | succ n ih =>
    intro hj y hy
    have hn : n < N := Nat.lt_of_succ_lt hj
    obtain ⟨O, hOmeas, hOsub, hOmass⟩ := hoverlap ⟨n, hn⟩ ⟨n + 1, hj⟩ rfl
    have hOU : O ⊆ U := fun x hx => hVU (hOsub hx).2
    have h₁ : ∀ y' ∈ O, a ^ (n + 1) * m0 ^ n / M ≤ p (((n : ℝ) + 1) * tau) z y' :=
      fun y' hy' => ih hn y' (hOsub hy').1.1
    have h₂ : ∀ y' ∈ O, a / M ≤ p tau y' y :=
      fun y' hy' => hstep (chain ⟨n + 1, hj⟩) y' (hOsub hy').2 (hOsub hy').1.2 y hy
    have hcomp := compose_lower hD hU hUb hp hpc
      (t₁ := ((n : ℝ) + 1) * tau) (t₂ := tau) (by positivity) htau
      (by positivity) ha.le hm0 hM hOmeas hOU hOmass
      (hVU hzV) (hinnerU (chain ⟨n + 1, hj⟩) hy) h₁ h₂
    have htime : ((n : ℝ) + 1) * tau + tau = ((n : ℝ) + 1 + 1) * tau := by ring
    rw [htime] at hcomp
    have harith : a ^ (n + 1) * m0 ^ n * a * m0 = a ^ (n + 1 + 1) * m0 ^ (n + 1) := by
      ring
    calc a ^ (n + 1 + 1) * m0 ^ (n + 1) / M
        = a ^ (n + 1) * m0 ^ n * a * m0 / M := by rw [harith]
      _ ≤ p (((n : ℝ) + 1 + 1) * tau) z y := hcomp
      _ = p ((((n + 1 : ℕ) : ℝ) + 1) * tau) z y := by push_cast; ring_nf

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
