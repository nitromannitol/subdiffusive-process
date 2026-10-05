module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerChain

@[expose] public section

/-!
# The off-diagonal upper bound for the killed density

`s.fixed.coefficient` and `mfd:sec-speed`, `s.fixed.coefficient` and `mfd:sec-speed`.

The manuscript uses the diagonal upper bound of
the basic assumptions of the local killed lower bound off the diagonal as well: the
Chapman–Kolmogorov identity and Cauchy–Schwarz give
`p_t^U(x,w) ≤ (p_t^U(x,x) p_t^U(w,w))^{1/2}`, so the diagonal bound
`p_t^U(z,z) ≤ (A/M)(1+F/t)^γ` bounds the whole kernel at time `t`.  Here that
step is carried out with the almost-everywhere semigroup identity
`density_semigroup_ae`, Hölder's inequality for `ℝ≥0∞`-valued functions, the
pointwise Chapman–Kolmogorov inequality `ofReal_density_lintegral_le` and the
pointwise symmetry `density_symm`; joint continuity upgrades the resulting
almost-everywhere bound to every endpoint of the domain.
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

/-- Cauchy–Schwarz: two functions with the same bound on their squared integrals have a
product integral with that bound. -/
theorem lintegral_mul_le_of_sq_le {α : Type*} [MeasurableSpace α] (mu : Measure α)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f mu) (hg : AEMeasurable g mu) {a : ℝ≥0∞}
    (ha : a ≠ ∞) (hfa : (∫⁻ y, (f y) ^ 2 ∂mu) ≤ a) (hga : (∫⁻ y, (g y) ^ 2 ∂mu) ≤ a) :
    (∫⁻ y, f y * g y ∂mu) ≤ a := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder : (∫⁻ y, f y * g y ∂mu)
      ≤ (∫⁻ y, (f y) ^ 2 ∂mu) ^ (1 / 2 : ℝ) * (∫⁻ y, (g y) ^ 2 ∂mu) ^ (1 / 2 : ℝ) := by
    simpa only [Pi.mul_apply, ENNReal.rpow_two] using
      ENNReal.lintegral_mul_le_Lp_mul_Lq mu hpq hf hg
  refine hholder.trans (le_trans (mul_le_mul' (ENNReal.rpow_le_rpow hfa (by norm_num))
    (ENNReal.rpow_le_rpow hga (by norm_num))) ?_)
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [ENNReal.zero_rpow_of_pos]
  · rw [← ENNReal.rpow_add _ _ ha0 ha]
    norm_num

/-- The squared `L²` mass of the killed density at a fixed point is at most its diagonal
value at twice the time. -/
theorem lintegral_density_sq_le (hD : LocalDiffusion c rho law) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U)
    (hp : IsKilledDensity law rho U p)
    (hpc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    (∫⁻ y, (ENNReal.ofReal (p t x y)) ^ 2 ∂((weightedMeasure rho).restrict U))
      ≤ ENNReal.ofReal (p (t + t) x x) := by
  have hcongr : ∀ᵐ y ∂((weightedMeasure rho).restrict U),
      (ENNReal.ofReal (p t x y)) ^ 2
        = ENNReal.ofReal (p t x y) * ENNReal.ofReal (p t y x) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    rw [density_symm hD hU hUb hp hpc ht hy hx, sq]
  rw [lintegral_congr_ae hcongr]
  exact ofReal_density_lintegral_le hD hU hUb hp hpc ht ht hx hx

/-- **The off-diagonal upper bound.**  A uniform diagonal bound at time `t` bounds the
killed density at time `t` at every pair of points of the domain. -/
theorem density_le_of_diagonal_le (hD : LocalDiffusion c rho law) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U)
    (hp : IsKilledDensity law rho U p)
    (hpc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    {t K : ℝ} (ht : 0 < t) (hdiag : ∀ z ∈ U, p t z z ≤ K) {x : Vec d} (hx : x ∈ U)
    {w : Vec d} (hw : w ∈ U) : p t x w ≤ K := by
  classical
  set mu := (weightedMeasure rho).restrict U with hmu
  have hhalf : 0 < t / 2 := by linarith
  have hsum : t / 2 + t / 2 = t := by ring
  have hK : 0 ≤ K := le_trans (hp.2.1 t ht x hx x hx) (hdiag x hx)
  -- the bound holds almost everywhere in the endpoint
  have hae : ∀ᵐ w' ∂mu, p t x w' ≤ K := by
    filter_upwards [density_semigroup_ae hD hU hUb hp hhalf hhalf hx,
      ae_restrict_mem hU.measurableSet] with w' hw' hw'U
    have hfsq : (∫⁻ y, (ENNReal.ofReal (p (t / 2) x y)) ^ 2 ∂mu)
        ≤ ENNReal.ofReal K := by
      refine le_trans (lintegral_density_sq_le hD hU hUb hp hpc hhalf hx) ?_
      rw [hsum]
      exact ENNReal.ofReal_le_ofReal (hdiag x hx)
    have hgsq : (∫⁻ y, (ENNReal.ofReal (p (t / 2) y w')) ^ 2 ∂mu)
        ≤ ENNReal.ofReal K := by
      have hcongr : ∀ᵐ y ∂mu, (ENNReal.ofReal (p (t / 2) y w')) ^ 2
          = (ENNReal.ofReal (p (t / 2) w' y)) ^ 2 := by
        filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
        rw [density_symm hD hU hUb hp hpc hhalf hy hw'U]
      rw [lintegral_congr_ae hcongr]
      refine le_trans (lintegral_density_sq_le hD hU hUb hp hpc hhalf hw'U) ?_
      rw [hsum]
      exact ENNReal.ofReal_le_ofReal (hdiag w' hw'U)
    have hprod : (∫⁻ y, ENNReal.ofReal (p (t / 2) x y) * ENNReal.ofReal (p (t / 2) y w') ∂mu)
        ≤ ENNReal.ofReal K :=
      lintegral_mul_le_of_sq_le mu (measurable_density hp hhalf x).aemeasurable
        (measurable_density_left hp hhalf w').aemeasurable ENNReal.ofReal_ne_top hfsq hgsq
    have hle : ENNReal.ofReal (p (t / 2 + t / 2) x w') ≤ ENNReal.ofReal K := hw'.trans_le hprod
    rw [hsum] at hle
    exact (ENNReal.ofReal_le_ofReal_iff hK).mp hle
  -- and upgrades to every endpoint by joint continuity
  obtain ⟨ws, hwsS, hwsU, hwslim⟩ :=
    exists_seq_tendsto_of_ae hU (coefficientOn_of_localDiffusion hD hUb) hae hw
  exact le_of_tendsto (tendsto_density_endpoint hpc ht hx hw hwsU hwslim)
    (Eventually.of_forall hwsS)

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
