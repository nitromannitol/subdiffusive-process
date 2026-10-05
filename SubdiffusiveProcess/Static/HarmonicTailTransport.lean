module

public import SubdiffusiveProcess.Static.LocalEstimateClauses
public import SubdiffusiveProcess.Static.AnchoredTailMoments
public import SubdiffusiveProcess.Static.UniformSupplierAssembly
public import SubdiffusiveProcess.Static.MassWindow
public import SubdiffusiveProcess.Static.InfraredComparison

@[expose] public section

/-! # Anchored tail transport of finite-prefix harmonic cutoff suppliers -/
open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Static
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Static

/-- One fixed tail window contains a finite family of arbitrary outer cubes. -/
theorem exists_harmonic_tail_window {d p : ℕ} (c : Fin p → Vec d) (s1 : Fin p → ℝ) :
    ∃ J : ℕ, ∀ (m : ℕ) (i : Fin p) (x : Vec d), x ∈ Metric.ball (c i) (s1 i / 2) →
      (3 : ℝ) ^ m • x ∈ Homogenization.openCubeSet
        (Homogenization.originCube d ((m : ℤ) + (J : ℤ))) := by
  classical
  let R := 1 + ∑ i : Fin p, (2 * ‖c i‖ + |s1 i|)
  obtain ⟨J, hJ⟩ := exists_mass_window (0 : Vec d) R
  refine ⟨J, ?_⟩
  intro m i x hx
  apply hJ m x
  rw [Metric.mem_ball, dist_zero_right]
  have hx' := Metric.mem_ball.mp hx
  rw [dist_eq_norm] at hx'
  have hsum : 2 * ‖c i‖ + |s1 i| ≤ ∑ j : Fin p, (2 * ‖c j‖ + |s1 j|) :=
    Finset.single_le_sum (f := fun j : Fin p => 2 * ‖c j‖ + |s1 j|)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have hn := norm_add_le (x - c i) (c i)
  rw [sub_add_cancel] at hn
  dsimp only [R]
  linarith [le_abs_self (s1 i)]

/-- Coefficient comparison preserves the exact cutoff, plateau, support and
all-radius energy clause, changing only the common constant. -/
theorem localHarmonicCutoffEstimates_of_comparison {d p : ℕ}
    {A0 A1 : Vec d → ℝ} {c : Fin p → Vec d} {s0 s1 : Fin p → ℝ} {K B F : ℝ}
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) (hF : 0 ≤ F)
    (hA : ∀ i, ∀ x ∈ Metric.ball (c i) (s1 i / 2), A1 x ≤ F * A0 x)
    (h : localHarmonicCutoffEstimates A0 c s0 s1 K B) :
    localHarmonicCutoffEstimates A1 c s0 s1 (F * K) B := by
  intro i n k hk
  obtain ⟨chi, hchi0, hchi1, hsupport, henergy⟩ := h i n k hk
  refine ⟨chi, hchi0, hchi1, hsupport, ?_⟩
  intro x r hr hr1
  let U := Metric.ball x r ∩ Metric.ball (c i)
    (((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
      (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2)
  have hU : MeasurableSet U := measurableSet_ball.inter measurableSet_ball
  have hUsub : U ⊆ Metric.ball (c i) (s1 i / 2) := by
    intro y hy
    apply Metric.ball_subset_ball _ hy.2
    have hn : (0 : ℝ) < 2 ^ n := by positivity
    have hk' : ((k + 1 : ℕ) : ℝ) ≤ 2 ^ n := by exact_mod_cast (by omega : k + 1 ≤ 2 ^ n)
    have ho : ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ 1 := (div_le_one hn).mpr hk'
    have hprod := mul_nonneg (sub_nonneg.mpr ho) (sub_nonneg.mpr (hs i).2.le)
    nlinarith only [hprod]
  have hE := energy_le_mul hU hF (fun y hy => hA i y (hUsub hy)) chi.grad
  change energy U A1 chi.grad ≤ _
  calc
    _ ≤ ENNReal.ofReal F * energy U A0 chi.grad := hE
    _ ≤ ENNReal.ofReal F * ENNReal.ofReal
        (K * ((s1 i - s0 i) / 2 ^ n / 2) ^ (-B) * r ^ ((d : ℝ) - 1 / 2)) :=
      mul_le_mul_right (henergy x r hr hr1) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hF]
      congr 1
      ring

/-- Transport of a proved finite-prefix harmonic cutoff bank to every finite
and infinite physical anchored normalization. -/
theorem localHarmonicCutoffSupplier_of_prefix (d p : ℕ)
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) (q : ℝ) (hq : 1 ≤ q)
    (hprefix : ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 → ∃ C : ℝ, 0 < C ∧
        ∀ (j m : ℕ), j ≤ m → ∀ z : Vec d,
          ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
            (∫⁻ ω, ENNReal.ofReal (K ω ^ (2 * q)) ∂M.P.toMeasure) ≤ ENNReal.ofReal C ∧
            ∀ᵐ ω ∂M.P.toMeasure,
              localHarmonicCutoffEstimates
                (fun x => (ahom M j)⁻¹ * aCutoff M j ω (z + (3 : ℝ) ^ m • x))
                c s0 s1 (K ω) 5) :
    UniformLocalMomentSupplier q (fun M L m z ω K =>
      localHarmonicCutoffEstimates
        (SubdiffusiveProcess.Static.localCoefficient M L m z ω)
        c s0 s1 K 5) := by
  have h2q : 1 ≤ 2 * q := by linarith
  obtain ⟨J, hwindow⟩ := exists_harmonic_tail_window c s1
  obtain ⟨δ0, hδ0, hprefix⟩ := hprefix
  obtain ⟨B, hB, htail⟩ := exists_uniform_local_tail_comparison d J (2 * q) h2q
  refine ⟨min δ0 1, lt_min hδ0 zero_lt_one, ?_⟩
  intro M hM
  have hMδ : M.delta ≤ δ0 := hM.trans (min_le_left _ _)
  have hM1 : M.delta ≤ 1 := hM.trans (min_le_right _ _)
  obtain ⟨A, hA, hprefixM⟩ := hprefix M hMδ
  refine ⟨B ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro L m z
  let j := localIndex L m
  have hjm : j ≤ m := by
    cases L using WithTop.recTopCoe
    · exact le_rfl
    · exact min_le_left _ _
  obtain ⟨W, hW, hWone, hWmom, hWdom⟩ := hprefixM j m hjm z
  obtain ⟨F, hF, hFone, hFmom, hFdom⟩ := htail M hM1 m z
  let V : AnchoredC11Sample d → ℝ := fun ω => W ω.1
  have hV : Measurable V := hW.comp measurable_subtype_coe
  have hVone : ∀ ω, 1 ≤ V ω := fun ω => hWone ω.1
  have hVmom : (∫⁻ ω, ENNReal.ofReal (V ω ^ (2 * q)) ∂localAnchoredLaw M) ≤
      ENNReal.ofReal A := by
    rw [anchored_moment_eq M W hW (2 * q)]
    exact hWmom
  refine ⟨fun ω => F ω * V ω, hF.mul hV,
    fun ω => one_le_mul_of_one_le_of_one_le (hFone ω) (hVone ω), ?_, ?_⟩
  · calc
      _ ≤ (∫⁻ ω, ENNReal.ofReal (F ω ^ (2 * q)) ∂localAnchoredLaw M) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, ENNReal.ofReal (V ω ^ (2 * q)) ∂localAnchoredLaw M) ^ (1 / 2 : ℝ) :=
        product_moment_le _ hF hV (fun ω => zero_le_one.trans (hFone ω))
          (fun ω => zero_le_one.trans (hVone ω)) q
      _ ≤ ENNReal.ofReal B ^ (1 / 2 : ℝ) * ENNReal.ofReal A ^ (1 / 2 : ℝ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hFmom (by norm_num))
          (ENNReal.rpow_le_rpow hVmom (by norm_num))
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB.le (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hA.le (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
  · have hWa := (measurePreserving_anchoredVal M).quasiMeasurePreserving.ae hWdom
    filter_upwards [hWa, hFdom] with ω hω hFω
    have hcomp : ∀ i, ∀ x ∈ Metric.ball (c i) (s1 i / 2),
        localCoefficient M L m z ω x ≤
          F ω * ((ahom M j)⁻¹ * aCutoff M j ω.1 (z + (3 : ℝ) ^ m • x)) := by
      intro i x hx
      have hdensity : localDensity M L m z ω x ≤
          F ω * aCutoff M j ω.1 (z + (3 : ℝ) ^ m • x) := by
        cases L using WithTop.recTopCoe
        · exact (hFω ⊤ le_top x (hwindow m i x hx)).2
        · rename_i L
          change localDensity M (L : WithTop ℕ) m z ω x ≤
            F ω * aCutoff M (min m L) ω.1 (z + (3 : ℝ) ^ m • x)
          by_cases hmL : m ≤ L
          · simpa only [min_eq_left hmL] using
              (hFω (L : WithTop ℕ) (WithTop.coe_le_coe.mpr hmL) x (hwindow m i x hx)).2
          · have hLm : L ≤ m := le_of_lt (lt_of_not_ge hmL)
            rw [min_eq_right hLm, localDensity_finite_of_le M hLm z ω x]
            exact le_mul_of_one_le_left (aCutoff_pos M L ω.1 _).le (hFone ω)
      have h := mul_le_mul_of_nonneg_left hdensity (inv_pos.mpr (ahom_pos M j)).le
      change (ahom M j)⁻¹ * localDensity M L m z ω x ≤ _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    exact localHarmonicCutoffEstimates_of_comparison hs (zero_le_one.trans (hFone ω)) hcomp hω

end SubdiffusiveProcess.Static
