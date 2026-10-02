import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane3.BandFiltration
import SubdiffusiveProcess.Probability.LayerProductBlocks
import SubdiffusiveProcess.Probability.RetainedResponseTransport
import SubdiffusiveProcess.Compactness.UniformApproximation
import SubdiffusiveProcess.Lane3.QueueHelpers
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper
noncomputable section

lemma aux_test_approx_compact {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : ℕ → Ω → ℝ} (hf : ∀ N, MemLp (f N) p μ)
    {c : ℕ → ℕ → Ω → ℝ} (hc : ∀ H N, MemLp (c H N) p μ)
    (hcompact : ∀ H, IsCompact (closure (Set.range (fun N =>
      (hc H N).toLp (c H N)))))
    {err : ℕ → ℝ} (herr : Tendsto err atTop (𝓝 0))
    (happrox : ∀ H N, dist ((hf N).toLp (f N)) ((hc H N).toLp (c H N)) ≤ err H) :
    IsCompact (closure (Set.range (fun N => (hf N).toLp (f N)))) := by
  exact SubdiffusiveProcess.isCompact_closure_range_of_approximating_compact_ranges
    hcompact herr happrox

lemma aux_compact_piecewise {X : Type} [TopologicalSpace X] [T2Space X]
    (f g : ℕ → X) (H : ℕ)
    (hg : IsCompact (closure (Set.range g))) :
    IsCompact (closure (Set.range (fun N => if H ≤ N then g N else f N))) := by
  let K : Set X := closure (Set.range g) ∪ f '' Set.Iio H
  have hKiio : IsCompact (f '' Set.Iio H) := by
    exact (Set.finite_Iio H).image f |>.isCompact
  have hK : IsCompact K := by
    exact hg.union hKiio
  have hsubset : closure (Set.range (fun N => if H ≤ N then g N else f N)) ⊆ K := by
    apply closure_minimal
    · rintro x ⟨N, rfl⟩
      by_cases hHN : H ≤ N
      · exact Or.inl (subset_closure ⟨N, by simp [hHN]⟩)
      · exact Or.inr ⟨N, Nat.lt_of_not_ge hHN, by simp [hHN]⟩
    · exact hK.isClosed
  exact IsCompact.of_isClosed_subset hK isClosed_closure hsubset

lemma aux_countable_compact_subseq {κ X : Type} [Countable κ]
    [PseudoMetricSpace X] (K : κ → Set X)
    (hK : ∀ k, IsCompact (K k)) (u : κ → ℕ → X)
    (hu : ∀ k n, u k n ∈ K k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, ∃ x, Tendsto (fun n => u k (φ n)) atTop (𝓝 x) := by
  classical
  letI : ∀ k, CompactSpace (K k) := fun k =>
    isCompact_iff_compactSpace.mp (hK k)
  let v : ℕ → ∀ k, K k := fun n k => ⟨u k n, hu k n⟩
  obtain ⟨z, φ, hφ, hlim⟩ :=
    CompactSpace.tendsto_subseq v
  refine ⟨φ, hφ, fun k => ⟨z k, ?_⟩⟩
  have hcont : Continuous (fun p : (∀ k, K k) => (p k : X)) :=
    continuous_subtype_val.comp (continuous_apply k)
  have hlim' := hcont.tendsto z |>.comp hlim
  simpa only [Function.comp_apply, v] using hlim'

lemma aux_compact_image_pair {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (f g : ℕ → X) (hf : IsCompact (closure (Set.range f)))
    (hg : IsCompact (closure (Set.range g))) (F : X × X → Y)
    (hF : Continuous F) (z : ℕ → Y)
    (hz : ∀ N, z N = F (f N, g N)) :
    IsCompact (closure (Set.range z)) := by
  have hK : IsCompact (closure (Set.range f) ×ˢ closure (Set.range g)) :=
    hf.prod hg
  have hIm : IsCompact (F ''
      (closure (Set.range f) ×ˢ closure (Set.range g))) := hK.image hF
  have hsub : closure (Set.range z) ⊆
      F '' (closure (Set.range f) ×ˢ closure (Set.range g)) := by
    apply closure_minimal
    · rintro y ⟨N, rfl⟩
      rw [hz N]
      refine ⟨(f N, g N), ?_, rfl⟩
      exact ⟨subset_closure ⟨N, rfl⟩, subset_closure ⟨N, rfl⟩⟩
    · exact hIm.isClosed
  exact IsCompact.of_isClosed_subset hIm isClosed_closure hsub

lemma aux_raw_tendsto_of_lp {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : ℕ → Ω → ℝ} (hf : ∀ n, MemLp (f n) p μ)
    {g : Lp ℝ p μ}
    (h : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 g)) :
    Tendsto (fun n => eLpNorm (f n - (g : Ω → ℝ)) p μ) atTop (𝓝 0) := by
  have hg : MemLp (g : Ω → ℝ) p μ := Lp.memLp g
  have hto : hg.toLp (g : Ω → ℝ) = g := Lp.toLp_coeFn g hg
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf (g : Ω → ℝ) hg).mp
  simpa only [hto] using h

lemma aux_layer_limit_meas
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] [IsProbabilityMeasure μ]
    (σ : ℕ → MeasurableSpace Ω) (hσmono : Monotone σ)
    (hσle : ∀ H, σ H ≤ (inferInstance : MeasurableSpace Ω))
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hf : MemLp f p μ) (hF : ∀ N, MemLp (F N) p μ)
    (hconv : Tendsto (fun N => eLpNorm (F (ψ N) - f) p μ)
      atTop (𝓝 0))
    (c : ℕ → ℕ → Ω → ℝ) (hc : ∀ H N, MemLp (c H N) p μ)
    {err : ℕ → ℝ} (herr : Tendsto err atTop (𝓝 0))
    (happrox : ∀ H N, H ≤ N →
      eLpNorm (F N - c H N) p μ ≤ ENNReal.ofReal (err H))
    (hmeas : ∀ H N, H ≤ N →
      AEStronglyMeasurable[σ H] (c H N) μ) :
    AEStronglyMeasurable[⨆ H, σ H] f μ := by
  let A : ℕ → Ω → ℝ := fun n => c n (ψ n)
  have hp1 : 1 ≤ p := (inferInstance : Fact (1 ≤ p)).out
  have hA : ∀ n, MemLp (A n) p μ := by
    intro n
    exact hc n (ψ n)
  have hAupper : ∀ n,
      eLpNorm (A n - f) p μ ≤
        ENNReal.ofReal (err n) + eLpNorm (F (ψ n) - f) p μ := by
    intro n
    calc
      eLpNorm (A n - f) p μ =
          eLpNorm ((A n - F (ψ n)) + (F (ψ n) - f)) p μ := by
        congr 1
        funext x
        dsimp [A]
        ring
      _ ≤ eLpNorm (A n - F (ψ n)) p μ +
          eLpNorm (F (ψ n) - f) p μ :=
        eLpNorm_add_le
          ((hA n).aestronglyMeasurable.sub (hF (ψ n)).aestronglyMeasurable)
          ((hF (ψ n)).aestronglyMeasurable.sub hf.aestronglyMeasurable) hp1
      _ = eLpNorm (F (ψ n) - A n) p μ +
          eLpNorm (F (ψ n) - f) p μ := by
        rw [eLpNorm_sub_comm]
      _ ≤ ENNReal.ofReal (err n) + eLpNorm (F (ψ n) - f) p μ := by
        gcongr
        simpa only [A] using happrox n (ψ n) (hψ.id_le n)
  have herr' : Tendsto (fun n => ENNReal.ofReal (err n)) atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal herr)
  have hupper : Tendsto (fun n =>
      ENNReal.ofReal (err n) + eLpNorm (F (ψ n) - f) p μ)
      atTop (𝓝 0) := by simpa using herr'.add hconv
  have hAconv : Tendsto (fun n => eLpNorm (A n - f) p μ)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => bot_le) hAupper
  have hLpconv : Tendsto (fun n => (hA n).toLp (A n)) atTop
      (𝓝 ((hf).toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' A hA f hf).mpr hAconv
  have hclosed : IsClosed {g : Lp ℝ p μ |
      AEStronglyMeasurable[⨆ H, σ H] (g : Ω → ℝ) μ} := by
    exact isClosed_aestronglyMeasurable
      (iSup_le fun H => hσle H)
  have hmemlim : (hf).toLp f ∈ {g : Lp ℝ p μ |
      AEStronglyMeasurable[⨆ H, σ H] (g : Ω → ℝ) μ} :=
    hclosed.mem_of_tendsto hLpconv (Eventually.of_forall fun n => by
      apply (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)
        (m := ⨆ H, σ H)).2
      exact AEStronglyMeasurable.congr
        ((hmeas n (ψ n) (hψ.id_le n)).mono (le_iSup σ n))
        (hA n).coeFn_toLp.symm)
  exact AEStronglyMeasurable.congr
    ((mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)
      (m := ⨆ H, σ H)).1 hmemlim)
    hf.coeFn_toLp

lemma aux_fixed_band_compact
    (d : ℕ)
    (Y : ℤ → Type) [instY : ∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j))
      [instP : ∀ j, IsProbabilityMeasure (laws j)]
    (Idx : Type) [Countable Idx]
    (Rf : Idx → ℕ → ((j : ℤ) → Y j) → ℝ)
    (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hpq : p < q) (hq : q ≠ ∞)
    (Kb : Idx → ℝ≥0∞) (hKb : ∀ i, Kb i ≠ ∞)
    (hmem : ∀ (i : Idx) (N : ℕ),
      MemLp (Rf i N) q (Measure.infinitePi laws))
    (hmom : ∀ (i : Idx) (N : ℕ),
      eLpNorm (Rf i N) q (Measure.infinitePi laws) ≤ Kb i)
    (Cp : Idx → ℝ) (a disorder : ℝ)
    (hsplit : ∀ (i : Idx) (H : ℕ),
      ∃ (X : Type) (_ : MetricSpace X)
        (_ : TopologicalSpace.SeparableSpace X) (_ : MeasurableSpace X)
        (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d))
        (R : Response Q)
        (V : ((j : bandSet H) → Y j.1) → X)
        (psi : X → Potential Q)
        (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet H}) → Y j.1) → Potential Q),
        Measurable V ∧
        LipschitzWith 1 psi ∧
        (∀ N : ℕ, H ≤ N →
          Measurable
            (fun z : X × ((j : {j : ℤ // j ∉ bandSet H}) → Y j.1) =>
              R.eval (psi z.1 + tail N z.2))) ∧
        (∀ N : ℕ, H ≤ N →
          ∀ ω : (j : ℤ) → Y j,
            Rf i N ω =
              R.eval
                (psi (V (fun j => ω j.1)) +
                  tail N (fun j => ω j.1))))
    (i : Idx) (H : ℕ)
    (hband : ∀ (H N : ℕ), H ≤ N →
      eLpNorm
        (fun ω => Rf i N ω -
          ((Measure.infinitePi laws)[Rf i N | bandSigma Y H]) ω)
        p (Measure.infinitePi laws) ≤
      ENNReal.ofReal (Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ))))) :
    ∃ (c : ℕ → ((j : ℤ) → Y j) → ℝ),
      ∃ (cmem : ∀ N, MemLp (c N) p (Measure.infinitePi laws)),
        IsCompact (closure (Set.range (fun N => (cmem N).toLp (c N)))) ∧
        (∀ N, H ≤ N →
          eLpNorm (fun ω => Rf i N ω - c N ω) p (Measure.infinitePi laws) ≤
            ENNReal.ofReal (Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ))))) ∧
        (∀ N, H ≤ N →
          AEStronglyMeasurable[bandSigma Y H] (c N)
            (Measure.infinitePi laws)) := by
  classical
  letI : DecidablePred (fun j : ℤ => j ∈ bandSet H) :=
    fun j => Classical.propDecidable _
  obtain ⟨X, _, _, _, _, Q, R, V, psi, tail, hV, hpsi, hmeas, hrepr⟩ := hsplit i H
  let e : ((j : ℤ) → Y j) ≃ᵐ
      (((j : bandSet H) → Y j.1) ×
        ((j : {j : ℤ // j ∉ bandSet H}) → Y j.1)) :=
    MeasurableEquiv.piEquivPiSubtypeProd Y (fun j => j ∈ bandSet H)
  have he : MeasurePreserving (e : ((j : ℤ) → Y j) → _) (Measure.infinitePi laws)
      ((Measure.infinitePi fun j : bandSet H => laws j.1).prod
        (Measure.infinitePi fun j : {j : ℤ // j ∉ bandSet H} => laws j.1)) := by
    exact measurePreserving_infinitePi_split laws (fun j => j ∈ bandSet H)
  have hσ :
      (inferInstance : MeasurableSpace ((j : bandSet H) → Y j.1)).comap
          (fun z : ((j : ℤ) → Y j) => (e z).1) = bandSigma Y H := by
    rw [bandSigma_eq_comap]
    rfl
  let F : {N : ℕ // H ≤ N} →
      X × ((j : {j : ℤ // j ∉ bandSet H}) → Y j.1) → ℝ :=
    fun N z => R.eval (psi z.1 + tail N.1 z.2)
  have hFm : ∀ N, Measurable (F N) := by
    intro N
    simpa only [F] using hmeas N.1 N.2
  have hFn : ∀ N x y, 0 ≤ F N (x, y) := by
    intro N x y
    simp only [F]
    exact R.eval_nonneg _
  have hFc : ∀ N x x' y,
      F N (x, y) ≤ Real.exp (1 * dist x x') * F N (x', y) := by
    intro N x x' y
    simp only [F]
    calc
      R.eval (psi x + tail N.1 y) ≤
          Real.exp ‖(psi x + tail N.1 y) - (psi x' + tail N.1 y)‖ *
            R.eval (psi x' + tail N.1 y) := R.exp_comparison _ _
      _ ≤ Real.exp (1 * dist x x') * R.eval (psi x' + tail N.1 y) := by
        apply mul_le_mul_of_nonneg_right
        · apply (Real.exp_le_exp).2
          simpa only [dist_eq_norm, add_sub_add_right_eq_sub] using hpsi.dist_le_mul x x'
        · exact R.eval_nonneg _
  have hFpull : ∀ N,
      MemLp (fun z : (j : ℤ) → Y j => F N (V (e z).1, (e z).2))
        q (Measure.infinitePi laws) := by
    intro N
    have heq : (fun z : (j : ℤ) → Y j => F N (V (e z).1, (e z).2)) = Rf i N.1 := by
      funext z
      simp only [F]
      exact (hrepr N.1 N.2 z).symm
    rw [heq]
    exact hmem i N.1
  have hFbound : ∀ N,
      eLpNorm (fun z : (j : ℤ) → Y j => F N (V (e z).1, (e z).2))
          q (Measure.infinitePi laws) ≤ Kb i := by
    intro N
    have heq : (fun z : (j : ℤ) → Y j => F N (V (e z).1, (e z).2)) = Rf i N.1 := by
      funext z
      simp only [F]
      exact (hrepr N.1 N.2 z).symm
    rw [heq]
    exact hmom i N.1
  have hcompact := SubdiffusiveProcess.retained_conditional_responses_equiv_isCompact_closure
    (e := e) he hV hFm hFn (C := 1) (by norm_num) hFc hpq hq (hKb i)
    hFpull hFbound
  let CE : {N : ℕ // H ≤ N} → ((j : ℤ) → Y j) → ℝ := fun N =>
    (Measure.infinitePi laws)[(fun z : (j : ℤ) → Y j =>
      F N (V (e z).1, (e z).2)) |
      (inferInstance : MeasurableSpace ((j : bandSet H) → Y j.1)).comap
        (fun z : (j : ℤ) → Y j => (e z).1)]
  have hCEmem : ∀ N, MemLp (CE N) p (Measure.infinitePi laws) := by
    intro N
    dsimp only [CE]
    exact memLp_condExp_equiv_fst e he hp.out (ne_top_of_lt hpq)
      ((hFpull N).mono_exponent hpq.le)
  let c : ℕ → ((j : ℤ) → Y j) → ℝ := fun N =>
    if hN : H ≤ N then CE ⟨N, hN⟩ else Rf i N
  have cmem : ∀ N, MemLp (c N) p (Measure.infinitePi laws) := by
    intro N
    by_cases hN : H ≤ N
    · simpa only [c, dif_pos hN] using hCEmem ⟨N, hN⟩
    · simpa only [c, dif_neg hN] using (hmem i N).mono_exponent hpq.le
  have hcompactCE : IsCompact (closure (Set.range (fun N =>
      (hCEmem N).toLp (CE N)))) := by
    simpa only [CE] using hcompact
  have hcompactC : IsCompact (closure (Set.range (fun N =>
      (cmem N).toLp (c N)))) := by
    have hlow : IsCompact (Set.range (fun N : Fin H =>
        ((hmem i N).mono_exponent hpq.le).toLp (Rf i N))) :=
      (Set.finite_range _).isCompact
    apply IsCompact.of_isClosed_subset (hlow.union hcompactCE) isClosed_closure
    apply closure_minimal
    · rintro x ⟨N, rfl⟩
      by_cases hN : H ≤ N
      · right
        apply subset_closure
        exact ⟨⟨N, hN⟩, by simp only [c, dif_pos hN, CE]⟩
      · left
        exact ⟨⟨N, Nat.lt_of_not_ge hN⟩, by
          simp only [c, dif_neg hN]⟩
    · exact hlow.isClosed.union hcompactCE.isClosed
  have hcmeas : ∀ N, H ≤ N →
      AEStronglyMeasurable[bandSigma Y H] (c N) (Measure.infinitePi laws) := by
    intro N hN
    simp only [c, dif_pos hN, CE]
    rw [← hσ]
    exact (stronglyMeasurable_condExp (μ := Measure.infinitePi laws)
      (f := fun z : (j : ℤ) → Y j => F ⟨N, hN⟩ (V (e z).1, (e z).2))).aestronglyMeasurable
  refine ⟨c, cmem, hcompactC, ?_, hcmeas⟩
  intro N hN
  have hreprN :
      (fun z : (j : ℤ) → Y j => F ⟨N, hN⟩ (V (e z).1, (e z).2)) = Rf i N := by
    funext z
    simp only [F]
    exact (hrepr N hN z).symm
  have hce :
      (Measure.infinitePi laws)[(fun z : (j : ℤ) → Y j =>
        F ⟨N, hN⟩ (V (e z).1, (e z).2)) |
        (inferInstance : MeasurableSpace ((j : bandSet H) → Y j.1)).comap
          (fun z : (j : ℤ) → Y j => (e z).1)] =ᵐ[Measure.infinitePi laws]
        (Measure.infinitePi laws)[Rf i N |
          (inferInstance : MeasurableSpace ((j : bandSet H) → Y j.1)).comap
            (fun z : (j : ℤ) → Y j => (e z).1)] :=
    condExp_congr_ae (Eventually.of_forall (fun z => congrFun hreprN z))
  have hce' :
      CE ⟨N, hN⟩ =ᵐ[Measure.infinitePi laws]
        (Measure.infinitePi laws)[Rf i N | bandSigma Y H] := by
    simpa only [CE, hσ] using hce
  apply (eLpNorm_congr_ae ?_).trans_le (hband H N hN)
  filter_upwards [hce'] with z hz
  simp only [c, dif_pos hN, hz]

lemma aux_pow_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H : ℕ => (3 : ℝ) ^ (-(a * (H : ℝ)))) atTop (𝓝 0) := by
  have hlt : (3 : ℝ) ^ (-a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h0 : 0 ≤ (3 : ℝ) ^ (-a) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpow : Tendsto (fun n : ℕ => ((3 : ℝ) ^ (-a)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 hlt
  refine hpow.congr' ?_
  filter_upwards with n
  rw [show -(a * (n : ℝ)) = (-a) * (n : ℝ) by ring]
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (-a) (n : ℝ)]
  rw [Real.rpow_natCast]

lemma aux_eLpNorm_smul_add_neg_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {c : ℝ} (hc : ‖c‖ₑ ≤ 1)
    (A B : α → ℝ) (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ) :
    eLpNorm (c • (A + (-B))) p μ ≤ eLpNorm A p μ + eLpNorm B p μ := by
  calc eLpNorm (c • (A + (-B))) p μ
      = ‖c‖ₑ * eLpNorm (A + (-B)) p μ := eLpNorm_const_smul c (A + (-B)) p μ
    _ ≤ 1 * eLpNorm (A + (-B)) p μ := by gcongr
    _ = eLpNorm (A + (-B)) p μ := one_mul _
    _ ≤ eLpNorm A p μ + eLpNorm (-B) p μ := eLpNorm_add_le hA hB.neg hp.out
    _ = eLpNorm A p μ + eLpNorm B p μ := by rw [eLpNorm_neg]



theorem prop_response_compact
    (d : ℕ)
    (Y : ℤ → Type) [instY : ∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j))
      [instP : ∀ j, IsProbabilityMeasure (laws j)]
    (Idx Pol : Type) [Countable Idx] [Countable Pol]
    (Rf : Idx → ℕ → ((j : ℤ) → Y j) → ℝ)
    (Gpol : Pol → ℕ → ((j : ℤ) → Y j) → ℝ)
    (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hpq : p < q) (hq : q ≠ ∞)
    (a disorder : ℝ) (ha : 0 < a) (hdisorder : 0 < disorder)
    (Cp : Idx → ℝ) (hCp : ∀ i, 0 ≤ Cp i)
    (Kb : Idx → ℝ≥0∞) (hKb : ∀ i, Kb i ≠ ∞)
    (hmem : ∀ (i : Idx) (N : ℕ),
      MemLp (Rf i N) q (Measure.infinitePi laws))
    (hmom : ∀ (i : Idx) (N : ℕ),
      eLpNorm (Rf i N) q (Measure.infinitePi laws) ≤ Kb i)
    (hband : ∀ (i : Idx) (H N : ℕ), H ≤ N →
      eLpNorm
        (fun ω => Rf i N ω -
          ((Measure.infinitePi laws)[Rf i N | bandSigma Y H]) ω)
        p (Measure.infinitePi laws) ≤
      ENNReal.ofReal (Cp i * disorder *
        (3 : ℝ) ^ (-(a * (H : ℝ)))))
    (hsplit : ∀ (i : Idx) (H : ℕ),
      ∃ (X : Type) (_ : MetricSpace X)
        (_ : TopologicalSpace.SeparableSpace X) (_ : MeasurableSpace X)
        (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d))
        (R : Response Q)
        (V : ((j : bandSet H) → Y j.1) → X)
        (psi : X → Potential Q)
        (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet H}) → Y j.1) → Potential Q),
        Measurable V ∧
        LipschitzWith 1 psi ∧
        (∀ N : ℕ, H ≤ N →
          Measurable
            (fun z : X × ((j : {j : ℤ // j ∉ bandSet H}) → Y j.1) =>
              R.eval (psi z.1 + tail N z.2))) ∧
        (∀ N : ℕ, H ≤ N →
          ∀ ω : (j : ℤ) → Y j,
            Rf i N ω =
              R.eval
                (psi (V (fun j => ω j.1)) +
                  tail N (fun j => ω j.1))))
    (plus minus : Pol → Idx)
    (hpolar : ∀ (w : Pol) (N : ℕ) (ω : (j : ℤ) → Y j),
      Gpol w N ω =
        (1 / 4 : ℝ) * (Rf (plus w) N ω - Rf (minus w) N ω)) :
    (∀ i : Idx,
      IsCompact (closure (Set.range (fun N : ℕ =>
        ((hmem i N).mono_exponent hpq.le).toLp (Rf i N))))) ∧
    (∃ hpmem : ∀ (w : Pol) (N : ℕ),
        MemLp (Gpol w N) q (Measure.infinitePi laws),
      ∀ w : Pol,
        IsCompact (closure (Set.range (fun N : ℕ =>
          ((hpmem w N).mono_exponent hpq.le).toLp (Gpol w N))))) ∧
    (∃ (phi : ℕ → ℕ), StrictMono phi ∧
      ∃ (Rlim : Idx → ((j : ℤ) → Y j) → ℝ)
        (Glim : Pol → ((j : ℤ) → Y j) → ℝ),
        (∀ i : Idx, MemLp (Rlim i) p (Measure.infinitePi laws)) ∧
        (∀ w : Pol, MemLp (Glim w) p (Measure.infinitePi laws)) ∧
        (∀ i : Idx,
          Tendsto
            (fun N => eLpNorm
              (fun ω => Rf i (phi N) ω - Rlim i ω)
              p (Measure.infinitePi laws))
            atTop (𝓝 0)) ∧
        (∀ w : Pol,
          Tendsto
            (fun N => eLpNorm
              (fun ω => Gpol w (phi N) ω - Glim w ω)
              p (Measure.infinitePi laws))
            atTop (𝓝 0)) ∧
        (∀ i : Idx,
          AEStronglyMeasurable[⨆ H : ℕ, bandSigma Y H]
            (Rlim i) (Measure.infinitePi laws)) ∧
        (∀ w : Pol,
          AEStronglyMeasurable[⨆ H : ℕ, bandSigma Y H]
            (Glim w) (Measure.infinitePi laws))) ∧
    (∀ i : Idx, ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∀ f : ((j : ℤ) → Y j) → ℝ,
        MemLp f p (Measure.infinitePi laws) →
        Tendsto
          (fun N => eLpNorm
            (fun ω => Rf i (ψ N) ω - f ω)
            p (Measure.infinitePi laws))
          atTop (𝓝 0) →
        AEStronglyMeasurable[⨆ H : ℕ, bandSigma Y H]
          f (Measure.infinitePi laws)) ∧
    (∀ w : Pol, ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∀ f : ((j : ℤ) → Y j) → ℝ,
        MemLp f p (Measure.infinitePi laws) →
        Tendsto
          (fun N => eLpNorm
            (fun ω => Gpol w (ψ N) ω - f ω)
            p (Measure.infinitePi laws))
          atTop (𝓝 0) →
        AEStronglyMeasurable[⨆ H : ℕ, bandSigma Y H]
          f (Measure.infinitePi laws)) := by
  classical
  have herr : ∀ i : Idx, Tendsto (fun H : ℕ => Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ)))) atTop (𝓝 0) := by
    intro i
    simpa using ((aux_pow_tendsto_zero ha).const_mul (Cp i * disorder))
  have herr_nonneg : ∀ i (H : ℕ), 0 ≤ Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ))) := by
    intro i H
    exact mul_nonneg (mul_nonneg (hCp i) (le_of_lt hdisorder))
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
  have hfixed : ∀ (i : Idx) (H : ℕ),
      ∃ (c : ℕ → ((j : ℤ) → Y j) → ℝ)
        (cmem : ∀ N, MemLp (c N) p (Measure.infinitePi laws)),
        IsCompact (closure (Set.range (fun N => (cmem N).toLp (c N)))) ∧
        (∀ N, H ≤ N → eLpNorm (fun ω => Rf i N ω - c N ω) p (Measure.infinitePi laws) ≤
            ENNReal.ofReal (Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ))))) ∧
        (∀ N, H ≤ N → AEStronglyMeasurable[bandSigma Y H] (c N) (Measure.infinitePi laws)) := by
    intro i H
    exact aux_fixed_band_compact d Y laws Idx Rf p q hpq hq Kb hKb hmem hmom Cp a disorder
      hsplit i H (fun H N h => hband i H N h)
  choose c cmem hrest using hfixed
  have hcomp_c : ∀ i H, IsCompact (closure (Set.range (fun N => (cmem i H N).toLp (c i H N)))) :=
    fun i H => (hrest i H).1
  have herr_c : ∀ i H N, H ≤ N →
      eLpNorm (fun ω => Rf i N ω - c i H N ω) p (Measure.infinitePi laws) ≤
        ENNReal.ofReal (Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ)))) :=
    fun i H => (hrest i H).2.1
  have hmeas_c : ∀ i H N, H ≤ N →
      AEStronglyMeasurable[bandSigma Y H] (c i H N) (Measure.infinitePi laws) :=
    fun i H => (hrest i H).2.2
  have hR_comp : ∀ i : Idx, IsCompact (closure (Set.range (fun N : ℕ =>
      ((hmem i N).mono_exponent hpq.le).toLp (Rf i N)))) := by
    intro i
    let cc : ℕ → ℕ → ((j : ℤ) → Y j) → ℝ := fun H N => if H ≤ N then c i H N else Rf i N
    have hcc : ∀ H N, MemLp (cc H N) p (Measure.infinitePi laws) := by
      intro H N
      by_cases h : H ≤ N
      · simp only [cc, if_pos h]; exact cmem i H N
      · simp only [cc, if_neg h]; exact (hmem i N).mono_exponent hpq.le
    refine aux_test_approx_compact (f := fun N => Rf i N)
      (hf := fun N => (hmem i N).mono_exponent hpq.le) (c := cc) hcc ?_
      (err := fun H => Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ)))) (herr i) ?_
    · intro H
      have hpiece : IsCompact (closure (Set.range (fun N =>
          if H ≤ N then (cmem i H N).toLp (c i H N)
          else ((hmem i N).mono_exponent hpq.le).toLp (Rf i N)))) :=
        aux_compact_piecewise (fun N => ((hmem i N).mono_exponent hpq.le).toLp (Rf i N))
          (fun N => (cmem i H N).toLp (c i H N)) H (hcomp_c i H)
      refine IsCompact.of_isClosed_subset hpiece isClosed_closure ?_
      apply closure_minimal _ isClosed_closure
      rintro y ⟨N, rfl⟩
      apply subset_closure
      refine ⟨N, ?_⟩
      show (if H ≤ N then (cmem i H N).toLp (c i H N)
          else ((hmem i N).mono_exponent hpq.le).toLp (Rf i N)) = (hcc H N).toLp (cc H N)
      by_cases h : H ≤ N
      · rw [if_pos h]
        apply Lp.ext
        filter_upwards [(hcc H N).coeFn_toLp, (cmem i H N).coeFn_toLp] with ω h1 h2
        rw [h1, h2]
        simp only [cc, if_pos h]
      · rw [if_neg h]
        apply Lp.ext
        filter_upwards [(hcc H N).coeFn_toLp,
          ((hmem i N).mono_exponent hpq.le).coeFn_toLp] with ω h1 h2
        rw [h1, h2]
        simp only [cc, if_neg h]
    · intro H N
      have hcoe : (((((hmem i N).mono_exponent hpq.le).toLp (Rf i N)) -
          ((hcc H N).toLp (cc H N))) : ((j : ℤ) → Y j) → ℝ)
          =ᵐ[Measure.infinitePi laws] (fun ω => Rf i N ω - cc H N ω) := by
        filter_upwards [((hmem i N).mono_exponent hpq.le).coeFn_toLp, (hcc H N).coeFn_toLp]
          with ω h1 h2
        simp only [Pi.sub_apply, h1, h2]
      have hb : eLpNorm (fun ω => Rf i N ω - cc H N ω) p (Measure.infinitePi laws) ≤
          ENNReal.ofReal (Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
        by_cases h : H ≤ N
        · simpa only [cc, if_pos h] using herr_c i H N h
        · simp only [cc, if_neg h]
          rw [show (fun ω => Rf i N ω - Rf i N ω) = (fun _ => (0 : ℝ)) by funext ω; ring]
          simp
      rw [Lp.dist_def, eLpNorm_congr_ae hcoe]
      calc (eLpNorm (fun ω => Rf i N ω - cc H N ω) p (Measure.infinitePi laws)).toReal
          ≤ (ENNReal.ofReal (Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ))))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
        _ = Cp i * disorder * (3 : ℝ) ^ (-(a * (H : ℝ))) := ENNReal.toReal_ofReal (herr_nonneg i H)
  have hpmem : ∀ (w : Pol) (N : ℕ), MemLp (Gpol w N) q (Measure.infinitePi laws) := by
    intro w N
    have hfun : Gpol w N = fun ω => (1 / 4 : ℝ) * (Rf (plus w) N ω - Rf (minus w) N ω) := by
      funext ω; rw [hpolar]
    rw [hfun]
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      ((hmem (plus w) N).sub (hmem (minus w) N)).const_smul (1 / 4 : ℝ)
  have hG_comp : ∀ w : Pol, IsCompact (closure (Set.range (fun N : ℕ =>
      ((hpmem w N).mono_exponent hpq.le).toLp (Gpol w N)))) := by
    intro w
    let Rplus : ℕ → Lp ℝ p (Measure.infinitePi laws) :=
      fun N => ((hmem (plus w) N).mono_exponent hpq.le).toLp (Rf (plus w) N)
    let Rminus : ℕ → Lp ℝ p (Measure.infinitePi laws) :=
      fun N => ((hmem (minus w) N).mono_exponent hpq.le).toLp (Rf (minus w) N)
    let F : Lp ℝ p (Measure.infinitePi laws) × Lp ℝ p (Measure.infinitePi laws) →
        Lp ℝ p (Measure.infinitePi laws) := fun q => (1 / 4 : ℝ) • (q.1 - q.2)
    have hF : Continuous F := continuous_const.smul (continuous_fst.sub continuous_snd)
    let z : ℕ → Lp ℝ p (Measure.infinitePi laws) :=
      fun N => ((hpmem w N).mono_exponent hpq.le).toLp (Gpol w N)
    have hz : ∀ N, z N = F (Rplus N, Rminus N) := by
      intro N
      apply Lp.ext
      filter_upwards [((hpmem w N).mono_exponent hpq.le).coeFn_toLp,
        ((hmem (plus w) N).mono_exponent hpq.le).coeFn_toLp,
        ((hmem (minus w) N).mono_exponent hpq.le).coeFn_toLp,
        Lp.coeFn_smul (1 / 4 : ℝ) (Rplus N - Rminus N),
        Lp.coeFn_sub (Rplus N) (Rminus N)] with ω h1 h2 h3 h4 h5
      simp only [z, F, Rplus, Rminus, h1, h4, h5, h2, h3,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hpolar w N ω]
    have := aux_compact_image_pair Rplus Rminus (hR_comp (plus w)) (hR_comp (minus w)) F hF z hz
    simpa only [z] using this
  obtain ⟨φ, hφ, hlim⟩ := aux_countable_compact_subseq
    (κ := Idx)
    (K := fun i => closure (Set.range (fun N =>
      ((hmem i N).mono_exponent hpq.le).toLp (Rf i N))))
    hR_comp
    (fun i N => ((hmem i N).mono_exponent hpq.le).toLp (Rf i N))
    (fun i N => subset_closure ⟨N, rfl⟩)
  choose x hxlim using hlim
  let Rlim : Idx → ((j : ℤ) → Y j) → ℝ := fun i => x i
  let Glim : Pol → ((j : ℤ) → Y j) → ℝ :=
    fun w => (1 / 4 : ℝ) • (Rlim (plus w) - Rlim (minus w))
  have hRlim : ∀ i : Idx, MemLp (Rlim i) p (Measure.infinitePi laws) :=
    fun i => Lp.memLp (x i)
  have hGlim : ∀ w : Pol, MemLp (Glim w) p (Measure.infinitePi laws) := by
    intro w
    have h : Glim w = (1 / 4 : ℝ) • (Rlim (plus w) - Rlim (minus w)) := rfl
    rw [h]
    exact ((hRlim (plus w)).sub (hRlim (minus w))).const_smul (1 / 4 : ℝ)
  have hc14 : ‖(1 / 4 : ℝ)‖ₑ ≤ 1 := by
    rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    exact (ENNReal.ofReal_le_one).mpr (by norm_num)
  have htend_R : ∀ i : Idx, Tendsto (fun N =>
      eLpNorm (fun ω => Rf i (φ N) ω - Rlim i ω) p (Measure.infinitePi laws)) atTop (𝓝 0) := by
    intro i
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun N => Rf i (φ N))
      (fun N => (hmem i (φ N)).mono_exponent hpq.le) (Rlim i) (hRlim i)).mp
    rw [show ((hRlim i).toLp (Rlim i)) = x i from Lp.toLp_coeFn (x i) (Lp.memLp (x i))]
    exact hxlim i
  have htend_G : ∀ w : Pol, Tendsto (fun N =>
      eLpNorm (fun ω => Gpol w (φ N) ω - Glim w ω) p (Measure.infinitePi laws)) atTop (𝓝 0) := by
    intro w
    have hA := htend_R (plus w)
    have hB := htend_R (minus w)
    have hlimsum : Tendsto (fun N =>
        eLpNorm (fun ω => Rf (plus w) (φ N) ω - Rlim (plus w) ω) p (Measure.infinitePi laws) +
        eLpNorm (fun ω => Rf (minus w) (φ N) ω - Rlim (minus w) ω) p (Measure.infinitePi laws))
        atTop (𝓝 0) := by simpa using hA.add hB
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimsum
      (fun _ => bot_le) ?_
    intro N
    have hpt : (fun ω => Gpol w (φ N) ω - Glim w ω) =
        (1 / 4 : ℝ) • ((fun ω => Rf (plus w) (φ N) ω - Rlim (plus w) ω) +
          (-(fun ω => Rf (minus w) (φ N) ω - Rlim (minus w) ω))) := by
      funext ω
      simp only [Glim, Rlim, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      rw [hpolar w (φ N) ω]
      ring
    change eLpNorm (fun ω => Gpol w (φ N) ω - Glim w ω) p (Measure.infinitePi laws) ≤ _
    rw [hpt]
    exact aux_eLpNorm_smul_add_neg_le hc14 _ _
      (((hmem (plus w) (φ N)).mono_exponent hpq.le).aestronglyMeasurable.sub
        (hRlim (plus w)).aestronglyMeasurable)
      (((hmem (minus w) (φ N)).mono_exponent hpq.le).aestronglyMeasurable.sub
        (hRlim (minus w)).aestronglyMeasurable)
  have hRlim_meas : ∀ i : Idx,
      AEStronglyMeasurable[⨆ H : ℕ, bandSigma Y H] (Rlim i) (Measure.infinitePi laws) := by
    intro i
    exact aux_layer_limit_meas (fun H => bandSigma Y H) bandSigma_mono bandSigma_le
      (fun N => Rf i N) (Rlim i) φ hφ (hRlim i)
      (fun N => (hmem i N).mono_exponent hpq.le) (htend_R i)
      (c i) (fun H N => cmem i H N) (herr i) (fun H N hHN => herr_c i H N hHN)
      (fun H N hHN => hmeas_c i H N hHN)
  have hGlim_meas : ∀ w : Pol,
      AEStronglyMeasurable[⨆ H : ℕ, bandSigma Y H] (Glim w) (Measure.infinitePi laws) := by
    intro w
    have h3 : AEStronglyMeasurable[⨆ H : ℕ, bandSigma Y H]
        (Rlim (plus w) - Rlim (minus w)) (Measure.infinitePi laws) :=
      (hRlim_meas (plus w)).sub (hRlim_meas (minus w))
    have h4 := h3.const_smul (1 / 4 : ℝ)
    convert h4 using 1
  refine ⟨hR_comp, ⟨hpmem, hG_comp⟩,
    ⟨φ, hφ, Rlim, Glim, hRlim, hGlim, htend_R, htend_G, hRlim_meas, hGlim_meas⟩, ?_, ?_⟩
  · intro i ψ hψ f hf hconv
    exact aux_layer_limit_meas (fun H => bandSigma Y H) bandSigma_mono bandSigma_le
      (fun N => Rf i N) f ψ hψ hf (fun N => (hmem i N).mono_exponent hpq.le) hconv
      (c i) (fun H N => cmem i H N) (herr i) (fun H N hHN => herr_c i H N hHN)
      (fun H N hHN => hmeas_c i H N hHN)
  · intro w ψ hψ f hf hconv
    let cG : ℕ → ℕ → ((j : ℤ) → Y j) → ℝ :=
      fun H N => (1 / 4 : ℝ) • (c (plus w) H N - c (minus w) H N)
    have hcG : ∀ H N, MemLp (cG H N) p (Measure.infinitePi laws) := by
      intro H N
      exact ((cmem (plus w) H N).sub (cmem (minus w) H N)).const_smul (1 / 4 : ℝ)
    have herrG : Tendsto (fun H : ℕ =>
        (Cp (plus w) + Cp (minus w)) * disorder * (3 : ℝ) ^ (-(a * (H : ℝ)))) atTop (𝓝 0) := by
      simpa using ((aux_pow_tendsto_zero ha).const_mul ((Cp (plus w) + Cp (minus w)) * disorder))
    have happroxG : ∀ H N, H ≤ N →
        eLpNorm (fun ω => Gpol w N ω - cG H N ω) p (Measure.infinitePi laws) ≤
          ENNReal.ofReal ((Cp (plus w) + Cp (minus w)) * disorder * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
      intro H N hHN
      have hpt : (fun ω => Gpol w N ω - cG H N ω) =
          (1 / 4 : ℝ) • ((fun ω => Rf (plus w) N ω - c (plus w) H N ω) +
            (-(fun ω => Rf (minus w) N ω - c (minus w) H N ω))) := by
        funext ω
        simp only [cG, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        rw [hpolar w N ω]
        ring
      rw [hpt]
      have hb := aux_eLpNorm_smul_add_neg_le
        (p := p) (μ := Measure.infinitePi laws) (c := (1 / 4 : ℝ)) hc14
        (fun ω => Rf (plus w) N ω - c (plus w) H N ω)
        (fun ω => Rf (minus w) N ω - c (minus w) H N ω)
        (((hmem (plus w) N).mono_exponent hpq.le).aestronglyMeasurable.sub
          (cmem (plus w) H N).aestronglyMeasurable)
        (((hmem (minus w) N).mono_exponent hpq.le).aestronglyMeasurable.sub
          (cmem (minus w) H N).aestronglyMeasurable)
      refine hb.trans ?_
      calc
        _ ≤ ENNReal.ofReal (Cp (plus w) * disorder * (3 : ℝ) ^ (-(a * (H : ℝ)))) +
            ENNReal.ofReal (Cp (minus w) * disorder * (3 : ℝ) ^ (-(a * (H : ℝ)))) :=
          add_le_add (herr_c (plus w) H N hHN) (herr_c (minus w) H N hHN)
        _ = ENNReal.ofReal ((Cp (plus w) * disorder * (3 : ℝ) ^ (-(a * (H : ℝ)))) +
            (Cp (minus w) * disorder * (3 : ℝ) ^ (-(a * (H : ℝ))))) :=
          (ENNReal.ofReal_add (herr_nonneg (plus w) H) (herr_nonneg (minus w) H)).symm
        _ = ENNReal.ofReal ((Cp (plus w) + Cp (minus w)) * disorder *
            (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
          congr 1
          ring
    have hmeasG : ∀ H N, H ≤ N →
        AEStronglyMeasurable[bandSigma Y H] (cG H N) (Measure.infinitePi laws) := by
      intro H N hHN
      exact ((hmeas_c (plus w) H N hHN).sub (hmeas_c (minus w) H N hHN)).const_smul (1 / 4 : ℝ)
    exact aux_layer_limit_meas (fun H => bandSigma Y H) bandSigma_mono bandSigma_le
      (fun N => Gpol w N) f ψ hψ hf (fun N => (hpmem w N).mono_exponent hpq.le) hconv
      cG hcG herrG happroxG hmeasG


end
end Paper
