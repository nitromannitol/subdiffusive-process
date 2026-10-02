import SubdiffusiveProcess.Lnorm.JointLpExtraction
import SubdiffusiveProcess.Lnorm.CoercivityNormalization
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Compactness.SequentialCompactness
import SubdiffusiveProcess.Probability.OpNormAdditiveTests
import SubdiffusiveProcess.Probability.OpNormCauchyInProbability
import SubdiffusiveProcess.Sobolev.VolumeResponseOperator
import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
import SubdiffusiveProcess.Paper.killed_inverse_mosco




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Collective compactness of the killed inverses on the good set `{Kc ≤ Mb}` (any index set of
pairs `(N, ω)`), from the `H^{3/4}` coercivity form and the compact `H^{3/4} ⊂ L²` embedding. -/
theorem aux_in_joint_extraction_inprob_compact
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type} (field : Ω → BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (GN : ℕ → Ω → DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hGN : ∀ N ω f, GN N ω f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient M H (field ω) N z hR)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (Kc : ℕ → Ω → ℝ) (good : Ω → Prop)
    (hcoer : ∀ N ω, good ω → ∀ v : killedSobolevGraph (centeredCube z R hR),
      cubeFractionalL2Seminorm hd z R hR threeQuarterOrder
          (fun _ : Fin 1 => (v : SobolevData (centeredCube z R hR)).1) < ⊤ ∧
      cubeFractionalSqNorm hd z R hR threeQuarterOrder
          (v : SobolevData (centeredCube z R hR)).1 ≤
        Kc N ω * sobolevCoefficientForm
          (Lane4.cutoffPositiveCoefficient M H (field ω) N z hR)
          (v : SobolevData (centeredCube z R hR))
          (v : SobolevData (centeredCube z R hR)))
    (Mb : ℝ) :
    IsCompact (closure {y : DomainL2 (centeredCube z R hR) | ∃ (N : ℕ) (ω : Ω), good ω ∧
      Kc N ω ≤ Mb ∧ ∃ f : DomainL2 (centeredCube z R hR), ‖f‖ ≤ 1 ∧ GN N ω f = y}) := by
  classical
  apply SubdiffusiveProcess.isCompact_closure_of_subseq_tendsto
  intro u hu
  choose N ω hgood hK f hf huf using hu
  let V : ℝ := volume.real (centeredCube z R hR : Set (SpatialCoordinates d))
  have hV : 0 < V := centeredCube_volume_pos z hR
  have hK' : 0 < V * max Mb 1 := mul_pos hV (lt_max_of_lt_right one_pos)
  have hcompact := aux_killed_inverse_mosco_compact d hd z R hR S
    (fun n => Lane4.cutoffPositiveCoefficient M H (field (ω n)) (N n) z hR)
    (fun n => GN (N n) (ω n)) (fun n f => hGN (N n) (ω n) f) hInterp
    (V * max Mb 1) hK' (by
      intro n v
      have hv : (v : SobolevData (centeredCube z R hR)) ∈
          killedSobolevGraph (centeredCube z R hR) := by
        rw [← hS]; exact v.2
      have hc := hcoer (N n) (ω n) (hgood n) ⟨(v : SobolevData (centeredCube z R hR)), hv⟩
      refine ⟨hc.1, ?_⟩
      have h1 := SubdiffusiveProcess.Lnorm.fractional_coercivity_unnormalized hd z R hR
        (v : SobolevData (centeredCube z R hR)).1 (Kc (N n) (ω n))
        (sobolevCoefficientForm
          (Lane4.cutoffPositiveCoefficient M H (field (ω n)) (N n) z hR)
          (v : SobolevData (centeredCube z R hR))
          (v : SobolevData (centeredCube z R hR))) hc.2
      refine h1.trans ?_
      have he : 0 ≤ sobolevCoefficientForm
          (Lane4.cutoffPositiveCoefficient M H (field (ω n)) (N n) z hR)
          (v : SobolevData (centeredCube z R hR))
          (v : SobolevData (centeredCube z R hR)) :=
        sobolevCoefficientForm_nonneg _ _
      have hle : V * Kc (N n) (ω n) ≤ V * max Mb 1 :=
        mul_le_mul_of_nonneg_left ((hK n).trans (le_max_left _ _)) hV.le
      simpa only [V, responseForm_apply, sobolevCoefficientForm_apply] using
        mul_le_mul_of_nonneg_right hle he)
  have hmem : ∀ n, u n ∈ closure (⋃ k : ℕ, (GN (N k) (ω k)) ''
      Metric.closedBall (0 : DomainL2 (centeredCube z R hR)) 1) := by
    intro n
    refine subset_closure (Set.mem_iUnion.2 ⟨n, ⟨f n, ?_, huf n⟩⟩)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hf n
  obtain ⟨x, -, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  exact ⟨x, φ, hφ, hlim⟩

/-- Summable-step sequences in a complete pseudo-metric space converge. -/
theorem aux_in_joint_extraction_inprob_tendsto_of_step
    {F : Type*} [PseudoMetricSpace F] [CompleteSpace F] (x : ℕ → F)
    (h : ∀ᶠ k in atTop, dist (x k) (x (k + 1)) < (1 / 2 : ℝ) ^ k) :
    ∃ a, Tendsto x atTop (𝓝 a) := by
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 h
  have hd : ∀ k : ℕ, dist (x (k + k0)) (x (k + 1 + k0)) ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    have h1 := hk0 (k + k0) (by omega)
    have h2 : (1 / 2 : ℝ) ^ (k + k0) ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h3 : k + k0 + 1 = k + 1 + k0 := Nat.add_right_comm _ _ _
    rw [← h3]
    exact (h1.trans_le h2).le
  have hsm : Summable fun k : ℕ => dist (x (k + k0)) (x (k + 1 + k0)) :=
    Summable.of_nonneg_of_le (fun _ => dist_nonneg) hd summable_geometric_two
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_summable_dist (f := fun k : ℕ => x (k + k0)) hsm)
  exact ⟨a, (tendsto_add_atTop_iff_nat (f := x) k0).1 ha⟩

/-- Countably many sequences of random elements, each Cauchy in probability, are simultaneously
almost surely convergent along one common subsequence (Borel–Cantelli; no measurability of the
random elements is needed, all probabilities are outer-measure values). -/
theorem aux_in_joint_extraction_inprob_common_subseq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {F : ℕ → Type*} [∀ i, PseudoMetricSpace (F i)] [∀ i, CompleteSpace (F i)]
    [∀ i, Nonempty (F i)] (X : ∀ i, ℕ → Ω → F i)
    (hcauchy : ∀ i, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
      ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ dist (X i N ω) (X i N' ω)} ≤ ENNReal.ofReal rho) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Xlim : ∀ i, Ω → F i,
      ∀ᵐ ω ∂P, ∀ i, Tendsto (fun k => X i (φ k) ω) atTop (𝓝 (Xlim i ω)) := by
  choose N0 hN0 using fun (i k : ℕ) =>
    hcauchy i ((1 / 2 : ℝ) ^ k) (by positivity) ((1 / 2 : ℝ) ^ k) (by positivity)
  let Mm : ℕ → ℕ := fun k => ∑ i ∈ Finset.range (k + 1), N0 i k
  have hM : ∀ i k : ℕ, i ≤ k → N0 i k ≤ Mm k := fun i k hik =>
    Finset.single_le_sum (f := fun j => N0 j k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
  let φ : ℕ → ℕ := fun k => k + ∑ j ∈ Finset.range (k + 1), Mm j
  have hφ : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    change k + ∑ j ∈ Finset.range (k + 1), Mm j <
      k + 1 + ∑ j ∈ Finset.range (k + 1 + 1), Mm j
    rw [Finset.sum_range_succ _ (k + 1)]
    omega
  have hφM : ∀ k, Mm k ≤ φ k := fun k =>
    (Finset.single_le_sum (f := Mm) (fun _ _ => Nat.zero_le _)
      (Finset.self_mem_range_succ k)).trans (Nat.le_add_left _ _)
  have hφM' : ∀ k, Mm k ≤ φ (k + 1) := fun k =>
    (hφM k).trans (hφ.monotone (Nat.le_succ k))
  have hstep : ∀ i k : ℕ, i ≤ k →
      P {ω | (1 / 2 : ℝ) ^ k ≤ dist (X i (φ k) ω) (X i (φ (k + 1)) ω)} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := fun i k hik =>
    hN0 i k _ _ ((hM i k hik).trans (hφM k)) ((hM i k hik).trans (hφM' k))
  have hae : ∀ i, ∀ᵐ ω ∂P, ∃ a, Tendsto (fun k => X i (φ k) ω) atTop (𝓝 a) := by
    intro i
    let s : ℕ → Set Ω := fun k =>
      {ω | i ≤ k ∧ (1 / 2 : ℝ) ^ k ≤ dist (X i (φ k) ω) (X i (φ (k + 1)) ω)}
    have hs : ∀ k, P (s k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
      intro k
      by_cases hik : i ≤ k
      · exact (measure_mono (fun ω hω => hω.2)).trans (hstep i k hik)
      · have : s k = ∅ := by
          ext ω
          simp only [s, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hik
        rw [this, measure_empty]
        exact zero_le _
    have hsum : ∑' k, P (s k) ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
        ?_ (ENNReal.tsum_le_tsum hs)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_geometric_two]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    refine aux_in_joint_extraction_inprob_tendsto_of_step (fun k => X i (φ k) ω) ?_
    filter_upwards [hω, eventually_ge_atTop i] with k hk hik
    by_contra hcon
    exact hk ⟨hik, not_lt.1 hcon⟩
  rw [← ae_all_iff] at hae
  refine ⟨φ, hφ, fun i ω => limUnder atTop (fun k => X i (φ k) ω), ?_⟩
  filter_upwards [hae] with ω hω i
  exact tendsto_nhds_limUnder (hω i)



theorem aux_in_joint_extraction_inprob_symm
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type} (field : Ω → BilateralField d)
    {z : SpatialCoordinates d} {R : ℝ} (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    {GN : ℕ → Ω → DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR)}
    (hGN : ∀ N ω f, GN N ω f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient M H (field ω) N z hR)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) :
    ∀ N ω (x y : DomainL2 (centeredCube z R hR)),
      ⟪GN N ω x, y⟫_ℝ = ⟪x, GN N ω y⟫_ℝ := by
  intro N ω x y
  rw [hGN N ω x, hGN N ω y, real_inner_comm]
  exact volumeResponse_pairing_symm S
    (Lane4.cutoffPositiveCoefficient M H (field ω) N z hR) y x

/-- **Almost-sure convergence gives Cauchy in probability** in the `ε`–`ρ` outer-measure form. -/
theorem aux_in_joint_extraction_inprob_cauchy_of_tendsto_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (hf : ∀ n, AEMeasurable (f n) P) (hF : AEMeasurable F P)
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (F ω))) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
      P {ω | eps ≤ |f N ω - f N' ω|} ≤ ENNReal.ofReal rho := by
  classical
  set f' : ℕ → Ω → ℝ := fun n => (hf n).mk (f n) with hf'def
  set F' : Ω → ℝ := hF.mk F with hF'def
  have hf'm : ∀ n, Measurable (f' n) := fun n => (hf n).measurable_mk
  have hF'm : Measurable F' := hF.measurable_mk
  have hgood : ∀ᵐ ω ∂P, (∀ n, f n ω = f' n ω) ∧ F ω = F' ω := by
    filter_upwards [ae_all_iff.2 (fun n => (hf n).ae_eq_mk), hF.ae_eq_mk] with ω hall hFω
    exact ⟨hall, hFω⟩
  have h' : ∀ᵐ ω ∂P, Tendsto (fun n => f' n ω) atTop (𝓝 (F' ω)) := by
    filter_upwards [h, hgood] with ω hω hg
    rw [← hg.2]
    exact hω.congr' (Eventually.of_forall fun n => hg.1 n)
  intro eps heps rho hrho
  let U : ℕ → Set Ω := fun n => ⋃ k ∈ Set.Ici n, {ω | eps / 2 ≤ |f' k ω - F' ω|}
  have hUmeas : ∀ n, MeasurableSet (U n) := by
    intro n
    refine MeasurableSet.biUnion (Set.to_countable _) fun k _ => ?_
    have hk : Measurable fun ω => |f' k ω - F' ω| :=
      measurable_norm.comp ((hf'm k).sub hF'm)
    exact measurableSet_le measurable_const (by simpa only [Real.norm_eq_abs] using hk)
  have hUanti : Antitone U := by
    intro m n hmn ω hω
    rcases Set.mem_iUnion₂.1 hω with ⟨k, hk, hkbad⟩
    exact Set.mem_iUnion₂.2 ⟨k, hmn.trans hk, hkbad⟩
  have hUnull : P (⋂ n, U n) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h')
    intro ω hω hconv
    have hω' : ∀ n, ∃ k, n ≤ k ∧ eps / 2 ≤ |f' k ω - F' ω| := by
      intro n
      rcases Set.mem_iInter.1 hω n with hmem
      rcases Set.mem_iUnion₂.1 hmem with ⟨k, hk, hkbad⟩
      exact ⟨k, hk, hkbad⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hconv (eps / 2) (half_pos heps))
    obtain ⟨k, hk, hkbad⟩ := hω' N
    have hlt := hN k hk
    rw [Real.dist_eq] at hlt
    exact absurd hlt (not_lt.2 hkbad)
  have hUfin : ∃ n, P (U n) ≠ ⊤ := ⟨0, measure_ne_top _ _⟩
  have hiInf : (⨅ n, P (U n)) = 0 := by
    rw [← hUanti.measure_iInter (fun n => (hUmeas n).nullMeasurableSet) hUfin]
    exact hUnull
  obtain ⟨N0, hN0⟩ : ∃ N0, P (U N0) < ENNReal.ofReal rho := by
    by_contra hcon
    push_neg at hcon
    have hle : ENNReal.ofReal rho ≤ ⨅ n, P (U n) := le_iInf hcon
    rw [hiInf] at hle
    exact not_le.2 (ENNReal.ofReal_pos.mpr hrho) hle
  refine ⟨N0, fun N N' hN hN' => ?_⟩
  have hbadnull : P {ω | ¬ ((∀ n, f n ω = f' n ω) ∧ F ω = F' ω)} = 0 := ae_iff.1 hgood
  calc P {ω | eps ≤ |f N ω - f N' ω|}
      ≤ P (U N0 ∪ {ω | ¬ ((∀ n, f n ω = f' n ω) ∧ F ω = F' ω)}) := by
        refine measure_mono ?_
        intro ω hω
        by_cases hg : (∀ n, f n ω = f' n ω) ∧ F ω = F' ω
        · refine Set.mem_union_left _ ?_
          have hsum : eps ≤ |f' N ω - F' ω| + |f' N' ω - F' ω| := by
            have htri := abs_sub_le (f' N ω) (F' ω) (f' N' ω)
            rw [abs_sub_comm (F' ω) (f' N' ω)] at htri
            calc eps ≤ |f N ω - f N' ω| := hω
              _ = |f' N ω - f' N' ω| := by rw [hg.1 N, hg.1 N']
              _ ≤ |f' N ω - F' ω| + |f' N' ω - F' ω| := htri
          have hmem : eps / 2 ≤ |f' N ω - F' ω| ∨ eps / 2 ≤ |f' N' ω - F' ω| := by
            by_contra hcon
            push_neg at hcon
            linarith [hcon.1, hcon.2]
          rcases hmem with hcase | hcase
          · exact Set.mem_iUnion₂.2 ⟨N, Set.mem_Ici.2 hN, hcase⟩
          · exact Set.mem_iUnion₂.2 ⟨N', Set.mem_Ici.2 hN', hcase⟩
        · exact Set.mem_union_right _ hg
    _ ≤ P (U N0) + P {ω | ¬ ((∀ n, f n ω = f' n ω) ∧ F ω = F' ω)} := measure_union_le _ _
    _ = P (U N0) := by rw [hbadnull, add_zero]
    _ ≤ ENNReal.ofReal rho := hN0.le

/-- The countable family of quadratic tests `⟨x, G_N ω x⟩` over the sigma-indexed test set. -/
def aux_in_joint_extraction_inprob_tests {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {Ω : Type}
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (D : (i : ℕ) → Set (DomainL2 (centeredCube (z i) (r i) (hr i)))) :
    (Σ i : ℕ, (D i)) → ℕ → Ω → ℝ :=
  fun p n ω => inner ℝ (p.2 : DomainL2 (centeredCube (z p.1) (r p.1) (hr p.1)))
    (GN p.1 n ω (p.2 : DomainL2 (centeredCube (z p.1) (r p.1) (hr p.1))))

/-- **Criterion application for one index.**  On the coercivity event `good`, the killed inverse
`GN i (τ ·)` is Cauchy in probability in operator norm as soon as its quadratic tests on `D i`
are; the operators outside `good` are set to zero and `{0}` is added to the compact set.

The coercivity hypothesis is stated at the *unshifted* index so that it is a syntactic match for
the collective-compactness lemma applied to the unshifted family `GN i`; the shift by `τ` is
transferred inside the proof by an explicit inclusion of the shifted image set. -/
theorem aux_in_joint_extraction_inprob_opcauchy_one
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (D : (i : ℕ) → Set (DomainL2 (centeredCube (z i) (r i) (hr i))))
    [hDcount : ∀ i, Countable (D i)]
    (hDdense : ∀ i, Dense (D i))
    (hDadd : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, x + y ∈ D i)
    (hGN : ∀ i N ω f, GN i N ω f =
      (responseSolution (Sspace i)
        (Lane4.cutoffPositiveCoefficient M H (field ω) N (z i) (hr i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
    (Kc : ℕ → ℕ → Ω → ℝ)
    (good : Ω → Prop) (hgoodnull : P {ω | ¬ good ω} = 0) (i : ℕ) (τ : ℕ → ℕ)
    (hcoercev : ∀ N ω, good ω →
      ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
        cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
        cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
            (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
          Kc i N ω *
            sobolevCoefficientForm
              (Lane4.cutoffPositiveCoefficient M H (field ω) N (z i) (hr i))
              (v : SobolevData (centeredCube (z i) (r i) (hr i)))
              (v : SobolevData (centeredCube (z i) (r i) (hr i))))
    (hS : (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (htight : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N : ℕ,
      P {ω | Mb < Kc i (τ N) ω} ≤ ENNReal.ofReal rho)
    (hquad : ∀ h ∈ D i, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
        ∀ N N', N0 ≤ N → N0 ≤ N' →
          P {ω | eps ≤ |⟪h, GN i (τ N) ω h⟫_ℝ - ⟪h, GN i (τ N') ω h⟫_ℝ|} ≤
            ENNReal.ofReal rho) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
      P {ω | eps ≤ dist (GN i (τ N) ω) (GN i (τ N') ω)} ≤ ENNReal.ofReal rho := by
  classical
  let Gseq : ℕ → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)) := fun N ω => GN i (τ N) ω
  let Gm : ℕ → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)) :=
    fun N ω => if good ω then Gseq N ω else 0
  let Kcseq : ℕ → Ω → ℝ := fun N ω => Kc i (τ N) ω
  have hGm_good : ∀ N ω, good ω → Gm N ω = Gseq N ω := by
    intro N ω hg
    show (if good ω then Gseq N ω else 0) = Gseq N ω
    rw [if_pos hg]
  have hGm_bad : ∀ N ω, ¬ good ω → Gm N ω = 0 := by
    intro N ω hg
    show (if good ω then Gseq N ω else 0) = 0
    rw [if_neg hg]
  have hGm_good_pt : ∀ N ω, good ω →
      ∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)), Gm N ω x = Gseq N ω x := by
    intro N ω hg x
    rw [hGm_good N ω hg]
  have hGm_bad_pt : ∀ N ω, ¬ good ω →
      ∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)), Gm N ω x = 0 := by
    intro N ω hg x
    rw [hGm_bad N ω hg]
    exact ContinuousLinearMap.zero_apply x
  have hs := aux_in_joint_extraction_inprob_symm d hd M H field (hr i) (Sspace i)
    (GN := GN i) (hGN := hGN i)
  have hsymm : ∀ N ω (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      ⟪Gm N ω x, y⟫_ℝ = ⟪x, Gm N ω y⟫_ℝ := by
    intro N ω x y
    by_cases hg : good ω
    · rw [hGm_good_pt N ω hg x, hGm_good_pt N ω hg y]
      exact hs (τ N) ω x y
    · rw [hGm_bad_pt N ω hg x, hGm_bad_pt N ω hg y]
      simp only [inner_zero_left, inner_zero_right]
  have hcomp' : ∀ Mb : ℝ, ∃ C : Set (DomainL2 (centeredCube (z i) (r i) (hr i))),
      IsCompact C ∧ ∀ N ω, Kcseq N ω ≤ Mb →
        ∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)), ‖x‖ ≤ 1 → Gm N ω x ∈ C := by
    intro Mb
    have hcc := aux_in_joint_extraction_inprob_compact d hd hInterp M H field (z i) (r i) (hr i)
      (Sspace i) hS (GN i) (hGN i) (Kc i) good hcoercev Mb
    let B : Set (DomainL2 (centeredCube (z i) (r i) (hr i))) :=
      closure {y : DomainL2 (centeredCube (z i) (r i) (hr i)) |
        ∃ (N : ℕ) (ω : Ω), good ω ∧ Kc i N ω ≤ Mb ∧
          ∃ f : DomainL2 (centeredCube (z i) (r i) (hr i)), ‖f‖ ≤ 1 ∧ GN i N ω f = y}
    refine ⟨B ∪ {0}, hcc.union isCompact_singleton, ?_⟩
    intro N ω hK x hx
    by_cases hg : good ω
    · refine Or.inl (subset_closure ⟨τ N, ω, hg, hK, x, hx, ?_⟩)
      exact (hGm_good_pt N ω hg x).symm
    · refine Or.inr ?_
      simpa only [Set.mem_singleton_iff] using hGm_bad_pt N ω hg x
  have hquadm : ∀ h ∈ D i, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
      ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ |⟪h, Gm N ω h⟫_ℝ - ⟪h, Gm N' ω h⟫_ℝ|} ≤ ENNReal.ofReal rho := by
    intro h hh eps heps rho hrho
    obtain ⟨N0, hN0⟩ := hquad h hh eps heps rho hrho
    refine ⟨N0, fun N N' hN hN' => ?_⟩
    have hsub : {ω | eps ≤ |⟪h, Gm N ω h⟫_ℝ - ⟪h, Gm N' ω h⟫_ℝ|} ⊆
        {ω | eps ≤ |⟪h, GN i (τ N) ω h⟫_ℝ - ⟪h, GN i (τ N') ω h⟫_ℝ|} ∪
          {ω | ¬ good ω} := by
      intro ω hω
      by_cases hg : good ω
      · refine Or.inl ?_
        show eps ≤ |⟪h, GN i (τ N) ω h⟫_ℝ - ⟪h, GN i (τ N') ω h⟫_ℝ|
        have hω' : eps ≤ |⟪h, (Gm N ω) h⟫_ℝ - ⟪h, (Gm N' ω) h⟫_ℝ| := hω
        rw [hGm_good_pt N ω hg h, hGm_good_pt N' ω hg h] at hω'
        exact hω'
      · exact Or.inr hg
    calc P {ω | eps ≤ |⟪h, Gm N ω h⟫_ℝ - ⟪h, Gm N' ω h⟫_ℝ|}
        ≤ P ({ω | eps ≤ |⟪h, GN i (τ N) ω h⟫_ℝ - ⟪h, GN i (τ N') ω h⟫_ℝ|} ∪
            {ω | ¬ good ω}) := measure_mono hsub
      _ ≤ P {ω | eps ≤ |⟪h, GN i (τ N) ω h⟫_ℝ - ⟪h, GN i (τ N') ω h⟫_ℝ|} +
            P {ω | ¬ good ω} := measure_union_le _ _
      _ = P {ω | eps ≤ |⟪h, GN i (τ N) ω h⟫_ℝ - ⟪h, GN i (τ N') ω h⟫_ℝ|} := by
            rw [hgoodnull, add_zero]
      _ ≤ ENNReal.ofReal rho := hN0 N N' hN hN'
  intro eps heps rho hrho
  have hop' := SubdiffusiveProcess.Probability.opNorm_cauchy_in_probability_of_additive_dense_tests
    P Gm hsymm Kcseq htight hcomp' (D i) (hDdense i) (hDadd i) hquadm
  obtain ⟨N0, hN0⟩ := hop' eps heps rho hrho
  refine ⟨N0, fun N N' hN hN' => ?_⟩
  have hsub : {ω | eps ≤ ‖GN i (τ N) ω - GN i (τ N') ω‖} ⊆
      {ω | eps ≤ ‖Gm N ω - Gm N' ω‖} ∪ {ω | ¬ good ω} := by
    intro ω hω
    by_cases hg : good ω
    · refine Or.inl ?_
      show eps ≤ ‖Gm N ω - Gm N' ω‖
      rw [hGm_good N ω hg, hGm_good N' ω hg]
      exact hω
    · exact Or.inr hg
  calc P {ω | eps ≤ ‖GN i (τ N) ω - GN i (τ N') ω‖}
      ≤ P ({ω | eps ≤ ‖Gm N ω - Gm N' ω‖} ∪ {ω | ¬ good ω}) := measure_mono hsub
    _ ≤ P {ω | eps ≤ ‖Gm N ω - Gm N' ω‖} + P {ω | ¬ good ω} := measure_union_le _ _
    _ = P {ω | eps ≤ ‖Gm N ω - Gm N' ω‖} := by rw [hgoodnull, add_zero]
    _ ≤ ENNReal.ofReal rho := hN0 N N' hN hN'

/-- **Operator-norm Cauchy extraction.**  From the frozen data one gets refined subsequences
`NE0 ∘ τE`, `NF0 ∘ τF` along which every killed inverse is Cauchy in probability in operator
norm. -/
theorem aux_in_joint_extraction_inprob_opcauchy
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (D : (i : ℕ) → Set (DomainL2 (centeredCube (z i) (r i) (hr i))))
    [hDcount : ∀ i, Countable (D i)]
    (hDdense : ∀ i, Dense (D i))
    (hDadd : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, x + y ∈ D i)
    (hGN : ∀ i N ω f, GN i N ω f =
      (responseSolution (Sspace i)
        (Lane4.cutoffPositiveCoefficient M H (field ω) N (z i) (hr i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
    (Kc : ℕ → ℕ → Ω → ℝ)
    (hcoer : ∀ i N, ∀ᵐ ω ∂P,
      ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
        cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
        cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
            (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
          Kc i N ω *
            sobolevCoefficientForm
              (Lane4.cutoffPositiveCoefficient M H (field ω) N (z i) (hr i))
              (v : SobolevData (centeredCube (z i) (r i) (hr i)))
              (v : SobolevData (centeredCube (z i) (r i) (hr i))))
    (htight : ∀ i, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
      P {ω | Mb < Kc i N ω} ≤ ENNReal.ofReal rho)
    (hmem : ∀ i (x : D i) n,
      MemLp (fun ω => inner ℝ (x : DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GN i n ω x)) 1 P)
    (hcompact : ∀ i (x : D i), IsCompact (closure (Set.range (fun n =>
      (hmem i x n).toLp (fun ω => inner ℝ
        (x : DomainL2 (centeredCube (z i) (r i) (hr i))) (GN i n ω x))))))
    (hprob : IsProbabilityMeasure P)
    (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (NE0 NF0 : ℕ → ℕ) (hNE0 : StrictMono NE0) (hNF0 : StrictMono NF0) :
    ∃ τE τF : ℕ → ℕ, StrictMono τE ∧ StrictMono τF ∧
      (∀ i, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ dist (GN i (NE0 (τE N)) ω) (GN i (NE0 (τE N')) ω)} ≤
          ENNReal.ofReal rho) ∧
      (∀ i, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ dist (GN i (NF0 (τF N)) ω) (GN i (NF0 (τF N')) ω)} ≤
          ENNReal.ofReal rho) := by
  classical
  haveI := hprob
  let good : Ω → Prop := fun ω => ∀ i N,
    ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
      cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
          (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
      cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
          (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
        Kc i N ω *
          sobolevCoefficientForm
            (Lane4.cutoffPositiveCoefficient M H (field ω) N (z i) (hr i))
            (v : SobolevData (centeredCube (z i) (r i) (hr i)))
            (v : SobolevData (centeredCube (z i) (r i) (hr i)))
  have hgoodEv : ∀ᵐ ω ∂P, good ω := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro N
    exact hcoer i N
  have hgoodnull : P {ω | ¬ good ω} = 0 := ae_iff.1 hgoodEv
  have hne : Nonempty (Σ i : ℕ, (D i)) := by
    haveI : Nonempty (DomainL2 (centeredCube (z 0) (r 0) (hr 0))) := ⟨0⟩
    have h0 : (D 0).Nonempty := (hDdense 0).nonempty
    exact ⟨⟨0, ⟨Classical.choose h0, Classical.choose_spec h0⟩⟩⟩
  let X : (Σ i : ℕ, (D i)) → ℕ → Ω → ℝ := aux_in_joint_extraction_inprob_tests z r hr GN D
  have hXmem : ∀ p n, MemLp (X p n) 1 P := fun p n => hmem p.1 p.2 n
  have hXcompact : ∀ p, IsCompact (closure (Set.range (fun n => (hXmem p n).toLp (X p n)))) :=
    fun p => hcompact p.1 p.2
  obtain ⟨τE, hτE, LE, hLE⟩ :=
    SubdiffusiveProcess.Lnorm.ae_subseq_of_countable_l1_compact_index P X hXmem hXcompact
      NE0 hNE0
  obtain ⟨τF, hτF, LF, hLF⟩ :=
    SubdiffusiveProcess.Lnorm.ae_subseq_of_countable_l1_compact_index P X hXmem hXcompact
      NF0 hNF0
  have hquadOf : ∀ (τ : ℕ → ℕ) (L : (Σ i : ℕ, (D i)) → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ p, Tendsto (fun n => X p (τ n) ω) atTop (𝓝 (L p ω))) →
      ∀ i, ∀ h ∈ D i, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
        ∀ N N', N0 ≤ N → N0 ≤ N' →
          P {ω | eps ≤ |⟪h, GN i (τ N) ω h⟫_ℝ - ⟪h, GN i (τ N') ω h⟫_ℝ|} ≤
            ENNReal.ofReal rho := by
    intro τ L hL i h hh eps heps rho hrho
    let fseq : ℕ → Ω → ℝ := fun n ω => X ⟨i, ⟨h, hh⟩⟩ (τ n) ω
    have hfseq : ∀ n, AEMeasurable (fseq n) P := fun n =>
      (hXmem ⟨i, ⟨h, hh⟩⟩ (τ n)).aemeasurable
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => fseq n ω) atTop (𝓝 (L ⟨i, ⟨h, hh⟩⟩ ω)) := by
      filter_upwards [hL] with ω hω
      exact hω ⟨i, ⟨h, hh⟩⟩
    have hLp : AEMeasurable (L ⟨i, ⟨h, hh⟩⟩) P :=
      aemeasurable_of_tendsto_metrizable_ae (u := atTop) hfseq hlim
    have hcauchy := aux_in_joint_extraction_inprob_cauchy_of_tendsto_ae P hfseq hLp hlim
    exact hcauchy eps heps rho hrho
  have hmain : ∀ (τ : ℕ → ℕ) (L : (Σ i : ℕ, (D i)) → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ p, Tendsto (fun n => X p (τ n) ω) atTop (𝓝 (L p ω))) →
      ∀ i, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ dist (GN i (τ N) ω) (GN i (τ N') ω)} ≤ ENNReal.ofReal rho := by
    intro τ L hL i eps heps rho hrho
    have hquad := hquadOf τ L hL i
    exact aux_in_joint_extraction_inprob_opcauchy_one d hd hInterp M H Ω P field z r hr Sspace
      GN D hDdense hDadd hGN Kc good hgoodnull i τ (fun N ω hg v => hg i N v) (hS i)
      (fun rho hrho => (htight i rho hrho).imp fun Mb hMb N => hMb (τ N)) hquad
      eps heps rho hrho
  refine ⟨τE, τF, hτE, hτF, ?_, ?_⟩
  · exact fun i => hmain (fun n => NE0 (τE n)) LE hLE i
  · exact fun i => hmain (fun n => NF0 (τF n)) LF hLF i



theorem in_joint_extraction_inprob
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (D : (i : ℕ) → Set (DomainL2 (centeredCube (z i) (r i) (hr i))))
    [hDcount : ∀ i, Countable (D i)]
    (hDdense : ∀ i, Dense (D i))
    (hDadd : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, x + y ∈ D i)
    (hGN : ∀ i N ω f, GN i N ω f =
      (responseSolution (Sspace i)
        (Lane4.cutoffPositiveCoefficient M H (field ω) N (z i) (hr i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
    (Kc : ℕ → ℕ → Ω → ℝ)
    (hcoer : ∀ i N, ∀ᵐ ω ∂P,
      ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
        cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
        cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
            (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
          Kc i N ω *
            sobolevCoefficientForm
              (Lane4.cutoffPositiveCoefficient M H (field ω) N (z i) (hr i))
              (v : SobolevData (centeredCube (z i) (r i) (hr i)))
              (v : SobolevData (centeredCube (z i) (r i) (hr i))))
    (htight : ∀ i, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
      P {ω | Mb < Kc i N ω} ≤ ENNReal.ofReal rho)
    (hmem : ∀ i (x : D i) n,
      MemLp (fun ω => inner ℝ (x : DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GN i n ω x)) 1 P)
    (hcompact : ∀ i (x : D i), IsCompact (closure (Set.range (fun n =>
      (hmem i x n).toLp (fun ω => inner ℝ
        (x : DomainL2 (centeredCube (z i) (r i) (hr i))) (GN i n ω x))))))
    (hprob : IsProbabilityMeasure P)
    (hfield : Measurable field)
    (hmap : Measure.map field P = (chaosSampleLaw M).toMeasure)
    (hH : InfraredCharacterization M H)
    (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (NE0 NF0 : ℕ → ℕ) (hNE0 : StrictMono NE0) (hNF0 : StrictMono NF0) :
    ∃ NE NF : ℕ → ℕ,
      ∃ GE GF : (i : ℕ) → Ω →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)),
      StrictMono NE ∧ StrictMono NF ∧
      in_joint_extracted_candidates d M H Ω P field z r hr Sspace
        (fun i N ω => GN i N ω) GE GF NE NF ∧
      (∃ δE δF : ℕ → ℕ, StrictMono δE ∧ StrictMono δF ∧ NE = NE0 ∘ δE ∧ NF = NF0 ∘ δF) := by
  classical
  haveI := hprob
  obtain ⟨τE, τF, hτE, hτF, hcauchyE, hcauchyF⟩ :=
    aux_in_joint_extraction_inprob_opcauchy d hd hInterp M H Ω P field z r hr Sspace GN D
      hDdense hDadd hGN Kc hcoer htight hmem hcompact hprob hS NE0 NF0 hNE0 hNF0
  obtain ⟨φE, hφE, GEm, hGEm⟩ :=
    aux_in_joint_extraction_inprob_common_subseq P
      (fun i N ω => GN i (NE0 (τE N)) ω)
      (fun i => hcauchyE i)
  obtain ⟨φF, hφF, GFm, hGFm⟩ :=
    aux_in_joint_extraction_inprob_common_subseq P
      (fun i N ω => GN i (NF0 (τF N)) ω)
      (fun i => hcauchyF i)
  refine ⟨fun n => NE0 (τE (φE n)), fun n => NF0 (τF (φF n)), GEm, GFm, ?_, ?_, ?_, ?_⟩
  · exact hNE0.comp (hτE.comp hφE)
  · exact hNF0.comp (hτF.comp hφF)
  · refine ⟨hprob, hfield, hmap, hH, ⟨hNE0.comp (hτE.comp hφE),
      hNF0.comp (hτF.comp hφF)⟩, hS, hGN, ?_⟩
    filter_upwards [hGEm, hGFm] with ω hEω hFω i
    exact ⟨hEω i, hFω i⟩
  · exact ⟨τE.comp φE, τF.comp φF, hτE.comp hφE, hτF.comp hφF, rfl, rfl⟩

end Paper
