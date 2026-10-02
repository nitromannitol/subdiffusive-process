import SubdiffusiveProcess.Paper.in_represented_bounds_seq_collar_family
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper

/-- A function vanishing on a positive collar has compact support inside the cube. -/
theorem aux_in_represented_bounds_seq_collar_uniform_support
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (f : SpatialCoordinates d → ℝ) (r : ℝ) (hr : 0 < r)
    (hf : ∀ x, Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r → f x = 0) :
    HasCompactSupport f ∧ tsupport f ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  have hclosed : IsClosed {x : SpatialCoordinates d | r ≤ Metric.infDist x Qᶜ} :=
    isClosed_le continuous_const (Metric.continuous_infDist_pt Qᶜ)
  have hsupp : Function.support f ⊆ {x | r ≤ Metric.infDist x Qᶜ} := by
    intro x hx
    by_contra h
    exact hx (hf x (le_of_lt (lt_of_not_ge h)))
  have htsupp := closure_minimal hsupp hclosed
  have hQ : tsupport f ⊆ Q := by
    intro x hx
    have hpos : 0 < Metric.infDist x Qᶜ := hr.trans_le (htsupp hx)
    by_contra hnot
    have hz : Metric.infDist x Qᶜ = 0 := Metric.infDist_zero_of_mem hnot
    exact (ne_of_gt hpos) hz
  exact ⟨HasCompactSupport.of_support_subset_isCompact
    ((centeredCube_isBounded z hR).isCompact_closure)
    ((subset_tsupport f).trans (hQ.trans subset_closure)), hQ⟩

/-- Joint represented collar family: one almost-sure event, a common energy constant
for all mesh levels and cutoffs, and a cutoff-uniform Holder constant at each level. -/
theorem in_represented_bounds_seq_collar_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ)
    (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ
      (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey :
      ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented :
      Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (hext : InfraredCharacterization M H → aux_lem_cutoffs_root_uniform_extrema d M H eta)
    (hseed : ∀ k : ℕ, ∃ b : T j0, (thetaH1 j0 b).toFun =
      bufferedCollarProfile d (z j0) (rad j0) (rad j0 / (10 * (3 : ℝ) ^ k))) :
    ∃ Ggood : Set Ω, MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P Ggoodᶜ = 0 ∧
      ∀ omega ∈ Ggood, ∃ Kenergy : ℝ, 0 ≤ Kenergy ∧
        ∃ w : ℕ → ℕ → H10Function
          (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
        ∀ k,
      ∃ Kchi : ℝ, 0 ≤ Kchi ∧ ∀ n,
        ContinuousOn (w k n).toH1Function.toFun
          (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))) ∧
        Lane4.IsHolderOn alpha
          (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
          (w k n).toH1Function.toFun ∧
        Lane4.cAlphaNorm alpha
          (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
          (w k n).toH1Function.toFun ≤ Kchi ∧
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          0 ≤ (w k n).toH1Function.toFun x ∧ (w k n).toH1Function.toFun x ≤ 1) ∧
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ ≤ (rad j0 / (10 * (3 : ℝ) ^ k)) →
            (w k n).toH1Function.toFun x = 0) ∧
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          3 * (rad j0 / (10 * (3 : ℝ) ^ k)) ≤ Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ →
            (w k n).toH1Function.toFun x = 1) ∧
        energy (cutoffCoefficient M H (env n omega) (cutoff n))
          (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) (w k n).toH1Function ≤
          Kenergy * (rad j0 / (10 * (3 : ℝ) ^ k)) ^ (-1 - eta) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hR : 0 < rad j0 := hrad j0
  obtain ⟨Cgrad, hCgrad, hprofile⟩ := aux_buffered_collar_profile_uniform d hd (z j0) (rad j0) (hrad j0)
  have hfields := aux_lem_cutoffs_root_uniform_represented_fields d hd M H Ω P cutoff env J j0 z rad
    hrad S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim
    constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented
  obtain ⟨Csum, hCsum, κ, hκ, g0, hg0root, hg0origin, jc, hjc, mlow, mhigh, KN, Ggood,
    hGm, hGsub, hGnull, hKNmeas, hKN1, hKNbd, hgrid, hcoarse, hextrema⟩ :=
    aux_lem_cutoffs_root_uniform_majorant_data d hd beta alpha eta t hrepresented.2.2.1.1
      hrepresented.2.2.1.2 hrepresented.2.1.1 hrepresented.2.1.2.1
      hrepresented.1.1 hrepresented.1.2 hrepresented.2.1.2.2 orders hrepresented.2.2.2.2.1
      Cext Cgrad hrepresented.2.2.2.1 hCgrad M H hext Ω P cutoff env J j0 z rad hrad S D f T theta
      thetaH1 usrc srcRep ucell E Index resp respLim constants G coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
      Grid origin gridRoot gridKey hfields
  refine ⟨Ggood, hGm, hGsub, hGnull, ?_⟩
  intro omega homega
  obtain ⟨Kstar, hKstar⟩ := hKNbd omega homega
  have hKbound : ∀ n, KN n omega ≤ Kstar := fun n => hKstar ⟨n, rfl⟩
  have hKstar0 : 0 ≤ Kstar := (zero_le_one.trans (hKN1 0 omega)).trans (hKbound 0)
  let Ccollar : ℝ := (d : ℝ) * 148 *
    (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2) *
    (rad j0) ^ (d - 1) * (10 / 243 : ℝ) ^ (-1 - eta)
  have hCext : 0 < Cext := hrepresented.2.2.2.1
  have hCcollar : 0 ≤ Ccollar := by dsimp [Ccollar]; positivity
  have hper (k : ℕ) :
    ∃ w : ℕ → H10Function (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      ∃ Kchi : ℝ, 0 ≤ Kchi ∧ ∀ n,
        ContinuousOn (w n).toH1Function.toFun
          (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))) ∧
        Lane4.IsHolderOn alpha
          (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
          (w n).toH1Function.toFun ∧
        Lane4.cAlphaNorm alpha
          (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
          (w n).toH1Function.toFun ≤ Kchi ∧
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          0 ≤ (w n).toH1Function.toFun x ∧ (w n).toH1Function.toFun x ≤ 1) ∧
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ ≤ (rad j0 / (10 * (3 : ℝ) ^ k)) →
            (w n).toH1Function.toFun x = 0) ∧
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          3 * (rad j0 / (10 * (3 : ℝ) ^ k)) ≤ Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ →
            (w n).toH1Function.toFun x = 1) ∧
        energy (cutoffCoefficient M H (env n omega) (cutoff n))
          (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) (w n).toH1Function ≤
          ((d : ℝ) * 148 * (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2) *
            (rad j0) ^ (d - 1) * (10 / 243 : ℝ) ^ (-1 - eta)) * (KN n omega) * (rad j0 / (10 * (3 : ℝ) ^ k)) ^ (-1 - eta) := by
    obtain ⟨b, hb⟩ := hseed k
    let r := rad j0 / (10 * (3 : ℝ) ^ k)
    have hr : 0 < r := by dsimp [r]; positivity
    have hrsmall : r < rad j0 / 2 := by
      have hp : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      dsimp [r]
      apply (div_lt_div_iff_of_pos_left hR (by positivity) (by norm_num)).2
      nlinarith
    obtain ⟨hsmooth, hrange, hzero, hone, hgradzero, hgrad⟩ := hprofile r hr hrsmall
    have hdata : HasCompactSupport (thetaH1 j0 b).toFun ∧
        tsupport (thetaH1 j0 b).toFun ⊆
          (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) := by
      rw [hb]
      exact aux_in_represented_bounds_seq_collar_uniform_support (z j0) (rad j0) (hrad j0) _
        (3 * r / 2) (by positivity) hzero
    exact in_represented_bounds_seq_collar_family d hd M H Cext beta alpha eta t orders Ω P cutoff env J
      j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G coercivityKey
      extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
      cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented Cgrad hCgrad κ hκ g0
      ⟨hg0root, hg0origin⟩ omega (hGsub homega) (fun n => KN n omega)
      (fun n => zero_le_one.trans (hKN1 n omega)) (hgrid omega homega)
      (fun n => mhigh (cutoff n) (env n omega))
      (fun n x hx => (hextrema omega homega n).2.1 x hx |>.2)
      (fun n => (hextrema omega homega n).2.2.1) k r rfl (jc (k + 5))
      (fun q => (hjc (k + 5) q).1) (fun q => (hjc (k + 5) q).2)
      (fun n q => hcoarse omega homega n (k + 5) q) b
      (by simpa only [hb] using hsmooth) hdata.1 hdata.2
      (by simpa only [hb] using hrange)
      (fun x _ hx => by rw [hb]; exact hzero x hx)
      (fun x _ hx => by rw [hb]; exact hone x hx)
      (by simpa only [hb] using hgrad)
  choose w Kchi hKchi hw using hper
  refine ⟨Ccollar * Kstar, mul_nonneg hCcollar hKstar0, w, fun k => ⟨Kchi k, hKchi k, fun n => ?_⟩⟩
  rcases hw k n with ⟨hc, hh, hn, hv, hz, ho, he⟩
  refine ⟨hc, hh, hn, hv, hz, ho, he.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hKbound n) hCcollar)
    (Real.rpow_nonneg (by positivity) _)

end Paper