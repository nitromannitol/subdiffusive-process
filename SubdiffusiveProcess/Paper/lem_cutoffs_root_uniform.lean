import SubdiffusiveProcess.Paper.lem_cutoffs
import SubdiffusiveProcess.Paper.lem_cutoffs_damped_extrema_uniform
import SubdiffusiveProcess.Paper.conv_represented_estimates
import SubdiffusiveProcess.CutoffsCommonMajorant
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.CutoffsOddCatalogue
import SubdiffusiveProcess.CutoffsUniformCollarSum

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Majorant for the damped extrema along the represented sequence (Borel--Cantelli), specialized
from `aux_cutoffs_common_majorant_core` to `q = 1` and no moment orders. -/
theorem aux_lem_cutoffs_root_uniform_KN
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω Index : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (nu : Measure (BilateralField d)) (cutoff : ℕ → ℕ) (hcut : StrictMono cutoff)
    (env : ℕ → Ω → BilateralField d) (henv : ∀ n, Measurable (env n))
    (hlaw : ∀ n, Measure.map (env n) P = nu)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω) (hG : P Gᶜ = 0)
    (hcm : ∀ i n, Measurable (constants i n))
    (hbdd : ∀ i : Index, ∀ om ∈ G, ∃ Mb : ℝ, ∀ N : ℕ, |constants i N om| ≤ Mb)
    (F : Finset Index) (eta : ℝ) (heta : 0 < eta)
    (good : ℕ → BilateralField d → Prop) (hgood : ∀ᵐ b ∂nu, ∀ N, good N b)
    (mlow mhigh : ℕ → BilateralField d → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hXmem : ∀ N : ℕ, MemLp (fun b => (3 : ℝ) ^ (-((N : ℝ) * eta)) * (mhigh N b + (mlow N b)⁻¹))
      1 nu)
    (hXbd : ∀ N : ℕ, eLpNorm (fun b => (3 : ℝ) ^ (-((N : ℝ) * eta)) * (mhigh N b + (mlow N b)⁻¹))
      1 nu ≤ ENNReal.ofReal (A * Real.exp (-(eta * Real.log 3 / 2)) ^ N)) :
    ∃ KN : ℕ → Ω → ℝ, ∃ Ggood : Set Ω,
      MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
      (∀ n : ℕ, Measurable (KN n)) ∧ (∀ n : ℕ, ∀ om : Ω, 1 ≤ KN n om) ∧
      (∀ om ∈ Ggood, BddAbove (Set.range (fun n : ℕ => KN n om))) ∧
      (∀ om ∈ Ggood, ∀ n : ℕ, ∀ i ∈ F, constants i n om ≤ KN n om) ∧
      (∀ om ∈ Ggood, ∀ n : ℕ, (∀ N, good N (env n om)) ∧
        (3 : ℝ) ^ (-((cutoff n : ℝ) * eta)) *
          (mhigh (cutoff n) (env n om) + (mlow (cutoff n) (env n om))⁻¹) ≤ KN n om) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨KN, Ggood, h1, h2, h3, h4, h5, -, h7, h8, h9⟩ :=
    aux_cutoffs_common_majorant_core P nu cutoff hcut env henv hlaw constants G hG hcm ∅
      (fun i p hp => absurd hp (Finset.notMem_empty p)) hbdd F good hgood
      (fun N b => (3 : ℝ) ^ (-((N : ℝ) * eta)) * (mhigh N b + (mlow N b)⁻¹)) 1 le_rfl
      (fun p hp => absurd hp (Finset.notMem_empty p)) A
      (Real.exp (-(eta * Real.log 3 / 2))) hA (Real.exp_pos _).le
      ((Real.exp_lt_exp.2 (by have := mul_pos heta hlog3; linarith)).trans_eq Real.exp_zero)
      (fun N => by simpa using hXmem N) (fun N => by simpa using hXbd N)
  exact ⟨KN, Ggood, h1, h2, h3, h4, h5, h7, h8, h9⟩

/-- Algebra: the damped bound gives the two-sided bound on the extrema. -/
theorem aux_lem_cutoffs_root_uniform_extrema_bound (lo hi K eta cutN : ℝ) (heta : 0 < eta)
    (hlow : 0 < lo) (hle : lo ≤ hi)
    (hX : (3 : ℝ) ^ (-(cutN * eta)) * (hi + lo⁻¹) ≤ K) :
    hi ≤ K * (3 : ℝ) ^ (cutN * eta) ∧ lo⁻¹ ≤ K * (3 : ℝ) ^ (cutN * eta) := by
  have hpos : 0 < (3 : ℝ) ^ (cutN * eta) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv_pos : 0 < lo⁻¹ := inv_pos.2 hlow
  have hhi : 0 ≤ hi := (hlow.trans_le hle).le
  have hX' : hi + lo⁻¹ ≤ K * (3 : ℝ) ^ (cutN * eta) := by
    have h : ((3 : ℝ) ^ (cutN * eta))⁻¹ * (hi + lo⁻¹) ≤ K := by
      rw [← Real.rpow_neg (by norm_num)]; exact hX
    rw [inv_mul_le_iff₀ hpos] at h
    rw [mul_comm]; exact h
  exact ⟨by linarith, by linarith⟩



def aux_lem_cutoffs_root_uniform_extrema
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (eta : ℝ) : Prop :=
        ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        ∃ A : ℝ, 0 ≤ A ∧
        ∃ mlow mhigh : ℕ → BilateralField d → ℝ,
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < mlow N om ∧
              ∀ x ∈ (closedCube z0 R hR : Set (SpatialCoordinates d)),
                mlow N om ≤ cutoffCoefficient M H om N x ∧
                  cutoffCoefficient M H om N x ≤ mhigh N om) ∧
          (∀ N : ℕ, MemLp (fun om => (3 : ℝ) ^ (-((N : ℝ) * eta)) *
              (mhigh N om + (mlow N om)⁻¹)) 1 (chaosSampleLaw M).toMeasure) ∧
          (∀ N : ℕ, eLpNorm (fun om => (3 : ℝ) ^ (-((N : ℝ) * eta)) *
              (mhigh N om + (mlow N om)⁻¹)) 1 (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (A * Real.exp (-(eta * Real.log 3 / 2)) ^ N))

/-! The following projection is deliberately isolated from the collar proof.
The source predicate is a large conjunction; destructing it once here keeps
its normalization cost out of the majorant and collar construction. -/
theorem aux_lem_cutoffs_root_uniform_represented_fields
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [_hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [_hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j → Homogenization.H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ) (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented : Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
      S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim
      constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
      sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey) :
    StrictMono cutoff ∧ InfraredCharacterization M H ∧
      (∀ n : ℕ, Measurable (env n)) ∧
      (∀ n : ℕ, Measure.map (env n) P = (chaosSampleLaw M).toMeasure) ∧
      Paper.conv_represented_sequence P resp respLim constants G ∧
      (∀ (j : J) (i : Fin d), ∃ q : ℚ, z j i = (q : ℝ)) ∧
      (∀ j : J, ∃ k : ℤ, rad j = (3 : ℝ) ^ k) ∧
      (∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
        (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) →
        (∃ k : ℤ, r' = (3 : ℝ) ^ k) →
        (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) →
        ∃ j : J, z j = z' ∧ rad j = r') ∧
      (∀ j : J, ∃ g : Grid, gridRoot g = j ∧ origin g = z j) ∧
      (∀ (i : Index) (n : ℕ), Measurable (constants i n)) := by
  rcases hrepresented with
    ⟨_, _, _, _, _, hcut, hIR, henv, hlaw, hseq, _, hcenter, hscale, hcomplete,
      _, hgridroot, _, _, _, _, _, _, _, _, _, hcm, _⟩
  exact ⟨hcut, hIR, henv, hlaw, hseq, hcenter, hscale, hcomplete, hgridroot, hcm⟩

theorem aux_lem_cutoffs_root_uniform_majorant_data
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (beta alpha eta t : ℝ) (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta) (htlow : (d : ℝ) - 1 < t) (htupper : t < (d : ℝ))
    (hetaalpha : 1 + eta < 2 * alpha) (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cext Cgrad : ℝ) (hCext : 0 < Cext) (hCgrad : 0 < Cgrad)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hext : InfraredCharacterization M H → aux_lem_cutoffs_root_uniform_extrema d M H eta) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
      (J : Type) [Countable J] [DecidableEq J] (j0 : J)
      (z : J → SpatialCoordinates d) (rad : J → ℝ) (hrad : ∀ j, 0 < rad j)
      (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
      (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
      [_hDc : ∀ j, Countable (D j)] (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
      (T : J → Type) [_hTc : ∀ j, Countable (T j)]
      (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
      (thetaH1 : ∀ j, T j → Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
      (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
      (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
      (ucell : ∀ j, T j → ℕ → Ω → Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
      (E : Paper.in_J d) (Index : Type) [Countable Index]
      (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
      (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
      (coercivityKey extensionKey lambdaKey : J → Index)
      (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
      (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
      (Grid : Type) [Countable Grid] (origin : Grid → SpatialCoordinates d)
      (gridRoot : Grid → J) (gridKey : Grid → Index)
      (hfields : StrictMono cutoff ∧ InfraredCharacterization M H ∧
        (∀ n : ℕ, Measurable (env n)) ∧
        (∀ n : ℕ, Measure.map (env n) P = (chaosSampleLaw M).toMeasure) ∧
        Paper.conv_represented_sequence P resp respLim constants G ∧
        (∀ (j : J) (i : Fin d), ∃ q : ℚ, z j i = (q : ℝ)) ∧
        (∀ j : J, ∃ k : ℤ, rad j = (3 : ℝ) ^ k) ∧
        (∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
          (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) →
          (∃ k : ℤ, r' = (3 : ℝ) ^ k) →
          (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
            (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) →
          ∃ j : J, z j = z' ∧ rad j = r') ∧
        (∀ j : J, ∃ g : Grid, gridRoot g = j ∧ origin g = z j) ∧
        (∀ (i : Index) (n : ℕ), Measurable (constants i n))),
      ∃ Csum : ℝ, 0 < Csum ∧ ∃ (κ : ℤ), rad j0 = (3 : ℝ) ^ κ ∧
      ∃ g0 : Grid, gridRoot g0 = j0 ∧ origin g0 = z j0 ∧
      ∃ jc : (Jr : ℕ) → OddGridIndex d (triadicHalf Jr) → J,
        (∀ Jr k, z (jc Jr k) = oddGridCenter (z j0) (rad j0) (triadicHalf Jr) k ∧
          rad (jc Jr k) = rad j0 / (3 : ℝ) ^ Jr) ∧
        ∃ (mlow mhigh : ℕ → BilateralField d → ℝ) (KN : ℕ → Ω → ℝ) (Ggood : Set Ω),
          MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
          (∀ n, Measurable (KN n)) ∧ (∀ n omega, 1 ≤ KN n omega) ∧
          (∀ omega ∈ Ggood, BddAbove (Set.range (fun n => KN n omega))) ∧
          (∀ omega ∈ Ggood, ∀ n, constants (gridKey g0) n omega ≤ KN n omega) ∧
          (∀ omega ∈ Ggood, ∀ (n Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)),
            (Jr : ℤ) < κ →
            constants (extensionKey (jc Jr k)) n omega ≤ KN n omega) ∧
          (∀ omega ∈ Ggood, ∀ n : ℕ,
            0 < mlow (cutoff n) (env n omega) ∧
            (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
              mlow (cutoff n) (env n omega) ≤ cutoffCoefficient M H (env n omega) (cutoff n) x ∧
                cutoffCoefficient M H (env n omega) (cutoff n) x ≤ mhigh (cutoff n) (env n omega)) ∧
            mhigh (cutoff n) (env n omega) ≤ KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta) ∧
            (mlow (cutoff n) (env n omega))⁻¹ ≤ KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta)) := by
  classical
  intro Ω _ P _ cutoff env J _ _ j0 z rad hrad S D _ f T _ theta thetaH1 usrc srcRep ucell E
    Index _ resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey
    sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid _ origin gridRoot
    gridKey hfields
  obtain ⟨Csum, hCsum0, hCsum⟩ := aux_cutoffs_uniform_collar_sum d hd (z j0) (rad j0) (hrad j0) eta
    (Cext * (1 + Cgrad) ^ 2 * (1 + (rad j0) ^ eta) + (d : ℝ) * Cgrad ^ 2)
    (by have := Real.rpow_nonneg (hrad j0).le eta; positivity)
  rcases hfields with ⟨hcut, hIR, henv, hlaw, hseq, hcenter, hscale, hcomplete, hgridroot, hcm⟩
  have hκ := Classical.choose_spec (hscale j0)
  have hg0 := Classical.choose_spec (hgridroot j0)
  choose jc hjc using fun (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)) =>
    aux_cutoffs_odd_cell_catalogue_of_geometry j0 z rad hrad (z j0) (rad j0) (hrad j0) rfl rfl
      hcenter hscale hcomplete Jr k
  let F : Finset Index := insert (gridKey (Classical.choose (hgridroot j0)))
    ((Finset.range (Classical.choose (hscale j0)).toNat).biUnion fun Jr =>
      Finset.univ.image fun k : OddGridIndex d (triadicHalf Jr) => extensionKey (jc Jr k))
  obtain ⟨_, _, hG, _, hbdd⟩ := hseq
  obtain ⟨A, hA, mlow, mhigh, hae, hXmem, hXbd⟩ := hext hIR (z j0) (rad j0) (hrad j0)
  obtain ⟨KN, Ggood, h1, h2, h3, h4, h5, h7, h8, h9⟩ :=
    aux_lem_cutoffs_root_uniform_KN P (chaosSampleLaw M).toMeasure cutoff hcut env henv hlaw
      constants G hG hcm hbdd F eta heta
      (fun N b => 0 < mlow N b ∧ ∀ x ∈ (closedCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
        mlow N b ≤ cutoffCoefficient M H b N x ∧ cutoffCoefficient M H b N x ≤ mhigh N b)
      (by filter_upwards [hae] with b hb N using hb N) mlow mhigh A hA hXmem hXbd
  have hz0mem : z j0 ∈ (closedCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) := by
    change z j0 ∈ Metric.closedBall (z j0) (rad j0 / 2)
    exact Metric.mem_closedBall_self (by have := hrad j0; positivity)
  have hExt : ∀ omega ∈ Ggood, ∀ n : ℕ,
      0 < mlow (cutoff n) (env n omega) ∧
      (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
        mlow (cutoff n) (env n omega) ≤ cutoffCoefficient M H (env n omega) (cutoff n) x ∧
          cutoffCoefficient M H (env n omega) (cutoff n) x ≤ mhigh (cutoff n) (env n omega)) ∧
      mhigh (cutoff n) (env n omega) ≤ KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta) ∧
      (mlow (cutoff n) (env n omega))⁻¹ ≤ KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta) := by
    intro omega homega n
    obtain ⟨hgd, hX⟩ := h9 omega homega n
    obtain ⟨hlow, hcube⟩ := hgd (cutoff n)
    have hQ : ∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
        x ∈ (closedCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) := by
      intro x hx
      exact Metric.closure_ball_subset_closedBall hx
    have hle : mlow (cutoff n) (env n omega) ≤ mhigh (cutoff n) (env n omega) :=
      (hcube (z j0) hz0mem).1.trans (hcube (z j0) hz0mem).2
    have hb := aux_lem_cutoffs_root_uniform_extrema_bound (mlow (cutoff n) (env n omega))
      (mhigh (cutoff n) (env n omega)) (KN n omega) eta ((cutoff n : ℕ) : ℝ) heta hlow hle hX
    exact ⟨hlow, fun x hx => hcube x (hQ x hx), hb.1, hb.2⟩
  refine ⟨Csum, hCsum0, Classical.choose (hscale j0), hκ, Classical.choose (hgridroot j0), hg0.1,
    hg0.2, jc, hjc, mlow, mhigh, KN, Ggood, h1, h2, h3, h4, h5, h7, ?_, ?_, hExt⟩
  · intro omega homega n
    exact h8 omega homega n _ (Finset.mem_insert_self _ _)
  · intro omega homega n Jr k hk
    exact h8 omega homega n _ (Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨Jr, Finset.mem_range.mpr (by omega),
        Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩))

section RootUniformCutoffAdapters
variable
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)] (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j → Homogenization.H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : Paper.in_J d) (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid] (origin : Grid → SpatialCoordinates d)
    (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hrepresented : Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
      S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim
      constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
      sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)

@[irreducible] noncomputable def aux_lem_cutoffs_root_uniform_plateau (omega : Ω) (homega : omega ∈ G) :=
  aux_lem_cutoffs_rep_plateau d hd M H Cext beta alpha eta t orders Ω P cutoff env J j0 z rad
    hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented omega homega

end RootUniformCutoffAdapters

section RootUniformCollarAdapter
variable
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)] (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j → Homogenization.H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : Paper.in_J d) (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid] (origin : Grid → SpatialCoordinates d)
    (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hrepresented : Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
      S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim
      constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
      sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (Cgrad : ℝ) (hCgrad : 0 < Cgrad) (Ccollar : ℝ) (hCsum : _)
    (κ : ℤ) (hκ : rad j0 = (3 : ℝ) ^ κ) (g0 : Grid)
    (hg0 : gridRoot g0 = j0 ∧ origin g0 = z j0)
    (jc : ∀ Jr : ℕ, OddGridIndex d (triadicHalf Jr) → J)
    (hjc : ∀ Jr k, z (jc Jr k) = oddGridCenter (z j0) (rad j0) (triadicHalf Jr) k ∧
      rad (jc Jr k) = rad j0 / (3 : ℝ) ^ Jr)
    (omega : Ω) (homega : omega ∈ G) (KN : ℕ → Ω → ℝ)
    (hKN : ∀ n, 1 ≤ KN n omega)
    (hgrid : ∀ n, constants (gridKey g0) n omega ≤ KN n omega)
    (hcoarse : ∀ n (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)), (Jr : ℤ) < κ →
      constants (extensionKey (jc Jr k)) n omega ≤ KN n omega)
    (Mhi : ℕ → ℝ)
    (hMhi : ∀ n x, x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) →
      cutoffCoefficient M H (env n omega) (cutoff n) x ≤ Mhi n)
    (hMK : ∀ n, Mhi n ≤ KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta))

@[irreducible] noncomputable def aux_lem_cutoffs_root_uniform_collar :=
  aux_lem_cutoffs_rep_collar d hd M H Cext beta alpha eta t orders Ω P cutoff env J j0 z rad hrad
    S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented
    Cgrad hCgrad Ccollar hCsum κ hκ g0 hg0 jc hjc omega homega KN hKN hgrid hcoarse Mhi hMhi hMK

end RootUniformCollarAdapter

def aux_lem_cutoffs_root_uniform_data
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (beta alpha eta t : ℝ)
    (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta)
    (htlow : (d : ℝ) - 1 < t) (htupper : t < (d : ℝ))
    (hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cext Cgrad : ℝ) (hCext : 0 < Cext) (hCgrad : 0 < Cgrad)

    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) : Prop :=
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
        (J : Type) [Countable J] [DecidableEq J] (j0 : J)
        (z : J → SpatialCoordinates d) (rad : J → ℝ)
        (hrad : ∀ j, 0 < rad j)
        (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
        (D : ∀ j, Submodule ℚ
          (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
        [_hDc : ∀ j, Countable (D j)]
        (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
        (T : J → Type) [_hTc : ∀ j, Countable (T j)]
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
            cellGrowthKey cellHolderKey Grid origin gridRoot gridKey),
        ∃ Ccollar : ℝ, 0 < Ccollar ∧
        let Q := centeredCube (z j0) (rad j0) (hrad j0)
        let S0 := S j0
        let aN := fun (omega : Ω) (n : ℕ) =>
          Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
            (z j0) (hrad j0)
        let rawAN := fun (omega : Ω) (n : ℕ) =>
          cutoffCoefficient M H (env n omega) (cutoff n)
        ∃ KN : ℕ → Ω → ℝ, ∃ Ggood : Set Ω,
          MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
          (∀ n : ℕ, Measurable (KN n)) ∧
          (∀ n : ℕ, ∀ omega : Ω, 1 ≤ KN n omega) ∧
          (∀ omega ∈ Ggood,
            BddAbove (Set.range (fun n : ℕ => KN n omega))) ∧
          ∀ omega ∈ Ggood,
            (∀ b : T j0, ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
              IsCompact K → IsOpen O →
              closure O ⊆ (Q : Set (SpatialCoordinates d)) →
              IsOpen W → K ⊆ W → W ⊆ O →
              (∀ x : SpatialCoordinates d,
                0 ≤ theta j0 b x ∧ theta j0 b x ≤ 1) →
              (∀ x ∈ W, theta j0 b x = 1) →
              tsupport (theta j0 b) ⊆ O →
              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                (closure
                    (oddGridCell (z j0) (rad j0) (hrad j0)
                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
                    {x : SpatialCoordinates d |
                      0 < theta j0 b x ∧ theta j0 b x < 1}).Nonempty →
                  closure
                      (oddGridCell (z j0) (rad j0) (hrad j0)
                        (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆
                    O \ K) →
              ∃ chiH : ℕ → Homogenization.H1Function
                  (Q : Set (SpatialCoordinates d)),
                ∃ chiS : ℕ → S0.space,
                  ∃ chic : ℕ → SpatialCoordinates d → ℝ,
                    ∃ V : Set (SpatialCoordinates d),
                      ∃ Benergy Ball Bholder : ℝ,
                        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
                        0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
                        (∀ n : ℕ,
                          (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                          ContinuousOn (chic n)
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (chiS n).val.1 =ᵐ[
                            volume.restrict (Q : Set (SpatialCoordinates d))]
                            chic n ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                          (∀ x ∈ V, chic n x = 1) ∧
                          (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                            x ∉ O → chic n x = 0) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            IsWeaklyHarmonicOn (rawAN omega n)
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k)) ∧
                            HasZeroTraceDifferenceOn
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))
                              ((thetaH1 j0 b).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                (chiS n).val.2 i x = 0) ∧
                          responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                            0 < s → s ≤ 1 →
                            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                              (fun y => ENNReal.ofReal
                                ((aN omega n).val y *
                                  ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                              (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t)) ∧
                          Lane4.IsHolderOn alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ∧
                          Lane4.cAlphaNorm alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ≤
                            Bholder) ∧
                        (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                          StrictMono sigma ∧
                          ContinuousOn chiLim
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                chiLim x = theta j0 b x))) ∧
            (∀ Jr : ℕ,
              let rho := rad j0 / (3 : ℝ) ^ Jr
                ∀ thetaR : SpatialCoordinates d → ℝ,
                  ContDiff ℝ ∞ thetaR →
                  (∀ x : SpatialCoordinates d,
                    0 ≤ thetaR x ∧ thetaR x ≤ 1) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                      thetaR x = 0) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    3 * rho ≤ Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) →
                      thetaR x = 1) →
                  (∀ x : SpatialCoordinates d,
                    norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
                  ∀ thetaRH1 : Homogenization.H1Function
                    (Q : Set (SpatialCoordinates d)),
                    thetaRH1.toFun = thetaR →
                    ∃ collarH : ℕ → Homogenization.H1Function
                        (Q : Set (SpatialCoordinates d)),
                      ∃ collarS : ℕ → S0.space,
                        ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                          ∀ n : ℕ,
                            (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                            ContinuousOn (collarC n)
                              (closure (Q : Set (SpatialCoordinates d))) ∧
                            (collarS n).val.1 =ᵐ[
                              volume.restrict (Q : Set (SpatialCoordinates d))]
                              collarC n ∧
                            (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                              0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                                collarC n x = 0) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              3 * rho ≤ Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                collarC n x = 1) ∧
                            (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                              (Q : Set (SpatialCoordinates d)),
                              3 * rho < Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                (collarS n).val.2 i x = 0) ∧
                            (∀ k : OddGridIndex d (triadicHalf Jr),
                              IsWeaklyHarmonicOn (rawAN omega n)
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k)) ∧
                              HasZeroTraceDifferenceOn
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))
                                (thetaRH1.restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))) ∧
                            responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                              Ccollar * KN n omega * rho ^ (-1 - eta))

@[irreducible] noncomputable def aux_lem_cutoffs_root_uniform_majorant_application
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (beta alpha eta t : ℝ) (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta) (htlow : (d : ℝ) - 1 < t) (htupper : t < (d : ℝ))
    (hetaalpha : 1 + eta < 2 * alpha) (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cext Cgrad : ℝ) (hCext : 0 < Cext) (hCgrad : 0 < Cgrad)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hext : InfraredCharacterization M H → aux_lem_cutoffs_root_uniform_extrema d M H eta) :=
  aux_lem_cutoffs_root_uniform_majorant_data d hd beta alpha eta t hbeta hbetaalpha halpha heta
    htlow htupper hetaalpha orders horders Cext Cgrad hCext hCgrad M H hext

theorem aux_lem_cutoffs_root_uniform_of_extrema
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (beta alpha eta t : ℝ)
    (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta)
    (htlow : (d : ℝ) - 1 < t) (htupper : t < (d : ℝ))
    (hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cext Cgrad : ℝ) (hCext : 0 < Cext) (hCgrad : 0 < Cgrad)

    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hext : InfraredCharacterization M H → aux_lem_cutoffs_root_uniform_extrema d M H eta) :
    aux_lem_cutoffs_root_uniform_data d hd beta alpha eta t hbeta hbetaalpha halpha heta htlow htupper hetaalpha orders horders Cext Cgrad hCext hCgrad M H := by
  classical
  intro Ω _ P _ cutoff env J _ _ j0 z rad hrad S D _ f T _ theta thetaH1 usrc srcRep
    ucell E Index _ resp respLim constants G coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid _ origin gridRoot gridKey hrepresented
  obtain ⟨Ccollar, hCcollar, hCsum⟩ := aux_cutoffs_uniform_collar_sum d hd (z j0) (rad j0) (hrad j0) eta
    (Cext * (1 + Cgrad) ^ 2 * (1 + (rad j0) ^ eta) + (d : ℝ) * Cgrad ^ 2)
    (by have := Real.rpow_nonneg (hrad j0).le eta; positivity)
  refine ⟨Ccollar, hCcollar, ?_⟩
  have hfields := aux_lem_cutoffs_root_uniform_represented_fields d hd M H Ω P cutoff env J j0 z rad
    hrad S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim
    constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented
  have hMajorant :=
    aux_lem_cutoffs_root_uniform_majorant_application d hd beta alpha eta t hbeta hbetaalpha halpha heta
      htlow htupper hetaalpha orders horders Cext Cgrad hCext hCgrad M H
      (fun hIR => hext hIR) Ω P cutoff env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep
      ucell E Index resp respLim constants G coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
      Grid origin gridRoot gridKey hfields
  obtain ⟨_, _, κ, hκ, g0, hg01, hg02, jc, hjc, mlow, mhigh, KN, Ggood,
      h1, h2, h3, h4, h5, h7, hbase, hcell, hExt⟩ := hMajorant
  intro Q S0 aN rawAN
  refine ⟨KN, Ggood, h1, h2, h3, h4, h5, h7, fun omega homega => ⟨?_, ?_⟩⟩
  · exact aux_lem_cutoffs_root_uniform_plateau d hd M H Cext beta alpha eta t orders Ω P cutoff env J j0 z
      rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented omega
      (h2 homega)
  · exact aux_lem_cutoffs_root_uniform_collar d hd M H Cext beta alpha eta t orders Ω P cutoff env J j0 z
      rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented
      Cgrad hCgrad Ccollar hCsum κ hκ g0 ⟨hg01, hg02⟩ jc hjc omega (h2 homega) KN
      (fun n => h5 n omega) (fun n => hbase omega homega n)
      (fun n Jr k hc => hcell omega homega n Jr k hc)
      (fun n => mhigh (cutoff n) (env n omega))
      (fun n x hx => ((hExt omega homega n).2.1 x hx).2)
      (fun n => (hExt omega homega n).2.2.1)



theorem lem_cutoffs_root_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (beta alpha eta t : ℝ)
    (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta)
    (htlow : (d : ℝ) - 1 < t) (htupper : t < (d : ℝ))
    (hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cext Cgrad : ℝ) (hCext : 0 < Cext) (hCgrad : 0 < Cgrad)
    :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        M.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
        (J : Type) [Countable J] [DecidableEq J] (j0 : J)
        (z : J → SpatialCoordinates d) (rad : J → ℝ)
        (hrad : ∀ j, 0 < rad j)
        (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
        (D : ∀ j, Submodule ℚ
          (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
        [_hDc : ∀ j, Countable (D j)]
        (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
        (T : J → Type) [_hTc : ∀ j, Countable (T j)]
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
            cellGrowthKey cellHolderKey Grid origin gridRoot gridKey),
        ∃ Ccollar : ℝ, 0 < Ccollar ∧
        let Q := centeredCube (z j0) (rad j0) (hrad j0)
        let S0 := S j0
        let aN := fun (omega : Ω) (n : ℕ) =>
          Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
            (z j0) (hrad j0)
        let rawAN := fun (omega : Ω) (n : ℕ) =>
          cutoffCoefficient M H (env n omega) (cutoff n)
        ∃ KN : ℕ → Ω → ℝ, ∃ Ggood : Set Ω,
          MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
          (∀ n : ℕ, Measurable (KN n)) ∧
          (∀ n : ℕ, ∀ omega : Ω, 1 ≤ KN n omega) ∧
          (∀ omega ∈ Ggood,
            BddAbove (Set.range (fun n : ℕ => KN n omega))) ∧
          ∀ omega ∈ Ggood,
            (∀ b : T j0, ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
              IsCompact K → IsOpen O →
              closure O ⊆ (Q : Set (SpatialCoordinates d)) →
              IsOpen W → K ⊆ W → W ⊆ O →
              (∀ x : SpatialCoordinates d,
                0 ≤ theta j0 b x ∧ theta j0 b x ≤ 1) →
              (∀ x ∈ W, theta j0 b x = 1) →
              tsupport (theta j0 b) ⊆ O →
              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                (closure
                    (oddGridCell (z j0) (rad j0) (hrad j0)
                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
                    {x : SpatialCoordinates d |
                      0 < theta j0 b x ∧ theta j0 b x < 1}).Nonempty →
                  closure
                      (oddGridCell (z j0) (rad j0) (hrad j0)
                        (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆
                    O \ K) →
              ∃ chiH : ℕ → Homogenization.H1Function
                  (Q : Set (SpatialCoordinates d)),
                ∃ chiS : ℕ → S0.space,
                  ∃ chic : ℕ → SpatialCoordinates d → ℝ,
                    ∃ V : Set (SpatialCoordinates d),
                      ∃ Benergy Ball Bholder : ℝ,
                        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
                        0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
                        (∀ n : ℕ,
                          (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                          ContinuousOn (chic n)
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (chiS n).val.1 =ᵐ[
                            volume.restrict (Q : Set (SpatialCoordinates d))]
                            chic n ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                          (∀ x ∈ V, chic n x = 1) ∧
                          (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                            x ∉ O → chic n x = 0) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            IsWeaklyHarmonicOn (rawAN omega n)
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k)) ∧
                            HasZeroTraceDifferenceOn
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))
                              ((thetaH1 j0 b).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                (chiS n).val.2 i x = 0) ∧
                          responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                            0 < s → s ≤ 1 →
                            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                              (fun y => ENNReal.ofReal
                                ((aN omega n).val y *
                                  ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                              (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t)) ∧
                          Lane4.IsHolderOn alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ∧
                          Lane4.cAlphaNorm alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ≤
                            Bholder) ∧
                        (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                          StrictMono sigma ∧
                          ContinuousOn chiLim
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                chiLim x = theta j0 b x))) ∧
            (∀ Jr : ℕ,
              let rho := rad j0 / (3 : ℝ) ^ Jr
                ∀ thetaR : SpatialCoordinates d → ℝ,
                  ContDiff ℝ ∞ thetaR →
                  (∀ x : SpatialCoordinates d,
                    0 ≤ thetaR x ∧ thetaR x ≤ 1) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                      thetaR x = 0) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    3 * rho ≤ Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) →
                      thetaR x = 1) →
                  (∀ x : SpatialCoordinates d,
                    norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
                  ∀ thetaRH1 : Homogenization.H1Function
                    (Q : Set (SpatialCoordinates d)),
                    thetaRH1.toFun = thetaR →
                    ∃ collarH : ℕ → Homogenization.H1Function
                        (Q : Set (SpatialCoordinates d)),
                      ∃ collarS : ℕ → S0.space,
                        ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                          ∀ n : ℕ,
                            (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                            ContinuousOn (collarC n)
                              (closure (Q : Set (SpatialCoordinates d))) ∧
                            (collarS n).val.1 =ᵐ[
                              volume.restrict (Q : Set (SpatialCoordinates d))]
                              collarC n ∧
                            (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                              0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                                collarC n x = 0) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              3 * rho ≤ Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                collarC n x = 1) ∧
                            (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                              (Q : Set (SpatialCoordinates d)),
                              3 * rho < Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                (collarS n).val.2 i x = 0) ∧
                            (∀ k : OddGridIndex d (triadicHalf Jr),
                              IsWeaklyHarmonicOn (rawAN omega n)
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k)) ∧
                              HasZeroTraceDifferenceOn
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))
                                (thetaRH1.restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))) ∧
                            responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                              Ccollar * KN n omega * rho ^ (-1 - eta)) := by
  classical
  obtain ⟨delta0, hdelta0, hext⟩ := lem_cutoffs_damped_extrema_uniform d hd eta heta
  refine ⟨delta0, hdelta0, ?_⟩
  intro M H hM
  exact aux_lem_cutoffs_root_uniform_of_extrema d hd beta alpha eta t hbeta hbetaalpha halpha heta htlow htupper hetaalpha orders horders Cext Cgrad hCext hCgrad M H
    (fun hIR => hext M H hIR hM)

end Paper
