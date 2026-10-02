import SubdiffusiveProcess.Paper.lem_as_regularity_score_pair_geometric
import SubdiffusiveProcess.Analysis.TwoDepthRates
import SubdiffusiveProcess.Probability.GrowingMeshTransfer

/-! The original physical bad and accumulated-error coordinates transfer to
one common limiting bank on every admissible growing catalogue. The depth
fractions follow the fixed response moment order and require no additional
disorder reduction. Deterministic iteration is not asserted in this file.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal BigOperators Topology
noncomputable section
namespace Paper

/-- The guarded physical original score coordinate at one cutoff. -/
def aux_lem_as_regularity_mesh_transfer_value {d : ℕ}
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
    (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (useD : Bool) (omega : BilateralField d) : ℝ :=
  if n ≤ (N : ℤ) then
    if useD then (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal
    else Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega
  else 0

/-- The two small depth fractions leave at least half the cutoff for every retained atom. -/
theorem aux_lem_as_regularity_mesh_transfer_depths
    (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) (hv1 : v ≤ 1 / 4)
    (N : ℕ) (n : ℤ) (hn : (n : ℝ) ≤ v * N) :
    n + (⌊u * N⌋₊ : ℤ) + (⌊(N : ℝ) / 2⌋₊ : ℤ) ≤ (N : ℤ) := by
  have hH := Nat.floor_le (mul_nonneg hu0 (Nat.cast_nonneg (α := ℝ) N))
  have hK := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) / 2 by positivity)
  have huN := mul_le_mul_of_nonneg_right hu1 (Nat.cast_nonneg (α := ℝ) N)
  have hvN := mul_le_mul_of_nonneg_right hv1 (Nat.cast_nonneg (α := ℝ) N)
  have hreal : (n : ℝ) + (⌊u * N⌋₊ : ℝ) + (⌊(N : ℝ) / 2⌋₊ : ℝ) ≤ (N : ℝ) := by
    linarith only [hn, hH, hK, huN, hvN]
  exact_mod_cast hreal

/-- The remaining cutoff and deterministic clipped tail satisfy their thresholds eventually. -/
theorem aux_lem_as_regularity_mesh_transfer_eventual (s u tol : ℝ)
    (hs : 0 < s) (hu : 0 < u) (htol : 0 < tol) (N0 : ℕ) :
    ∃ Nstart : ℕ, ∀ N : ℕ, Nstart ≤ N →
      N0 ≤ ⌊(N : ℝ) / 2⌋₊ ∧
      (3 : ℝ) ^ (-(s / 2) * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ)) ≤ tol := by
  have hr0 : 0 < (3 : ℝ) ^ (-(s / 2) * u) := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(s / 2) * u) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith only [mul_pos hs hu])
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds htol))
  refine ⟨max N1 (2 * N0), fun N hN => ⟨?_, ?_⟩⟩
  · apply Nat.le_floor
    have hnn : (2 : ℝ) * N0 ≤ (N : ℝ) := by
      exact_mod_cast (le_max_right N1 (2 * N0)).trans hN
    linarith only [hnn]
  · refine (discarded_depth_rate_le (s / 2) u (by positivity) N).trans ?_
    rw [Real.rpow_mul_natCast (show (0 : ℝ) ≤ 3 by norm_num)]
    exact (hN1 N ((le_max_left _ _).trans hN)).le

/-- A common larger threshold turns either guarded coordinate exception into the two-score exception. -/
theorem aux_lem_as_regularity_mesh_transfer_event {d : ℕ}
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
    (n : ℤ) (z : SpatialCoordinates d) (N N' : ℕ)
    (hn : n ≤ (N : ℤ)) (hn' : n ≤ (N' : ℤ))
    (a az ad : ℝ) (haz : az ≤ a) (had : ad ≤ a) (useD : Bool) :
    {omega | a < aux_lem_as_regularity_mesh_transfer_value Z Draw N n z useD omega -
        aux_lem_as_regularity_mesh_transfer_value Z Draw N' n z useD omega} ⊆
      {omega | az < Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega -
          Z N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega ∨
        ad < (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal -
          (Draw N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega).toReal} := by
  intro omega homega
  cases useD with
  | false =>
    exact Or.inl (haz.trans_lt (by
      simpa only [aux_lem_as_regularity_mesh_transfer_value, if_pos hn, if_pos hn',
        Bool.false_eq_true, ↓reduceIte, mem_setOf_eq] using homega))
  | true =>
    exact Or.inr (had.trans_lt (by
      simpa only [aux_lem_as_regularity_mesh_transfer_value, if_pos hn, if_pos hn',
        ↓reduceIte, mem_setOf_eq] using homega))

/-- Actual finite-cutoff scores are eventually below their common limits plus any admitted margin on a growing mesh. -/
theorem lem_as_regularity_mesh_transfer
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (s eps q : ℝ) (hs : 0 < s) (heps : 0 < eps)
    (hq : 1 ≤ q) (hsq : 8 * (d : ℝ) < s * q) (g : ℝ) (hg : 0 ≤ g) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ tol loss : ℝ, 0 < tol → tol ≤ 1 →
        (2 * tol) * (1 + eps ^ 2) / (eps ^ 2 - eps ^ 2 / 4) < loss →
        Real.sqrt (2 * tol) + 2 * tol < loss →
      ∃ u v : ℝ, (0 < u ∧ u < 1 / 4) ∧ (0 < v ∧ v < 1 / 4) ∧
        ∀ eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
          (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
          (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          primitive_scores d M s eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        ∀ (Pos : Type) (level : Pos → ℤ) (centre : Pos → SpatialCoordinates d)
          (phi : ℕ → ℕ), StrictMono phi →
        ∀ Vlim : Pos → Bool → BilateralField d → ℝ,
        (∀ pos useD, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun j => aux_lem_as_regularity_mesh_transfer_value Z Draw (phi j)
            (level pos) (centre pos) useD) atTop (Vlim pos useD)) →
        ∀ (k : ℕ → ℕ) (entry : ∀ N, Fin (k N) → Pos) (b : ℕ) (Ccount : ℝ),
          0 ≤ Ccount →
          (∀ N, (k N : ℝ) ≤ Ccount * ((N : ℝ) + 1) ^ b * (3 : ℝ) ^ ((g * v) * N)) →
          (∀ N i, (level (entry N i) : ℝ) ≤ v * N) →
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ᶠ N in atTop,
            ∀ (i : Fin (k N)) (useD : Bool),
              aux_lem_as_regularity_mesh_transfer_value Z Draw N
                (level (entry N i)) (centre (entry N i)) useD omega ≤
                Vlim (entry N i) useD omega + loss := by
  obtain ⟨delta0, hdelta0, hrate⟩ := lem_as_regularity_score_pair_geometric
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp s eps q hs heps hq hsq
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hM tol loss htol htol1 hZloss hDloss
  obtain ⟨A, c, N0, hA, hc, htail⟩ := hrate M Rm Sreg It H hH hM tol htol htol1
  let a : ℝ := s / 8 - (d : ℝ) / q
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have ha : 0 < a := by
    have hdiv : (d : ℝ) / q < s / 8 := by
      apply (div_lt_iff₀ hq0).mpr
      nlinarith only [hsq]
    exact sub_pos.mpr hdiv
  obtain ⟨u, v, hu, hv, hret, hdisc⟩ := exists_two_depth_rates ((d : ℝ) + 1) g a c
    (by positivity) hg ha hc
  obtain ⟨Nstart, hstart⟩ := aux_lem_as_regularity_mesh_transfer_eventual s u tol hs hu.1 htol N0
  refine ⟨u, v, hu, hv, ?_⟩
  intro eta hEta F Praw Rraw Draw Z rawGood hPrim Pos level centre phi hphi Vlim hconv
    k entry b Ccount hCcount hcard hlevel
  let errZ : ℝ := (2 * tol) * (1 + eps ^ 2) / (eps ^ 2 - eps ^ 2 / 4)
  let errD : ℝ := Real.sqrt (2 * tol) + 2 * tol
  let thresh : ℝ := (loss + max errZ errD) / 2
  have hmax : max errZ errD < loss := max_lt hZloss hDloss
  have ht : thresh < loss := by dsimp only [thresh]; linarith only [hmax]
  have hz : errZ ≤ thresh := by
    have hle := le_max_left errZ errD
    dsimp only [thresh]
    linarith only [hle, hmax]
  have hd' : errD ≤ thresh := by
    have hle := le_max_right errZ errD
    dsimp only [thresh]
    linarith only [hle, hmax]
  let B : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal (A *
    ((3 : ℝ) ^ (((d : ℝ) + 1) * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ) - c * (⌊(N : ℝ) / 2⌋₊ : ℝ)) +
      (3 : ℝ) ^ (-a * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ))))
  have hsum : (∑' N, (k N : ℝ≥0∞) * B N) ≠ ⊤ :=
    two_depth_mesh_tsum_ne_top k b Ccount A ((d : ℝ) + 1) g a c u v hCcount hA.le
      (by positivity) hc.le ha.le hu.1.le
      (by linarith only [hret, hc]) (by nlinarith only [hdisc, mul_pos ha hu.1]) hcard
  have htag (useD : Bool) := ae_eventually_growing_mesh_le_limit (chaosSampleLaw M).toMeasure
    (fun N pos => aux_lem_as_regularity_mesh_transfer_value Z Draw N (level pos) (centre pos) useD)
    (fun pos => Vlim pos useD) phi hphi.tendsto_atTop (fun pos => hconv pos useD)
    k entry thresh loss ht B Nstart (by
      intro N hN i
      have hNK := aux_lem_as_regularity_mesh_transfer_depths u v hu.1.le hu.2.le hv.2.le
        N (level (entry N i)) (hlevel N i)
      obtain ⟨M0, hNM0, hM0⟩ := htail eta hEta F Praw Rraw Draw Z rawGood hPrim
        (level (entry N i)) (centre (entry N i)) N ⌊(N : ℝ) / 2⌋₊ ⌊u * N⌋₊
        (hstart N hN).1 hNK (hstart N hN).2
      refine eventually_atTop.mpr ⟨M0, fun N' hN' => ?_⟩
      refine (measure_mono (aux_lem_as_regularity_mesh_transfer_event Z Draw
        (level (entry N i)) (centre (entry N i)) N N' (by omega) (by omega)
        thresh errZ errD hz hd' useD)).trans (hM0 N' hN')) hsum
  filter_upwards [htag true, htag false] with omega htrue hfalse
  filter_upwards [htrue, hfalse] with N htrueN hfalseN
  intro i useD
  cases useD with
  | false => exact hfalseN i
  | true => exact htrueN i

end Paper
