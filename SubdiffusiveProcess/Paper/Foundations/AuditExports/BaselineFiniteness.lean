module

public import SubdiffusiveProcess.Paper.inputs_baseline_native
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.lfsgs_primitive_scores_exists
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The discounted annular response term of the extended baseline. -/
def baselineResponseTerm (d : ℕ) (M : GMCModel d) (s : ℝ) (k : ℕ) (z : Vec d)
    (omega : PotentialSample d) : ENNReal :=
  (sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
            (min (sSup {u : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
              u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^ (1 / 2 : ℝ)})

/-- The discounted shell-block supremum of the extended baseline. -/
def baselineBlockTerm (d : ℕ) (s : ℝ) (k : ℕ) (z : Vec d)
    (omega : PotentialSample d) : ENNReal :=
  (sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
            sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
              u = ENNReal.ofReal |shellBlock k j omega x|}})

/-- The scale-zero anchor supremum of the extended baseline. -/
def baselineAnchorTerm (d : ℕ) (s : ℝ) (k : ℕ) (z : Vec d)
    (omega : PotentialSample d) : ENNReal :=
  (ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |omega 0 x|})

/-- The infinite gradient suffix of the extended baseline. -/
def baselineGradientTerm (d : ℕ) (k : ℕ) (z : Vec d)
    (omega : PotentialSample d) : ENNReal :=
  (∑' j : ℕ, if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
          else 0)

/-- The literal sum in primitive_scores, before any real conversion. -/
def baselineExtendedScore (d : ℕ) (M : GMCModel d) (s : ℝ)
    (k : ℕ) (z : Vec d) (omega : PotentialSample d) : ENNReal :=
  baselineResponseTerm d M s k z omega +
    baselineBlockTerm d s k z omega +
    baselineAnchorTerm d s k z omega +
    baselineGradientTerm d k z omega

/-- N2 / Foundation F7: each extended term and their sum are almost surely
finite, with the native moment constants chosen before the model and cube. -/
theorem baseline_native_finite (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (s q : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hq : 1 ≤ q) :
    ∃ C delta0 : ℝ, 0 < C ∧ 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ min 1 delta0 →
        ∀ (k : ℕ) (z : Vec d),
          (∀ᵐ omega ∂M.P.toMeasure,
            baselineResponseTerm d M s k z omega ≠ ∞ ∧
            baselineBlockTerm d s k z omega ≠ ∞ ∧
            baselineAnchorTerm d s k z omega ≠ ∞ ∧
            baselineGradientTerm d k z omega ≠ ∞ ∧
            baselineExtendedScore d M s k z omega ≠ ∞) ∧
          MemLp (fun omega => (baselineExtendedScore d M s k z omega).toReal)
            (ENNReal.ofReal q) M.P.toMeasure ∧
          eLpNorm (fun omega => (baselineExtendedScore d M s k z omega).toReal)
            (ENNReal.ofReal q) M.P.toMeasure ≤
              ENNReal.ofReal (C * M.delta ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, delta0, hC, hdelta0, h⟩ := _root_.SubdiffusiveProcess.Paper.inputs_baseline_native d hd s q hs hq
  refine ⟨C, delta0, hC, hdelta0, ?_⟩
  intro M hsmall k z
  obtain ⟨hf, hm, hn⟩ := h M hsmall k z
  change (∀ᵐ omega ∂M.P.toMeasure, baselineExtendedScore d M s k z omega ≠ ∞) at hf
  refine ⟨?_, hm, hn⟩
  filter_upwards [hf] with omega hfinite
  have ht := hfinite
  simp only [baselineExtendedScore, ENNReal.add_ne_top] at ht
  exact ⟨ht.1.1.1, ht.1.1.2, ht.1.2, ht.2, hfinite⟩

/-- N2 / Foundation F7 on the relabelled bilateral field. The representation
identities are exactly those of the baseline package; finiteness is retained
before reversing toReal. Constants are independent of the cutoff and cube. -/
theorem baseline_relabelled_finite (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ CD deltaD : ℝ → ℝ,
      (∀ q : ℝ, 1 ≤ q → 0 < CD q ∧ 0 < deltaD q) ∧
      ∀ q : ℝ, 1 ≤ q →
        ∀ M : GMCModel d, M.delta ≤ min 1 (deltaD q) →
          ∀ eta : ℕ → BilateralField d → PotentialSample d,
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
                omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
          ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
            (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
            (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
              _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta N omega)
                (fun m y => F N m y omega) (fun m y => Praw N m y omega)
                (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
                (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
            ∀ (N k : ℕ) (z : Vec d),
              (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                baselineResponseTerm d M s k z (eta N omega) ≠ ∞ ∧
                baselineBlockTerm d s k z (eta N omega) ≠ ∞ ∧
                baselineAnchorTerm d s k z (eta N omega) ≠ ∞ ∧
                baselineGradientTerm d k z (eta N omega) ≠ ∞ ∧
                Draw N k z omega ≠ ∞ ∧
                ENNReal.ofReal (Draw N k z omega).toReal = Draw N k z omega) ∧
              MemLp (fun omega => (Draw N k z omega).toReal)
                (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
              eLpNorm (fun omega => (Draw N k z omega).toReal)
                (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
                  ENNReal.ofReal (CD q * M.delta ^ (1 / 2 : ℝ)) := by
  classical
  have banks := fun q : ℝ => baseline_native_finite d hd s (max 1 q) hs (le_max_left 1 q)
  choose C delta0 hC hdelta0 hbank using banks
  refine ⟨C, delta0, fun q _ => ⟨hC q, hdelta0 q⟩, ?_⟩
  intro q hq M hsmall eta hEta F Praw Rraw Draw Z rawGood hprim N k z
  obtain ⟨hfinite, hmem, hnorm⟩ := hbank q M hsmall k z
  rw [max_eq_right hq] at hmem hnorm
  have hmeasEta := _root_.SubdiffusiveProcess.Paper.prefix_eta_aemeasurable M eta hEta N
  have hlaw := _root_.SubdiffusiveProcess.Paper.prefix_eta_law M eta hEta N
  have hfiniteMap := hfinite
  rw [← hlaw] at hfiniteMap
  have hfiniteComp := ae_of_ae_map hmeasEta hfiniteMap
  have hraw : Draw N k z =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun omega => baselineExtendedScore d M s k z (eta N omega)) := by
    filter_upwards [hprim] with omega hprim
    obtain ⟨_, _, _, _, _, _, _, hD, _⟩ := hprim N
    exact hD k z
  have hreal := hraw.fun_comp ENNReal.toReal
  have hmemMap : MemLp (fun omega => (baselineExtendedScore d M s k z omega).toReal)
      (ENNReal.ofReal q) (Measure.map (eta N) (chaosSampleLaw M).toMeasure) := by
    rw [hlaw]
    exact hmem
  refine ⟨?_, (memLp_congr_ae hreal).2 (hmemMap.comp_of_map hmeasEta), ?_⟩
  · filter_upwards [hfiniteComp, hraw] with omega hf hd
    have hDraw : Draw N k z omega ≠ ∞ := by rw [hd]; exact hf.2.2.2.2
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hDraw,
      ENNReal.ofReal_toReal hDraw⟩
  · have hnormMap := eLpNorm_map_measure (p := ENNReal.ofReal q)
      hmemMap.aestronglyMeasurable hmeasEta
    rw [hlaw] at hnormMap
    exact ((eLpNorm_congr_ae hreal).trans hnormMap.symm).le.trans hnorm

/-- N2 / Foundation F7 for actual scores: the relabelled field and every
score identity are produced internally, and all four extended baseline terms
are finite before the ENNReal-toReal round trip. -/
theorem baseline_scores_finite (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s eps : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ CD deltaD : ℝ → ℝ,
      (∀ q : ℝ, 1 ≤ q → 0 < CD q ∧ 0 < deltaD q) ∧
      ∀ q : ℝ, 1 ≤ q →
        ∀ M : GMCModel d, M.delta ≤ min 1 (deltaD q) →
          ∃ (eta : ℕ → BilateralField d → PotentialSample d)
            (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
            (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
            (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
                omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) ∧
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
              _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta N omega)
                (fun m y => F N m y omega) (fun m y => Praw N m y omega)
                (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
                (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) ∧
            ∀ (N k : ℕ) (z : Vec d),
              (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                baselineResponseTerm d M s k z (eta N omega) ≠ ∞ ∧
                baselineBlockTerm d s k z (eta N omega) ≠ ∞ ∧
                baselineAnchorTerm d s k z (eta N omega) ≠ ∞ ∧
                baselineGradientTerm d k z (eta N omega) ≠ ∞ ∧
                Draw N k z omega ≠ ∞ ∧
                ENNReal.ofReal (Draw N k z omega).toReal = Draw N k z omega) ∧
              MemLp (fun omega => (Draw N k z omega).toReal)
                (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
              eLpNorm (fun omega => (Draw N k z omega).toReal)
                (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
                  ENNReal.ofReal (CD q * M.delta ^ (1 / 2 : ℝ)) := by
  obtain ⟨CD, deltaD, hpos, h⟩ :=
    baseline_relabelled_finite d hd s eps ⟨hs.1, hs.2.le⟩
  refine ⟨CD, deltaD, hpos, ?_⟩
  intro q hq M hsmall
  obtain ⟨eta, F, Praw, Rraw, Draw, Z, rawGood, hEta, hprim⟩ :=
    _root_.SubdiffusiveProcess.Paper.lfsgs_primitive_scores_exists M s eps hs heps
  exact ⟨eta, F, Praw, Rraw, Draw, Z, rawGood, hEta, hprim,
    h q hq M hsmall eta hEta F Praw Rraw Draw Z rawGood hprim⟩

end SubdiffusiveProcess.AuditExports
