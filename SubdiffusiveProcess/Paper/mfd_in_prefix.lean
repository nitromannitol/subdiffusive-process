module

public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.PrefixScores.BadScoreTail
public import SubdiffusiveProcess.PrefixScores.ErrorScoreTail

@[expose] public section

/-!
Lemma `mfd:in-prefix` ("Sums of scores at a fixed centre", paper label `mfd:in-prefix` ).

Statement.  Fix the ramp/score parameters `s ∈ (0,1]`, `ε ∈ (0,1)`, `λ > 0` and `A < ∞`.  There are a disorder
threshold `delta0 > 0` and a constant `C`, chosen before the model (the paper's `C` is a dimensional constant, independent of the disorder,
the centre and the interval), such that for every model `M` with `M.delta ≤ delta0`, every deterministic centre `z`, every interval
`n, …, n+k-1` of physical scales and each score `X ∈ {Z, 𝐆}`
`P[∑_{i<k} X_{n+i,z} > λ k / 4] ≤ C e^{-A k}`.

The scores are the primitive scores of `SubdiffusiveProcess.Paper.primitive_scores` (the full-response, extended-valued encoding,
carried at the stored sample `ω`; `Zsc` is the bad score `Z_{m,z}`, `Dsc` is the error score `𝐆_{m,z}(s)` of `e.def.bfG.mhq`, `ENNReal`-valued),
specified as ARBITRARY families `ω ↦ (Fsc ω, …, goodEvt ω)` that satisfy `primitive_scores` at every sample `ω`; that predicate pins them
uniquely (equations (2)-(7)), so no cutoff or definitional substitution is made.  "At a single cutoff" is the fact that all entries of a prefix
are the scores of ONE sample `ω`, at physical scales `n, …, n+k-1`; the position of the interval is `n` and the shift of the finite-cutoff
frame is stationarity (`a.g1`), already built into the law `M.P`.  The two conclusions are outer-measure bounds (the events are measurable in truth;
the bound for the outer measure is the stronger statement and is what the sibling lemmas `l_exp_goodscales`, `l_sum_the_errors` assert).
-/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem mfd_in_prefix (d : ℕ) [NeZero d] (s eps : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (lam A : ℝ) (hlam : 0 < lam) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
        ∀ (Fsc Psc Rsc Dsc : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ → Vec d → ENNReal)
          (Zsc : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ → Vec d → ℝ)
          (goodEvt : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ → Vec d → Prop),
          (∀ ω : _root_.SubdiffusiveProcess.Model.PotentialSample d,
            _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps ω (Fsc ω) (Psc ω) (Rsc ω) (Dsc ω) (Zsc ω)
              (goodEvt ω)) →
          ∀ (z : Vec d) (n k : ℕ),
            M.P.toMeasure {ω | lam * (k : ℝ) / 4 < ∑ i ∈ Finset.range k, Zsc ω (n + i) z} ≤
                ENNReal.ofReal (C * Real.exp (-(A * (k : ℝ)))) ∧
              M.P.toMeasure {ω | ENNReal.ofReal (lam * (k : ℝ) / 4) <
                  ∑ i ∈ Finset.range k, Dsc ω (n + i) z} ≤
                ENNReal.ofReal (C * Real.exp (-(A * (k : ℝ)))) := by
  obtain ⟨deltaZ, hdeltaZ, hZtail⟩ :=
    SubdiffusiveProcess.PrefixScores.exists_badScore_tail d s eps lam A hs heps hlam
  obtain ⟨deltaD, hdeltaD, hDtail⟩ :=
    SubdiffusiveProcess.PrefixScores.exists_errorScore_tail d s lam A hs hlam
  refine ⟨min deltaZ deltaD, 3, lt_min hdeltaZ hdeltaD, by norm_num, ?_⟩
  intro M hdelta Fsc Psc Rsc Dsc Zsc goodEvt hprim z n k
  have hZeq : ∀ ω : _root_.SubdiffusiveProcess.Model.PotentialSample d, ∀ m : ℕ,
      Zsc ω m z = SubdiffusiveProcess.primitiveBadScore M s eps ω m z := by
    intro ω m
    obtain ⟨_hs, _hs1, _heps, _heps1, hF, hP, hR, _hD, _hGood, hZ, _hbase⟩ := hprim ω
    rw [(hZ m z).1, hF m z, hP m z, hR m z]
    rfl
  have hDeq : ∀ ω : _root_.SubdiffusiveProcess.Model.PotentialSample d, ∀ m : ℕ,
      Dsc ω m z = SubdiffusiveProcess.primitiveErrorScore M s ω m z := by
    intro ω m
    obtain ⟨_hs, _hs1, _heps, _heps1, _hF, _hP, _hR, hD, _hGood, _hZ, _hbase⟩ := hprim ω
    exact hD m z
  constructor
  · simp_rw [hZeq]
    exact hZtail M (hdelta.trans (min_le_left _ _)) z n k
  · simp_rw [hDeq]
    apply (hDtail M (hdelta.trans (min_le_right _ _)) z n k).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (by norm_num : (2 : ℝ) ≤ 3) (Real.exp_pos _).le)

end SubdiffusiveProcess.Paper
