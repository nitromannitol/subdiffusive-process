module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.ResponseMoments.Subdivision

@[expose] public section

/-! Finite convergence-in-measure banks admit common subsequences and strict finite-horizon events. This module does not assert any PDE estimate. -/

open Filter MeasureTheory Set
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A finite family of convergence-in-measure sequences has a common almost-surely convergent subsequence. -/
lemma aux_candidate_good_estimates_finite_bank_support_finite_ae_subseq
    {Om : Type*} [MeasurableSpace Om] (P : MeasureTheory.Measure Om)
    (n : ℕ) (X : Fin n → ℕ → Om → ℝ) (Xlim : Fin n → Om → ℝ)
    (hconv : ∀ i : Fin n, TendstoInMeasure P (fun m => X i m) atTop (Xlim i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ omega ∂P, ∀ i : Fin n, Tendsto (fun m => X i (ns m) omega) atTop (𝓝 (Xlim i omega)) := by
  induction n with
  | zero =>
      exact ⟨id, strictMono_id, by
        filter_upwards with omega i
        exact i.elim0⟩
  | succ n ih =>
      obtain ⟨ns, hns, hae⟩ :=
        ih (fun i => X i.castSucc) (fun i => Xlim i.castSucc) (fun i => hconv i.castSucc)
      have hconvLast : TendstoInMeasure P (fun m => X (Fin.last n) (ns m)) atTop
          (Xlim (Fin.last n)) :=
        fun ε hε => (hconv (Fin.last n) ε hε).comp hns.tendsto_atTop
      obtain ⟨ms, hms, hae'⟩ := hconvLast.exists_seq_tendsto_ae
      refine ⟨ns ∘ ms, hns.comp hms, ?_⟩
      filter_upwards [hae, hae'] with omega hprev hlast
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact (hprev j).comp hms.tendsto_atTop
      · exact hlast


/-- A finite index type admits a common almost-surely convergent subsequence. -/
lemma aux_candidate_good_estimates_finite_bank_support_finite_ae_subseq_fintype
    {Om : Type*} [MeasurableSpace Om] (P : MeasureTheory.Measure Om)
    {ι : Type*} [Fintype ι]
    (X : ι → ℕ → Om → ℝ) (Xlim : ι → Om → ℝ)
    (hconv : ∀ i : ι, TendstoInMeasure P (fun m => X i m) atTop (Xlim i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ omega ∂P, ∀ i : ι, Tendsto (fun m => X i (ns m) omega) atTop (𝓝 (Xlim i omega)) := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨ns, hns, hae⟩ :=
    aux_candidate_good_estimates_finite_bank_support_finite_ae_subseq P (Fintype.card ι)
      (fun k m => X (e.symm k) m) (fun k => Xlim (e.symm k)) (fun k => hconv (e.symm k))
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae] with omega h i
  simpa using h (e i)


section CgeEventsSection
open Filter MeasureTheory Set
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology

/-- The strict finite bank of tests holds eventually on one subsequence.
The bank is fixed before the cutoff tends to infinity. -/
lemma aux_candidate_good_estimates_finite_bank_support_finite_event
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : ι → ℕ → Ω → ℝ) (L : ι → Ω → ℝ)
    (hconv : ∀ i, TendstoInMeasure P (X i) atTop (L i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ omega ∂P,
      ∀ b : ι → ℝ, (∀ i, L i omega < b i) →
        ∀ᶠ n in atTop, ∀ i, X i (ns n) omega < b i := by
  obtain ⟨ns, hns, hAE⟩ := aux_candidate_good_estimates_finite_bank_support_finite_ae_subseq_fintype P X L hconv
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hAE] with omega homega
  intro b hb
  exact eventually_all.2 (fun i => (homega i).eventually (gt_mem_nhds (hb i)))

/-- One common subsequence makes two finite scalar banks satisfy their strict
limits. This keeps the later event proof independent of the concrete bank
index types. -/
lemma aux_candidate_good_estimates_finite_bank_support_finite_event_sum
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (P : Measure Ω)
    (X : ι → ℕ → Ω → ℝ) (L : ι → Ω → ℝ) (b : ι → ℝ)
    (hconv : ∀ i, TendstoInMeasure P (X i) atTop (L i))
    (Y : κ → ℕ → Ω → ℝ) (M : κ → Ω → ℝ) (c : κ → ℝ)
    (hconvY : ∀ i, TendstoInMeasure P (Y i) atTop (M i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ omega ∂P,
      (∀ i, L i omega < b i) → (∀ i, M i omega < c i) →
        ∀ᶠ n in atTop,
          (∀ i, X i (ns n) omega < b i) ∧ (∀ i, Y i (ns n) omega < c i) := by
  let ι' := ι ⊕ κ
  let X' : ι' → ℕ → Ω → ℝ := Sum.elim X Y
  let L' : ι' → Ω → ℝ := Sum.elim L M
  let b' : ι' → ℝ := Sum.elim b c
  have hconv' : ∀ i, TendstoInMeasure P (X' i) atTop (L' i) := by
    intro i
    cases i with
    | inl i => exact hconv i
    | inr i => exact hconvY i
  obtain ⟨ns, hns, hEvent⟩ :=
    aux_candidate_good_estimates_finite_bank_support_finite_event P X' L' hconv'
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hEvent] with omega homega
  intro hb hc
  have hbound : ∀ i : ι', L' i omega < b' i := by
    intro i
    cases i with
    | inl i => exact hb i
    | inr i => exact hc i
  have hev := homega b' hbound
  filter_upwards [hev] with n hn
  constructor
  · intro i
    exact hn (Sum.inl i)
  · intro i
    exact hn (Sum.inr i)

/-- A single subsequence enters any finite family of open windows whose
pointwise limits lie strictly inside those windows. -/
lemma aux_candidate_good_estimates_finite_bank_support_finite_window_event
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : ι → ℕ → Ω → ℝ) (L lo hi : ι → Ω → ℝ)
    (hconv : ∀ i, TendstoInMeasure P (X i) atTop (L i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ omega ∂P,
      (∀ i, lo i omega < L i omega ∧ L i omega < hi i omega) →
        ∀ᶠ n in atTop, ∀ i, lo i omega < X i (ns n) omega ∧ X i (ns n) omega < hi i omega := by
  have hconvNeg : ∀ i, TendstoInMeasure P (fun n omega => -X i n omega) atTop
      (fun omega => -L i omega) := by
    intro i ε hε
    simpa only [TendstoInMeasure, edist_neg_neg] using hconv i ε hε
  let ι' := ι ⊕ ι
  let X' : ι' → ℕ → Ω → ℝ := Sum.elim X (fun i n omega => -X i n omega)
  let L' : ι' → Ω → ℝ := Sum.elim L (fun i omega => -L i omega)
  have hconv' : ∀ i, TendstoInMeasure P (X' i) atTop (L' i) := by
    intro i
    cases i with
    | inl i => exact hconv i
    | inr i => exact hconvNeg i
  obtain ⟨ns, hns, hEvent⟩ := aux_candidate_good_estimates_finite_bank_support_finite_event P X' L' hconv'
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hEvent] with omega homega
  intro hmargin
  let b : ι' → ℝ := Sum.elim (fun i => (L i omega + hi i omega) / 2)
    (fun i => -((lo i omega + L i omega) / 2))
  have hb : ∀ i, L' i omega < b i := by
    intro i
    cases i with
    | inl i => dsimp [L', b]; linarith only [(hmargin i).2]
    | inr i => dsimp [L', b]; linarith only [(hmargin i).1]
  have hEv := homega b hb
  filter_upwards [hEv] with n hn
  intro i
  constructor
  · have hmid := hn (Sum.inr i)
    dsimp [X', b] at hmid
    linarith only [(hmargin i).1, hmid]
  · have hmid := hn (Sum.inl i)
    dsimp [X', b] at hmid
    linarith only [(hmargin i).2, hmid]

/-- One finite horizon can retain the strict prefix, coefficient, error, and
reference-ratio margins at once. -/
lemma aux_candidate_good_estimates_finite_bank_support_finite_candidate_margin_event
    {Ω ι κ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [Fintype ν]
    (P : Measure Ω)
    (prefixN : ι → ℕ → Ω → ℝ) (prefixLim scoreCut : ι → Ω → ℝ)
    (lowN highN : κ → ℕ → Ω → ℝ) (lowLim highLim : κ → Ω → ℝ)
    (errN : ℕ → Ω → ℝ) (errLim : Ω → ℝ)
    (ratioN : ν → ℕ → Ω → ℝ) (ratioLim : ν → Ω → ℝ)
    (hPrefix : ∀ i, TendstoInMeasure P (prefixN i) atTop (prefixLim i))
    (hLow : ∀ i, TendstoInMeasure P (lowN i) atTop (lowLim i))
    (hHigh : ∀ i, TendstoInMeasure P (highN i) atTop (highLim i))
    (hErr : TendstoInMeasure P errN atTop errLim)
    (hRatio : ∀ i, TendstoInMeasure P (ratioN i) atTop (ratioLim i))
    (cell epshom cdet : ℝ) (hcell : 0 < cell) (hepshom : 0 < epshom)
    (hcdet : 0 < cdet)
    (good : Ω → Prop)
    (hGood : ∀ᵐ omega ∂P, good omega →
      (∀ i, prefixLim i omega < scoreCut i omega) ∧
      (∀ i, cell ≤ lowLim i omega ∧ highLim i omega ≤ cell⁻¹) ∧
      errLim omega ≤ epshom * cdet ∧
      (∀ i, ratioLim i omega ∈ Set.Ioo (1 / 2 : ℝ) 2)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ omega ∂P, good omega → ∀ᶠ n in atTop,
      (∀ i, prefixN i (ns n) omega < scoreCut i omega) ∧
      (∀ i, cell / 2 < lowN i (ns n) omega ∧ highN i (ns n) omega < 2 * cell⁻¹) ∧
      errN (ns n) omega < 2 * epshom * cdet ∧
      (∀ i, ratioN i (ns n) omega ∈ Set.Ioo (1 / 2 : ℝ) 2) := by
  let J := ι ⊕ ((κ × Bool) ⊕ (Unit ⊕ ν))
  let XJ : J → ℕ → Ω → ℝ := Sum.elim prefixN
    (Sum.elim (fun q => if q.2 then highN q.1 else lowN q.1)
      (Sum.elim (fun _ => errN) ratioN))
  let LJ : J → Ω → ℝ := Sum.elim prefixLim
    (Sum.elim (fun q => if q.2 then highLim q.1 else lowLim q.1)
      (Sum.elim (fun _ => errLim) ratioLim))
  let loJ : J → Ω → ℝ := Sum.elim (fun i omega => prefixLim i omega - 1)
    (Sum.elim (fun q omega => if q.2 then highLim q.1 omega - 1 else cell / 2)
      (Sum.elim (fun _ omega => errLim omega - 1)
        (fun i _ => (1 / 2 : ℝ))))
  let hiJ : J → Ω → ℝ := Sum.elim scoreCut
    (Sum.elim (fun q omega => if q.2 then 2 * cell⁻¹ else lowLim q.1 omega + 1)
      (Sum.elim (fun _ omega => 2 * epshom * cdet)
        (fun i _ => (2 : ℝ))))
  have hconvJ : ∀ i, TendstoInMeasure P (XJ i) atTop (LJ i) := by
    intro i
    rcases i with i | q
    · exact hPrefix i
    · rcases q with q | e
      · rcases q with ⟨k, b⟩
        cases b
        · exact hLow k
        · exact hHigh k
      · rcases e with e | j
        · cases e
          exact hErr
        · exact hRatio j
  have hMargin : ∀ᵐ omega ∂P, good omega →
      ∀ i, loJ i omega < LJ i omega ∧ LJ i omega < hiJ i omega := by
    filter_upwards [hGood] with omega homega
    intro hg
    have hGoodomega := homega hg
    intro i
    rcases i with i | q
    · constructor
      · dsimp [loJ, LJ]
        have hpos : (0 : ℝ) < 1 := by norm_num
        linarith only [hpos]
      · dsimp [LJ, hiJ]
        exact hGoodomega.1 i
    · rcases q with q | e
      · rcases q with ⟨k, b⟩
        cases b
        · constructor
          · dsimp [loJ, LJ]
            calc
              cell / 2 < cell := by linarith only [hcell]
              _ ≤ lowLim k omega := (hGoodomega.2.1 k).1
          · dsimp [hiJ, LJ]
            exact lt_add_of_pos_right _ one_pos
        · constructor
          · dsimp [loJ, LJ]
            exact sub_lt_self _ one_pos
          · dsimp [hiJ, LJ]
            have hinv : 0 < cell⁻¹ := inv_pos.mpr hcell
            have hinv' : cell⁻¹ < 2 * cell⁻¹ := by linarith only [hinv]
            exact (hGoodomega.2.1 k).2.trans_lt hinv'
      · rcases e with e | j
        · cases e
          constructor
          · dsimp [loJ, LJ]
            exact sub_lt_self _ one_pos
          · dsimp [hiJ, LJ]
            have hprod : 0 < epshom * cdet := mul_pos hepshom hcdet
            have hstrict : epshom * cdet < 2 * epshom * cdet := by
              linarith only [hprod]
            exact hGoodomega.2.2.1.trans_lt hstrict
        · constructor
          · dsimp [loJ, LJ]
            exact (hGoodomega.2.2.2 j).1
          · dsimp [hiJ, LJ]
            exact (hGoodomega.2.2.2 j).2
  obtain ⟨ns, hns, hWindow⟩ :=
    aux_candidate_good_estimates_finite_bank_support_finite_window_event P XJ LJ loJ hiJ hconvJ
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hWindow, hMargin] with omega homega hmargin
  intro hg
  have hEv := homega (hmargin hg)
  filter_upwards [hEv] with n hn
  refine ⟨?_, ?_⟩
  · intro i
    have h := hn (Sum.inl i)
    simpa [XJ, LJ, hiJ] using h.2
  · refine ⟨?_, ?_⟩
    · intro i
      refine ⟨?_, ?_⟩
      · have h := hn (Sum.inr (Sum.inl (i, false)))
        simpa [XJ, LJ, loJ] using h.1
      · have h := hn (Sum.inr (Sum.inl (i, true)))
        simpa [XJ, hiJ] using h.2
    · refine ⟨?_, ?_⟩
      · have h := hn (Sum.inr (Sum.inr (Sum.inl ())))
        simpa [XJ, hiJ] using h.2
      · intro i
        have h := hn (Sum.inr (Sum.inr (Sum.inr i)))
        simpa [XJ, loJ, hiJ] using h

/-- The finite code space for a prefix test at a fixed depth. -/
abbrev aux_candidate_good_estimates_finite_bank_support_prefix_code (d : ℕ) (Enl Shift : Type*) (D : ℕ) :=
  (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)

/-- The subtype of prefix codes whose depth lies in a finite horizon. -/
abbrev aux_candidate_good_estimates_finite_bank_support_prefix_event_index
    (d : ℕ) (Enl Shift : Type*) (horizon k0 : ℕ) :=
  (Enl × Shift) ×
    (Σ D : Fin (horizon + 1),
      {_code : aux_candidate_good_estimates_finite_bank_support_prefix_code d Enl Shift D.val // k0 ≤ D.val})

/-- At each fixed horizon, strict limit margins provide one common subsequence
for both prefix banks, cell ellipticity, the error, and all reference ratios. -/
lemma aux_candidate_good_estimates_finite_bank_support_finite_horizon_event
    {d : ℕ} {Ω Enl Shift Cmp : Type*} [MeasurableSpace Ω]
    [Fintype Enl] [Fintype Shift] [Fintype Cmp]
    (P : Measure Ω) (horizon k0 : ℕ)
    (prefixZN prefixDN : aux_candidate_good_estimates_finite_bank_support_prefix_event_index d Enl Shift horizon k0 → ℕ → Ω → ℝ)
    (prefixZLim prefixDLim : aux_candidate_good_estimates_finite_bank_support_prefix_event_index d Enl Shift horizon k0 → Ω → ℝ)
    (lowN highN : Enl × Shift → ℕ → Ω → ℝ)
    (lowLim highLim : Enl × Shift → Ω → ℝ)
    (errN : ℕ → Ω → ℝ) (errLim : Ω → ℝ)
    (ratioN : Cmp → ℕ → Ω → ℝ) (ratioLim : Cmp → Ω → ℝ)
    (hPrefixZ : ∀ i, TendstoInMeasure P (prefixZN i) atTop (prefixZLim i))
    (hPrefixD : ∀ i, TendstoInMeasure P (prefixDN i) atTop (prefixDLim i))
    (hLow : ∀ i, TendstoInMeasure P (lowN i) atTop (lowLim i))
    (hHigh : ∀ i, TendstoInMeasure P (highN i) atTop (highLim i))
    (hErr : TendstoInMeasure P errN atTop errLim)
    (hRatio : ∀ i, TendstoInMeasure P (ratioN i) atTop (ratioLim i))
    (cell epshom cdet lambdaCut : ℝ) (hcell : 0 < cell)
    (hepshom : 0 < epshom) (hcdet : 0 < cdet)
    (good : Ω → Prop)
    (hGood : ∀ᵐ omega ∂P, good omega →
      (∀ i, prefixZLim i omega < lambdaCut * (i.2.1.val : ℝ) ∧
        prefixDLim i omega < lambdaCut * (i.2.1.val : ℝ)) ∧
      (∀ i, cell ≤ lowLim i omega ∧ highLim i omega ≤ cell⁻¹) ∧
      errLim omega ≤ epshom * cdet ∧
      (∀ i, ratioLim i omega ∈ Set.Ioo (1 / 2 : ℝ) 2)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ omega ∂P, good omega → ∀ᶠ n in atTop,
      (∀ i, prefixZN i (ns n) omega < lambdaCut * (i.2.1.val : ℝ) ∧
        prefixDN i (ns n) omega < lambdaCut * (i.2.1.val : ℝ)) ∧
      (∀ i, cell / 2 < lowN i (ns n) omega ∧ highN i (ns n) omega < 2 * cell⁻¹) ∧
      errN (ns n) omega < 2 * epshom * cdet ∧
      (∀ i, ratioN i (ns n) omega ∈ Set.Ioo (1 / 2 : ℝ) 2) := by
  let Pref := aux_candidate_good_estimates_finite_bank_support_prefix_event_index d Enl Shift horizon k0
  let Bank := Pref × Bool
  let prefixN : Bank → ℕ → Ω → ℝ := fun p n omega =>
    if p.2 then prefixDN p.1 n omega else prefixZN p.1 n omega
  let prefixLim : Bank → Ω → ℝ := fun p omega =>
    if p.2 then prefixDLim p.1 omega else prefixZLim p.1 omega
  let cut : Bank → Ω → ℝ := fun p _ => lambdaCut * (p.1.2.1.val : ℝ)
  have hPrefix : ∀ p, TendstoInMeasure P (prefixN p) atTop (prefixLim p) := by
    intro p
    rcases p with ⟨i, b⟩
    cases b
    · simpa [prefixN, prefixLim] using hPrefixZ i
    · simpa [prefixN, prefixLim] using hPrefixD i
  have hGood' : ∀ᵐ omega ∂P, good omega →
      (∀ p, prefixLim p omega < cut p omega) ∧
      (∀ i, cell ≤ lowLim i omega ∧ highLim i omega ≤ cell⁻¹) ∧
      errLim omega ≤ epshom * cdet ∧
      (∀ i, ratioLim i omega ∈ Set.Ioo (1 / 2 : ℝ) 2) := by
    filter_upwards [hGood] with omega homega
    intro hg
    have homega' := homega hg
    refine ⟨?_, homega'.2⟩
    intro p
    rcases p with ⟨i, b⟩
    cases b
    · simpa [prefixLim, cut] using (homega'.1 i).1
    · simpa [prefixLim, cut] using (homega'.1 i).2
  obtain ⟨ns, hns, hEvent⟩ :=
    aux_candidate_good_estimates_finite_bank_support_finite_candidate_margin_event P
      prefixN prefixLim cut lowN highN lowLim highLim errN errLim ratioN ratioLim
      hPrefix hLow hHigh hErr hRatio cell epshom cdet hcell hepshom hcdet good hGood'
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hEvent] with omega homega
  intro hg
  filter_upwards [homega hg] with n hn
  refine ⟨?_, ?_⟩
  · intro i
    constructor
    · exact hn.1 ⟨i, false⟩
    · exact hn.1 ⟨i, true⟩
  · exact hn.2

/-- A finite prefix bank has one common subsequence retaining all strict horizon margins. -/
theorem candidate_good_estimates_finite_bank_support
    {d : ℕ} {Ω Enl Shift Cmp : Type*} [MeasurableSpace Ω]
    [Fintype Enl] [Fintype Shift] [Fintype Cmp]
    (P : Measure Ω) (horizon k0 : ℕ)
    (prefixZ prefixD : ℕ → (U : Enl × Shift) → (D : ℕ) →
      aux_candidate_good_estimates_finite_bank_support_prefix_code d Enl Shift D → Ω → ℝ)
    (prefixZLim prefixDLim : (U : Enl × Shift) → (D : ℕ) →
      aux_candidate_good_estimates_finite_bank_support_prefix_code d Enl Shift D → Ω → ℝ)
    (lowN highN : Enl × Shift → ℕ → Ω → ℝ)
    (lowLim highLim : Enl × Shift → Ω → ℝ)
    (errN : ℕ → Ω → ℝ) (errLim : Ω → ℝ)
    (ratioN : Cmp → ℕ → Ω → ℝ) (ratioLim : Cmp → Ω → ℝ)
    (hPrefixZ : ∀ U D code, TendstoInMeasure P (fun n => prefixZ n U D code) atTop
      (prefixZLim U D code))
    (hPrefixD : ∀ U D code, TendstoInMeasure P (fun n => prefixD n U D code) atTop
      (prefixDLim U D code))
    (hLow : ∀ U, TendstoInMeasure P (lowN U) atTop (lowLim U))
    (hHigh : ∀ U, TendstoInMeasure P (highN U) atTop (highLim U))
    (hErr : TendstoInMeasure P errN atTop errLim)
    (hRatio : ∀ c, TendstoInMeasure P (ratioN c) atTop (ratioLim c))
    (cell epshom cdet lambdaCut : ℝ) (hcell : 0 < cell)
    (hepshom : 0 < epshom) (hcdet : 0 < cdet) (good : Ω → Prop)
    (hGood : ∀ᵐ omega ∂P, good omega →
      (∀ U D, k0 ≤ D → ∀ code,
        prefixZLim U D code omega < lambdaCut * (D : ℝ) ∧
        prefixDLim U D code omega < lambdaCut * (D : ℝ)) ∧
      (∀ U, cell ≤ lowLim U omega ∧ highLim U omega ≤ cell⁻¹) ∧
      errLim omega ≤ epshom * cdet ∧
      (∀ c, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ omega ∂P, good omega → ∀ᶠ n in atTop,
      (∀ U D, k0 ≤ D → D ≤ horizon → ∀ code,
        prefixZ (ns n) U D code omega < lambdaCut * (D : ℝ) ∧
        prefixD (ns n) U D code omega < lambdaCut * (D : ℝ)) ∧
      (∀ U, cell / 2 < lowN U (ns n) omega ∧ highN U (ns n) omega < 2 * cell⁻¹) ∧
      errN (ns n) omega < 2 * epshom * cdet ∧
      (∀ c, ratioN c (ns n) omega ∈ Set.Ioo (1 / 2 : ℝ) 2) := by
  let Pref := aux_candidate_good_estimates_finite_bank_support_prefix_event_index d Enl Shift horizon k0
  let prefixZN : Pref → ℕ → Ω → ℝ := fun i n omega =>
    prefixZ n i.1 i.2.1.val i.2.2.1 omega
  let prefixDN : Pref → ℕ → Ω → ℝ := fun i n omega =>
    prefixD n i.1 i.2.1.val i.2.2.1 omega
  let prefixZL : Pref → Ω → ℝ := fun i omega => prefixZLim i.1 i.2.1.val i.2.2.1 omega
  let prefixDL : Pref → Ω → ℝ := fun i omega => prefixDLim i.1 i.2.1.val i.2.2.1 omega
  have hGood' : ∀ᵐ omega ∂P, good omega →
      (∀ i : Pref, prefixZL i omega < lambdaCut * (i.2.1.val : ℝ) ∧
        prefixDL i omega < lambdaCut * (i.2.1.val : ℝ)) ∧
      (∀ U, cell ≤ lowLim U omega ∧ highLim U omega ≤ cell⁻¹) ∧
      errLim omega ≤ epshom * cdet ∧ (∀ c, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2) := by
    filter_upwards [hGood] with omega hlim
    intro hg
    rcases hlim hg with ⟨hpfx, hcell, herr, hratio⟩
    refine ⟨?_, hcell, herr, hratio⟩
    intro i
    simpa only [prefixZL, prefixDL] using
      hpfx i.1 i.2.1.val i.2.2.2 i.2.2.1
  obtain ⟨ns, hns, hevent⟩ :=
    aux_candidate_good_estimates_finite_bank_support_finite_horizon_event P horizon k0
      prefixZN prefixDN prefixZL prefixDL lowN highN lowLim highLim errN errLim ratioN ratioLim
      (by intro i; simpa only [prefixZN, prefixZL] using
        hPrefixZ i.1 i.2.1.val i.2.2.1)
      (by intro i; simpa only [prefixDN, prefixDL] using
        hPrefixD i.1 i.2.1.val i.2.2.1)
      hLow hHigh hErr hRatio cell epshom cdet lambdaCut hcell hepshom hcdet good hGood'
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hevent] with omega he
  intro hg
  filter_upwards [he hg] with n hn
  refine ⟨?_, hn.2⟩
  intro U D hD hDh code
  exact hn.1 ⟨U, ⟨⟨D, Nat.lt_succ_of_le hDh⟩, ⟨code, hD⟩⟩⟩

/-- Horizon-wise eventual events admit a diagonal family of strict subsequences. -/
lemma aux_candidate_good_estimates_finite_bank_support_diagonal_horizons
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (good : Ω → Prop)
    (event : ℕ → ℕ → Ω → Prop)
    (hEvent : ∀ horizon, ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ omega ∂P, good omega → ∀ᶠ n in atTop, event horizon (ns n) omega) :
    ∃ nu : ℕ → ℕ → ℕ, (∀ horizon, StrictMono (nu horizon)) ∧
      ∀ᵐ omega ∂P, good omega → ∀ horizon, ∀ᶠ n in atTop,
        event horizon (nu horizon n) omega := by
  choose nu hnu hnuEvent using hEvent
  refine ⟨nu, hnu, ?_⟩
  have hAE : ∀ᵐ omega ∂P, ∀ horizon, good omega →
      ∀ᶠ n in atTop, event horizon (nu horizon n) omega := ae_all_iff.mpr hnuEvent
  filter_upwards [hAE] with omega hω
  exact fun hg horizon => hω horizon hg

/-- Uniform moments give a pathwise bounded subsequence, including for
nonmeasurable representatives of measurable equivalence classes. -/
lemma aux_candidate_good_estimates_finite_bank_support_moment_subseq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ → Ω → ℝ) (p : ℝ≥0∞) (hp : p ≠ 0) (C : ℝ≥0)
    (hK : ∀ n, AEStronglyMeasurable (K n) P)
    (hC : ∀ n, eLpNorm (K n) p P ≤ C) :
    ∀ᵐ omega ∂P, ∃ (B : ℝ) (ns : ℕ → ℕ),
      0 ≤ B ∧ StrictMono ns ∧ ∀ n, |K (ns n) omega| ≤ B := by
  let F : ℕ → Ω → ℝ := fun n => (hK n).mk (K n)
  have hF : ∀ n, Measurable (F n) := fun n => (hK n).measurable_mk
  have heq : ∀ n, K n =ᵐ[P] F n := fun n => (hK n).ae_eq_mk
  have hFC : ∀ n, eLpNorm (F n) p P ≤ C := by
    intro n
    rw [← eLpNorm_congr_ae (heq n)]
    exact hC n
  have hlim := ae_bdd_liminf_atTop_of_eLpNorm_bdd hp hFC
  filter_upwards [hlim, ae_all_iff.2 heq] with omega homega hEq
  obtain ⟨B, hB⟩ := ENNReal.exists_nat_gt homega.ne
  have hfreq : ∃ᶠ n in atTop, ‖F n omega‖ₑ < (B : ℝ≥0∞) :=
    frequently_lt_of_liminf_lt (h := hB)
  obtain ⟨ns, hns, hbound⟩ := extraction_of_frequently_atTop hfreq
  refine ⟨B, ns, Nat.cast_nonneg B, hns, ?_⟩
  intro n
  rw [hEq (ns n)]
  have h := ENNReal.toReal_mono (by simp : (B : ℝ≥0∞) ≠ ⊤) (hbound n).le
  simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_natCast] using h

/-- Eventual finite-horizon tests and budgets pass through a horizonwise subsequence into any supplied estimate. -/
theorem aux_candidate_good_estimates_finite_bank_support_eventual_camp
    {Ω A : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (good : Ω → Prop) (seq ns : ℕ → ℕ → ℕ)
    (event budget : ℕ → ℕ → Ω → Prop)
    (out : ℕ → ℕ → Ω → ℕ → A → Prop)
    (hevent : ∀ᵐ omega ∂P, good omega → ∀ h, ∀ᶠ n in atTop, event h (seq h n) omega)
    (hbudget : ∀ᵐ omega ∂P, good omega → ∀ h n,
      event h (seq h n) omega → budget h (seq h n) omega)
    (hns : ∀ h, StrictMono (ns h))
    (hcamp : ∀ h n omega, event h (seq h n) omega → budget h (seq h n) omega →
      ∀ D, D ≤ h → ∀ x, out h (seq h n) omega D x) :
    ∀ᵐ omega ∂P, good omega → ∀ h D, D ≤ h → ∀ x,
      ∀ᶠ n in atTop, out h (seq h (ns h n)) omega D x := by
  filter_upwards [hevent, hbudget] with omega he hb
  intro hg h D hDh x
  have hev := (hns h).tendsto_atTop.eventually (he hg h)
  filter_upwards [hev] with n htest
  exact hcamp h (ns h n) omega htest (hb hg h (ns h n) htest) D hDh x


end CgeEventsSection
end SubdiffusiveProcess.Paper
end
