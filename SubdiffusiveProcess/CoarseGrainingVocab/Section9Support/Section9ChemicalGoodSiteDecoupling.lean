module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalLocalCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalGuardedDecoupling

@[expose] public section

/-!
# Decoupling of the full good-site indicator field

Goodness in a finite spatial ball depends on event centres outside that ball.
The high-scale tail here includes the cardinality of every influence box.
`exists_goodSiteDecoupling` consequently applies to the full bad-site indicator
sigma-algebras, with no cylinder-approximation or mixing input added.

The cutoff has guard `R ≥ 100 (2 Cbox + Cdep + 1)`. A single natural threshold
absorbs all entropy terms, and the rate is a positive constant times `q`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open MeasureTheory Set ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal
noncomputable section
theorem tsum_ofReal_weighted_linear_le {Cp N A : ℝ} (hCp : 0 ≤ Cp)
 (hN : 1 ≤ N) (hA : Real.log N + Real.log 2 ≤ A) :
 (∑' n : ℕ, ENNReal.ofReal (Cp*N^n*Real.exp (-(A*((n:ℝ)+1))))) ≤
 ENNReal.ofReal (2*Cp*Real.exp (-A)) := by
  have hN0 : 0 ≤ N := by linarith
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (summable_pow_mul_exp_neg (Cp := Cp) hN hA)]
  exact ENNReal.ofReal_le_ofReal (tsum_pow_mul_exp_neg_le hCp hN hA)

theorem triadic_weight_absorbed {N A : ℝ} (hN : 1 ≤ N)
 (hA : 2*Real.log N ≤ A) (j : ℕ) :
 N^(j+1)*Real.exp (-(A*3^((3:ℝ)*(j+1)/2))) ≤
 Real.exp (-((A/2)*3^((3:ℝ)*(j+1)/2))) := by
  have hNpos : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hT : ((j+1 : ℕ) : ℝ) ≤ (3:ℝ)^((3:ℝ)*(j+1)/2) := by
    have h := three_rpow_three_halves_mul_ge (j+1)
    push_cast at h ⊢
    linarith
  have hkey := (mul_le_mul_of_nonneg_right hT hlog).trans
    (mul_le_mul_of_nonneg_left (show Real.log N ≤ A/2 by linarith)
      (by positivity : 0 ≤ (3:ℝ)^((3:ℝ)*(j+1)/2)))
  calc N^(j+1)*Real.exp (-(A*3^((3:ℝ)*(j+1)/2)))
      = Real.exp ((((j+1:ℕ):ℝ)*Real.log N) + -(A*3^((3:ℝ)*(j+1)/2))) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hNpos]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem badSite_agrees_truncation_off_tail {d Cbox j0 : ℕ} {Ω : Type*}
 (E : ℕ → Lattice d → Set Ω) (z : Lattice d) (ω : Ω)
 (h : ω ∉ highLevelInfluence E Cbox j0 z) :
 (ω ∈ percolationBadSite E Cbox z ↔ ω ∈ truncatedBadSite E Cbox j0 z) := by
 constructor
 · intro hfull
   rcases (percolationBadSite_subset_truncated_union_tail E z hfull) with htr | htail
   · exact htr
   · exact absurd htail h
 · exact fun htr => truncatedBadSite_subset E z htr

theorem measurableSet_percolationBadSite {d Cbox : ℕ} {Ω : Type*}
 [MeasurableSpace Ω] (E : ℕ → Lattice d → Set Ω)
 (hE : ∀ j z, MeasurableSet (E j z)) (z : Lattice d) :
 MeasurableSet (percolationBadSite E Cbox z) := by
 rw [percolationBadSite_eq_iUnion]
 unfold influenceFailure
 exact MeasurableSet.iUnion fun j =>
 MeasurableSet.iUnion fun u =>
 MeasurableSet.iUnion fun _hu => hE j u

theorem measurableSet_truncatedBadSite_ambient {d Cbox j0 : ℕ} {Ω : Type*}
 [MeasurableSpace Ω] (E : ℕ → Lattice d → Set Ω)
 (hE : ∀ j z, MeasurableSet (E j z)) (z : Lattice d) :
 MeasurableSet (truncatedBadSite E Cbox j0 z) := by
  unfold truncatedBadSite influenceFailure
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _hj =>
    MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun _hu => hE j u

theorem exists_badSite_truncation {d Cbox j0 : ℕ} {Ω : Type*}
 (E : ℕ → Lattice d → Set Ω) (S : Set (Lattice d)) {A : Set Ω}
 (hA : MeasurableSet[eventFieldSigma (percolationBadSite E Cbox) S] A) :
 ∃ B, MeasurableSet[eventFieldSigma (truncatedBadSite E Cbox j0) S] B ∧
 ∀ ω, ω ∉ (⋃ z∈S, highLevelInfluence E Cbox j0 z) → (ω∈A ↔ ω∈B) := by
  refine exists_measurable_agree_off
    (eventFieldSigma (truncatedBadSite E Cbox j0) S) _ _ ?_ hA
  rintro A' ⟨z, hz, rfl⟩
  refine ⟨truncatedBadSite E Cbox j0 z, measurableSet_event_of_mem hz, ?_⟩
  intro ω hω
  exact badSite_agrees_truncation_off_tail E z ω
    (fun ht => hω (Set.mem_iUnion₂.mpr ⟨z, hz, ht⟩))

theorem measure_finite_highLevelInfluence_le {d Cbox j0 : ℕ} {Ω : Type*}
 [MeasurableSpace Ω] (μ : Measure Ω) (E : ℕ → Lattice d → Set Ω)
 (F : Finset (Lattice d)) (b : ℝ≥0∞)
 (h : ∀ z, μ (highLevelInfluence E Cbox j0 z) ≤ b) :
 μ (⋃ z∈F, highLevelInfluence E Cbox j0 z) ≤ F.card*b := by
  calc μ (⋃ z ∈ F, highLevelInfluence E Cbox j0 z)
      ≤ ∑ z ∈ F, μ (highLevelInfluence E Cbox j0 z) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ F, b := Finset.sum_le_sum fun z _ => h z
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem eventFieldSigma_le_ambient {d : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
 (F : Lattice d → Set Ω) (hF : ∀ z, MeasurableSet (F z)) (S : Set (Lattice d)) :
 eventFieldSigma F S ≤ m := by
 exact eventFieldSigma_le_of_measurable F S m (fun z _ => hF z)

theorem exists_badSite_truncation_measure {d Cbox j0 : ℕ} {Ω : Type*}
 [MeasurableSpace Ω] (μ : Measure Ω) (E : ℕ → Lattice d → Set Ω)
 (hE : ∀ j z, MeasurableSet (E j z)) (F : Finset (Lattice d)) {A : Set Ω}
 (hA : MeasurableSet[eventFieldSigma (percolationBadSite E Cbox) (F : Set (Lattice d))] A) :
 ∃ B, MeasurableSet[eventFieldSigma (truncatedBadSite E Cbox j0) (F : Set (Lattice d))] B ∧
 μ (A\B)+μ (B\A) ≤ μ (⋃z∈F, highLevelInfluence E Cbox j0 z) := by
  obtain ⟨B, hB, hagree⟩ := exists_badSite_truncation (j0 := j0) E (F : Set (Lattice d)) hA
  have hAamb : MeasurableSet A :=
    (eventFieldSigma_le_ambient _ (measurableSet_percolationBadSite E hE) _) _ hA
  have hBamb : MeasurableSet B :=
    (eventFieldSigma_le_ambient _ (measurableSet_truncatedBadSite_ambient E hE) _) _ hB
  exact ⟨B, hB, measure_differences_le μ hAamb hBamb
    (sdiff_union_subset_of_agree_off hagree)⟩

theorem tsum_ofReal_shifted_weighted_le {Cp N A : ℝ} (hCp : 0 ≤ Cp)
 (hN : 1 ≤ N) (hA : Real.log N + Real.log 2 ≤ A) (j : ℕ) :
 (∑' n : ℕ, ENNReal.ofReal (Cp*N^(n+j+1)*Real.exp (-(A*3^((3:ℝ)*(n+j+1)/2))))) ≤
 ENNReal.ofReal (2*(Cp*N^(j+1))*Real.exp (-(A*3^((3:ℝ)*(j+1)/2)))) := by
  have hN0 : 0 ≤ N := by linarith
  have hA0 : 0 ≤ A := (add_nonneg (Real.log_nonneg hN)
    (Real.log_nonneg (by norm_num : (1:ℝ)≤2))).trans hA
  have hT : (1:ℝ) ≤ (3:ℝ)^((3:ℝ)*(j+1)/2) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hAt : Real.log N + Real.log 2 ≤ A*(3:ℝ)^((3:ℝ)*(j+1)/2) := by
    refine hA.trans ?_
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hT hA0
  have hs := tsum_ofReal_weighted_linear_le (Cp := Cp*N^(j+1)) (by positivity) hN hAt
  refine (ENNReal.tsum_le_tsum (fun n => ?_)).trans hs
  apply ENNReal.ofReal_le_ofReal
  calc Cp*N^(n+j+1)*Real.exp (-(A*3^((3:ℝ)*(n+j+1)/2)))
      ≤ Cp*N^(n+j+1)*Real.exp (-((A*3^((3:ℝ)*(j+1)/2))*((n:ℝ)+1))) :=
        mul_le_mul_of_nonneg_left (shifted_exp_le hA0 n j) (by positivity)
    _ = _ := by rw [show n+j+1 = n+(j+1) by omega, pow_add]; ring

theorem measure_highLevelInfluence_le_exp {d Cbox j0 : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (E : ℕ → Lattice d → Set Ω)
    {Cprob A : ℝ} (hCbox : 1 ≤ Cbox) (hCprob : 0 ≤ Cprob)
    (hA : 2*(Real.log ((3:ℝ)^d)+Real.log 2) ≤ A)
    (hp : ∀ j z, μ (E j z) ≤ ENNReal.ofReal (Cprob*Real.exp (-(A*3^((3:ℝ)*j/2)))))
    (z : Lattice d) :
    μ (highLevelInfluence E Cbox j0 z) ≤
      ENNReal.ofReal (2*(Cprob*(((3*Cbox)^d:ℕ):ℝ))*Real.exp (-((A/2)*3^((3:ℝ)*(j0+1)/2)))) := by
  let Cp : ℝ := Cprob*(((3*Cbox)^d:ℕ):ℝ)
  let N : ℝ := (3:ℝ)^d
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hN : 1 ≤ N := by dsimp [N]; exact one_le_pow₀ (by norm_num)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hl2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hent : Real.log N + Real.log 2 ≤ A := by dsimp [N] at *; linarith
  have hlog : 2*Real.log N ≤ A := by dsimp [N] at *; linarith
  have hbase := measure_highLevelInfluence_le_tsum μ E Cbox j0 z _ hp
  have hterm : ∀ n : ℕ,
      (((2*(Cbox*3^(n+j0+1))+1)^d:ℕ):ℝ≥0∞)*
        ENNReal.ofReal (Cprob*Real.exp (-(A*3^((3:ℝ)*(n+j0+1)/2)))) ≤
      ENNReal.ofReal (Cp*N^(n+j0+1)*Real.exp (-(A*3^((3:ℝ)*(n+j0+1)/2)))) := by
    intro n
    have hcount : (((2*(Cbox*3^(n+j0+1))+1)^d:ℕ):ℝ) ≤
        (((3*Cbox)^d:ℕ):ℝ)*N^(n+j0+1) := by
      dsimp [N]
      exact_mod_cast card_influenceBox_le hCbox d (n+j0+1)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc (((2*(Cbox*3^(n+j0+1))+1)^d:ℕ):ℝ)*
        (Cprob*Real.exp (-(A*3^((3:ℝ)*(n+j0+1)/2))))
        ≤ ((((3*Cbox)^d:ℕ):ℝ)*N^(n+j0+1))*
          (Cprob*Real.exp (-(A*3^((3:ℝ)*(n+j0+1)/2)))) :=
            mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by dsimp [Cp]; ring
  have hs := (ENNReal.tsum_le_tsum hterm).trans
    (tsum_ofReal_shifted_weighted_le hCp hN hent j0)
  have htail : μ (highLevelInfluence E Cbox j0 z) ≤
      ENNReal.ofReal (2*(Cp*N^(j0+1))*Real.exp (-(A*3^((3:ℝ)*(j0+1)/2)))) := by
    refine hbase.trans ?_
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
  have h := mul_le_mul_of_nonneg_left (triadic_weight_absorbed hN hlog j0)
    (show 0 ≤ 2*Cp by positivity)
  dsimp [Cp] at h
  convert h using 1
  ring

theorem goodSite_decoupling_of_probability {d Cbox Cdep : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Lattice d → Set Ω) (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales μ E)
    (hr : MultiscaleFiniteRangeIndependentEvents μ (fun j => Cdep*3^j) E)
    {Cp A : ℝ} (hCbox : 1 ≤ Cbox) (hCp : 0 ≤ Cp)
    (hA : 2*(Real.log ((3:ℝ)^d)+Real.log 2) ≤ A)
    (hp : ∀ j z, μ (E j z) ≤ ENNReal.ofReal (Cp*Real.exp (-(A*3^((3:ℝ)*j/2)))))
    (habs : 2*(Real.log (max 1 (4*(Cp*(((3*Cbox)^d:ℕ):ℝ))*(21:ℝ)^d))+d) ≤
      (A/2)/((100*(2*Cbox+Cdep+1):ℕ):ℝ)^((3:ℝ)/2)) :
    ∀ L R : ℕ, 1 ≤ L → 100*(2*Cbox+Cdep+1) ≤ R →
    ∀ U V : Set Ω, ∀ x y : Lattice d, R*L ≤ latticeDist x y →
    MeasurableSet[eventFieldSigma (percolationBadSite E Cbox) (latticeBallFinset x (10*L) : Set (Lattice d))] U →
    MeasurableSet[eventFieldSigma (percolationBadSite E Cbox) (latticeBallFinset y (10*L) : Set (Lattice d))] V →
    ∃ j0 : ℕ, ∃ U' V' : Set Ω,
      MeasurableSet[eventFieldSigma (truncatedBadSite E Cbox j0) (latticeBallFinset x (10*L) : Set (Lattice d))] U' ∧
      MeasurableSet[eventFieldSigma (truncatedBadSite E Cbox j0) (latticeBallFinset y (10*L) : Set (Lattice d))] V' ∧
      μ (U'\U)+μ (U\U')+μ (V'\V)+μ (V\V') ≤
        ENNReal.ofReal (Real.exp (-((A/(4*((100*(2*Cbox+Cdep+1):ℕ):ℝ)^((3:ℝ)/2)))*((R*L:ℕ):ℝ)^((3:ℝ)/2)))) ∧
      μ (U'∩V') = μ U'*μ V' := by
  intro L R hL hR U V x y hxy hU hV
  obtain ⟨j, _hlower, hupper, _hcut, hsep⟩ := guarded_cutoff hL hR
  obtain ⟨U', hU', heU⟩ := exists_badSite_truncation_measure (j0 := j) μ E hE
    (latticeBallFinset x (10*L)) hU
  obtain ⟨V', hV', heV⟩ := exists_badSite_truncation_measure (j0 := j) μ E hE
    (latticeBallFinset y (10*L)) hV
  have hi := finiteRangeIndependentEvents_truncatedBadSite (Cbox := Cbox) (j0 := j) μ E hE hsc hr
    (latticeBallFinset x (10*L)) (latticeBallFinset y (10*L))
    (fun u hu v hv => latticeDist_separated_balls (hsep.trans_le hxy)
      (mem_latticeBallFinset_iff.mp hu) (mem_latticeBallFinset_iff.mp hv))
  refine ⟨j, U', V', hU', hV', ?_, (Indep_iff _ _ _).mp hi U' V' hU' hV'⟩
  let Cp' : ℝ := Cp*(((3*Cbox)^d:ℕ):ℝ)
  let T : ℝ≥0∞ := ENNReal.ofReal
    (2*((((20*L+1)^d:ℕ):ℝ)*Cp')*Real.exp (-((A/2)*3^((3:ℝ)*(j+1)/2))))
  have ht : ∀ z : Lattice d, μ (⋃ u ∈ latticeBallFinset z (10*L),
      highLevelInfluence E Cbox j u) ≤ T := by
    intro z
    have h := measure_finite_highLevelInfluence_le (j0 := j) μ E (latticeBallFinset z (10*L)) _
      (measure_highLevelInfluence_le_exp μ E hCbox hCp hA hp)
    rw [card_latticeBallFinset, show 2*(10*L)+1 = 20*L+1 by omega,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at h
    simpa only [T, Cp', mul_comm, mul_left_comm, mul_assoc] using h
  refine (two_errors_le (heU.trans (ht x)) (heV.trans (ht y))).trans ?_
  have hlN : 0 ≤ Real.log ((3:ℝ)^d) := Real.log_nonneg (one_le_pow₀ (by norm_num))
  have hlog : Real.log 2 ≤ A/2 := by linarith
  have htwo : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
  dsimp [T]
  rw [htwo, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hd := two_ball_tail_decay (Cp := Cp') (by dsimp [Cp']; positivity) hlog
    d L R (100*(2*Cbox+Cdep+1)) j hL (by omega) (by omega) hupper habs
  convert hd using 1
  · ring
  · congr 1
    ring

/-- Decoupling for the local sigma-algebras of the full bad-site indicator field. -/
def GoodSiteDecoupling {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Lattice d → Set Ω) (Cbox R0 : ℕ) (cP : ℝ) : Prop :=
    ∀ L R : ℕ, 1 ≤ L → R0 ≤ R →
    ∀ U V : Set Ω, ∀ x y : Lattice d, R*L ≤ latticeDist x y →
    MeasurableSet[eventFieldSigma (percolationBadSite E Cbox) (latticeBallFinset x (10*L) : Set (Lattice d))] U →
    MeasurableSet[eventFieldSigma (percolationBadSite E Cbox) (latticeBallFinset y (10*L) : Set (Lattice d))] V →
    ∃ j0 : ℕ, ∃ U' V' : Set Ω,
      MeasurableSet[eventFieldSigma (truncatedBadSite E Cbox j0) (latticeBallFinset x (10*L) : Set (Lattice d))] U' ∧
      MeasurableSet[eventFieldSigma (truncatedBadSite E Cbox j0) (latticeBallFinset y (10*L) : Set (Lattice d))] V' ∧
      μ (U'\U)+μ (U\U')+μ (V'\V)+μ (V\V') ≤
        ENNReal.ofReal (Real.exp (-(cP*((R*L:ℕ):ℝ)^((3:ℝ)/2)))) ∧
      μ (U'∩V') = μ U'*μ V' 

/-- Good-site P3 with uniform constants, including all influence-box centres. -/
theorem exists_goodSiteDecoupling (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 : ℕ, ∃ cP : ℝ, 0 < cP ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : ℕ → Lattice d → Set Ω) (q : ℝ), (q0 : ℝ) ≤ q →
        (∀ j z, μ (E j z) ≤
          ENNReal.ofReal (Cprob*Real.exp (-cprob*q*3^((3:ℝ)*j/2)))) →
        IndependentEventScales μ E →
        MultiscaleFiniteRangeIndependentEvents μ (fun j => Cdep*3^j) E →
        TranslationInvariantEventLaw μ E →
        GoodSiteDecoupling μ E Cbox (100*(2*Cbox+Cdep+1)) (cP*q) := by
  let D : ℕ := 100*(2*Cbox+Cdep+1)
  let Dp : ℝ := (D:ℝ)^((3:ℝ)/2)
  let Cp : ℝ := Cprob*(((3*Cbox)^d:ℕ):ℝ)
  have hD : 0 < D := by dsimp [D]; omega
  have hDp : 0 < Dp := by dsimp [Dp]; positivity
  obtain ⟨qdec, hqdec⟩ := exists_decoupling_threshold d D Cp (cprob/2) (by positivity) hD
  obtain ⟨qent, hqent⟩ := exists_uniform_threshold
    (X := 2*(Real.log ((3:ℝ)^d)+Real.log 2)) hcprob
  refine ⟨max qdec qent, cprob/(4*Dp), by positivity, ?_⟩
  intro Ω _ μ _ E q hq hp hsc hr hlaw
  have hdq : (qdec:ℝ) ≤ q := (show (qdec:ℝ) ≤ (max qdec qent:ℕ) by exact_mod_cast Nat.le_max_left _ _).trans hq
  have heq : (qent:ℝ) ≤ q := (show (qent:ℝ) ≤ (max qdec qent:ℕ) by exact_mod_cast Nat.le_max_right _ _).trans hq
  obtain ⟨_hlog, habs⟩ := hqdec q hdq
  have habs' : 2*(Real.log (max 1 (4*Cp*(21:ℝ)^d))+d) ≤ ((cprob*q)/2)/Dp := by
    dsimp [Dp]
    convert habs using 1
    ring
  have hp' : ∀ j z, μ (E j z) ≤
      ENNReal.ofReal (Cprob*Real.exp (-((cprob*q)*3^((3:ℝ)*j/2)))) := by
    intro j z
    simpa only [neg_mul] using hp j z
  have h := goodSite_decoupling_of_probability μ E hlaw.1 hsc hr hCbox hCprob.le
    (hqent q heq) hp' habs'
  change GoodSiteDecoupling μ E Cbox D ((cprob*q)/(4*Dp)) at h
  convert h using 1
  ring

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
