module

public import SubdiffusiveProcess.Paper.lfgc_fp_bridge
public import SubdiffusiveProcess.Paper.lfgc_p1_final4
public import SubdiffusiveProcess.Paper.lfgc_draw_carrier

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_tail_cover_three_halves_exp_le {R : ℝ} (hR : 0 < R) (h : ℕ+) :
    ENNReal.ofReal (Real.exp (-(R + 1) * (h : ℝ)) / 2) + ENNReal.ofReal (Real.exp (-(R + 1) * (h : ℝ)) / 2) +
      ENNReal.ofReal (Real.exp (-(R + 1) * (h : ℝ)) / 2) ≤ ENNReal.ofReal (Real.exp (-R * (h : ℝ))) := by
  have hh : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h.one_le
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity)
    (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsplit : Real.exp (-(R + 1) * (h : ℝ)) = Real.exp (-R * (h : ℝ)) * Real.exp (-(h : ℝ)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have he : Real.exp (-(h : ℝ)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have he1 : Real.exp (-1 : ℝ) < 1 / 2 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hE : 0 < Real.exp (-R * (h : ℝ)) := Real.exp_pos _
  nlinarith



theorem lfgc_tail_cover (hd : 2 ≤ d) [NeZero d] (I : Paper.in_J d)
    (Poincare : Paper.in_poincare d hd I) (Extension : Paper.in_extension d hd I)
    (MeyersMorrey : Lane4.SmallPerturbationInput d) (Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d) (Dbase : Paper.sum_errors_baseline_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (lam : ℝ) (hlam : 0 < lam) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hθ₀8 : θ₀ ≤ 1 / 8) (en nc ns : ℕ) (padRoot : Fin en) (enDepth : Fin en → ℕ)
    (hdepth : ∀ e, enDepth e ≤ 3) (hpad : enDepth padRoot = 1)
    (cmpShift : Fin nc → Vec d) (shift : Fin ns → Vec d) (buffer k0 : ℕ) (hk0 : 1 ≤ k0)
    {R : ℝ} (hR : 0 < R) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (eta : ℕ → BilateralField d → PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          Paper.primitive_scores d M sigma eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
      ∀ Carrier : Set (BilateralField d), (chaosSampleLaw M).toMeasure Carrierᶜ = 0 →
        (∀ omega ∈ Carrier, ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
          omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        (∀ omega ∈ Carrier, ∀ N, Paper.primitive_scores d M sigma eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => Praw N m y omega)
          (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        (∀ omega ∈ Carrier, ∀ (N n : ℕ) (y : Vec d), Draw N n y omega ≠ ⊤) →
        (∀ omega ∈ Carrier, Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
      ∀ (m k : ℕ) (z : Vec d),
        IsTailCover (chaosSampleLaw M).toMeasure (aux_lfgc_family_cover_nodeWin d k)
          (Carrier ∩ {omega | ¬ (aux_lfgc_rhs_bridge_rhsDrawOK en nc ns enDepth cmpShift shift buffer Draw m k z omega ∧
            aux_lfgc_rhs_bridge_rhsFPOK en ns padRoot enDepth shift F Praw m k z omega ∧
            aux_lfgc_rhs_bridge_rhsP1OK en nc ns enDepth cmpShift shift buffer k0 lam Draw Z m k z omega ∧
            aux_lfgc_root_stat_nearAll I M H sigma (en * ns) (aux_lfgc_rhs_bridge_lfgcOffset enDepth) (aux_lfgc_rhs_bridge_lfgcShift enDepth shift) (m + k)
              (k : ℤ) z θ₀ omega ∧
            aux_lfgc_root_stat_nearAll I M 0 sigma (en * ns) (aux_lfgc_rhs_bridge_lfgcOffset enDepth) (aux_lfgc_rhs_bridge_lfgcShift enDepth shift) (m + k)
              (k : ℤ) z θ₀ omega)})
          (fun h => ENNReal.ofReal (Real.exp (-R * (h : ℝ)))) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hR1 : 0 < R + 1 := by linarith
  have hoff : ∀ i, -3 ≤ aux_lfgc_rhs_bridge_lfgcOffset (ns := ns) enDepth i ∧ aux_lfgc_rhs_bridge_lfgcOffset (ns := ns) enDepth i ≤ 0 := by
    intro i
    unfold aux_lfgc_rhs_bridge_lfgcOffset
    have := hdepth (finProdFinEquiv.symm i).1
    constructor <;> omega
  obtain ⟨δS, hδS, hS⟩ := lfgc_single_theorem hd I Poincare Extension MeyersMorrey Sobolev D Dbase
    Cresp hCresp sigma hsigma eps heps hθ₀ hθ₀8 (en * ns) (aux_lfgc_rhs_bridge_lfgcOffset enDepth)
    (aux_lfgc_rhs_bridge_lfgcShift enDepth shift) hoff hR1
  obtain ⟨δF, hδF, hF⟩ := lfgc_fp_main (d := d) sigma hsigma.1 hsigma.2 ns hR1
  obtain ⟨δP, hδP, hP⟩ := lfgc_p1_final4 hd I Poincare Extension MeyersMorrey Sobolev D Dbase Cresp hCresp
    sigma hsigma eps heps lam hlam en nc ns enDepth hdepth buffer k0 hk0 hR1
  refine ⟨min δS (min δF δP), lt_min hδS (lt_min hδF hδP), ?_⟩
  intro M hM Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim Carrier hnull hC1 hC2 hC3
    hC4 m k z
  have hMS : M.delta ≤ δS := hM.trans (min_le_left _ _)
  have hMF : M.delta ≤ δF := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMP : M.delta ≤ δP := hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcanon0 : ∀ omega ∈ Carrier, ∀ (j : ℕ) (y : Vec d),
      (aux_lfgc_layer_tail_canonEta 0 omega j : Vec d → ℝ) y = omega (j : ℤ) y := by
    intro omega homega j y
    have hc := aux_lfgc_layer_tail_canonEta_eq 0 (eta 0) omega (fun i x => hC1 omega homega 0 i x)
    rw [← hc, hC1 omega homega 0 j y]
    simp
  have cS := hS M hMS Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim Carrier hnull hC4
    hcanon0 m k z
  set yF : Fin ns → Vec d := fun t => (3 : ℝ) ^ (m + k) •
    (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot) • shift t) with hyF
  have cF := hF M hMF m k yF
  have cP := hP M hMP Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim Carrier hC1 hC2
    hC3 m k z cmpShift shift
  have cU := (cF.union cP).union cS
  refine cU.mono ?_ fun h => aux_lfgc_tail_cover_three_halves_exp_le hR h
  rintro omega ⟨homega, hbad⟩
  simp only [Set.mem_setOf_eq, not_and_or] at hbad
  have hDraw : aux_lfgc_rhs_bridge_rhsDrawOK en nc ns enDepth cmpShift shift buffer Draw m k z omega := by
    intro e D w _ j _ _
    exact hC3 omega homega _ _ _
  rcases hbad with h1 | h2 | h3 | h4 | h5
  · exact absurd hDraw h1
  · left; left
    by_contra hnot
    exact h2 (lfgc_fp_bridge hd1 M sigma eps hsigma.1.le eta F Praw Rraw Draw Z rawGood omega en
      ns padRoot enDepth hpad shift m k z (fun i y => hC1 omega homega (m + k) i y)
      (hC2 omega homega (m + k)) hnot)
  · left; right; exact ⟨homega, h3⟩
  · right; exact ⟨homega, Or.inl h4⟩
  · right; exact ⟨homega, Or.inr h5⟩

end Paper
