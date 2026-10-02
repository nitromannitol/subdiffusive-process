import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryMollifiedRealization

/-!
# Strong orbit continuity from a horizontal gradient

The literal GMC carrier is intentionally not replaced by a convenient Polish
model.  For the potential-approximation argument this causes no loss: a scalar
with all strong horizontal derivatives already has a strongly continuous
Koopman orbit.  This is the carrier-free substitute for the ambient topology
used in Superdiffusion's `GradientIdentification.lean`.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable [AddAction (Vec d) Omega]
variable [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

/-- Strongly continuous Koopman vectors form a norm-closed class.  The
uniformity needed here is automatic because every Koopman operator is an
isometry. -/
theorem continuous_koopmanOrbit_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : ℕ → Lp E 2 mu) (Y : Lp E 2 mu)
    (hX : ∀ n, Continuous (fun z : Vec d => koopman (mu := mu) z (X n)))
    (hXY : Filter.Tendsto X Filter.atTop (nhds Y)) :
    Continuous (fun z : Vec d => koopman (mu := mu) z Y) := by
  apply continuous_koopmanOrbit_of_continuousAt_zero Y
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  have hepsilon4 : 0 < epsilon / 4 := by positivity
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hXY) (epsilon / 4) hepsilon4
  have hcont : ContinuousAt
      (fun z : Vec d => koopman (mu := mu) z (X N)) 0 :=
    (hX N).continuousAt
  obtain ⟨delta, hdelta, hball⟩ :=
    Metric.continuousAt_iff.1 hcont (epsilon / 2) (by positivity)
  refine ⟨delta, hdelta, ?_⟩
  intro z hz
  have hmiddle : dist (koopman (mu := mu) z (X N)) (X N) < epsilon / 2 := by
    have := hball hz
    simpa only [koopman_zero] using this
  have hleft : dist (koopman (mu := mu) z Y)
      (koopman (mu := mu) z (X N)) = dist Y (X N) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, LinearIsometry.norm_map]
  have hright : dist (X N) Y < epsilon / 4 := hN N le_rfl
  have hfinal : dist (koopman (mu := mu) z Y) Y < epsilon := by
    calc
      dist (koopman (mu := mu) z Y) Y ≤
        dist (koopman (mu := mu) z Y)
            (koopman (mu := mu) z (X N)) +
          dist (koopman (mu := mu) z (X N)) Y :=
        dist_triangle _ _ _
      _ ≤ dist (koopman (mu := mu) z Y)
            (koopman (mu := mu) z (X N)) +
          (dist (koopman (mu := mu) z (X N)) (X N) + dist (X N) Y) := by
        gcongr
        exact dist_triangle _ _ _
      _ < epsilon := by rw [hleft, dist_comm Y (X N)]; linarith
  simpa only [koopman_zero] using hfinal

private def horizontalQuotScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem horizontalQuotScale_pos (n : ℕ) :
    0 < horizontalQuotScale n := by
  unfold horizontalQuotScale
  positivity

private theorem tendsto_horizontalQuotScale :
    Filter.Tendsto horizontalQuotScale Filter.atTop
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) := by
  have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Filter.Tendsto horizontalQuotScale Filter.atTop
      (nhds (0 : ℝ)) := by
    refine h.congr fun n => ?_
    rw [horizontalQuotScale, one_div]
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    horizontalQuotScale hlim ?_
  exact Filter.Eventually.of_forall fun n => (horizontalQuotScale_pos n).ne'

/-- Koopman translation commutes with stationary mollification when the
particular orbit being mollified is strongly continuous. -/
theorem koopman_mollifyL2_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X : Lp E 2 mu)
    (hX : Continuous (fun w : Vec d => koopman (mu := mu) w X)) :
    koopman (mu := mu) z (mollifyL2 (mu := mu) kappa X) =
      mollifyL2 (mu := mu) kappa (koopman (mu := mu) z X) := by
  rw [mollifyL2, mollifyL2]
  have hint := integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
    (mu := mu) hkappa hcompact X hX
  change (koopman (mu := mu) z).toContinuousLinearMap
      (∫ y : Vec d, kappa y • koopman (mu := mu) (-y) X) = _
  rw [← (koopman (mu := mu) z).toContinuousLinearMap.integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [map_smul]
  change kappa y • koopman (mu := mu) z (koopman (mu := mu) (-y) X) =
    kappa y • koopman (mu := mu) (-y) (koopman (mu := mu) z X)
  rw [koopman_koopman, koopman_koopman]
  congr 2
  abel_nf

/-- Stationary mollification preserves a norm limit inside the class of
strongly continuous particular Koopman orbits. -/
theorem tendsto_mollifyL2_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {alpha : Type*} {l : Filter alpha} {X : alpha → Lp E 2 mu}
    {Y : Lp E 2 mu} {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa)
    (hX : ∀ a, Continuous (fun z : Vec d => koopman (mu := mu) z (X a)))
    (hY : Continuous (fun z : Vec d => koopman (mu := mu) z Y))
    (hXY : Filter.Tendsto X l (nhds Y)) :
    Filter.Tendsto (fun a => mollifyL2 (mu := mu) kappa (X a)) l
      (nhds (mollifyL2 (mu := mu) kappa Y)) := by
  let C : ℝ := ∫ y : Vec d, |kappa y|
  have hC0 : 0 ≤ C := integral_nonneg fun _ => abs_nonneg _
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let eta : ℝ := epsilon / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon hC1
  filter_upwards [(Metric.tendsto_nhds.1 hXY) eta heta] with a ha
  have hsub := mollifyL2_sub_of_continuous (mu := mu) hkappa hcompact
    (X a) Y (hX a) hY
  have hbound := norm_mollifyL2_le (mu := mu) hkappa hcompact (X a - Y)
  have hfrac : C / (C + 1) < 1 := (div_lt_one hC1).2 (by linarith)
  have hCe : C * eta < epsilon := by
    calc
      C * eta = epsilon * (C / (C + 1)) := by
        dsimp only [eta]
        field_simp
      _ < epsilon * 1 := mul_lt_mul_of_pos_left hfrac hepsilon
      _ = epsilon := mul_one _
  rw [dist_eq_norm, ← hsub]
  exact hbound.trans_lt (lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (by
      simpa only [dist_eq_norm] using ha.le) hC0)
    hCe)

private theorem norm_koopman_finsetSum_sub_le
    (phi : ScalarL2 mu) (z : Vec d) :
    ∀ s : Finset (Fin d),
      ‖koopman (mu := mu)
          (∑ i ∈ s, z i • (basisVec i : Vec d)) phi - phi‖ ≤
        ∑ i ∈ s,
          ‖koopman (mu := mu) (z i • (basisVec i : Vec d)) phi - phi‖ := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsum : ∑ j ∈ insert i s, z j • (basisVec j : Vec d) =
          z i • (basisVec i : Vec d) +
            ∑ j ∈ s, z j • (basisVec j : Vec d) := by
        simp [hi]
      have hdecomp :
          koopman (mu := mu)
              (z i • (basisVec i : Vec d) +
                ∑ j ∈ s, z j • (basisVec j : Vec d)) phi - phi =
            koopman (mu := mu) (z i • (basisVec i : Vec d))
                (koopman (mu := mu)
                  (∑ j ∈ s, z j • (basisVec j : Vec d)) phi - phi) +
              (koopman (mu := mu) (z i • (basisVec i : Vec d)) phi - phi) := by
        rw [map_sub, koopman_koopman]
        rw [add_comm (∑ j ∈ s, z j • (basisVec j : Vec d))
          (z i • (basisVec i : Vec d))]
        module
      rw [hsum, hdecomp]
      calc
        ‖koopman (mu := mu) (z i • (basisVec i : Vec d))
              (koopman (mu := mu)
                (∑ j ∈ s, z j • (basisVec j : Vec d)) phi - phi) +
            (koopman (mu := mu) (z i • (basisVec i : Vec d)) phi - phi)‖ ≤
          ‖koopman (mu := mu) (z i • (basisVec i : Vec d))
              (koopman (mu := mu)
                (∑ j ∈ s, z j • (basisVec j : Vec d)) phi - phi)‖ +
            ‖koopman (mu := mu) (z i • (basisVec i : Vec d)) phi - phi‖ :=
              norm_add_le _ _
        _ = ‖koopman (mu := mu)
              (∑ j ∈ s, z j • (basisVec j : Vec d)) phi - phi‖ +
            ‖koopman (mu := mu) (z i • (basisVec i : Vec d)) phi - phi‖ := by
              rw [LinearIsometry.norm_map]
        _ ≤ (∑ j ∈ s,
              ‖koopman (mu := mu) (z j • (basisVec j : Vec d)) phi - phi‖) +
            ‖koopman (mu := mu) (z i • (basisVec i : Vec d)) phi - phi‖ :=
              add_le_add ih le_rfl
        _ = ∑ j ∈ insert i s,
            ‖koopman (mu := mu) (z j • (basisVec j : Vec d)) phi - phi‖ := by
              rw [Finset.sum_insert hi]
              ring

private theorem sum_smul_basisVec (z : Vec d) :
    ∑ i : Fin d, z i • (basisVec i : Vec d) = z := by
  funext j
  simp [basisVec, Pi.single_apply]

/-- A scalar stationary `L²` field with all strong horizontal derivatives has
a strongly continuous full translation orbit. -/
theorem HasHorizontalGradient.continuous_koopmanOrbit
    {phi : ScalarL2 mu} {F : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F) :
    Continuous (fun z : Vec d => koopman (mu := mu) z phi) := by
  apply continuous_koopmanOrbit_of_continuousAt_zero phi
  have hcoord : ∀ i : Fin d, ContinuousAt
      (fun z : Vec d =>
        koopman (mu := mu) (z i • (basisVec i : Vec d)) phi) 0 := by
    intro i
    have hline := (hphi i).continuousAt
    have harg : ContinuousAt (fun z : Vec d => z i) 0 :=
      (continuous_apply i).continuousAt
    simpa only [Function.comp_def, basisVec] using
      hline.comp_of_eq harg rfl
  let g : Vec d → ℝ := fun z => ∑ i : Fin d,
    ‖koopman (mu := mu) (z i • (basisVec i : Vec d)) phi - phi‖
  have hg : ContinuousAt g 0 := by
    have hterm : ∀ i : Fin d, ContinuousAt
        (fun z : Vec d =>
          ‖koopman (mu := mu) (z i • (basisVec i : Vec d)) phi - phi‖) 0 :=
      fun i => ((hcoord i).sub continuousAt_const).norm
    have hsum : ∀ s : Finset (Fin d), ContinuousAt
        (fun z : Vec d => ∑ i ∈ s,
          ‖koopman (mu := mu) (z i • (basisVec i : Vec d)) phi - phi‖) 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa using
            (continuousAt_const : ContinuousAt (fun _ : Vec d => (0 : ℝ)) 0)
      | @insert i s hi ih =>
          simpa [Finset.sum_insert hi] using (hterm i).add ih
    simpa only [g, Finset.sum_filter] using hsum (Finset.univ : Finset (Fin d))
  have hg0 : g 0 = 0 := by simp [g]
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hball⟩ :=
    Metric.continuousAt_iff.1 hg epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro z hz
  have hglt : g z < epsilon := by
    have := hball hz
    have hnonneg : 0 ≤ g z := by
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    simpa only [hg0, Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using this
  have hbound := norm_koopman_finsetSum_sub_le phi z Finset.univ
  rw [sum_smul_basisVec] at hbound
  change ‖koopman (mu := mu) z phi - phi‖ ≤ g z at hbound
  simpa only [koopman_zero, dist_eq_norm] using hbound.trans_lt hglt

/-- Every coordinate of a strong horizontal gradient also has a strongly
continuous full Koopman orbit.  It is the norm limit of the corresponding
difference quotients of the scalar orbit. -/
theorem HasHorizontalGradient.continuous_koopmanOrbit_coord
    {phi : ScalarL2 mu} {F : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F) (i : Fin d) :
    Continuous (fun z : Vec d =>
      koopman (mu := mu) z (vectorL2Coord (mu := mu) i F)) := by
  let A : ℕ → ScalarL2 mu := fun n =>
    (horizontalQuotScale n)⁻¹ •
      (koopman (mu := mu)
          (horizontalQuotScale n • (basisVec i : Vec d)) phi - phi)
  have hphiCont := hphi.continuous_koopmanOrbit
  have hA : ∀ n, Continuous (fun z : Vec d => koopman (mu := mu) z (A n)) := by
    intro n
    have hshift : Continuous (fun z : Vec d =>
        koopman (mu := mu)
          (horizontalQuotScale n • (basisVec i : Vec d) + z) phi) :=
      hphiCont.comp (continuous_const.add continuous_id)
    have hformula : (fun z : Vec d => koopman (mu := mu) z (A n)) =
        fun z => (horizontalQuotScale n)⁻¹ •
          (koopman (mu := mu)
              (horizontalQuotScale n • (basisVec i : Vec d) + z) phi -
            koopman (mu := mu) z phi) := by
      funext z
      dsimp only [A]
      rw [map_smul, map_sub, koopman_koopman]
    rw [hformula]
    exact (hshift.sub hphiCont).const_smul _
  have hslope : Filter.Tendsto
      (fun t : ℝ => t⁻¹ •
        (koopman (mu := mu) (t • (basisVec i : Vec d)) phi - phi))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds (vectorL2Coord (mu := mu) i F)) := by
    have hthis := hasDerivAt_iff_tendsto_slope.1 (hphi i)
    simpa only [slope_fun_def, vsub_eq_sub, sub_zero, basisVec, zero_smul,
      koopman_zero] using hthis
  have hlim : Filter.Tendsto A Filter.atTop
      (nhds (vectorL2Coord (mu := mu) i F)) :=
    hslope.comp tendsto_horizontalQuotScale
  exact continuous_koopmanOrbit_of_tendsto A _ hA hlim

/-- Topology-free gradient identification for stationary mollification.  The
derivative is transported through the mollifier by its norm bound, using only
strong continuity of the two particular orbits supplied by the horizontal
gradient. -/
theorem HasHorizontalGradient.hasDerivAt_koopman_mollifyL2
    {phi : ScalarL2 mu} {F : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F)
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (i : Fin d) :
    HasDerivAt
      (fun t : ℝ => koopman (mu := mu)
        (t • (basisVec i : Vec d))
        (Stationary.mollifyL2 (mu := mu) kappa phi))
      (Stationary.mollifyL2 (mu := mu) kappa
        (vectorL2Coord (mu := mu) i F)) 0 := by
  let G := vectorL2Coord (mu := mu) i F
  let S : ℝ → ScalarL2 mu := fun t =>
    t⁻¹ • (koopman (mu := mu) (t • (basisVec i : Vec d)) phi - phi)
  have hphiCont := hphi.continuous_koopmanOrbit
  have hGCont : Continuous (fun z : Vec d => koopman (mu := mu) z G) := by
    exact hphi.continuous_koopmanOrbit_coord i
  have hSCont : ∀ t, Continuous
      (fun z : Vec d => koopman (mu := mu) z (S t)) := by
    intro t
    have hshift : Continuous (fun z : Vec d =>
        koopman (mu := mu) (t • (basisVec i : Vec d) + z) phi) :=
      hphiCont.comp (continuous_const.add continuous_id)
    have hformula : (fun z : Vec d => koopman (mu := mu) z (S t)) =
        fun z => t⁻¹ •
          (koopman (mu := mu) (t • (basisVec i : Vec d) + z) phi -
            koopman (mu := mu) z phi) := by
      funext z
      dsimp only [S]
      rw [map_smul, map_sub, koopman_koopman]
    rw [hformula]
    exact (hshift.sub hphiCont).const_smul _
  have hslope : Filter.Tendsto S (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds G) := by
    have hthis := hasDerivAt_iff_tendsto_slope.1 (hphi i)
    simpa only [S, G, slope_fun_def, vsub_eq_sub, sub_zero, basisVec,
      zero_smul, koopman_zero] using hthis
  have hmoll := Stationary.tendsto_mollifyL2_of_continuous
    (mu := mu) hkappa hcompact hSCont hGCont hslope
  apply hasDerivAt_iff_tendsto_slope.2
  apply hmoll.congr'
  filter_upwards [] with t
  have hshiftCont : Continuous (fun z : Vec d =>
      koopman (mu := mu) z
        (koopman (mu := mu) (t • (basisVec i : Vec d)) phi)) := by
    have hcomp := hphiCont.comp
      (continuous_const.add continuous_id : Continuous
        (fun z : Vec d => t • (basisVec i : Vec d) + z))
    simpa only [Function.comp_apply, koopman_koopman] using hcomp
  simp only [slope_fun_def, vsub_eq_sub, sub_zero, basisVec]
  rw [zero_smul, koopman_zero,
    Stationary.koopman_mollifyL2_of_continuous (mu := mu)
      (t • (Pi.single i 1 : Vec d)) hkappa hcompact phi hphiCont,
    Stationary.mollifyL2_smul (mu := mu),
    Stationary.mollifyL2_sub_of_continuous (mu := mu) hkappa hcompact _ _
      hshiftCont hphiCont,
    ]
  rfl

/-- Kernel differentiation and mollification of the strong horizontal
gradient agree on the literal GMC-style carrier, without any ambient topology
on the sample space. -/
theorem HasHorizontalGradient.mollifyL2_kernelDeriv_eq_coord
    {phi : ScalarL2 mu} {F : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i : Fin d) :
    Stationary.mollifyL2 (mu := mu) (kernelDeriv kappa i) phi =
      Stationary.mollifyL2 (mu := mu) kappa
        (vectorL2Coord (mu := mu) i F) := by
  have hleft := Stationary.hasDerivAt_koopman_mollifyL2_of_continuous
    (mu := mu) hcompact hkappa phi hphi.continuous_koopmanOrbit i
  have hright := hphi.hasDerivAt_koopman_mollifyL2
    hkappa.continuous hcompact i
  exact hleft.unique hright

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary
