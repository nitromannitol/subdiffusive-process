import SubdiffusiveProcess.Paper.goodext_parent_oscillation_from_graph
import SubdiffusiveProcess.Analysis.CenteredL2Continuity




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal

noncomputable section
namespace Paper


/-- Uniform source convergence and energy-measure recovery convert coarse oscillation into parent energy. -/
theorem aux_goodext_parent_oscillation_of_l2_cutoff
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (un : ℕ → weakSobolevGraph (centeredCube z r hr))
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, ((un n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] UN n)
    (hU : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hosc : Tendsto (fun n => normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => UN n x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ * ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), UN n y)) atTop
      (𝓝 (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
        (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ * ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y))))
    (sigma cell : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1) (hcell : 0 < cell)
    (sN : ℕ → ℝ) (s : ℝ) (hsN : ∀ n, 0 < sN n) (hs : 0 < s)
    (hsLim : Tendsto sN atTop (𝓝 s))
    (hell : ∀ n, cell * sN n ≤ I.lam z r hr (a n) z r sigma 2)
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    [hfinN : ∀ n, IsFiniteMeasure (muN n)] [IsFiniteMeasure mu]
    (henergy : ∀ n, (muN n (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      localGradientEnergy (a n) (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (un n).val))
    (parentCell : Set (SpatialCoordinates d)) (hparent : MeasurableSet parentCell)
    (chi : SpatialCoordinates d → ℝ)
    (hchiN : ∀ n, Integrable chi (muN n)) (hchi : Integrable chi mu)
    (hchi0 : ∀ x, 0 ≤ chi x) (hchi1 : ∀ x, chi x ≤ 1)
    (hchiQ : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), chi x = 1)
    (hchiP : ∀ x ∉ parentCell, chi x = 0)
    (hrec : Tendsto (fun n => ∫ x, chi x ∂muN n) atTop (𝓝 (∫ x, chi x ∂mu))) :
    (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
      (Pin.C ^ 2 * r ^ 2 *
        ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
          Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * s⁻¹ *
        (mu parentCell).toReal := by
  let C := Pin.C ^ 2 * r ^ 2 *
    ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  have hc0 : 0 < Homogenization.Book.Ch02.geometricDiscount sigma 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1 := div_pos
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by positivity))
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by norm_num))
  have hC : 0 ≤ C := div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (inv_nonneg.mpr (mul_pos hc0 hcell).le)) (centeredCube_volume_pos z hr).le
  apply oscillation_bound_of_energy_measure_recovery muN mu
    (centeredCube z r hr : Set (SpatialCoordinates d)) parentCell
    (centeredCube z r hr).isOpen.measurableSet hparent chi hchiN hchi
    hchi0 hchi1 hchiQ hchiP hrec sN s hsN hs hsLim _ _ hosc C hC
  intro n
  rw [henergy n]
  exact aux_goodext_coarse_poincare_squared hd I Pin z r hr (a n) (un n) (UN n) (hUN n)
    sigma cell (sN n) hsigma hsigma1 hcell (hsN n) (hell n)

/-- A padded local oscillation is controlled by the recovered energy of its open parent. -/
theorem aux_goodext_parent_oscillation_of_l2_chi
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (un : ℕ → weakSobolevGraph (centeredCube z r hr))
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, ((un n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] UN n)
    (hU : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hosc : Tendsto (fun n => normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => UN n x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ * ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), UN n y)) atTop
      (𝓝 (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
        (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ * ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y))))
    (sigma cell : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1) (hcell : 0 < cell)
    (sN : ℕ → ℝ) (s : ℝ) (hsN : ∀ n, 0 < sN n) (hs : 0 < s)
    (hsLim : Tendsto sN atTop (𝓝 s))
    (hell : ∀ n, cell * sN n ≤ I.lam z r hr (a n) z r sigma 2)
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    [hfinN : ∀ n, IsFiniteMeasure (muN n)] [IsFiniteMeasure mu]
    (henergy : ∀ n, (muN n (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      localGradientEnergy (a n) (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (un n).val))
    (parentCell : Set (SpatialCoordinates d)) (hparent : IsOpen parentCell)
    (hpad : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ parentCell)
    (hrec : ∀ chi : SpatialCoordinates d → ℝ, Continuous chi → HasCompactSupport chi →
      Tendsto (fun n => ∫ x, chi x ∂muN n) atTop (𝓝 (∫ x, chi x ∂mu))) :
    (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
      (Pin.C ^ 2 * r ^ 2 *
        ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
          Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * s⁻¹ *
        (mu parentCell).toReal := by
  obtain ⟨chi, hchiQ, hchiPc, hchiP, hchiBounds⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (centeredCube_isBounded z hr).isCompact_closure hparent hpad
  have hbound : ∀ x, ‖chi x‖ ≤ (1 : ℝ) := by
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hchiBounds x).1] using (hchiBounds x).2
  have hintN : ∀ n, Integrable chi (muN n) := by
    intro n
    exact (integrable_const (1 : ℝ)).mono' chi.continuous.aestronglyMeasurable
      (Eventually.of_forall hbound)
  have hint : Integrable chi mu :=
    (integrable_const (1 : ℝ)).mono' chi.continuous.aestronglyMeasurable
      (Eventually.of_forall hbound)
  exact aux_goodext_parent_oscillation_of_l2_cutoff hd I Pin z r hr a un UN U hUN hU hosc
    sigma cell hsigma hsigma1 hcell sN s hsN hs hsLim hell muN mu henergy
    parentCell hparent.measurableSet chi hintN hint
    (fun x => (hchiBounds x).1) (fun x => (hchiBounds x).2)
    (fun x hx => hchiQ (subset_closure hx))
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun hx' => hx (hchiP hx')))
    (hrec chi chi.continuous hchiPc)


/-- Native global energy recovery supplies the exact local energy premise for the parent oscillation bound. -/
theorem aux_goodext_parent_oscillation_of_l2_native
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Q : Opens (SpatialCoordinates d)) (hq : centeredCube z r hr ≤ Q)
    (aRoot : ℕ → PositiveCoefficient Q)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hab : ∀ n, (aRoot n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] (a n).val)
    (un : ℕ → Homogenization.H1Function (Q : Set (SpatialCoordinates d)))
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, (un n).toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] UN n)
    (hU : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hosc : Tendsto (fun n => normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => UN n x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ * ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), UN n y)) atTop
      (𝓝 (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
        (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ * ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y))))
    (sigma cell : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1) (hcell : 0 < cell)
    (sN : ℕ → ℝ) (s : ℝ) (hsN : ∀ n, 0 < sN n) (hs : 0 < s)
    (hsLim : Tendsto sN atTop (𝓝 s))
    (hell : ∀ n, cell * sN n ≤ I.lam z r hr (a n) z r sigma 2)
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    [IsFiniteMeasure mu]
    (henergy : ∀ n, muN n = gradientEnergyMeasure (aRoot n)
      (sobolevGradient (sobolevDataOfH1 (un n))))
    (parentCell : Set (SpatialCoordinates d)) (hparent : IsOpen parentCell)
    (hpad : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ parentCell)
    (hrec : ∀ chi : SpatialCoordinates d → ℝ, Continuous chi → HasCompactSupport chi →
      Tendsto (fun n => ∫ x, chi x ∂muN n) atTop (𝓝 (∫ x, chi x ∂mu))) :
    (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
      (Pin.C ^ 2 * r ^ 2 *
        ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
          Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * s⁻¹ *
        (mu parentCell).toReal := by

  let q : Opens (SpatialCoordinates d) := centeredCube z r hr
  let unLocal : ℕ → weakSobolevGraph q := fun n =>
    ⟨sobolevDataOfH1 ((un n).restrict q.isOpen hq),
      sobolevDataOfH1_mem_weak ((un n).restrict q.isOpen hq)⟩
  have hUNLocal : ∀ n,
      ((unLocal n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] UN n := by
    intro n
    change ((sobolevDataOfH1 ((un n).restrict q.isOpen hq)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] UN n
    calc
      ((sobolevDataOfH1 ((un n).restrict q.isOpen hq)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))]
          ((un n).restrict q.isOpen hq).toFun :=
        sobolevDataOfH1_fst_coeFn ((un n).restrict q.isOpen hq)
      _ =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] (un n).toFun := by
        simpa only [H1Function.restrict] using
          (Filter.EventuallyEq.rfl : (un n).toFun =ᶠ[ae (volume.restrict (q : Set (SpatialCoordinates d)))] (un n).toFun)
      _ =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] UN n :=
        ae_restrict_of_ae_restrict_of_subset hq (hUN n)
  letI hfiniteMuN : ∀ n, IsFiniteMeasure (muN n) := fun n => by
    letI hfiniteRoot : IsFiniteMeasure
        (gradientEnergyMeasure (aRoot n)
          (sobolevGradient (sobolevDataOfH1 (un n)))) :=
      (gradientEnergyMeasure_finite_and_real (aRoot n)
        (sobolevGradient (sobolevDataOfH1 (un n)))).1
    rw [henergy n]
    exact hfiniteRoot
  have hrestrict (n : ℕ) :
      (gradientEnergyMeasure (aRoot n)
        (sobolevGradient (sobolevDataOfH1 (un n)))).restrict (q : Set (SpatialCoordinates d)) =
        gradientEnergyMeasure (a n) (sobolevGradient (unLocal n).val) := by
    exact gradientEnergyMeasure_restrict_of_native_data hq (aRoot n) (a n) (hab n)
      (un n) (unLocal n) rfl
  have hmass (n : ℕ) :
      muN n (q : Set (SpatialCoordinates d)) =
        gradientEnergyMeasure (a n) (sobolevGradient (unLocal n).val)
          (q : Set (SpatialCoordinates d)) := by
    calc
      muN n (q : Set (SpatialCoordinates d)) =
          (gradientEnergyMeasure (aRoot n)
            (sobolevGradient (sobolevDataOfH1 (un n)))).restrict
              (q : Set (SpatialCoordinates d)) (q : Set (SpatialCoordinates d)) := by
        rw [henergy n]
        exact (Measure.restrict_apply_self _ _).symm
      _ = gradientEnergyMeasure (a n) (sobolevGradient (unLocal n).val)
          (q : Set (SpatialCoordinates d)) :=
        congrArg (fun nu : Measure (SpatialCoordinates d) => nu (q : Set (SpatialCoordinates d)))
          (hrestrict n)
  have henergyLocal : ∀ n,
      ((muN n) (q : Set (SpatialCoordinates d))).toReal =
        localGradientEnergy (a n) q.isOpen.measurableSet (sobolevGradient (unLocal n).val) := by
    intro n
    rw [hmass n]
    exact (gradientEnergyMeasure_finite_and_real (a n)
      (sobolevGradient (unLocal n).val)).2 (q : Set (SpatialCoordinates d))
        q.isOpen.measurableSet
  exact aux_goodext_parent_oscillation_of_l2_chi hd I Pin z r hr a unLocal UN U hUNLocal hU hosc
    sigma cell hsigma hsigma1 hcell sN s hsN hs hsLim hell muN mu henergyLocal
    parentCell hparent hpad hrec


/-- Eventual coarse ellipticity, `L²` convergence of the weak graph sequence and energy-measure
recovery give the parent-energy oscillation bound. -/
theorem goodext_parent_oscillation_of_l2
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Q : Opens (SpatialCoordinates d)) (hq : centeredCube z r hr ≤ Q)
    (aRoot : ℕ → PositiveCoefficient Q)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hab : ∀ n, (aRoot n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] (a n).val)
    (un : ℕ → weakSobolevGraph Q)
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, ((un n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] UN n)
    (u : DomainL2 Q) (hconv : Tendsto (fun n => (un n).val.1) atTop (𝓝 u))
    (hU : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U)
    (sigma cell : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1) (hcell : 0 < cell)
    (sN : ℕ → ℝ) (s : ℝ) (hsN : ∀ n, 0 < sN n) (hs : 0 < s)
    (hsLim : Tendsto sN atTop (𝓝 s))
    (hell : ∀ᶠ n in atTop, cell * sN n ≤ I.lam z r hr (a n) z r sigma 2)
    (mu : Measure (SpatialCoordinates d)) [IsFiniteMeasure mu]
    (parentCell : Set (SpatialCoordinates d)) (hparent : IsOpen parentCell)
    (hpad : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ parentCell)
    (hrec : ∀ chi : SpatialCoordinates d → ℝ, Continuous chi → HasCompactSupport chi →
      Tendsto (fun n => ∫ x in (Q : Set (SpatialCoordinates d)),
        chi x * (aRoot n).val x * ∑ i : Fin d, ((sobolevGradient (un n).val i) x) ^ 2) atTop (𝓝 (∫ x, chi x ∂mu))) :
    (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
      (Pin.C ^ 2 * r ^ 2 *
        ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
          Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * s⁻¹ *
        (mu parentCell).toReal := by
  classical
  have hcubeQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (Q : Set (SpatialCoordinates d)) := hq
  have hULp : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    ((Lp.memLp u).ae_eq hU).mono_measure (Measure.restrict_mono hcubeQ le_rfl)
  have hoscFull := tendsto_centered_normalizedL2_of_tendsto_domainL2
    (centeredCube z r hr : Set (SpatialCoordinates d)) hcubeQ
    (centeredCube z r hr).isOpen.measurableSet (centeredCube_volume_pos z hr)
    (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top)
    (fun n => (un n).val.1) u hconv UN U hUN hU
  choose vn hvn hdata using fun n => exists_nativeH1Function_of_ae_representative
    (un n) (UN n) (hUN n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hell
  let seq : ℕ → ℕ := fun n => N + n
  have hseq : StrictMono seq := fun i j hij => Nat.add_lt_add_left hij N
  let muN : ℕ → Measure (SpatialCoordinates d) := fun n =>
    gradientEnergyMeasure (aRoot (seq n)) (sobolevGradient (un (seq n)).val)
  have hrec' : ∀ chi : SpatialCoordinates d → ℝ, Continuous chi → HasCompactSupport chi →
      Tendsto (fun n => ∫ x, chi x ∂muN n) atTop (𝓝 (∫ x, chi x ∂mu)) := by
    intro chi hc hsupp
    have h := (hrec chi hc hsupp).comp hseq.tendsto_atTop
    simpa only [muN, gradientEnergyMeasure_integral] using h
  apply aux_goodext_parent_oscillation_of_l2_native hd I Pin z r hr Q hq
    (fun n => aRoot (seq n)) (fun n => a (seq n)) (fun n => hab (seq n))
    (fun n => vn (seq n)) (fun n => UN (seq n)) U
    (fun n => EventuallyEq.of_eq (hvn (seq n))) hULp
    (hoscFull.comp hseq.tendsto_atTop)
    sigma cell hsigma hsigma1 hcell (fun n => sN (seq n)) s
    (fun n => hsN (seq n)) hs (hsLim.comp hseq.tendsto_atTop)
    (fun n => hN (seq n) (Nat.le_add_right N n)) muN mu
    (fun n => by rw [hdata (seq n)]) parentCell hparent hpad hrec'

end Paper
