import SubdiffusiveProcess.Paper.goodext_parent_oscillation_from_native
import SubdiffusiveProcess.Sobolev.NativeRepresentativeData

/-! The actual weak graph test-integral recovery controls local source oscillation.
The supplied eventual lower coefficient is retained with its original reference sequence. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal
noncomputable section
namespace Paper

/-- Eventual coarse ellipticity and actual weak graph recovery give the parent-energy oscillation bound. -/
theorem goodext_parent_oscillation_from_graph
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
    (hU : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hlim : TendstoUniformlyOn UN U atTop (centeredCube z r hr : Set (SpatialCoordinates d)))
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
  apply goodext_parent_oscillation_from_native hd I Pin z r hr Q hq
    (fun n => aRoot (seq n)) (fun n => a (seq n)) (fun n => hab (seq n))
    (fun n => vn (seq n)) (fun n => UN (seq n)) U
    (fun n => EventuallyEq.of_eq (hvn (seq n))) hU
    (hlim.seq_tendstoUniformlyOn seq hseq.tendsto_atTop)
    sigma cell hsigma hsigma1 hcell (fun n => sN (seq n)) s
    (fun n => hsN (seq n)) hs (hsLim.comp hseq.tendsto_atTop)
    (fun n => hN (seq n) (Nat.le_add_right N n)) muN mu
    (fun n => by rw [hdata (seq n)]) parentCell hparent hpad hrec'

end Paper
