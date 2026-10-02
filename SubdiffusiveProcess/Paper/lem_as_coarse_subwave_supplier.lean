import SubdiffusiveProcess.Paper.lem_as_coarse_subwavelength

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Choose the subwavelength exponential rate before the disorder threshold.
This is the scalar small-disorder choice used by the parent proof. -/
theorem aux_lem_as_coarse_subwave_supplier_rate
    (s Cp Cd : ℝ) (hs : 0 < s) (hCp : 0 < Cp) (hCd : 0 < Cd) :
    ∃ delta0 gamma : ℝ, 0 < delta0 ∧ 0 < gamma ∧
      gamma < s * Real.log 3 ∧
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ delta0 →
        Cd * delta + Cp * delta ^ 2 ≤ gamma := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let t : ℝ := s * Real.log 3
  let D : ℝ := Cd + Cp
  have ht : 0 < t := mul_pos hs hlog
  have hD : 0 < D := add_pos hCd hCp
  have h4D : 0 < 4 * D := by positivity
  refine ⟨min 1 (t / (4 * D)), t / 2, lt_min zero_lt_one (div_pos ht h4D),
    half_pos ht, ?_, ?_⟩
  · dsimp [t]
    linarith
  · intro delta hdelta hsmall
    have hle1 : delta ≤ 1 := hsmall.trans (min_le_left _ _)
    have hlet : delta ≤ t / (4 * D) := hsmall.trans (min_le_right _ _)
    have hsq : delta ^ 2 ≤ delta := by
      nlinarith [mul_nonneg hdelta (sub_nonneg.mpr hle1)]
    have hrate : Cd * delta + Cp * delta ^ 2 ≤ D * delta := by
      dsimp [D]
      nlinarith [mul_nonneg hCp.le (sub_nonneg.mpr hsq)]
    have hmul := mul_le_mul_of_nonneg_left hlet hD.le
    have hid : D * (t / (4 * D)) = t / 4 := by
      field_simp
    rw [hid] at hmul
    linarith

/-- A rate condition on the scalar exponent in the fixed-cube estimate.  The
majorants and their moment bounds are the data supplied by
`aux_lem_extremes_upper`, separately for the two infrared conventions. -/
theorem aux_lem_as_coarse_subwave_supplier
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s p : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hp : 1 ≤ p)
    (mlow mhigh : Bool → ℕ → BilateralField d → ℝ)
    (C gamma : Bool → ℝ)
    (hpositive : ∀ b, 0 < C b ∧ 0 < gamma b ∧ gamma b < s * Real.log 3)
    (henvelope : ∀ b N om, 0 ≤ mhigh b N om + (mlow b N om)⁻¹)
    (hmeas : ∀ b N, AEStronglyMeasurable
      (fun om => mhigh b N om + (mlow b N om)⁻¹)
      (chaosSampleLaw M).toMeasure)
    (hmoment : ∀ b N, eLpNorm
      (fun om => mhigh b N om + (mlow b N om)⁻¹)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (C b * Real.exp (gamma b * (N : ℝ)))) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ Ksub : ℝ, 0 < Ksub ∧ ∀ b : Bool, ∀ N0 N : ℕ, N0 ≤ N →
        (3 : ℝ) ^ (-(s * (N : ℝ))) *
          (mhigh b N om + (mlow b N om)⁻¹) ≤ Ksub := by
  have htail := lem_as_coarse_subwavelength d hd M s p hs hp
    (fun b N om => mhigh b N om + (mlow b N om)⁻¹)
    henvelope hmeas (fun b => ⟨C b, gamma b,
      (hpositive b).1, (hpositive b).2.1, (hpositive b).2.2, hmoment b⟩)
  filter_upwards [htail] with om hom
  obtain ⟨Ksub, hKsub, hbound⟩ := hom
  exact ⟨Ksub, hKsub, fun b N0 N _ => hbound b N⟩

/-- The form usable with the existential witnesses of `aux_lem_extremes_upper`:
positivity of the lower and upper majorants is needed only almost surely.
Taking absolute values makes the envelope globally nonnegative without changing
its `eLpNorm`; on the extrema event the absolute value is the envelope itself. -/
theorem aux_lem_as_coarse_subwave_supplier_ae
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s p : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hp : 1 ≤ p)
    (mlow mhigh : Bool → ℕ → BilateralField d → ℝ)
    (C gamma : Bool → ℝ)
    (hpositive : ∀ b, 0 < C b ∧ 0 < gamma b ∧ gamma b < s * Real.log 3)
    (hext : ∀ b : Bool, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ N, 0 < mlow b N om ∧ mlow b N om ≤ mhigh b N om)
    (hmem : ∀ b N, MemLp
      (fun om => mhigh b N om + (mlow b N om)⁻¹)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hmoment : ∀ b N, eLpNorm
      (fun om => mhigh b N om + (mlow b N om)⁻¹)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (C b * Real.exp (gamma b * (N : ℝ)))) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ Ksub : ℝ, 0 < Ksub ∧ ∀ b : Bool, ∀ N0 N : ℕ, N0 ≤ N →
        (3 : ℝ) ^ (-(s * (N : ℝ))) *
          (mhigh b N om + (mlow b N om)⁻¹) ≤ Ksub := by
  let f : Bool → ℕ → BilateralField d → ℝ :=
    fun b N om => mhigh b N om + (mlow b N om)⁻¹
  have htail := lem_as_coarse_subwavelength d hd M s p hs hp
    (fun b N om => |f b N om|)
    (fun b N om => abs_nonneg _)
    (fun b N => by
      have h := (hmem b N).1.norm
      simpa only [Real.norm_eq_abs] using h)
    (fun b => ⟨C b, gamma b, (hpositive b).1, (hpositive b).2.1,
      (hpositive b).2.2, fun N => by
        simpa only [f, ← Real.norm_eq_abs, eLpNorm_norm] using hmoment b N⟩)
  filter_upwards [htail, hext true, hext false] with om hom ht hf
  obtain ⟨Ksub, hKsub, hbound⟩ := hom
  refine ⟨Ksub, hKsub, ?_⟩
  intro b N0 N _
  have hpos : 0 ≤ f b N om := by
    have hb : 0 < mlow b N om ∧ mlow b N om ≤ mhigh b N om := by
      cases b with
      | true => exact ht N
      | false => exact hf N
    exact add_nonneg (le_trans hb.1.le hb.2) (inv_nonneg.mpr hb.1.le)
  simpa only [abs_of_nonneg hpos] using hbound b N

/-- The `aux_lem_extremes_upper` witness clauses, with one scalar choice of a
slightly larger positive exponent below `s log 3`, yield the exact pathwise
`hSN` input.  The two Bool indices correspond to the two infrared fields. -/
theorem lem_as_coarse_subwave_supplier
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s p : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hp : 1 ≤ p)
    (H : Bool → BilateralField d → C(SpatialCoordinates d, ℝ))
    (mlow mhigh : Bool → ℕ → BilateralField d → ℝ)
    (Cp Cd gamma : ℝ) (hCp : 0 < Cp)
    (hgamma : 0 < gamma ∧
      Cd * M.delta + Cp * M.delta ^ 2 ≤ gamma ∧ gamma < s * Real.log 3)
    (hext : ∀ b : Bool, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ N, 0 < mlow b N om ∧
        ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          mlow b N om ≤ cutoffCoefficient M (H b) om N x ∧
            cutoffCoefficient M (H b) om N x ≤ mhigh b N om)
    (hmem : ∀ b N, MemLp
      (fun om => mhigh b N om + (mlow b N om)⁻¹)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hmoment : ∀ b N, eLpNorm
      (fun om => mhigh b N om + (mlow b N om)⁻¹)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cp * Real.exp
        ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)))) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ Ksub : ℝ, 0 < Ksub ∧ ∀ b : Bool, ∀ N0 N : ℕ, N0 ≤ N →
        (3 : ℝ) ^ (-(s * (N : ℝ))) *
          (mhigh b N om + (mlow b N om)⁻¹) ≤ Ksub := by
  have hz : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    change dist z z ≤ r / 2
    rw [dist_self]
    positivity
  apply aux_lem_as_coarse_subwave_supplier_ae d hd M s p hs hp mlow mhigh
    (fun _ => Cp) (fun _ => gamma)
  · intro b
    exact ⟨hCp, hgamma.1, hgamma.2.2⟩
  · intro b
    filter_upwards [hext b] with om hom
    intro N
    exact ⟨(hom N).1, ((hom N).2 z hz).1.trans ((hom N).2 z hz).2⟩
  · exact hmem
  · intro b N
    have hrate :
        (Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ) ≤ gamma * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hgamma.2.1 (Nat.cast_nonneg N)
    have hbound : Cp * Real.exp
        ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)) ≤
        Cp * Real.exp (gamma * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) hCp.le
    exact (hmoment b N).trans (ENNReal.ofReal_le_ofReal hbound)


/-- Freeze the scalar rate before selecting a model; the extrema witnesses then
give the subwavelength pathwise estimate without an extra rate hypothesis. -/
theorem aux_lem_as_coarse_subwave_supplier_rate_interface
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s p Cp Cd : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hp : 1 ≤ p)
    (hCp : 0 < Cp) (hCd : 0 < Cd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (H : Bool → BilateralField d → C(SpatialCoordinates d, ℝ))
        (mlow mhigh : Bool → ℕ → BilateralField d → ℝ),
        (∀ b : Bool, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ N, 0 < mlow b N om ∧
            ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              mlow b N om ≤ cutoffCoefficient M (H b) om N x ∧
                cutoffCoefficient M (H b) om N x ≤ mhigh b N om) →
        (∀ b N, MemLp
          (fun om => mhigh b N om + (mlow b N om)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
        (∀ b N, eLpNorm
          (fun om => mhigh b N om + (mlow b N om)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * Real.exp
            ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)))) →
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∃ Ksub : ℝ, 0 < Ksub ∧ ∀ b : Bool, ∀ N0 N : ℕ, N0 ≤ N →
            (3 : ℝ) ^ (-(s * (N : ℝ))) *
              (mhigh b N om + (mlow b N om)⁻¹) ≤ Ksub := by
  obtain ⟨delta0, gamma, hdelta0, hgamma0, hgammalt, hrate⟩ :=
    aux_lem_as_coarse_subwave_supplier_rate s Cp Cd hs.1 hCp hCd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM z r hr H mlow mhigh hext hmem hmoment
  exact lem_as_coarse_subwave_supplier d hd M z r hr s p hs hp H mlow mhigh
    Cp Cd gamma hCp
    ⟨hgamma0, hrate M.delta M.shellPrefix.delta_pos.le hM, hgammalt⟩
    hext hmem hmoment

end Paper
