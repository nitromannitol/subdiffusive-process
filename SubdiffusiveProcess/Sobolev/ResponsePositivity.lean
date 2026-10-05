module

public import SubdiffusiveProcess.Sobolev.ResponseSpace

@[expose] public section

/-! # Positivity and linearity of the actual weak source response -/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Poincare and positive ellipticity exclude zero-energy nonzero variations. -/
theorem responseForm_self_eq_zero_iff (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (u : S.space) : responseForm S a u u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    obtain ⟨c, hc, ha⟩ := a.property
    have hg : subspaceGradient S.space u = 0 :=
      eq_zero_of_coercive_self_le_zero (weightedGradientForm_coercive a.val hc ha) hu.le
    obtain ⟨K, hP⟩ := S.poincare
    apply (subspaceGradient_antilipschitz S.space K hP).injective
    simpa only [map_zero] using hg
  · rintro rfl
    simp only [map_zero]

/-- The zero load has the zero solution. -/
theorem responseSolution_zero (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) :
    responseSolution S a 0 = 0 := by
  symm
  apply responseSolution_eq
  intro v
  simp only [map_zero, zero_apply]

/-- The solution is additive in its actual continuous linear load. -/
theorem responseSolution_add (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L M : S.space →L[ℝ] ℝ) :
    responseSolution S a (L + M) = responseSolution S a L + responseSolution S a M := by
  symm
  apply responseSolution_eq
  intro v
  simp only [map_add, add_apply, responseSolution_spec]

/-- The solution is homogeneous in the load, for every real scalar. -/
theorem responseSolution_smul (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (r : ℝ) (L : S.space →L[ℝ] ℝ) :
    responseSolution S a (r • L) = r • responseSolution S a L := by
  symm
  apply responseSolution_eq
  intro v
  simp only [map_smul, smul_apply, responseSolution_spec]

/-- The canonical solution is a linear map on the space of loads. -/
def responseSolutionLinear (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) :
    (S.space →L[ℝ] ℝ) →ₗ[ℝ] S.space where
  toFun := responseSolution S a
  map_add' := responseSolution_add S a
  map_smul' := responseSolution_smul S a

/-- The inverse response vanishes precisely for the zero load. -/
theorem inverseResponse_eq_zero_iff (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) : inverseResponse S a L = 0 ↔ L = 0 := by
  constructor
  · intro h
    have hu : responseSolution S a L = 0 := (responseForm_self_eq_zero_iff S a _).mp h
    ext v
    have he := responseSolution_spec S a L v
    rw [hu, map_zero, zero_apply] at he
    exact he.symm
  · rintro rfl
    rw [inverseResponse_eq_load]
    rfl

/-- Every nonzero load has a strictly positive scalar inverse response. -/
theorem inverseResponse_pos_iff (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) : 0 < inverseResponse S a L ↔ L ≠ 0 := by
  rw [lt_iff_le_and_ne]
  simp only [inverseResponse_nonneg, true_and]
  exact ne_comm.trans (not_congr (inverseResponse_eq_zero_iff S a L))

/-- Polarization of actual inverse responses recovers the mixed load pairing. -/
theorem inverseResponse_polarization
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L M : S.space →L[ℝ] ℝ) :
    inverseResponse S a (L + M) - inverseResponse S a L - inverseResponse S a M =
      2 * L (responseSolution S a M) := by
  let u := responseSolution S a L
  let v := responseSolution S a M
  have huv : responseSolution S a (L + M) = u + v := responseSolution_add S a L M
  have huvload : responseForm S a u v = L v := responseSolution_spec S a L v
  have hvuload : responseForm S a v u = L v :=
    (responseForm_symm S a v u).trans huvload
  change responseForm S a (responseSolution S a (L + M))
      (responseSolution S a (L + M)) - responseForm S a u u - responseForm S a v v =
        2 * L v
  rw [huv]
  have hexpand : responseForm S a (u + v) (u + v) =
      (responseForm S a u u + responseForm S a u v) +
        (responseForm S a v u + responseForm S a v v) := by
    calc
      responseForm S a (u + v) (u + v) =
          (responseForm S a u + responseForm S a v) (u + v) := by
            exact congrArg (fun f : S.space →L[ℝ] ℝ => f (u + v))
              (map_add (responseForm S a) u v)
      _ = responseForm S a u (u + v) + responseForm S a v (u + v) :=
        add_apply _ _ _
      _ = (responseForm S a u u + responseForm S a u v) +
          (responseForm S a v u + responseForm S a v v) := by
            exact congrArg₂ (· + ·) (map_add (responseForm S a u) u v)
              (map_add (responseForm S a v) u v)
  calc
    responseForm S a (u + v) (u + v) - responseForm S a u u - responseForm S a v v =
        ((responseForm S a u u + responseForm S a u v) +
          (responseForm S a v u + responseForm S a v v)) -
            responseForm S a u u - responseForm S a v v := by
              exact congrArg (fun x : ℝ => x - responseForm S a u u - responseForm S a v v)
                hexpand
    _ = 2 * L v := by
      linear_combination huvload + hvuload

/-- Volume-source pairings of the actual weak solver are symmetric and nonnegative. -/
theorem volumeResponse_pairing_symm
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f g : DomainL2 Ω) :
    inner ℝ f (responseSolution S a ((sobolevVolumeLoad g).comp S.space.subtypeL)).val.1 =
      inner ℝ g (responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 := by
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad f).comp S.space.subtypeL
  let M : S.space →L[ℝ] ℝ := (sobolevVolumeLoad g).comp S.space.subtypeL
  change L (responseSolution S a M) = M (responseSolution S a L)
  rw [← responseSolution_spec S a L (responseSolution S a M),
    ← responseSolution_spec S a M (responseSolution S a L)]
  exact responseForm_symm S a _ _

theorem volumeResponse_pairing_nonneg
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f : DomainL2 Ω) :
    0 ≤ inner ℝ f
      (responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 := by
  change 0 ≤ ((sobolevVolumeLoad f).comp S.space.subtypeL)
    (responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL))
  rw [← inverseResponse_eq_load]
  exact inverseResponse_nonneg S a _

/-- The actual weak solution depends continuously on its linear load. -/
theorem continuous_responseSolution
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) :
    Continuous (responseSolution S a) := by
  obtain ⟨K, hP⟩ := S.poincare
  obtain ⟨c, hc, ha⟩ := a.property
  obtain ⟨c', hc', hcoercive⟩ := weightedGradientForm_coercive a.val hc ha
  let A : ℝ := (max K 1 : ℝ≥0)
  have hC : 0 ≤ A ^ 2 / c' :=
    div_nonneg (sq_nonneg _) hc'.le
  suffices hbound : ∀ L : S.space →L[ℝ] ℝ,
      ‖responseSolution S a L‖ ≤
        (A ^ 2 / c') * ‖L‖ by
    exact continuous_of_linear_of_bound (f := responseSolution S a)
      (responseSolution_add S a) (responseSolution_smul S a) hbound
  intro L
  let u := responseSolution S a L
  let g := subspaceGradient S.space u
  have hug : ‖u‖ ≤ A * ‖g‖ := by
    exact sobolevData_norm_le_gradient (u : SobolevData Ω) (hP u)
  have henergy : c' * ‖g‖ * ‖g‖ ≤ L u := by
    calc
      c' * ‖g‖ * ‖g‖ ≤ weightedGradientForm a.val g g := hcoercive g
      _ = responseForm S a u u := rfl
      _ = L u := responseSolution_spec S a L u
  have hload : L u ≤ ‖L‖ * ‖u‖ := by
    exact (le_abs_self (L u)).trans (L.le_opNorm u)
  by_cases hg : ‖g‖ = 0
  · have hu_zero : ‖u‖ = 0 := by
      apply le_antisymm
      · simpa only [hg, mul_zero] using hug
      · exact norm_nonneg u
    have hfinal : ‖u‖ ≤ (A ^ 2 / c') * ‖L‖ := by
      rw [hu_zero]
      exact mul_nonneg hC (norm_nonneg L)
    simpa only [u] using hfinal
  · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg)
    have hcpos : 0 < c' := hc'
    have hAnneg : 0 ≤ A := by positivity
    have hLnneg : 0 ≤ ‖L‖ := norm_nonneg L
    have hcg : (c' * ‖g‖) * ‖g‖ ≤
        (‖L‖ * A) * ‖g‖ := by
      calc
        (c' * ‖g‖) * ‖g‖ = c' * ‖g‖ * ‖g‖ := rfl
        _ ≤ L u := henergy
        _ ≤ ‖L‖ * ‖u‖ := hload
        _ ≤ ‖L‖ * (A * ‖g‖) :=
          mul_le_mul_of_nonneg_left hug hLnneg
        _ = (‖L‖ * A) * ‖g‖ := by rw [mul_assoc]
    have hcg' : c' * ‖g‖ ≤ ‖L‖ * A :=
      le_of_mul_le_mul_right hcg hgpos
    have hg_bound : ‖g‖ ≤
        (‖L‖ * A) / c' :=
      (le_div_iff₀ hcpos).2 (by simpa only [mul_comm] using hcg')
    have hfinal : ‖u‖ ≤ (A ^ 2 / c') * ‖L‖ := by
      calc
        ‖u‖ ≤ A * ‖g‖ := hug
        _ ≤ A * ((‖L‖ * A) / c') :=
          mul_le_mul_of_nonneg_left hg_bound hAnneg
        _ = A ^ 2 / c' * ‖L‖ := by
          simp only [div_eq_mul_inv, pow_two]
          ac_rfl
    simpa only [u] using hfinal

/-- The finite source variational formula gives the load-energy Schwarz bound. -/
theorem sq_load_le_inverseResponse_mul_responseForm
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) (w : S.space) :
    (L w) ^ 2 ≤ inverseResponse S a L * responseForm S a w w := by
  have hquadratic : ∀ s : ℝ,
      0 ≤ responseForm S a w w * (s * s) + (-2 * L w) * s + inverseResponse S a L := by
    intro s
    have hmax := (inverseResponse_isGreatest S a L).2
      (show 2 * L (s • w) - responseForm S a (s • w) (s • w) ∈
        Set.range (fun v : S.space => 2 * L v - responseForm S a v v) from
          ⟨s • w, rfl⟩)
    simp only [map_smul, smul_apply, smul_eq_mul] at hmax
    nlinarith
  have hdisc := discrim_le_zero hquadratic
  simp only [discrim] at hdisc
  nlinarith

/-- The actual volume-source solver has a unique continuous linear representation. -/
theorem existsUnique_volumeResponseOperator
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) :
    ∃! G : DomainL2 Ω →L[ℝ] DomainL2 Ω,
      ∀ f : DomainL2 Ω,
        G f = (responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 := by
  let : NormedSpace ℝ S.space := Submodule.normedSpace S.space
  let first : S.space →L[ℝ] DomainL2 Ω :=
    (ContinuousLinearMap.fst ℝ _ _).comp S.space.subtypeL
  let load : DomainL2 Ω →L[ℝ] (S.space →L[ℝ] ℝ) :=
    ((ContinuousLinearMap.compL ℝ S.space (DomainL2 Ω) ℝ).flip first).comp
      (innerSL ℝ)
  let sol : (S.space →L[ℝ] ℝ) →L[ℝ] S.space :=
    { responseSolutionLinear S a with
      cont := continuous_responseSolution S a }
  let G : DomainL2 Ω →L[ℝ] DomainL2 Ω := first.comp (sol.comp load)
  refine ⟨G, ?_, ?_⟩
  · intro f
    rfl
  · intro H hH
    apply ContinuousLinearMap.ext
    intro f
    exact (hH f).trans (by rfl)

end SubdiffusiveProcess
