module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationTestFunctions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationGenerator

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open Homogenization hiding Vec contDiff_vecNormSq
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty

theorem exists_distance_pair_generators {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D) (hcnn : ∀ y, 0 ≤ c y)
    (x : Vec d) {C Bcap a eps : ℝ} (hC : 0 ≤ C) (hBcap : 0 ≤ Bcap)
    (ha : 1 ≤ a) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hquad : ∀ y, |coeffFluxDiv c (fun z ↦ vecNormSq (z-x)) y/rho y| ≤
      C*(a+vecNormSq (y-x)))
    (hcap : ∀ y, c y/rho y ≤ Bcap*(a+vecNormSq (y-x))) :
    let S := (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense).c0Semigroup
    ∃ f g : S.generatorDomain,
      (∀ y, eps⁻¹+(f : C₀(Vec d, ℝ)) y = vecNormSq (y-x)/(1+eps*vecNormSq (y-x))) ∧
      (∀ y, (eps⁻¹)^2+(g : C₀(Vec d, ℝ)) y = (vecNormSq (y-x)/(1+eps*vecNormSq (y-x)))^2) ∧
      (∀ y, S.generator f y ≤ C*(a+(eps⁻¹+(f : C₀(Vec d, ℝ)) y))) ∧
      (∀ y, S.generator g y ≤ (2*C+8*Bcap)*
        (a*(eps⁻¹+(f : C₀(Vec d, ℝ)) y)+((eps⁻¹)^2+(g : C₀(Vec d, ℝ)) y))) := by
  let A := eps⁻¹
  let q : Vec d → ℝ := fun y ↦ vecNormSq (y-x)
  let J : Vec d → ℝ := fun y ↦ q y/(1+eps*q y)
  let w : C₀(Vec d, ℝ) := -translateC0 x (distanceComplementC0 eps heps heps1)
  have hw : ContDiff ℝ (⊤ : ℕ∞) (w : Vec d → ℝ) :=
    ((contDiff_distanceComplement heps).comp (contDiff_id.sub contDiff_const)).neg
  have hJ : (fun y ↦ A+w y) = J := by
    funext y
    exact (distanceRegularization_eq_const_sub heps (vecNormSq_nonneg (y-x))).symm
  let w2 : C₀(Vec d, ℝ) := (2*A) • w+w*w
  have hw2 : ContDiff ℝ (⊤ : ℕ∞) (w2 : Vec d → ℝ) :=
    contDiff_c0_square_affine w hw A
  have hJ2 : (fun y ↦ A^2+w2 y) = (fun y ↦ (J y)^2) := by
    funext y
    rw [← congrFun hJ y]
    exact (c0_square_affine A w y).symm
  have hflux (y : Vec d) : coeffFluxDiv c w y/rho y =
      (coeffFluxDiv c (fun z ↦ q z) y/rho y)*((1+eps*q y)⁻¹)^2-
      8*eps*q y*(c y/rho y)*((1+eps*q y)⁻¹)^3 := by
    rw [← coeffFluxDiv_const_add c w A y, hJ]
    rw [coeffFluxDiv_comp_centeredVecNormSq (hc.differentiable (by norm_num))
      (fun _ hq ↦ hasDerivAt_distanceRegularization heps hq)
      (fun _ hq ↦ hasDerivAt_distanceRegularizationD heps hq),
      coeffFluxDiv_centeredNormSq (hc.differentiable (by norm_num))]
    exact distance_flux_algebra _ _ _ _ _ _
  let v : Vec d → ℝ := fun y ↦ coeffFluxDiv c w y/rho y
  have hv : Continuous v := (continuous_coeffFluxDiv hc hw).div hrho
    (fun y ↦ (B.weight_pos y).ne')
  let barrier := translateC0 x (radialBarrierC0 2 (by norm_num))
  let K1 := (C+8*Bcap)*a*(eps⁻¹)^2
  have hvb : ∀ y, ‖v y‖ ≤ K1*barrier y := by
    intro y
    change |coeffFluxDiv c w y/rho y| ≤ K1*radialBarrier 1 2 (y-x)
    rw [hflux, radialBarrier_two]
    exact norm_distance_flux_decay heps heps1 (vecNormSq_nonneg (y-x)) ha
      (div_nonneg (hcnn y) (B.weight_pos y).le) hC hBcap (hquad y) (hcap y)
  let v0 := dominatedC0 v hv barrier K1 hvb
  obtain ⟨hm, hgen⟩ := exists_generator_of_smooth_c0 B hc D hdense hD w v0 hw (fun _ ↦ rfl)
  let carre : Vec d → ℝ := fun y ↦ 8*q y*(c y/rho y)*((1+eps*q y)⁻¹)^4
  have hqcont : Continuous q := (contDiff_vecNormSq (d := d) (n := ⊤)).continuous.comp
    (continuous_id.sub continuous_const)
  have hcwcont : Continuous (fun y ↦ c y/rho y) := hc.continuous.div hrho
    (fun y ↦ (B.weight_pos y).ne')
  have hden (y : Vec d) : 1+eps*q y ≠ 0 := by
    have hq := vecNormSq_nonneg (y-x)
    dsimp only [q]
    positivity
  have hcarre : Continuous carre := by
    dsimp only [carre]
    exact ((continuous_const.mul hqcont).mul hcwcont).mul
      (((continuous_const.add (continuous_const.mul hqcont)).inv₀ hden).pow 4)
  let K2 := 8*Bcap*a*(eps⁻¹)^3
  have hcarreb : ∀ y, ‖carre y‖ ≤ K2*barrier y := by
    intro y
    change |8*q y*(c y/rho y)*((1+eps*q y)⁻¹)^4| ≤ K2*radialBarrier 1 2 (y-x)
    rw [radialBarrier_two]
    exact carre_distance_decay heps heps1 (vecNormSq_nonneg (y-x)) ha
      (div_nonneg (hcnn y) (B.weight_pos y).le) hBcap (hcap y)
  let carre0 := dominatedC0 carre hcarre barrier K2 hcarreb
  let v2 : C₀(Vec d, ℝ) := (2*A) • v0+(2:ℝ) • (w*v0)+carre0
  have hflux2 (y : Vec d) : coeffFluxDiv c w2 y/rho y = 2*J y*v y+carre y := by
    rw [← coeffFluxDiv_const_add c w2 (A^2) y, hJ2]
    rw [coeffFluxDiv_comp_centeredVecNormSq (hc.differentiable (by norm_num))
      (fun _ hq ↦ hasDerivAt_squareDistanceRegularization heps hq)
      (fun _ hq ↦ hasDerivAt_squareDistanceRegularizationD heps hq)]
    rw [paired_flux_algebra]
    congr 1
    congr 1
    change _ = coeffFluxDiv c w y/rho y
    rw [hflux, coeffFluxDiv_centeredNormSq (hc.differentiable (by norm_num))]
    exact distance_flux_algebra _ _ _ _ _ _
  have hv2 (y : Vec d) : v2 y = coeffFluxDiv c w2 y/rho y := by
    rw [hflux2, ← congrFun hJ y]
    change 2*A*v y+2*(w y*v y)+carre y = 2*(A+w y)*v y+carre y
    ring
  obtain ⟨hm2, hgen2⟩ := exists_generator_of_smooth_c0 B hc D hdense hD w2 v2 hw2 hv2
  refine ⟨⟨w, hm⟩, ⟨w2, hm2⟩, congrFun hJ, congrFun hJ2, ?_, ?_⟩
  · intro y
    rw [hgen]
    change coeffFluxDiv c w y/rho y ≤ C*(a+(A+w y))
    rw [hflux, congrFun hJ y]
    exact distance_drift_le heps (vecNormSq_nonneg (y-x)) (zero_le_one.trans ha)
      (div_nonneg (hcnn y) (B.weight_pos y).le) hC ((le_abs_self _).trans (hquad y))
  · intro y
    rw [hgen2, hv2, hflux2, congrFun hJ y, congrFun hJ2 y]
    have hvle : v y ≤ C*(a+J y) := by
      dsimp only [v]
      rw [hflux]
      exact distance_drift_le heps (vecNormSq_nonneg (y-x)) (zero_le_one.trans ha)
        (div_nonneg (hcnn y) (B.weight_pos y).le) hC ((le_abs_self _).trans (hquad y))
    exact square_distance_drift_le heps (vecNormSq_nonneg (y-x)) (zero_le_one.trans ha)
      (div_nonneg (hcnn y) (B.weight_pos y).le) hC hBcap hvle (hcap y)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
