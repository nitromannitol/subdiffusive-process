module

public import SubdiffusiveProcess.Paper.in_represented_bounds_seq_collar_error
public import SubdiffusiveProcess.Analysis.BoundedSetBallGrowth

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Convert the catalogue growth clause to all-centre real-valued bounds by the
existing finite-cover estimate. The cube may have arbitrary positive side. -/
theorem aux_in_represented_bounds_seq_collar_product_growth
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR)) (u : ℕ → S.space)
    (t : ℝ) (ht0 : 0 ≤ t) (Bg : ℝ) (hBg : 0 ≤ Bg)
    (hG : ∀ n x, x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y *
            ∑ i : Fin d, ((u n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)))
          (Metric.ball x r) ≤ ENNReal.ofReal (Bg * r ^ t)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n x r, 0 < r → r ≤ 1 →
      (((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((a n).val y *
          ∑ i : Fin d, ((u n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)))
        (Metric.ball x r)).toReal ≤ B * r ^ t := by
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  obtain ⟨A, hA, hgeom⟩ := boundedSet_measure_ball_growth Q
    (isCompact_closure_centeredCube z hR)
  let Bg' : ℝ := 2 ^ t * (A * Bg)
  have hBg' : 0 ≤ Bg' := by dsimp [Bg']; have hA0 := zero_le_one.trans hA; positivity
  refine ⟨Bg', hBg', ?_⟩
  intro n x r hr hr1
  let density : SpatialCoordinates d → ENNReal := fun y => ENNReal.ofReal ((a n).val y *
    ∑ i : Fin d, ((u n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)
  let mu := volume.withDensity density
  have heq : (volume.restrict Q).withDensity density = mu.restrict Q :=
    (restrict_withDensity (centeredCube z R hR).isOpen.measurableSet density).symm
  have hg : ∀ y ∈ Q, ∀ s : ℝ, 0 < s → s ≤ 1 →
      mu (Metric.ball y s ∩ Q) ≤ ENNReal.ofReal (Bg * s ^ t) := by
    intro y hy s hs hs1
    have h := hG n y (subset_closure hy) s hs hs1
    change ((volume.restrict Q).withDensity density) _ ≤ _ at h
    rwa [heq, Measure.restrict_apply Metric.isOpen_ball.measurableSet] at h
  have hall := (hgeom mu Bg t hBg ht0 hg).2 x r hr hr1
  change ((volume.restrict Q).withDensity density (Metric.ball x r)).toReal ≤ _
  rw [heq, Measure.restrict_apply Metric.isOpen_ball.measurableSet]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hall
  rw [ENNReal.toReal_ofReal (mul_nonneg hBg' (Real.rpow_nonneg hr.le _))] at hreal
  exact hreal

/-- A single constant absorbs the source Holder and growth bounds, including
conversion from the Euclidean Holder convention to the ambient supremum metric. -/
theorem aux_in_represented_bounds_seq_collar_product_source
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (u : ℕ → S.space) (uc : ℕ → SpatialCoordinates d → ℝ)
    (alpha t Kh Bg : ℝ) (halpha : 0 < alpha) (hKh : 0 ≤ Kh)
    (hHolder : ∀ n,
      ContinuousOn (uc n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc n) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc n) ≤ Kh ∧
      ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)), uc n x = 0)
    (hG : ∀ n x r, 0 < r → r ≤ 1 →
      (((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((a n).val y *
          ∑ i : Fin d, ((u n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)))
        (Metric.ball x r)).toReal ≤ Bg * r ^ t) :
    ∃ K : ℝ, 1 ≤ K ∧
      (∀ n x y, x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
        y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
        |uc n x - uc n y| ≤ K * dist x y ^ alpha) ∧
      (∀ n x r, 0 < r → r ≤ 1 →
        (((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y *
            ∑ i : Fin d, ((u n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)))
          (Metric.ball x r)).toReal ≤ K * r ^ t) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  let Kh' : ℝ := Kh * (Real.sqrt (d : ℝ)) ^ alpha
  let K : ℝ := max 1 (max Kh' Bg)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKhK : Kh' ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hBgK : Bg ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hHolderMetric : ∀ n x y, x ∈ closure Q → y ∈ closure Q →
      |uc n x - uc n y| ≤ K * dist x y ^ alpha := by
    intro n x y hx hy
    have hdata := aux_prop_regularity_product_limit_holder_data
      (isCompact_closure_centeredCube z hR)
      (hHolder n).1 (hHolder n).2.1 (hHolder n).2.2.1 halpha
    calc
      |uc n x - uc n y| ≤
          Kh * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha :=
        hdata.2 x hx y hy
      _ ≤ Kh * (Real.sqrt (d : ℝ) * dist x y) ^ alpha :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.sqrt_nonneg _)
          (aux_prop_regularity_product_limit_euclidean_le hd x y) halpha.le) hKh
      _ = Kh' * dist x y ^ alpha := by
        rw [Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg]
        simp only [Kh', mul_assoc]
      _ ≤ K * dist x y ^ alpha :=
        mul_le_mul_of_nonneg_right hKhK (Real.rpow_nonneg dist_nonneg _)
  have hGrowthK : ∀ n x r, 0 < r → r ≤ 1 →
      (((volume.restrict Q).withDensity (fun y => ENNReal.ofReal ((a n).val y *
        ∑ i : Fin d, ((u n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)))
        (Metric.ball x r)).toReal ≤ K * r ^ t := by
    intro n x r hr hr1
    exact (hG n x r hr hr1).trans
      (mul_le_mul_of_nonneg_right hBgK (Real.rpow_nonneg hr.le _))
  exact ⟨K, hK1, hHolderMetric, hGrowthK⟩

/-- Put the same native collar into the killed response space, preserving its
profile, zero gradient on the plateau and quantitative energy. -/
theorem aux_in_represented_bounds_seq_collar_product_cutoff
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (rho : ℕ → ℝ) (eta Kenergy : ℝ)
    (v : ℕ → ℕ → H10Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hRange : ∀ k n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      0 ≤ (v k n).toH1Function.toFun x ∧ (v k n).toH1Function.toFun x ≤ 1)
    (hOne : ∀ k n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho k ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (v k n).toH1Function.toFun x = 1)
    (hEnergy : ∀ k n,
      energy (a n).val (centeredCube z R hR : Set (SpatialCoordinates d))
        (v k n).toH1Function ≤ Kenergy * rho k ^ (-1 - eta)) :
    ∃ chi : ℕ → ℕ → S.space,
      (∀ k n, (chi k n).val = sobolevDataOfH1 (v k n).toH1Function) ∧
      (∀ k n, (chi k n).val.1 =ᵐ[volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))] (v k n).toH1Function.toFun) ∧
      (∀ k n, ∀ᵐ x ∂volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ (chi k n).val.1 x ∧ (chi k n).val.1 x ≤ 1) ∧
      (∀ k n, ∀ᵐ x ∂volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)),
        3 * rho k ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          (chi k n).val.1 x = 1) ∧
      (∀ k n (i : Fin d), ∀ᵐ x ∂volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d)),
        3 * rho k < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          (chi k n).val.2 i x = 0) ∧
      (∀ k n, responseForm S (a n) (chi k n) (chi k n) ≤
        Kenergy * rho k ^ (-1 - eta)) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  let chi : ℕ → ℕ → S.space := fun k n =>
    ⟨sobolevDataOfH1 (v k n).toH1Function,
      hS ▸ sobolevDataOfH1_mem_killed (v k n)⟩
  have hchi (k n : ℕ) : (chi k n).val.1 =ᵐ[volume.restrict Q]
      (v k n).toH1Function.toFun :=
    sobolevDataOfH1_fst_coeFn (v k n).toH1Function
  have hchiRange : ∀ k n, ∀ᵐ x ∂volume.restrict Q,
      0 ≤ (chi k n).val.1 x ∧ (chi k n).val.1 x ≤ 1 := by
    intro k n
    filter_upwards [hchi k n, ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet]
      with x hx hxQ
    rw [hx]
    exact hRange k n x (subset_closure hxQ)
  have hchiOne : ∀ k n, ∀ᵐ x ∂volume.restrict Q,
      3 * rho k ≤ Metric.infDist x Qᶜ → (chi k n).val.1 x = 1 := by
    intro k n
    filter_upwards [hchi k n, ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet]
      with x hx hxQ hdist
    rw [hx]
    exact hOne k n x (subset_closure hxQ) hdist
  have hchiGrad := fun k n => aux_in_represented_bounds_seq_collar_error_grad_zero
    z R hR S hS (chi k n) (v k n).toH1Function.toFun (rho k) (hchi k n) (hOne k n)
  have hchiEnergy : ∀ k n,
      responseForm S (a n) (chi k n) (chi k n) ≤ Kenergy * rho k ^ (-1 - eta) := by
    intro k n
    rw [aux_lem_cutoffs_resp_energy z hR S (a n) (a n).val Filter.EventuallyEq.rfl
      (v k n).toH1Function (chi k n) rfl]
    exact hEnergy k n
  exact ⟨chi, fun _ _ => rfl, hchi, hchiRange, hchiOne, hchiGrad, hchiEnergy⟩

/-- The actual native product has the quantitative collar error, using the source catalogue bounds. -/
theorem aux_in_represented_bounds_seq_collar_product_error
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (u : ℕ → S.space)
    (uc : ℕ → SpatialCoordinates d → ℝ)
    (hUrep : ∀ n : ℕ,
      (u n).val.1
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc n)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hUholder : ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ n : ℕ,
      ContinuousOn (uc n)
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc n) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc n) ≤ Kf ∧
      ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)),
        uc n x = 0)
    (t eta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (ha : 1 / 2 < alpha) (ha1 : alpha < 1)
    (he : 0 < eta) (hea : 1 + eta < 2 * alpha)
    (rho : ℕ → ℝ) (hrho : ∀ k, 0 < rho k)
    (hGrowth : ∃ B : ℝ, 0 ≤ B ∧ ∀ n x,
      x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∀ r, 0 < r → r ≤ 1 →
      (((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((a n).val y *
          ∑ i : Fin d, ((u n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)))
        (Metric.ball x r)) ≤ ENNReal.ofReal (B * r ^ t))
    (v : ℕ → ℕ → H10Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hRange : ∀ k n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      0 ≤ (v k n).toH1Function.toFun x ∧ (v k n).toH1Function.toFun x ≤ 1)
    (hOne : ∀ k n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho k ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (v k n).toH1Function.toFun x = 1)
    (Kenergy : ℝ) (hKenergy : 0 ≤ Kenergy)
    (hEnergy : ∀ k n,
      energy (a n).val (centeredCube z R hR : Set (SpatialCoordinates d))
        (v k n).toH1Function ≤ Kenergy * rho k ^ (-1 - eta))
    (un : ℕ → H10Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hunval : ∀ n, (un n).toH1Function.toFun =ᵐ[volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))] uc n)
    (hungrad : ∀ n i, (fun x => (un n).toH1Function.grad x i) =ᵐ[volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))]
      (fun x => (u n).val.2 i x))
    (w : ℕ → ℕ → S.space)
    (hwval : ∀ k n, (w k n).val.1 =ᵐ[volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))]
      (fun x => uc n x * (v k n).toH1Function.toFun x))
    (hwgrad : ∀ k n i, (fun x => (w k n).val.2 i x) =ᵐ[volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))]
      (fun x => (un n).toH1Function.toFun x * (v k n).toH1Function.grad x i +
        (v k n).toH1Function.toFun x * (un n).toH1Function.grad x i)) :
    ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ k n,
      responseForm S (a n) (u n - w k n) (u n - w k n) ≤
        Kf * (rho k ^ (t - (d : ℝ) + 1) + rho k ^ (2 * alpha - 1 - eta)) := by
  classical
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  obtain ⟨chi, hchiData, hchi, hchiRange, hchiOne, hchiGrad, hchiEnergy⟩ :=
    aux_in_represented_bounds_seq_collar_product_cutoff z R hR S hS a rho eta Kenergy
      v hRange hOne hEnergy
  obtain ⟨Kh, hKh, hHolder⟩ := hUholder
  obtain ⟨Bg0, hBg0, hG0⟩ := hGrowth
  have ht0 : 0 ≤ t := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hd', ht]
  obtain ⟨Bg, hBg, hG⟩ := aux_in_represented_bounds_seq_collar_product_growth
    z R hR S a (u) t ht0 Bg0 hBg0 hG0
  obtain ⟨K, hK1, hHolderMetric, hGrowthK⟩ :=
    aux_in_represented_bounds_seq_collar_product_source hd z R hR S a (u) (uc)
      alpha t Kh Bg halpha hKh hHolder hG
  have hProduct : ∀ k n,
      (((u n - w k n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict Q] (fun x => uc n x * (1 - (chi k n).val.1 x))) ∧
      (∀ i : Fin d,
        (fun x => ((u n - w k n).val.2 i : SpatialCoordinates d → ℝ) x)
          =ᵐ[volume.restrict Q]
            (fun x => (1 - (chi k n).val.1 x) * (u n).val.2 i x -
              uc n x * (chi k n).val.2 i x)) := by
    intro k n
    apply aux_in_represented_bounds_seq_collar_error_subtraction
      z R hR S (u n) (w k n) (chi k n) (un n)
      (v k n).toH1Function (uc n) (v k n).toH1Function.toFun (hchiData k n)
      (hchi k n) (hUrep n) (hunval n) ?_ (hwval k n) (hwgrad k n)
    intro i
    exact hungrad n i
  have hEnergyK : ∀ k n,
      responseForm S (a n) (chi k n) (chi k n) ≤
        (Kenergy + 1) * K * rho k ^ (-1 - eta) := by
    intro k n
    apply (hchiEnergy k n).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hrho k).le _)
    calc
      Kenergy ≤ Kenergy + 1 := le_add_of_nonneg_right zero_le_one
      _ ≤ (Kenergy + 1) * K := le_mul_of_one_le_right (add_nonneg hKenergy zero_le_one) hK1
  exact in_represented_bounds_seq_collar_error d hd z R hR t alpha eta ht htd ha ha1 he hea
    S hS a rho hrho (fun _ => K) K (fun _ => ⟨hK1, le_rfl⟩)
    (u) (uc) (hUrep) (fun n => (hHolder n).1)
    (fun n => (hHolder n).2.2.2) hHolderMetric hGrowthK chi (w)
    hchiRange hchiOne hchiGrad (Kenergy + 1) (lt_add_of_le_of_pos hKenergy zero_lt_one) hEnergyK
    (fun k n => (hProduct k n).1) (fun k n => (hProduct k n).2)


/-- The joint native collar family supplies the actual products and collar-error field
of the represented bounds bundle. All constants are uniform in both indices. -/
theorem in_represented_bounds_seq_collar_product
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    (u : DomainL2 (centeredCube z R hR) → ℕ → S.space)
    (uc : DomainL2 (centeredCube z R hR) → ℕ → SpatialCoordinates d → ℝ)
    (hU : ∀ (f : DomainL2 (centeredCube z R hR)) (n : ℕ),
      u f n = responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL))
    (hUrep : ∀ (f : DomainL2 (centeredCube z R hR)) (n : ℕ),
      (u f n).val.1
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc f n)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hUholder : ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ n : ℕ,
      ContinuousOn (uc f.val n)
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc f.val n) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc f.val n) ≤ Kf ∧
      ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)),
        uc f.val n x = 0)
    (t eta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (ha : 1 / 2 < alpha) (ha1 : alpha < 1)
    (he : 0 < eta) (hea : 1 + eta < 2 * alpha)
    (rho : ℕ → ℝ) (hrho : ∀ k, 0 < rho k)
    (hGrowth : ∀ f : D, ∃ B : ℝ, 0 ≤ B ∧ ∀ n x,
      x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∀ r, 0 < r → r ≤ 1 →
      (((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((a n).val y *
          ∑ i : Fin d, ((u f.val n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)))
        (Metric.ball x r)) ≤ ENNReal.ofReal (B * r ^ t))
    (v : ℕ → ℕ → H10Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hRange : ∀ k n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      0 ≤ (v k n).toH1Function.toFun x ∧ (v k n).toH1Function.toFun x ≤ 1)
    (hOne : ∀ k n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho k ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (v k n).toH1Function.toFun x = 1)
    (Kenergy : ℝ) (hKenergy : 0 ≤ Kenergy)
    (hEnergy : ∀ k n,
      energy (a n).val (centeredCube z R hR : Set (SpatialCoordinates d))
        (v k n).toH1Function ≤ Kenergy * rho k ^ (-1 - eta)) :
    ∃ w : DomainL2 (centeredCube z R hR) → ℕ → ℕ → S.space,
      (∀ (f : D) (k n : ℕ),
        ((w f.val k n).val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => uc f.val n x * (v k n).toH1Function.toFun x)) ∧
      (∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ k n,
        responseForm S (a n) (u f.val n - w f.val k n) (u f.val n - w f.val k n) ≤
          Kf * (rho k ^ (t - (d : ℝ) + 1) + rho k ^ (2 * alpha - 1 - eta))) := by
  classical
  obtain ⟨un, hunval, hungrad, w, hwval, hwgrad⟩ := conv_represented_bounds_env_product
    z R hR S hS a D u uc hU hUrep alpha halpha hUholder
      (fun k n => (v k n).toH1Function) (fun k n => (v k n).toH1Function.toFun)
      (fun _ _ => Filter.EventuallyEq.rfl) hRange
  refine ⟨w, hwval, ?_⟩
  intro f
  exact aux_in_represented_bounds_seq_collar_product_error d hd z R hR S hS a
    (u f.val) (uc f.val) (hUrep f.val) alpha halpha (hUholder f) t eta ht htd ha ha1 he hea
    rho hrho (hGrowth f) v hRange hOne Kenergy hKenergy hEnergy (un f) (hunval f)
    (by intro n i; rw [hU f.val n]; exact hungrad f n i) (w f.val) (hwval f) (hwgrad f)

end SubdiffusiveProcess.Paper
