import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Sobolev.GradientEnergyMeasure
import SubdiffusiveProcess.Lane3.StripCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal

namespace Paper

private theorem aux_collar_subset_oddGridStrip
    {d : ℕ} (hd : 1 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (r : ℝ) (hr : 0 < r) (hsmall : 4 * r < R)
    {x : SpatialCoordinates d}
    (hx : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hxd : Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r) :
    x ∈ SubdiffusiveProcess.Lane3.oddGridStrip z R m (4 * r) := by
  classical
  have hcomp : ((centeredCube z R hR : Set (SpatialCoordinates d))ᶜ).Nonempty := by
    let y : SpatialCoordinates d := fun j => z j + R
    refine ⟨y, ?_⟩
    change y ∉ Metric.ball z (R / 2)
    intro hy
    have hy' := (dist_pi_lt_iff (by linarith [hR])).mp hy
    have hzero := hy' ⟨0, by omega⟩
    have hdist : dist (y ⟨0, by omega⟩) (z ⟨0, by omega⟩) = R := by
      rw [Real.dist_eq]
      simp [y, abs_of_pos hR]
    rw [hdist] at hzero
    linarith

  have hxd' : Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ < 4 * r :=
    lt_of_le_of_lt hxd (by linarith)
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff hcomp).mp hxd'
  have hyout : ¬ dist y z < R / 2 := by
    intro hyin
    exact hy (by simpa [centeredCube] using hyin)
  have hcoord : ∃ i : Fin d, R / 2 ≤ dist (y i) (z i) := by
    by_contra hno
    push_neg at hno
    apply hyout
    rw [dist_pi_lt_iff (by linarith [hR])]
    intro i
    exact hno i
  obtain ⟨i, hi⟩ := hcoord
  have hxyi : dist (x i) (y i) ≤ dist x y := dist_le_pi_dist x y i
  have hxi : dist (x i) (z i) < R / 2 := by
    exact (dist_le_pi_dist x z i).trans_lt (Metric.mem_ball.mp hx)
  rcases le_total (z i) (y i) with hright | hleft
  · refine ⟨i, (m : ℤ), ?_⟩
    change |x i - (z i + (((m : ℤ) : ℝ) + 1 / 2) *
      (R / (2 * (m : ℝ) + 1)))| ≤ 4 * r
    have hface : (((m : ℤ) : ℝ) + 1 / 2) * (R / (2 * (m : ℝ) + 1)) = R / 2 := by
      push_cast
      field_simp
    rw [hface]
    rw [Real.dist_eq] at hxyi hxi
    have hxu : x i < z i + R / 2 := by
      linarith [abs_lt.mp hxi |>.2]
    have hycoord : R / 2 ≤ y i - z i := by
      simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hright)] using hi
    have hyb : z i + R / 2 ≤ y i := by linarith
    rw [abs_of_nonpos (by linarith)]
    rw [abs_of_nonpos (by linarith : x i - y i ≤ 0)] at hxyi
    linarith
  · have hycoord : R / 2 ≤ |y i - z i| := by
      simpa [Real.dist_eq] using hi
    have hycoord' : y i ≤ z i - R / 2 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hleft)] at hycoord
      linarith
    refine ⟨i, -(m : ℤ) - 1, ?_⟩
    change |x i - (z i + (((-(m : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) *
      (R / (2 * (m : ℝ) + 1)))| ≤ 4 * r
    have hface : ((((-(m : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) *
        (R / (2 * (m : ℝ) + 1))) = -(R / 2) := by
      push_cast
      field_simp; ring
    rw [hface]
    rw [Real.dist_eq] at hxyi hxi
    have hxl : z i - R / 2 < x i := by
      linarith [abs_lt.mp hxi |>.1]
    rw [abs_of_nonneg (by linarith)]
    rw [abs_of_nonneg (by linarith : 0 ≤ x i - y i)] at hxyi
    linarith

private theorem aux_collar_mass_of_growth
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (t : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    : ∃ C : ℝ, 0 < C ∧ ∀ (ν : Measure (SpatialCoordinates d)) (_hν : IsFiniteMeasure ν)
      (_hsupp : ν (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ = 0)
      (K : ℝ) (_hK : 0 ≤ K)
      (_hgrowth : ∀ (x : SpatialCoordinates d) (s : ℝ), 0 < s → s ≤ 1 →
        ν (Metric.ball x s) ≤ ENNReal.ofReal (K * s ^ t)),
      ∀ (r : ℝ), 0 < r →
        (ν {x : SpatialCoordinates d | x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
          Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r}).toReal
          ≤ C * K * r ^ (t - (d : ℝ) + 1) := by
  classical
  let α : ℝ := t - (d : ℝ) + 1
  have hα : 0 < α := by dsimp [α]; linarith
  have hα0 : 0 ≤ α := hα.le
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cstrip, hCstrip, hstrip⟩ :=
    SubdiffusiveProcess.Lane3.strip_and_core_masses d hd1 t ht_lower
      (le_of_lt ht_upper)
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have hmR : R / (2 * (m : ℝ) + 1) ≤ 1 := by
    have hden : 0 < 2 * (m : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hden).2
    have hm' : R ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  let ρ : ℝ := min (R / (4 * (2 * (m : ℝ) + 1))) (1 / 8)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by norm_num)
  obtain ⟨F, hF⟩ := (isCompact_closedBall z (R / 2)).elim_finite_subcover
    (fun w : SpatialCoordinates d => Metric.ball w 1)
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  let N : ℝ := (F.card : ℝ) + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let Csmall : ℝ := Cstrip * R ^ (d : ℝ) * ((2 * (m : ℝ) + 1) / R) * 4 ^ α
  let Clarge : ℝ := N / ρ ^ α
  refine ⟨Csmall + Clarge, by positivity, ?_⟩
  intro ν hν hsupp K hK hgrowth
  letI := hν
  intro r hr
  let collar : Set (SpatialCoordinates d) :=
    {x : SpatialCoordinates d | x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r}
  have hΩcover : (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆
      ⋃ w ∈ F, Metric.ball w 1 := by
    exact Metric.ball_subset_closedBall.trans hF
  have hwhole : ν (centeredCube z R hR : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal ((F.card : ℝ) * K) := by
    calc
      ν (centeredCube z R hR : Set (SpatialCoordinates d)) ≤
          ν (⋃ w ∈ F, Metric.ball w 1) := measure_mono hΩcover
      _ ≤ ∑ w ∈ F, ν (Metric.ball w 1) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _w ∈ F, ENNReal.ofReal K := by
        gcongr with w hw
        simpa using hgrowth w 1 (by norm_num) (by norm_num)
      _ = ENNReal.ofReal ((F.card : ℝ) * K) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
  have hreal_whole : (ν (centeredCube z R hR : Set (SpatialCoordinates d))).toReal ≤
      (F.card : ℝ) * K := by
    have h := ENNReal.toReal_mono (a := ν (centeredCube z R hR : Set (SpatialCoordinates d)))
      (b := ENNReal.ofReal ((F.card : ℝ) * K)) ENNReal.ofReal_ne_top hwhole
    simpa [ENNReal.toReal_ofReal hK] using h
  by_cases hsmall : 4 * r < R / (2 * (m : ℝ) + 1) ∧ r < 1 / 8
  · have hden : 0 < 2 * (m : ℝ) + 1 := by positivity
    have hcell : 4 * r < R / (2 * (m : ℝ) + 1) := hsmall.1
    have hcellR : 4 * r < R := by
      have hden1 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have hquot : R / (2 * (m : ℝ) + 1) ≤ R := by
        apply (div_le_iff₀ hden).2
        nlinarith [hR]
      exact hcell.trans_le hquot
    have hstrip' := hstrip z R hR m ν K hK hgrowth hsupp hmR
    have hmass := hstrip'.1 (4 * r) (by positivity) (by nlinarith [hsmall.2]) hcell
    have hsub : collar ⊆ SubdiffusiveProcess.Lane3.oddGridStrip z R m (4 * r) := by
      intro x hx
      exact aux_collar_subset_oddGridStrip hd1 z R hR m r hr hcellR hx.1 hx.2
    have hcollar : ν collar ≤
        ENNReal.ofReal (Cstrip * K * R ^ (d : ℝ) *
          ((2 * (m : ℝ) + 1) / R) * (4 * r) ^ α) := by
      exact (measure_mono hsub).trans hmass
    have hnonneg : 0 ≤ Cstrip * K * R ^ (d : ℝ) *
        ((2 * (m : ℝ) + 1) / R) * (4 * r) ^ α := by positivity
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcollar
    rw [ENNReal.toReal_ofReal hnonneg] at hreal
    change (ν collar).toReal ≤ (Csmall + Clarge) * K * r ^ α
    calc
      (ν collar).toReal ≤ Cstrip * K * R ^ (d : ℝ) *
          ((2 * (m : ℝ) + 1) / R) * (4 * r) ^ α := hreal
      _ = Csmall * K * r ^ α := by
        dsimp [Csmall]
        rw [Real.mul_rpow (by norm_num) hr.le]
        ring
      _ ≤ (Csmall + Clarge) * K * r ^ α := by
        have hnonneg : 0 ≤ Clarge * K * r ^ α := by positivity
        nlinarith
  · have hrho : ρ ≤ r := by
      by_contra hnot
      have hlt : r < ρ := lt_of_not_ge hnot
      have hlt1 : r < R / (4 * (2 * (m : ℝ) + 1)) := by
        have hlt' : r < min (R / (4 * (2 * (m : ℝ) + 1))) (1 / 8) := by
          simpa [ρ] using hlt
        exact (lt_min_iff.mp hlt').1
      have hlt2 : r < 1 / 8 := by
        have hlt' : r < min (R / (4 * (2 * (m : ℝ) + 1))) (1 / 8) := by
          simpa [ρ] using hlt
        exact (lt_min_iff.mp hlt').2
      apply hsmall
      constructor
      · have hden : 0 < 2 * (m : ℝ) + 1 := by positivity
        apply (lt_div_iff₀ hden).2
        have hlt1' := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (2 * (m : ℝ) + 1))).mp hlt1
        nlinarith
      · exact hlt2
    have hcollarΩ : collar ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
      intro x hx
      exact hx.1
    have hreal_collar : (ν collar).toReal ≤
        (ν (centeredCube z R hR : Set (SpatialCoordinates d))).toReal := by
      exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hcollarΩ)
    have hq : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ _
    have hp : ρ ^ α ≤ r ^ α := Real.rpow_le_rpow hρ.le hrho hα0
    have hNcard : (F.card : ℝ) ≤ N := by
      dsimp [N]
      linarith
    have hratio : 1 ≤ r ^ α / ρ ^ α := by
      apply (le_div_iff₀ hq).2
      linarith
    have hbase : (F.card : ℝ) ≤ N * (r ^ α / ρ ^ α) := by
      calc
        (F.card : ℝ) ≤ N := hNcard
        _ = N * 1 := by ring
        _ ≤ N * (r ^ α / ρ ^ α) :=
          mul_le_mul_of_nonneg_left hratio hN.le
    have hcard : (F.card : ℝ) * K ≤ Clarge * K * r ^ α := by
      have hbase' := mul_le_mul_of_nonneg_right hbase hK
      calc
        (F.card : ℝ) * K ≤ N * (r ^ α / ρ ^ α) * K := hbase'
        _ = Clarge * K * r ^ α := by
          dsimp [Clarge]
          field_simp
    change (ν collar).toReal ≤ (Csmall + Clarge) * K * r ^ α
    calc
      (ν collar).toReal ≤
          (ν (centeredCube z R hR : Set (SpatialCoordinates d))).toReal := hreal_collar
      _ ≤ (F.card : ℝ) * K := hreal_whole
      _ ≤ Clarge * K * r ^ α := hcard
      _ ≤ (Csmall + Clarge) * K * r ^ α := by
        have hnonneg : 0 ≤ Csmall * K * r ^ α := by positivity
        nlinarith



/- The existing argument works for every positive collar radius. -/
theorem aux_lem_20_collar_mass_all_radii
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (t : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : ResponseSpace (centeredCube z R hR)),
      S.space = killedSobolevGraph (centeredCube z R hR) →
      ∀ (a : PositiveCoefficient (centeredCube z R hR)) (u : S.space)
        (KN : ℝ), 1 ≤ KN →
      (∀ (x : SpatialCoordinates d) (s : ℝ), 0 < s → s ≤ 1 →
      (((volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a.val y *
              ∑ i : Fin d, (u.val.2 i y) ^ 2)))
          (Metric.ball x s)).toReal ≤ KN * s ^ t) →
      ∀ (r : ℝ), 0 < r →
        (((volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a.val y *
              ∑ i : Fin d, (u.val.2 i y) ^ 2)))
          {x : SpatialCoordinates d | x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
            Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r}).toReal
          ≤ C * KN * r ^ (t - (d : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ :=
    aux_collar_mass_of_growth hd z R hR t ht_lower ht_upper
  refine ⟨C, hC, ?_⟩
  intro S hS a u KN hKN hgrowth r hr
  let g : HilbertGradient (centeredCube z R hR) := sobolevGradient u.val
  let μ : Measure (SpatialCoordinates d) :=
    (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (a.val y * ∑ i : Fin d, (g i y) ^ 2))
  have hdata := gradientEnergy_withDensity_finite_and_real a g
  have hμ : IsFiniteMeasure μ := by
    dsimp [μ]
    simpa only [Finset.mul_sum, g, sobolevGradient] using hdata.1
  have hsupport : μ (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ = 0 := by
    dsimp [μ]
    rw [withDensity_apply _ (MeasurableSet.compl (centeredCube z R hR).isOpen.measurableSet)]
    simp [(centeredCube z R hR).isOpen.measurableSet]
  have hgrowth' : ∀ (x : SpatialCoordinates d) (s : ℝ), 0 < s → s ≤ 1 →
      μ (Metric.ball x s) ≤ ENNReal.ofReal (KN * s ^ t) := by
    intro x s hs hs1
    have hnonneg : 0 ≤ KN * s ^ t :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hs.le _)
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mp
    simpa [μ, g, sobolevGradient, ENNReal.toReal_ofReal hnonneg] using hgrowth x s hs hs1
  have := hbound μ hμ hsupport KN (by linarith) hgrowth' r hr
  simpa [μ, g] using this

theorem lem_20_collar_mass
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (t : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : ResponseSpace (centeredCube z R hR)),
      S.space = killedSobolevGraph (centeredCube z R hR) →
      ∀ (a : PositiveCoefficient (centeredCube z R hR)) (u : S.space)
        (KN : ℝ), 1 ≤ KN →
      (∀ (x : SpatialCoordinates d) (s : ℝ), 0 < s → s ≤ 1 →
      (((volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a.val y *
              ∑ i : Fin d, (u.val.2 i y) ^ 2)))
          (Metric.ball x s)).toReal ≤ KN * s ^ t) →
      ∀ (r : ℝ), 0 < r → r ≤ 1 →
        (((volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a.val y *
              ∑ i : Fin d, (u.val.2 i y) ^ 2)))
          {x : SpatialCoordinates d | x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
            Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r}).toReal
          ≤ C * KN * r ^ (t - (d : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ := aux_lem_20_collar_mass_all_radii d hd z R hR t ht_lower ht_upper
  exact ⟨C, hC, fun S hS a u KN hKN hgrowth r hr _ => hbound S hS a u KN hKN hgrowth r hr⟩

end Paper
