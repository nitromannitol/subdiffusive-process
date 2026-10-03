module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Variational.QuadraticSaving
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

lemma aux_relative_response_variation_sum_quad_bound
    {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : ∀ v, 0 ≤ Q v) (s : Finset ι) (f : ι → V) :
    Q (∑ i ∈ s, f i) ≤ (2 : ℝ) ^ s.card * ∑ i ∈ s, Q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      have h := SubdiffusiveProcess.quadratic_add_le Q hQ (f a) (∑ i ∈ s, f i)
        (t := 1) (by norm_num)
      have hfa : 0 ≤ Q (f a) := hQ _
      have hs : 0 ≤ ∑ i ∈ s, Q (f i) := Finset.sum_nonneg (fun i hi => hQ _)
      have hpow : 1 ≤ (2 : ℝ) ^ s.card := one_le_pow₀ (by norm_num)
      have hprodA := mul_nonneg (sub_nonneg.mpr hpow) hfa
      have hprodS := mul_nonneg (sub_nonneg.mpr hpow) hs
      norm_num at h
      nlinarith [ih]

lemma aux_relative_response_variation_quad_bound
    (d : ℕ) (Q : QuadraticForm ℝ (Fin d → ℝ)) (hQ : ∀ p, 0 ≤ Q p)
    (D : ℝ) (hD : D = ∑ j : Fin d, Q (Pi.single j (1 : ℝ)))
    (p : Fin d → ℝ) :
    Q p ≤ (2 : ℝ) ^ d * (∑ j : Fin d, (p j) ^ 2) * D := by
  classical
  have hp : p = ∑ j : Fin d, p j • (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply, eq_comm]
  have hcoord : ∀ j : Fin d, Q (Pi.single j (1 : ℝ) : Fin d → ℝ) ≤ D := by
    intro j
    rw [hD]
    exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin d)))
      (fun k hk => hQ (Pi.single k (1 : ℝ))) (Finset.mem_univ j)
  have hsum := aux_relative_response_variation_sum_quad_bound Q hQ Finset.univ
    (fun j : Fin d => p j • (Pi.single j (1 : ℝ) : Fin d → ℝ))
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hterm : ∀ j : Fin d,
      Q (p j • (Pi.single j (1 : ℝ) : Fin d → ℝ)) ≤ (p j) ^ 2 * D := by
    intro j
    rw [QuadraticMap.map_smul]
    simpa only [smul_eq_mul, pow_two] using
      (mul_le_mul_of_nonneg_left (hcoord j) (sq_nonneg (p j)))
  have hsum' := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
    (fun j _ => hterm j)
  calc
    Q p = Q (∑ j : Fin d, p j • (Pi.single j (1 : ℝ) : Fin d → ℝ)) := congrArg Q hp
    _ ≤ (2 : ℝ) ^ d * ∑ j : Fin d,
        Q (p j • (Pi.single j (1 : ℝ) : Fin d → ℝ)) := hsum
    _ ≤ (2 : ℝ) ^ d * ∑ j : Fin d, (p j) ^ 2 * D :=
      mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = (2 : ℝ) ^ d * (∑ j : Fin d, (p j) ^ 2) * D := by
      rw [← Finset.sum_mul]
      ring

lemma aux_relative_response_variation_measure_sub_le
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    {E : DirichletForm.ClosedForm m} (Γ : DirichletForm.EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure u B).toReal ≤
      2 * (Γ.measure v B).toReal + 2 * (Γ.measure (u - v) B).toReal := by
  have huv : u - v ∈ E.domain := E.domain.sub_mem hu hv
  have hsum : v + (u - v) = u := by abel
  have hexp := Γ.cross_add_self_apply hv huv B
  have hcross := Γ.abs_cross_le v hv (u - v) huv B hB
  have ha : 0 ≤ (Γ.measure v B).toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ (Γ.measure (u - v) B).toReal := ENNReal.toReal_nonneg
  have hsqrt :
      2 * (Real.sqrt (Γ.measure v B).toReal) *
          (Real.sqrt (Γ.measure (u - v) B).toReal) ≤
        (Γ.measure v B).toReal + (Γ.measure (u - v) B).toReal := by
    have hsq := sq_nonneg
      (Real.sqrt (Γ.measure v B).toReal - Real.sqrt (Γ.measure (u - v) B).toReal)
    have hva := Real.sq_sqrt ha
    have hvb := Real.sq_sqrt hb
    nlinarith
  have hcross' :
      2 * Γ.cross v (u - v) B ≤
        (Γ.measure v B).toReal + (Γ.measure (u - v) B).toReal := by
    have hle := le_trans (le_abs_self (Γ.cross v (u - v) B)) hcross
    nlinarith
  calc
    (Γ.measure u B).toReal = Γ.cross u u B :=
      (Γ.cross_self u hu B hB).symm
    _ = Γ.cross (v + (u - v)) (v + (u - v)) B := by rw [hsum]
    _ = Γ.cross v v B + 2 * Γ.cross v (u - v) B +
        Γ.cross (u - v) (u - v) B := hexp
    _ = (Γ.measure v B).toReal + 2 * Γ.cross v (u - v) B +
        (Γ.measure (u - v) B).toReal := by
      rw [Γ.cross_self v hv B hB, Γ.cross_self (u - v) huv B hB]
    _ ≤ 2 * (Γ.measure v B).toReal + 2 * (Γ.measure (u - v) B).toReal := by
      nlinarith [hcross']

lemma aux_relative_response_variation_normalized_sum_toReal
    {X ι : Type*} [MeasurableSpace X]
    (D : ℝ) (hD : 0 < D) (s : Finset ι) (μ : ι → Measure X) (B : Set X)
    (hfinite : ∀ i ∈ s, μ i B ≠ ⊤) :
    ((ENNReal.ofReal D⁻¹ • (∑ i ∈ s, μ i)) B).toReal =
      D⁻¹ * ∑ i ∈ s, (μ i B).toReal := by
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hD)),
    Measure.finset_sum_apply, ENNReal.toReal_sum hfinite]

lemma aux_relative_response_variation_ratio_bounds
    (C0 m M : ℝ) (hC0 : 1 ≤ C0) (hm : C0⁻¹ ≤ m)
    (hmM : m ≤ M) (hM : M ≤ C0) :
    0 < m ∧ 0 ≤ M - m ∧
      ((M - m) / m) ^ 2 ≤ (C0 ^ 2 - 1) ^ 2 ∧
      ((M - m) / m) ^ 2 ≤ C0 ^ 2 * (M - m) ^ 2 := by
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr hC0pos) hm
  have hdel : 0 ≤ M - m := sub_nonneg.mpr hmM
  have hC0sq : 0 ≤ C0 ^ 2 - 1 := by nlinarith [sq_nonneg (C0 - 1)]
  have hdel_le : M - m ≤ C0 - C0⁻¹ := by linarith
  have hmul := mul_le_mul_of_nonneg_left hm hC0sq
  have heq : (C0 ^ 2 - 1) * C0⁻¹ = C0 - C0⁻¹ := by
    field_simp [ne_of_gt hC0pos]
  have hdel_le' : M - m ≤ (C0 ^ 2 - 1) * m := by
    exact hdel_le.trans (heq ▸ hmul)
  have hratio : (M - m) / m ≤ C0 ^ 2 - 1 :=
    (div_le_iff₀ hmpos).2 hdel_le'
  have hratio_nonneg : 0 ≤ (M - m) / m := div_nonneg hdel (le_of_lt hmpos)
  have hratio_sq : ((M - m) / m) ^ 2 ≤ (C0 ^ 2 - 1) ^ 2 :=
    (sq_le_sq₀ hratio_nonneg hC0sq).2 hratio
  have hinv : m⁻¹ ≤ C0 := (inv_le_comm₀ hmpos hC0pos).2 hm
  have hinv_sq : (m⁻¹) ^ 2 ≤ C0 ^ 2 :=
    (sq_le_sq₀ (inv_nonneg.mpr hmpos.le) (le_of_lt hC0pos)).2 hinv
  have hratio_sq' : ((M - m) / m) ^ 2 ≤ C0 ^ 2 * (M - m) ^ 2 := by
    calc
      ((M - m) / m) ^ 2 = (M - m) ^ 2 * (m⁻¹) ^ 2 := by
        field_simp [ne_of_gt hmpos]
      _ ≤ (M - m) ^ 2 * C0 ^ 2 :=
        mul_le_mul_of_nonneg_left hinv_sq (sq_nonneg _)
      _ = C0 ^ 2 * (M - m) ^ 2 := by ring
  exact ⟨hmpos, hdel, hratio_sq, hratio_sq'⟩



theorem relative_response_variation
    (d : ℕ) (hd : 2 ≤ d) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (slopes : Finset (Fin d → ℝ))
    (hcoords : ∀ j : Fin d, (Pi.single j (1 : ℝ) : Fin d → ℝ) ∈ slopes)
    (hpolar : ∀ i j : Fin d, (Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ) ∈ slopes) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : Opens (SpatialCoordinates d)) (z : SpatialCoordinates d) (r : ℝ)
      (hr : 0 < r)
      (hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
        Q = centeredCube zQ rQ hrQ),
    let q := centeredCube z r hr
    ∀ (hcontain : closure (q : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
      (E F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : DirichletForm.EnergyMeasure E) (GammaF : DirichletForm.EnergyMeasure F)
      (hdom : E.domain = F.domain)
      (m M c : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
      (hmc : m ≤ c) (hcM : c ≤ M)
      (horder : ∀ u ∈ E.domain,
        m * (GammaE.measure u q).toReal ≤ (GammaF.measure u q).toReal ∧
        (GammaF.measure u q).toReal ≤ M * (GammaE.measure u q).toReal)
      (uE uF : (Fin d → ℝ) → DomainL2 Q)
      (UE UF : (Fin d → ℝ) → SpatialCoordinates d → ℝ)
      (huE : ∀ p, uE p ∈ E.domain) (huF : ∀ p, uF p ∈ F.domain)
      (hcontE : ∀ p, ContinuousOn (UE p) (closure (Q : Set (SpatialCoordinates d))))
      (hcontF : ∀ p, ContinuousOn (UF p) (closure (Q : Set (SpatialCoordinates d))))
      (haeE : ∀ p, (uE p : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] UE p)
      (haeF : ∀ p, (uF p : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] UF p)
      (hbdE : ∀ p x, x ∈ frontier (q : Set (SpatialCoordinates d)) → UE p x = ∑ j, p j * x j)
      (hbdF : ∀ p x, x ∈ frontier (q : Set (SpatialCoordinates d)) → UF p x = ∑ j, p j * x j)
      (hminE : ∀ p, ∀ v ∈ E.domain, ∀ V : SpatialCoordinates d → ℝ,
        ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) →
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) →
        (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), V x = ∑ j, p j * x j) →
        (GammaE.measure (uE p) q).toReal ≤ (GammaE.measure v q).toReal)
      (hminF : ∀ p, ∀ v ∈ F.domain, ∀ V : SpatialCoordinates d → ℝ,
        ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) →
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) →
        (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), V x = ∑ j, p j * x j) →
        (GammaF.measure (uF p) q).toReal ≤ (GammaF.measure v q).toReal)
      (QE QF : QuadraticForm ℝ (Fin d → ℝ))
      (hQE : ∀ p, QE p = (GammaE.measure (uE p) q).toReal)
      (hQF : ∀ p, QF p = (GammaF.measure (uF p) q).toReal)
      (hdiff : ∀ p, (GammaE.measure (uF p - uE p) q).toReal ≤
        ((M - m) / m)^2 * (GammaE.measure (uE p) q).toReal)
      (Dq : ℝ) (hDdef : Dq = ∑ j : Fin d, QE ((Pi.single j (1 : ℝ) : Fin d → ℝ))) (hD : 0 < Dq)
      (t : ℝ) (ht : (d : ℝ) - 1 < t)
      (KE KF : (Fin d → ℝ) → ℝ)
      (hKE : ∀ p ∈ slopes, 0 ≤ KE p) (hKF : ∀ p ∈ slopes, 0 ≤ KF p)
      (hgrowE : ∀ p ∈ slopes, ∀ (x : SpatialCoordinates d) (rho : ℝ),
        0 < rho → rho ≤ 1 →
        (GammaE.measure (uE p) (Metric.ball x rho ∩ (q : Set (SpatialCoordinates d)))).toReal ≤ KE p * rho^t)
      (hgrowF : ∀ p ∈ slopes, ∀ (x : SpatialCoordinates d) (rho : ℝ),
        0 < rho → rho ≤ 1 →
        (GammaE.measure (uF p) (Metric.ball x rho ∩ (q : Set (SpatialCoordinates d)))).toReal ≤ KF p * rho^t),
    let nu : Measure (SpatialCoordinates d) := ENNReal.ofReal Dq⁻¹ •
      (∑ p ∈ slopes, (GammaE.measure (uE p) + GammaE.measure (uF p)))
    let zeta : Measure (SpatialCoordinates d) := ENNReal.ofReal Dq⁻¹ •
      (∑ p ∈ slopes, GammaE.measure (uF p - uE p))
    let R : (Fin d → ℝ) → ℝ := fun p => (QF p - c * QE p) / Dq
    (nu q).toReal ≤ C ∧
    (zeta q).toReal ≤ C * (M - m)^2 ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ (x : SpatialCoordinates d) (rho : ℝ),
      0 < rho → rho ≤ 1 →
      (nu (Metric.ball x rho ∩ (q : Set (SpatialCoordinates d)))).toReal ≤ K * rho^t) ∧
    ∀ i j : Fin d,
      ((QF ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) - QF ((Pi.single i (1 : ℝ) : Fin d → ℝ)) - QF ((Pi.single j (1 : ℝ) : Fin d → ℝ))) / 2 -
        c * (QE ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) - QE ((Pi.single i (1 : ℝ) : Fin d → ℝ)) - QE ((Pi.single j (1 : ℝ) : Fin d → ℝ))) / 2) / Dq =
      (R ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) - R ((Pi.single i (1 : ℝ) : Fin d → ℝ)) - R ((Pi.single j (1 : ℝ) : Fin d → ℝ))) / 2 := by
  let a : (Fin d → ℝ) → ℝ := fun p => ∑ j : Fin d, (p j) ^ 2
  let A : ℝ := ∑ p ∈ slopes, a p
  let K0 : ℝ := (2 : ℝ) ^ d * A
  let delta0 : ℝ := C0 ^ 2 - 1
  let C : ℝ := 1 + K0 * (3 + 2 * delta0 ^ 2 + C0 ^ 2)
  have hA : 0 ≤ A := by
    dsimp [A, a]
    positivity
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    positivity
  have hdelta0 : 0 ≤ delta0 := by
    dsimp [delta0]
    nlinarith [sq_nonneg (C0 - 1)]
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith [hK0, hdelta0, sq_nonneg C0]
  refine ⟨C, hCpos, ?_⟩
  intro Q z r hr hQ
  dsimp only
  generalize hq : centeredCube z r hr = q
  intro hcontain E F GammaE GammaF hdom m M c hm hmM hM hmc hcM horder
    uE uF UE UF huE huF hcontE hcontF haeE haeF hbdE hbdF hminE hminF
    QE QF hQE hQF hdiff Dq hDdef hD t ht KE KF hKE hKF hgrowE hgrowF
  have hqmeas : MeasurableSet (q : Set (SpatialCoordinates d)) := q.2.measurableSet
  have hratio := aux_relative_response_variation_ratio_bounds C0 m M hC0 hm hmM hM
  rcases hratio with ⟨hmpos, hdel, hratio0, hratio1⟩
  have huF_E : ∀ p, uF p ∈ E.domain := by
    intro p
    rw [hdom]
    exact huF p
  have hQE_nonneg : ∀ p, 0 ≤ QE p := by
    intro p
    rw [hQE p]
    exact ENNReal.toReal_nonneg
  have hQE_term : ∀ p, QE p ≤ (2 : ℝ) ^ d * a p * Dq := by
    intro p
    simpa [a] using
      (aux_relative_response_variation_quad_bound d QE hQE_nonneg Dq hDdef p)
  have hQE_sum : ∑ p ∈ slopes, QE p ≤ K0 * Dq := by
    have hs := Finset.sum_le_sum (s := slopes)
      (fun p hp => hQE_term p)
    calc
      ∑ p ∈ slopes, QE p ≤ ∑ p ∈ slopes, (2 : ℝ) ^ d * a p * Dq := hs
      _ = (∑ p ∈ slopes, (2 : ℝ) ^ d * a p) * Dq := by
        rw [Finset.sum_mul]
      _ = ((2 : ℝ) ^ d * ∑ p ∈ slopes, a p) * Dq := by
        rw [Finset.mul_sum]
      _ = K0 * Dq := by rfl
  have hdiff_sum :
      ∑ p ∈ slopes, (GammaE.measure (uF p - uE p) q).toReal ≤
        ((M - m) / m) ^ 2 * (K0 * Dq) := by
    have hs := Finset.sum_le_sum (s := slopes)
      (fun p hp => hdiff p)
    calc
      ∑ p ∈ slopes, (GammaE.measure (uF p - uE p) q).toReal ≤
          ∑ p ∈ slopes, ((M - m) / m) ^ 2 *
            (GammaE.measure (uE p) q).toReal := hs
      _ = ((M - m) / m) ^ 2 *
          ∑ p ∈ slopes, (GammaE.measure (uE p) q).toReal := by
        rw [Finset.mul_sum]
      _ = ((M - m) / m) ^ 2 * ∑ p ∈ slopes, QE p := by
        simp_rw [hQE]
      _ ≤ ((M - m) / m) ^ 2 * (K0 * Dq) :=
        mul_le_mul_of_nonneg_left hQE_sum (sq_nonneg _)
  have hdiff_sum0 :
      ∑ p ∈ slopes, (GammaE.measure (uF p - uE p) q).toReal ≤
        delta0 ^ 2 * (K0 * Dq) := by
    apply le_trans hdiff_sum
    exact mul_le_mul_of_nonneg_right hratio0 (by positivity)
  have hUF_sum :
      ∑ p ∈ slopes, (GammaE.measure (uF p) q).toReal ≤
        2 * (K0 * Dq) + 2 * delta0 ^ 2 * (K0 * Dq) := by
    have hterm : ∀ p, (GammaE.measure (uF p) q).toReal ≤
        2 * (GammaE.measure (uE p) q).toReal +
          2 * (GammaE.measure (uF p - uE p) q).toReal := by
      intro p
      exact aux_relative_response_variation_measure_sub_le GammaE
        (huF_E p) (huE p) hqmeas
    have hs := Finset.sum_le_sum (s := slopes) (fun p hp => hterm p)
    calc
      ∑ p ∈ slopes, (GammaE.measure (uF p) q).toReal ≤
          ∑ p ∈ slopes, (2 * (GammaE.measure (uE p) q).toReal +
            2 * (GammaE.measure (uF p - uE p) q).toReal) := hs
      _ = 2 * (∑ p ∈ slopes, (GammaE.measure (uE p) q).toReal) +
          2 * (∑ p ∈ slopes, (GammaE.measure (uF p - uE p) q).toReal) := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * (∑ p ∈ slopes, QE p) +
          2 * (∑ p ∈ slopes, (GammaE.measure (uF p - uE p) q).toReal) := by
        simp_rw [hQE]
      _ ≤ 2 * (K0 * Dq) + 2 * delta0 ^ 2 * (K0 * Dq) := by
        calc
          2 * (∑ p ∈ slopes, QE p) +
              2 * (∑ p ∈ slopes, (GammaE.measure (uF p - uE p) q).toReal) ≤
              2 * (K0 * Dq) + 2 * (delta0 ^ 2 * (K0 * Dq)) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hQE_sum (by norm_num))
              (mul_le_mul_of_nonneg_left hdiff_sum0 (by norm_num))
          _ = 2 * (K0 * Dq) + 2 * delta0 ^ 2 * (K0 * Dq) := by ring
  have hpair_finite : ∀ p ∈ slopes,
      (GammaE.measure (uE p) + GammaE.measure (uF p)) q ≠ ⊤ := by
    intro p hp
    rw [Measure.add_apply]
    exact (ENNReal.add_ne_top).2 ⟨GammaE.measure_ne_top (huE p) q,
      GammaE.measure_ne_top (huF_E p) q⟩
  have hpair_toReal : ∀ p ∈ slopes,
      ((GammaE.measure (uE p) + GammaE.measure (uF p)) q).toReal =
        QE p + (GammaE.measure (uF p) q).toReal := by
    intro p hp
    rw [Measure.add_apply,
      ENNReal.toReal_add (GammaE.measure_ne_top (huE p) q)
        (GammaE.measure_ne_top (huF_E p) q), hQE p]
  have hnu_formula :
      ((ENNReal.ofReal Dq⁻¹ •
        (∑ p ∈ slopes, (GammaE.measure (uE p) + GammaE.measure (uF p)))) q).toReal =
        Dq⁻¹ * ∑ p ∈ slopes,
          ((GammaE.measure (uE p) + GammaE.measure (uF p)) q).toReal :=
    aux_relative_response_variation_normalized_sum_toReal Dq hD slopes
      (fun p => GammaE.measure (uE p) + GammaE.measure (uF p)) q hpair_finite
  have hmass_bound :
      Dq⁻¹ * ∑ p ∈ slopes,
          ((GammaE.measure (uE p) + GammaE.measure (uF p)) q).toReal ≤ C := by
    rw [show (∑ p ∈ slopes,
        ((GammaE.measure (uE p) + GammaE.measure (uF p)) q).toReal) =
        ∑ p ∈ slopes, (QE p + (GammaE.measure (uF p) q).toReal) by
          apply Finset.sum_congr rfl
          intro p hp
          exact hpair_toReal p hp]
    rw [Finset.sum_add_distrib]
    have hsum_total := add_le_add hQE_sum hUF_sum
    have hmul := mul_le_mul_of_nonneg_left hsum_total
      (le_of_lt (inv_pos.mpr hD))
    have heq : Dq⁻¹ * (K0 * Dq +
        (2 * (K0 * Dq) + 2 * delta0 ^ 2 * (K0 * Dq))) =
        K0 * (3 + 2 * delta0 ^ 2) := by
      field_simp [ne_of_gt hD]
      ring
    have hconst : K0 * (3 + 2 * delta0 ^ 2) ≤ C := by
      dsimp [C]
      nlinarith [hK0, hdelta0]
    exact heq ▸ hmul |>.trans hconst
  have hdiff_finite : ∀ p ∈ slopes,
      GammaE.measure (uF p - uE p) q ≠ ⊤ := by
    intro p hp
    exact GammaE.measure_ne_top (E.domain.sub_mem (huF_E p) (huE p)) q
  have hzeta_formula :
      ((ENNReal.ofReal Dq⁻¹ •
        (∑ p ∈ slopes, GammaE.measure (uF p - uE p))) q).toReal =
        Dq⁻¹ * ∑ p ∈ slopes, (GammaE.measure (uF p - uE p) q).toReal :=
    aux_relative_response_variation_normalized_sum_toReal Dq hD slopes
      (fun p => GammaE.measure (uF p - uE p)) q hdiff_finite
  have hzeta_bound :
      Dq⁻¹ * ∑ p ∈ slopes, (GammaE.measure (uF p - uE p) q).toReal ≤
        C * (M - m) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hdiff_sum
      (le_of_lt (inv_pos.mpr hD))
    have hstep : Dq⁻¹ *
        (((M - m) / m) ^ 2 * (K0 * Dq)) ≤
        K0 * ((M - m) / m) ^ 2 := by
      field_simp [ne_of_gt hD, ne_of_gt hmpos]
      exact le_rfl
    have hstep2 := hstep.trans
      (mul_le_mul_of_nonneg_left hratio1 hK0)
    have hconst : K0 * C0 ^ 2 ≤ C := by
      dsimp [C]
      nlinarith [hK0, hdelta0]
    have hstep2' : K0 * (C0 ^ 2 * (M - m) ^ 2) =
        (K0 * C0 ^ 2) * (M - m) ^ 2 := by ring
    have hstep2b := hstep2.trans (le_of_eq hstep2')
    have hstep3 := hstep2b.trans
      (mul_le_mul_of_nonneg_right hconst (sq_nonneg (M - m)))
    exact hmul.trans hstep3
  refine ⟨hnu_formula ▸ hmass_bound, hzeta_formula ▸ hzeta_bound, ?_, ?_⟩
  · let K : ℝ := Dq⁻¹ * ∑ p ∈ slopes, (KE p + KF p)
    have hsumK : 0 ≤ ∑ p ∈ slopes, (KE p + KF p) :=
      Finset.sum_nonneg (fun p hp => add_nonneg (hKE p hp) (hKF p hp))
    have hK : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg (le_of_lt (inv_pos.mpr hD)) hsumK
    refine ⟨K, hK, ?_⟩
    intro x rho hrho hrho1
    let S : Set (SpatialCoordinates d) := Metric.ball x rho ∩ (q : Set (SpatialCoordinates d))
    have hfinite : ∀ p ∈ slopes,
        (GammaE.measure (uE p) + GammaE.measure (uF p)) S ≠ ⊤ := by
      intro p hp
      rw [Measure.add_apply]
      exact (ENNReal.add_ne_top).2 ⟨GammaE.measure_ne_top (huE p) S,
        GammaE.measure_ne_top (huF_E p) S⟩
    have hgrowth_term : ∀ p ∈ slopes,
        ((GammaE.measure (uE p) + GammaE.measure (uF p)) S).toReal ≤
          (KE p + KF p) * rho ^ t := by
      intro p hp
      rw [Measure.add_apply,
        ENNReal.toReal_add (GammaE.measure_ne_top (huE p) S)
          (GammaE.measure_ne_top (huF_E p) S)]
      calc
        ((GammaE.measure (uE p) S).toReal + (GammaE.measure (uF p) S).toReal) ≤
            KE p * rho ^ t + KF p * rho ^ t := by
          simpa [S] using add_le_add (hgrowE p hp x rho hrho hrho1)
            (hgrowF p hp x rho hrho hrho1)
        _ = (KE p + KF p) * rho ^ t := by ring
    have hsumgrowth := Finset.sum_le_sum (s := slopes)
      (fun p hp => hgrowth_term p hp)
    have hnorm := aux_relative_response_variation_normalized_sum_toReal Dq hD slopes
      (fun p => GammaE.measure (uE p) + GammaE.measure (uF p)) S hfinite
    have hnorm_bound :
        ((ENNReal.ofReal Dq⁻¹ •
          (∑ p ∈ slopes, (GammaE.measure (uE p) + GammaE.measure (uF p)))) S).toReal ≤
          K * rho ^ t := by
      rw [hnorm]
      calc
        Dq⁻¹ * ∑ p ∈ slopes,
            ((GammaE.measure (uE p) + GammaE.measure (uF p)) S).toReal ≤
            Dq⁻¹ * ∑ p ∈ slopes, (KE p + KF p) * rho ^ t :=
          mul_le_mul_of_nonneg_left hsumgrowth (le_of_lt (inv_pos.mpr hD))
        _ = K * rho ^ t := by
          dsimp [K]
          rw [← Finset.sum_mul]
          ring
    simpa [S] using hnorm_bound
  · intro i j
    field_simp [ne_of_gt hD]
    ring

end
end Paper
