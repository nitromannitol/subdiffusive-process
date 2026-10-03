module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalLocalIndependence

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal
noncomputable section
/-- A retained triadic scale exists under the large-distance guard, and its two supports are separated. -/
theorem guarded_cutoff {C L R : ℕ} (hL : 1 ≤ L) (hR : 100 * (C + 1) ≤ R) :
 ∃ j : ℕ, 100 * (C + 1) * 3^j ≤ R*L ∧ R*L < 100*(C+1)*3^(j+1) ∧
 100*(C*3^j) ≤ R*L ∧ 2*(10*L)+C*3^j < R*L := by
  have hD : 0 < 100 * (C + 1) := by omega
  have hRpos : R ≤ R * L := by nlinarith [mul_le_mul_right hL R]
  have hN : 100 * (C + 1) ≤ R * L := hR.trans hRpos
  obtain ⟨j, hj1, hj2⟩ := exists_triadic_cutoff hD hN
  refine ⟨j, hj1, hj2, ?_, ?_⟩
  · have h1 : 100 * (C * 3^j) ≤ 100 * (C + 1) * 3^j := by
      nlinarith [pow_pos (by norm_num : 0 < 3) j]
    exact h1.trans hj1
  · have ht : 0 < 3^j := pow_pos (by norm_num : 0 < 3) j
    have h2 : 300 * (C + 1) ≤ 3 * R := by nlinarith [hR]
    have hj2' : R * L < 300 * (C + 1) * 3^j := by
      have h := hj2
      rw [pow_succ] at h
      nlinarith [show 100 * (C + 1) * (3 * 3^j) = 300 * (C + 1) * 3^j from by ring]
    have h3 : R * L < R * (3 * 3^j) := by
      calc R * L < 300 * (C + 1) * 3^j := hj2'
        _ ≤ 3 * R * 3^j := mul_le_mul_left h2 (3^j : ℕ)
        _ = R * (3 * 3^j) := by ring
    have hL3 : L + 1 ≤ 3 * 3^j := Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left h3)
    nlinarith [hj1, hL3, ht]

theorem three_rpow_shift (n j : ℕ) :
 (3 : ℝ)^((3:ℝ)*(n+j+1)/2) = (3:ℝ)^((3:ℝ)*(j+1)/2) * (3:ℝ)^((3:ℝ)*n/2) := by
  rw [show (3:ℝ)*((n:ℝ)+(j:ℝ)+1)/2 = (3:ℝ)*((j:ℝ)+1)/2+(3:ℝ)*(n:ℝ)/2 by ring,
    Real.rpow_add (by norm_num : (0:ℝ)<3)]

theorem three_rpow_shift_ge (n j : ℕ) :
 (3:ℝ)^((3:ℝ)*(j+1)/2) * ((n:ℝ)+1) ≤ (3:ℝ)^((3:ℝ)*(n+j+1)/2) := by
  rw [three_rpow_shift n j]
  exact mul_le_mul_of_nonneg_left (three_rpow_three_halves_mul_ge n) (by positivity)

/-- A single natural threshold absorbs a fixed real constant in a positive linear rate. -/
theorem exists_uniform_threshold {c X : ℝ} (hc : 0<c) :
 ∃ q0 : ℕ, ∀ q : ℝ, (q0:ℝ) ≤ q → X ≤ c*q := by
  refine ⟨⌈X/c⌉₊, fun q hq => ?_⟩
  have h1 : X/c ≤ (⌈X/c⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : X/c ≤ q := h1.trans hq
  have h3 : X ≤ q * c := (div_le_iff₀ hc).mp h2
  simpa [mul_comm] using h3

theorem cutoff_power {N D j : ℕ} (h : N < D*3^(j+1)) :
 (N:ℝ)^((3:ℝ)/2) ≤ (D:ℝ)^((3:ℝ)/2) * (3:ℝ)^((3:ℝ)*(j+1)/2) := by
  have hcast : (N:ℝ) ≤ (D:ℝ)*(3:ℝ)^(j+1) := by
    exact_mod_cast h.le
  calc (N:ℝ)^((3:ℝ)/2)
      ≤ ((D:ℝ)*(3:ℝ)^(j+1))^((3:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) hcast (by norm_num)
    _ = (D:ℝ)^((3:ℝ)/2) * ((3:ℝ)^(j+1))^((3:ℝ)/2) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = (D:ℝ)^((3:ℝ)/2) * (3:ℝ)^((3:ℝ)*(j+1)/2) := by
        rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ (3:ℝ)) (n := j+1) (z := ((3:ℝ)/2)),
          show ((j+1:ℕ):ℝ) * ((3:ℝ)/2) = (3:ℝ)*(j+1)/2 by push_cast; ring]

theorem ball_count_bound (d L N : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N) :
    (((20*L+1)^d : ℕ):ℝ) ≤ (21:ℝ)^d * (N:ℝ)^d := by
  have h : 20*L + 1 ≤ 21*N := by omega
  have hp := Nat.pow_le_pow_left h d
  have hmul : (21*N)^d = 21^d * N^d := Nat.mul_pow 21 N d
  push_cast
  exact_mod_cast (hmul ▸ hp)

theorem log_power_bound {K N : ℝ} (d : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
 Real.log K + (d:ℝ)*Real.log N ≤ (Real.log K + d)*N^((3:ℝ)/2) := by
  have hN0 : (0:ℝ) ≤ N := by linarith
  have hlogK0 : (0:ℝ) ≤ Real.log K := Real.log_nonneg hK
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have hN32 : (1:ℝ) ≤ N^((3:ℝ)/2) := Real.one_le_rpow hN (by norm_num : (0:ℝ) ≤ 3/2)
  have hlogN : Real.log N ≤ N := (Real.log_le_self hN0).trans (by linarith)
  have h1 : N^((1:ℝ)) ≤ N^((3:ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1:ℝ) ≤ 3/2)
  rw [Real.rpow_one] at h1
  have hlogN32 : Real.log N ≤ N^((3:ℝ)/2) := hlogN.trans h1
  have hKterm : Real.log K ≤ Real.log K * N^((3:ℝ)/2) := by
    nlinarith [hlogK0, hN32]
  have hdterm : (d:ℝ)*Real.log N ≤ (d:ℝ)*N^((3:ℝ)/2) := by
    nlinarith [hlogN32, hd0]
  linear_combination hKterm + hdterm

/-- Absorb a polynomial prefactor without making the threshold depend on the radius. -/
theorem polynomial_prefactor_absorption {K N a : ℝ} (d : ℕ)
 (hK : 1 ≤ K) (hN : 1 ≤ N) (ha : 2*(Real.log K+d)≤a) :
 K*N^d*Real.exp (-(a*N^((3:ℝ)/2))) ≤ Real.exp (-(a/2*N^((3:ℝ)/2))) := by
  have hKT : 0 < K := by linarith
  have hNT : 0 < N := by linarith
  have hT0 : 0 ≤ N ^ ((3 : ℝ) / 2) := by positivity
  have hle := (log_power_bound d hK hN).trans
    (mul_le_mul_of_nonneg_right (show Real.log K + (d : ℝ) ≤ a / 2 by linarith) hT0)
  calc K * N ^ d * Real.exp (-(a * N ^ ((3 : ℝ) / 2)))
      = Real.exp (Real.log K + (d : ℝ) * Real.log N + -(a * N ^ ((3 : ℝ) / 2))) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hKT, Real.exp_log hNT]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem shifted_exp_le {A : ℝ} (hA : 0≤A) (n j : ℕ) :
 Real.exp (-(A*(3:ℝ)^((3:ℝ)*(n+j+1)/2))) ≤
 Real.exp (-((A*(3:ℝ)^((3:ℝ)*(j+1)/2))*((n:ℝ)+1))) := by
  have h := mul_le_mul_of_nonneg_left (three_rpow_shift_ge n j) hA
  refine Real.exp_le_exp.mpr ?_
  nlinarith

theorem shifted_threshold {A : ℝ} (hA : Real.log 2 ≤ A) (j : ℕ) :
 Real.log (1:ℝ)+Real.log 2 ≤ A*(3:ℝ)^((3:ℝ)*(j+1)/2) := by
  have hA0 : 0 ≤ A := (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans hA
  have hT : (1:ℝ) ≤ 3^((3:ℝ)*(j+1)/2) := Real.one_le_rpow (by norm_num) (by positivity)
  have hmul : A ≤ A*3^((3:ℝ)*(j+1)/2) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hT hA0
  simpa only [Real.log_one, zero_add] using hA.trans hmul

theorem tsum_ofReal_linear_exp_le {Cp A : ℝ} (hCp : 0 ≤ Cp)
    (hA : Real.log 2 ≤ A) :
    (∑' n : ℕ, ENNReal.ofReal (Cp * Real.exp (-(A * ((n : ℝ) + 1))))) ≤
      ENNReal.ofReal (2 * Cp * Real.exp (-A)) := by
  have hs : Summable (fun n : ℕ => Cp * Real.exp (-(A * ((n : ℝ) + 1)))) := by
    simpa using (summable_pow_mul_exp_neg (Cp := Cp) (N := 1) (A := A) le_rfl
      (by simpa using hA))
  have hb := tsum_pow_mul_exp_neg_le (Cp := Cp) hCp
    (show (1 : ℝ) ≤ 1 from le_rfl)
    (show Real.log (1 : ℝ) + Real.log 2 ≤ A by simpa using hA)
  simp only [one_pow, mul_one] at hb
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg hCp (Real.exp_pos _).le) hs]
  exact ENNReal.ofReal_le_ofReal hb

theorem tsum_shifted_exp_le {Cp A : ℝ} (hCp : 0≤Cp) (hA : Real.log 2≤A) (j : ℕ) :
 (∑' n:ℕ, ENNReal.ofReal (Cp*Real.exp (-(A*(3:ℝ)^((3:ℝ)*(n+j+1)/2))))) ≤
 ENNReal.ofReal (2*Cp*Real.exp (-(A*(3:ℝ)^((3:ℝ)*(j+1)/2)))) := by
  have hA0 : 0 ≤ A := (Real.log_nonneg (by norm_num : (1:ℝ)≤2)).trans hA
  refine (ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (shifted_exp_le hA0 n j) hCp))).trans
    (tsum_ofReal_linear_exp_le hCp ?_)
  simpa only [Real.log_one, zero_add] using shifted_threshold hA j

theorem two_errors_le {a b c d T : ℝ≥0∞} (ha:a+b≤T) (hb:c+d≤T) :
 b+a+d+c≤2*T := by
  have h := add_le_add ha hb
  calc b+a+d+c = (a+b)+(c+d) := by abel
    _ ≤ T+T := h
    _ = 2*T := by ring

theorem coefficient_bound {C N : ℝ} (d : ℕ) (_hC : 0≤C) (hN : 0≤N) :
 4*C*((21:ℝ)^d*N^d) ≤ max 1 (4*C*(21:ℝ)^d)*N^d := by
  calc 4*C*((21:ℝ)^d*N^d)
      = (4*C*(21:ℝ)^d)*N^d := by ring
    _ ≤ max 1 (4*C*(21:ℝ)^d)*N^d :=
      mul_le_mul_of_nonneg_right (le_max_right 1 _) (pow_nonneg hN d)

theorem decay_convert {A D N T : ℝ} (hA : 0≤A) (hD : 0<D)
 (hNT : N≤D*T) : (A/D)*N≤A*T := by
  have h1 : (A/D)*(D*T) = A*T := by
    field_simp
  calc (A/D)*N ≤ (A/D)*(D*T) :=
      mul_le_mul_of_nonneg_left hNT (div_nonneg hA hD.le)
    _ = A*T := h1
/-- The discarded-event sum on an arbitrary finite set, with its cardinality explicit. -/
theorem finite_event_tail_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
 (μ:Measure Ω) (E:ℕ→Lattice d→Set Ω) (F:Finset (Lattice d))
 {Cp A : ℝ} (hCp:0≤Cp) (hA:Real.log 2≤A) (j:ℕ)
 (hp:∀ n z, μ (E n z)≤ENNReal.ofReal (Cp*Real.exp (-(A*(3:ℝ)^((3:ℝ)*n/2))))) :
 (∑' n:ℕ, ∑ z∈F, μ (E (n+j+1) z)) ≤
 ENNReal.ofReal (2*((F.card:ℝ)*Cp)*Real.exp (-(A*(3:ℝ)^((3:ℝ)*(j+1)/2)))) := by
  have hstep : ∀ n : ℕ, (∑ z ∈ F, μ (E (n+j+1) z)) ≤
      ENNReal.ofReal ((F.card : ℝ)*Cp*Real.exp (-(A*(3:ℝ)^((3:ℝ)*(n+j+1)/2)))) := by
    intro n
    calc (∑ z ∈ F, μ (E (n+j+1) z))
        ≤ ∑ _z ∈ F, ENNReal.ofReal (Cp*Real.exp (-(A*(3:ℝ)^((3:ℝ)*(n+j+1)/2)))) := by
          exact Finset.sum_le_sum fun z _ => by
            simpa only [Nat.cast_add, Nat.cast_one] using hp (n+j+1) z
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  exact (ENNReal.tsum_le_tsum hstep).trans
    (tsum_shifted_exp_le (Cp := (F.card : ℝ)*Cp) (by positivity) hA j)

/-- The complete numerical truncation bound for two radius-`10 L` balls. -/
theorem two_ball_tail_decay {Cp A : ℝ} (hCp : 0 ≤ Cp)
    (hA : Real.log 2 ≤ A) (d L R D j : ℕ) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hD : 0 < D) (hupper : R*L < D*3^(j+1))
    (habs : 2*(Real.log (max 1 (4*Cp*(21:ℝ)^d)) + d) ≤
      A / (D:ℝ)^((3:ℝ)/2)) :
    4*Cp*(((20*L+1)^d:ℕ):ℝ)*Real.exp (-(A*(3:ℝ)^((3:ℝ)*(j+1)/2))) ≤
      Real.exp (-(A/(2*(D:ℝ)^((3:ℝ)/2))*((R*L:ℕ):ℝ)^((3:ℝ)/2))) := by
  let N : ℕ := R*L
  let K : ℝ := max 1 (4*Cp*(21:ℝ)^d)
  let Dp : ℝ := (D:ℝ)^((3:ℝ)/2)
  have hA0 : 0 ≤ A := (Real.log_nonneg (by norm_num : (1:ℝ)≤2)).trans hA
  have hDp : 0 < Dp := by dsimp [Dp]; positivity
  have hLN : L ≤ N := by dsimp [N]; nlinarith
  have hN : (1:ℝ) ≤ N := by exact_mod_cast hL.trans hLN
  have hcut := decay_convert hA0 hDp (cutoff_power hupper)
  have he : Real.exp (-(A*(3:ℝ)^((3:ℝ)*(j+1)/2))) ≤
      Real.exp (-(A/Dp*(N:ℝ)^((3:ℝ)/2))) :=
    Real.exp_le_exp.mpr (by dsimp [N, Dp]; linarith)
  have hcoeff : 4*Cp*(((20*L+1)^d:ℕ):ℝ) ≤ K*(N:ℝ)^d := by
    calc 4*Cp*(((20*L+1)^d:ℕ):ℝ)
        ≤ 4*Cp*((21:ℝ)^d*(N:ℝ)^d) :=
          mul_le_mul_of_nonneg_left (ball_count_bound d L N hL hLN) (by positivity)
      _ ≤ _ := coefficient_bound d hCp (by positivity)
  calc 4*Cp*(((20*L+1)^d:ℕ):ℝ)*Real.exp (-(A*(3:ℝ)^((3:ℝ)*(j+1)/2)))
      ≤ (K*(N:ℝ)^d)*Real.exp (-(A/Dp*(N:ℝ)^((3:ℝ)/2))) :=
        mul_le_mul hcoeff he (by positivity) (by dsimp [K]; positivity)
    _ ≤ Real.exp (-((A/Dp)/2*(N:ℝ)^((3:ℝ)/2))) :=
      polynomial_prefactor_absorption d (le_max_left _ _) hN habs
    _ = _ := by congr 2; dsimp [N, Dp]; ring

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
