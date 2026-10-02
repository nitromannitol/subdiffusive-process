import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsMesoscopicLift




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The arithmetic of the two summations -/

/-- **The Cauchy–Schwarz summation of the mesoscopic price.**

If each cell obeys `|c_i| ≤ beta P E_i + beta⁻¹ R √(E_i) √(M_i)` and the cell
energies and masses sum into `E` and `M`, then the total obeys the *same* price
with the same `P` and `R`.  The cross term is the only place where the cells
interact, and Cauchy–Schwarz is what keeps the constant unchanged. -/
theorem abs_sum_le_price_of_cell_prices {ι : Type*} (I : Finset ι)
    {Ei Mi : ι → ℝ} {c : ι → ℝ} {E M beta P R : ℝ}
    (hEi : ∀ i, 0 ≤ Ei i) (hMi : ∀ i, 0 ≤ Mi i)
    (hE : ∑ i ∈ I, Ei i ≤ E) (hM : ∑ i ∈ I, Mi i ≤ M)
    (hbeta : 0 < beta) (hP : 0 ≤ P) (hR : 0 ≤ R)
    (hc : ∀ i ∈ I, |c i| ≤
      beta * P * Ei i + beta⁻¹ * R * Real.sqrt (Ei i) * Real.sqrt (Mi i)) :
    |∑ i ∈ I, c i| ≤ beta * P * E + beta⁻¹ * R * Real.sqrt E * Real.sqrt M := by
  classical
  have hbetainv : 0 ≤ beta⁻¹ := le_of_lt (inv_pos.mpr hbeta)
  have htri : |∑ i ∈ I, c i| ≤ ∑ i ∈ I, |c i| := Finset.abs_sum_le_sum_abs _ _
  have hsum : ∑ i ∈ I, |c i| ≤
      ∑ i ∈ I, (beta * P * Ei i +
        beta⁻¹ * R * (Real.sqrt (Ei i) * Real.sqrt (Mi i))) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have := hc i hi
    linarith [this]
  have hsplit : ∑ i ∈ I, (beta * P * Ei i +
      beta⁻¹ * R * (Real.sqrt (Ei i) * Real.sqrt (Mi i))) =
      beta * P * (∑ i ∈ I, Ei i) +
        beta⁻¹ * R * ∑ i ∈ I, Real.sqrt (Ei i) * Real.sqrt (Mi i) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hcs : ∑ i ∈ I, Real.sqrt (Ei i) * Real.sqrt (Mi i) ≤
      Real.sqrt (∑ i ∈ I, Ei i) * Real.sqrt (∑ i ∈ I, Mi i) :=
    Real.sum_sqrt_mul_sqrt_le I hEi hMi
  have hEsum_nonneg : 0 ≤ ∑ i ∈ I, Ei i := Finset.sum_nonneg fun i _ => hEi i
  have hMsum_nonneg : 0 ≤ ∑ i ∈ I, Mi i := Finset.sum_nonneg fun i _ => hMi i
  have hsqE : Real.sqrt (∑ i ∈ I, Ei i) ≤ Real.sqrt E := Real.sqrt_le_sqrt hE
  have hsqM : Real.sqrt (∑ i ∈ I, Mi i) ≤ Real.sqrt M := Real.sqrt_le_sqrt hM
  have hprod : Real.sqrt (∑ i ∈ I, Ei i) * Real.sqrt (∑ i ∈ I, Mi i) ≤
      Real.sqrt E * Real.sqrt M :=
    mul_le_mul hsqE hsqM (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfirst : beta * P * (∑ i ∈ I, Ei i) ≤ beta * P * E :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have hsecond : beta⁻¹ * R * (∑ i ∈ I, Real.sqrt (Ei i) * Real.sqrt (Mi i)) ≤
      beta⁻¹ * R * (Real.sqrt E * Real.sqrt M) :=
    mul_le_mul_of_nonneg_left (hcs.trans hprod) (by positivity)
  calc
    |∑ i ∈ I, c i| ≤ ∑ i ∈ I, |c i| := htri
    _ ≤ ∑ i ∈ I, (beta * P * Ei i +
        beta⁻¹ * R * (Real.sqrt (Ei i) * Real.sqrt (Mi i))) := hsum
    _ = beta * P * (∑ i ∈ I, Ei i) +
        beta⁻¹ * R * ∑ i ∈ I, Real.sqrt (Ei i) * Real.sqrt (Mi i) := hsplit
    _ ≤ beta * P * E + beta⁻¹ * R * (Real.sqrt E * Real.sqrt M) := by linarith
    _ = beta * P * E + beta⁻¹ * R * Real.sqrt E * Real.sqrt M := by ring

/-- **The additivity of the coarse energy bound.**  From `t e_i ≤ Gam m_i` on
each mesoscopic cell, `e ≤ Σ e_i` and `Σ m_i ≤ N M`, the parent obeys
`t e ≤ (N Gam) M`; the overlap multiplicity `N` of the mesoscopic cover is the
only loss. -/
theorem cell_energy_bound_sum {ι : Type*} (I : Finset ι)
    {ei mi : ι → ℝ} {e M N Gam t : ℝ}
    (hGam : 0 ≤ Gam) (ht : 0 < t)
    (hcell : ∀ i ∈ I, t * ei i ≤ Gam * mi i)
    (he : e ≤ ∑ i ∈ I, ei i)
    (hm : ∑ i ∈ I, mi i ≤ N * M) :
    t * e ≤ Gam * (N * M) := by
  have h1 : t * e ≤ t * ∑ i ∈ I, ei i := mul_le_mul_of_nonneg_left he ht.le
  have h2 : t * ∑ i ∈ I, ei i = ∑ i ∈ I, t * ei i := by rw [Finset.mul_sum]
  have h3 : ∑ i ∈ I, t * ei i ≤ ∑ i ∈ I, Gam * mi i :=
    Finset.sum_le_sum hcell
  have h4 : ∑ i ∈ I, Gam * mi i = Gam * ∑ i ∈ I, mi i := by rw [Finset.mul_sum]
  have h5 : Gam * ∑ i ∈ I, mi i ≤ Gam * (N * M) :=
    mul_le_mul_of_nonneg_left hm hGam
  linarith [h1, h3, h5, h2.symm.le, h2.le, h4.le, h4.symm.le]

/-! ## The two predicates at the contraction cube -/

/-- **`CoarseEnergyBoundOn` at the contraction cube from the mesoscopic cells.**

The geometric input is the pair of integrated hypotheses: the cell cores cover
the intermediate set (`henergy`) and the cell parents have bounded overlap
inside the contraction cube (`hmass`).  The constant degrades exactly by the
overlap multiplicity `N`. -/
theorem coarseEnergyBoundOn_of_cells {ι : Type*} (I : Finset ι)
    {a : Vec d → ℝ} {W V : Set (Vec d)} {Ws Vs : ι → Set (Vec d)}
    {w : Vec d → ℝ} {G : Vec d → Vec d} {t Gam N : ℝ}
    (hGam : 0 ≤ Gam) (ht : 0 < t)
    (hcell : ∀ i ∈ I, CoarseEnergyBoundOn a (Ws i) (Vs i) w G t Gam)
    (henergy : (∫ x in V, a x * vecNormSq (G x) ∂volume) ≤
      ∑ i ∈ I, ∫ x in Vs i, a x * vecNormSq (G x) ∂volume)
    (hmass : (∑ i ∈ I, ∫ x in Ws i, w x ^ 2 ∂volume) ≤
      N * ∫ x in W, w x ^ 2 ∂volume) :
    CoarseEnergyBoundOn a W V w G t (Gam * N) := by
  have hsum := cell_energy_bound_sum I (ei := fun i => ∫ x in Vs i,
      a x * vecNormSq (G x) ∂volume)
    (mi := fun i => ∫ x in Ws i, w x ^ 2 ∂volume)
    (e := ∫ x in V, a x * vecNormSq (G x) ∂volume)
    (M := ∫ x in W, w x ^ 2 ∂volume) (N := N) (Gam := Gam) (t := t)
    hGam ht (fun i hi => hcell i hi) henergy hmass
  have : Gam * (N * ∫ x in W, w x ^ 2 ∂volume) =
      Gam * N * ∫ x in W, w x ^ 2 ∂volume := by ring
  rw [this] at hsum
  exact hsum

/-- **`MesoscopicCrossPriceEnergyOn` at the contraction cube from the mesoscopic
cells.**

The cross term splits over the cells (`hsplit`), the cell energies and masses
sum into the parent's (`henergy`, `hmass`), and `abs_sum_le_price_of_cell_prices`
does the rest — with the **same** `P`, `R` and `Sc`, by Cauchy–Schwarz.  This is
the step that lets the price be taken at the balanced mesoscopic scale, where
`Sc` is dimension-only, and still be consumed at the contraction cube. -/
theorem mesoscopicCrossPriceEnergyOn_of_cells {ι : Type*} (I : Finset ι)
    {a : Vec d → ℝ} {W V : Set (Vec d)} {Ws Vs : ι → Set (Vec d)}
    {w : Vec d → ℝ} {G : Vec d → Vec d} {chi : Vec d → ℝ} {t P R Sc : ℝ}
    (ht : 0 < t) (hP : 0 ≤ P) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hEinn : ∀ i, 0 ≤ ∫ x in Vs i, a x * vecNormSq (G x) ∂volume)
    (hMinn : ∀ i, 0 ≤ ∫ x in Ws i, w x ^ 2 ∂volume)
    (hcell : ∀ i ∈ I,
      MesoscopicCrossPriceEnergyOn a (Ws i) (Vs i) w G chi t P R Sc)
    (hsplit : (2 * ∫ x in W, a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume) =
      ∑ i ∈ I, 2 * ∫ x in Ws i, a x * chi x * w x *
        vecDot (G x) (fun j ↦ (fderiv ℝ chi x) (basisVec j)) ∂volume)
    (henergy : (∑ i ∈ I, ∫ x in Vs i, a x * vecNormSq (G x) ∂volume) ≤
      ∫ x in V, a x * vecNormSq (G x) ∂volume)
    (hmass : (∑ i ∈ I, ∫ x in Ws i, w x ^ 2 ∂volume) ≤
      ∫ x in W, w x ^ 2 ∂volume) :
    MesoscopicCrossPriceEnergyOn a W V w G chi t P R Sc := by
  intro beta hbeta0 hbeta1
  set Ei : ι → ℝ := fun i =>
    (∫ x in Vs i, a x * vecNormSq (G x) ∂volume) +
      Sc * (t⁻¹ * ∫ x in Ws i, w x ^ 2 ∂volume) with hEidef
  set Mi : ι → ℝ := fun i => ∫ x in Ws i, w x ^ 2 ∂volume with hMidef
  set E : ℝ := (∫ x in V, a x * vecNormSq (G x) ∂volume) +
    Sc * (t⁻¹ * ∫ x in W, w x ^ 2 ∂volume) with hEdef
  set M : ℝ := ∫ x in W, w x ^ 2 ∂volume with hMdef
  have htinv : 0 ≤ t⁻¹ := le_of_lt (inv_pos.mpr ht)
  have hEinn' : ∀ i, 0 ≤ Ei i := by
    intro i
    have := hEinn i
    have h2 : 0 ≤ Sc * (t⁻¹ * ∫ x in Ws i, w x ^ 2 ∂volume) :=
      mul_nonneg hSc (mul_nonneg htinv (hMinn i))
    rw [hEidef]
    linarith
  have hMinn' : ∀ i, 0 ≤ Mi i := hMinn
  have hEsum : ∑ i ∈ I, Ei i ≤ E := by
    have hsplitsum : ∑ i ∈ I, Ei i =
        (∑ i ∈ I, ∫ x in Vs i, a x * vecNormSq (G x) ∂volume) +
          Sc * (t⁻¹ * ∑ i ∈ I, ∫ x in Ws i, w x ^ 2 ∂volume) := by
      rw [hEidef]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [hsplitsum, hEdef]
    have h2 : Sc * (t⁻¹ * ∑ i ∈ I, ∫ x in Ws i, w x ^ 2 ∂volume) ≤
        Sc * (t⁻¹ * ∫ x in W, w x ^ 2 ∂volume) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass htinv) hSc
    linarith
  have hMsum : ∑ i ∈ I, Mi i ≤ M := hmass
  have hcprice : ∀ i ∈ I,
      |2 * ∫ x in Ws i, a x * chi x * w x *
          vecDot (G x) (fun j ↦ (fderiv ℝ chi x) (basisVec j)) ∂volume| ≤
        beta * P * Ei i + beta⁻¹ * R * Real.sqrt (Ei i) * Real.sqrt (Mi i) := by
    intro i hi
    exact hcell i hi beta hbeta0 hbeta1
  have hres := abs_sum_le_price_of_cell_prices I (Ei := Ei) (Mi := Mi)
    (c := fun i => 2 * ∫ x in Ws i, a x * chi x * w x *
      vecDot (G x) (fun j ↦ (fderiv ℝ chi x) (basisVec j)) ∂volume)
    hEinn' hMinn' hEsum hMsum hbeta0 hP hR hcprice
  rw [hsplit]
  exact hres

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
