module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamilyLocalCore
public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamilyCompletedCross

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- The completed quadratic measure family, before proving its differential calculus. -/
structure EnergyFamily (F : _root_.DirichletForm m) (U : Set X) where
  measure : Lp ℝ 2 m → Measure X
  cross : Lp ℝ 2 m → Lp ℝ 2 m → SignedMeasure X
  finite : ∀ u ∈ F.domain, measure u univ < ⊤
  mass : ∀ u ∈ F.domain, (measure u univ).toReal = F.form u u
  carried : ∀ u ∈ F.domain, measure u Uᶜ = 0
  regular : ∀ u ∈ F.domain, (measure u).Regular
  cross_symm : ∀ u ∈ F.domain, ∀ v ∈ F.domain, cross u v = cross v u
  cross_self : ∀ u ∈ F.domain, ∀ B, MeasurableSet B → cross u u B = (measure u B).toReal
  cross_add_right : ∀ u ∈ F.domain, ∀ v ∈ F.domain, ∀ w ∈ F.domain,
    cross u (v + w) = cross u v + cross u w
  cross_smul_right : ∀ c : ℝ, ∀ u ∈ F.domain, ∀ v ∈ F.domain,
    cross u (c • v) = c • cross u v
  cross_univ : ∀ u ∈ F.domain, ∀ v ∈ F.domain, cross u v univ = F.form u v
  cross_le : ∀ u ∈ F.domain, ∀ v ∈ F.domain, ∀ B, MeasurableSet B →
    |cross u v B| ≤ Real.sqrt (measure u B).toReal * Real.sqrt (measure v B).toReal
  defining : ∀ u φ, F.toClosedForm.MemCoreOn U u → F.toClosedForm.MemCoreOn U φ →
    ∀ uc φc : X → ℝ, Continuous uc → Continuous φc →
      ⇑u =ᵐ[m] uc → ⇑φ =ᵐ[m] φc →
      ∀ uφ u2 : Lp ℝ 2 m, uφ ∈ F.domain → u2 ∈ F.domain →
        (⇑uφ =ᵐ[m] fun x => uc x * φc x) → (⇑u2 =ᵐ[m] fun x => uc x ^ 2) →
        (∫ x, φc x ∂measure u) = F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ

namespace EnergyFamily

variable {F : _root_.DirichletForm m} {U : Set X} (Γ : EnergyFamily F U)

theorem cross_add_left {u v w : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (hw : w ∈ F.domain) : Γ.cross (u + v) w = Γ.cross u w + Γ.cross v w := by
  rw [Γ.cross_symm _ (F.domain.add_mem hu hv) w hw, Γ.cross_add_right w hw u hu v hv,
    Γ.cross_symm w hw u hu, Γ.cross_symm w hw v hv]

/-- `Γ` is homogeneous in its first argument, on `D(E)`. -/
theorem cross_smul_left (c : ℝ) {u v : Lp ℝ 2 m} (hu : u ∈ F.domain)
    (hv : v ∈ F.domain) : Γ.cross (c • u) v = c • Γ.cross u v := by
  rw [Γ.cross_symm _ (F.domain.smul_mem c hu) v hv, Γ.cross_smul_right c v hv u hu,
    Γ.cross_symm v hv u hu]

/-- Expansion of `Γ(u + v, u + v)` on a set, for `u, v ∈ D(E)`. -/
theorem cross_add_self_apply {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (B : Set X) :
    Γ.cross (u + v) (u + v) B =
      Γ.cross u u B + 2 * Γ.cross u v B + Γ.cross v v B := by
  have huv := F.domain.add_mem hu hv
  rw [Γ.cross_add_left hu hv huv, VectorMeasure.add_apply,
    Γ.cross_add_right u hu u hu v hv, Γ.cross_add_right v hv u hu v hv,
    VectorMeasure.add_apply, VectorMeasure.add_apply, Γ.cross_symm v hv u hu]
  ring

/-- Expansion of `Γ(u - v, u - v)` on a set, for `u, v ∈ D(E)`. -/
theorem cross_sub_self_apply {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (B : Set X) :
    Γ.cross (u - v) (u - v) B =
      Γ.cross u u B - 2 * Γ.cross u v B + Γ.cross v v B := by
  have hnv : (-1 : ℝ) • v ∈ F.domain := F.domain.smul_mem _ hv
  have h : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h, Γ.cross_add_self_apply hu hnv, Γ.cross_smul_right (-1) u hu v hv,
    Γ.cross_smul_left (-1) hv hnv, Γ.cross_smul_right (-1) v hv v hv,
    VectorMeasure.smul_apply, VectorMeasure.smul_apply, VectorMeasure.smul_apply,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- Polarization of the energy measure, for `u, v ∈ D(E)`. -/
theorem cross_eq_polarization {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (B : Set X) :
    Γ.cross u v B =
      (Γ.cross (u + v) (u + v) B - Γ.cross (u - v) (u - v) B) / 4 := by
  rw [Γ.cross_add_self_apply hu hv, Γ.cross_sub_self_apply hu hv]
  ring

/-- `Γ(u)` is finite on every set, for `u ∈ D(E)`. -/
theorem measure_lt_top {u : Lp ℝ 2 m} (hu : u ∈ F.domain) (B : Set X) :
    Γ.measure u B < ⊤ :=
  lt_of_le_of_lt (measure_mono (Set.subset_univ B)) (Γ.finite u hu)

theorem measure_ne_top {u : Lp ℝ 2 m} (hu : u ∈ F.domain) (B : Set X) :
    Γ.measure u B ≠ ⊤ := (Γ.measure_lt_top hu B).ne

/-- `Γ(u, u) ≥ 0` on measurable sets. -/
theorem cross_self_nonneg {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {B : Set X}
    (hB : MeasurableSet B) : 0 ≤ Γ.cross u u B := by
  rw [Γ.cross_self u hu B hB]
  exact ENNReal.toReal_nonneg

/-- The energy measure of an element of the domain is monotone in the set. -/
theorem toReal_measure_mono {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {B C : Set X}
    (hBC : B ⊆ C) : (Γ.measure u B).toReal ≤ (Γ.measure u C).toReal :=
  ENNReal.toReal_mono (Γ.measure_ne_top hu C) (measure_mono hBC)

/-- The total mass of `Γ(u)` is the energy of `u`. -/
theorem toReal_measure_le_form {u : Lp ℝ 2 m} (hu : u ∈ F.domain) (B : Set X) :
    (Γ.measure u B).toReal ≤ F.form u u := by
  rw [← Γ.mass u hu]
  exact Γ.toReal_measure_mono hu (Set.subset_univ B)


end EnergyFamily

theorem exists_energyFamily [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    [SecondCountableTopology X] (F : _root_.DirichletForm m) {U : Set X}
    (h : Data F U) (Γ : CoreMeasure F U) :
    ∃ G : EnergyFamily F U, ∀ u, F.toClosedForm.MemCoreOn U u → G.measure u = Γ.measure u := by
  classical
  obtain ⟨M⟩ := exists_completedCoreFamily h Γ
  let μ : Lp ℝ 2 m → Measure X := fun u =>
    if hu : u ∈ F.domain then M.measure ⟨u, hu⟩ else 0
  let C : Lp ℝ 2 m → Lp ℝ 2 m → SignedMeasure X := fun u v =>
    if hu : u ∈ F.domain then
      if hv : v ∈ F.domain then M.cross ⟨u, hu⟩ ⟨v, hv⟩ else 0
    else 0
  have hμ : ∀ u (hu : u ∈ F.domain), μ u = M.measure ⟨u, hu⟩ := by
    intro u hu
    exact dif_pos hu
  have hC : ∀ u (hu : u ∈ F.domain) v (hv : v ∈ F.domain),
      C u v = M.cross ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u hu v hv
    simp only [C, dif_pos hu, dif_pos hv]
  let G : EnergyFamily F U := {
    measure := μ
    cross := C
    finite := by
      intro u hu
      rw [hμ u hu]
      exact (M.finite ⟨u, hu⟩).measure_univ_lt_top
    mass := by
      intro u hu
      rw [hμ u hu]
      exact M.mass h ⟨u, hu⟩
    carried := by
      intro u hu
      rw [hμ u hu]
      exact M.carried h ⟨u, hu⟩
    regular := by
      intro u hu
      rw [hμ u hu]
      exact M.regular ⟨u, hu⟩
    cross_symm := by
      intro u hu v hv
      rw [hC u hu v hv, hC v hv u hu]
      exact M.cross_symm h ⟨u, hu⟩ ⟨v, hv⟩
    cross_self := by
      intro u hu B hB
      rw [hC u hu u hu, hμ u hu]
      exact M.cross_self h ⟨u, hu⟩ hB
    cross_add_right := by
      intro u hu v hv w hw
      rw [hC u hu (v + w) (F.domain.add_mem hv hw), hC u hu v hv, hC u hu w hw]
      exact M.cross_add_right h ⟨u, hu⟩ ⟨v, hv⟩ ⟨w, hw⟩
    cross_smul_right := by
      intro c u hu v hv
      rw [hC u hu (c • v) (F.domain.smul_mem c hv), hC u hu v hv]
      exact M.cross_smul_right h c ⟨u, hu⟩ ⟨v, hv⟩
    cross_univ := by
      intro u hu v hv
      rw [hC u hu v hv]
      exact M.cross_univ h ⟨u, hu⟩ ⟨v, hv⟩
    cross_le := by
      intro u hu v hv B hB
      rw [hC u hu v hv, hμ u hu, hμ v hv]
      exact M.cross_le h ⟨u, hu⟩ ⟨v, hv⟩ hB
    defining := by
      intro u φ hu hφ uc φc huc hφc huae hφae uφ u2 huφ hu2 hprod hsq
      rw [hμ u hu.1, M.core_eq ⟨u, hu.1⟩ hu]
      exact Γ.defining u φ hu hφ uc φc huc hφc huae hφae uφ u2 huφ hu2 hprod hsq }
  refine ⟨G, ?_⟩
  intro u hu
  change μ u = Γ.measure u
  rw [hμ u hu.1, M.core_eq ⟨u, hu.1⟩ hu]

theorem EnergyFamily.difference_bound {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    {B : Set X} (hB : MeasurableSet B) :
    |(Γ.measure u B).toReal - (Γ.measure v B).toReal| ≤
      Real.sqrt (F.form (u - v) (u - v)) *
        (Real.sqrt (F.form u u) + Real.sqrt (F.form v v)) := by
  have hd := F.domain.sub_mem hu hv
  have he : Γ.cross (u - v) u B + Γ.cross (u - v) v B =
      (Γ.measure u B).toReal - (Γ.measure v B).toReal := by
    have hs : u - v = u + (-1 : ℝ) • v := by module
    rw [hs, Γ.cross_add_left hu (F.domain.smul_mem (-1) hv) hu,
      Γ.cross_add_left hu (F.domain.smul_mem (-1) hv) hv,
      Γ.cross_smul_left (-1) hv hu, Γ.cross_smul_left (-1) hv hv,
      VectorMeasure.add_apply, VectorMeasure.add_apply,
      VectorMeasure.smul_apply, VectorMeasure.smul_apply,
      Γ.cross_symm v hv u hu, Γ.cross_self u hu B hB, Γ.cross_self v hv B hB]
    simp only [smul_eq_mul]
    ring
  have hbd : ∀ w ∈ F.domain,
      |Γ.cross (u - v) w B| ≤ Real.sqrt (F.form (u - v) (u - v)) * Real.sqrt (F.form w w) := by
    intro w hw
    apply (Γ.cross_le _ hd w hw B hB).trans
    exact mul_le_mul (Real.sqrt_le_sqrt (Γ.toReal_measure_le_form hd B))
      (Real.sqrt_le_sqrt (Γ.toReal_measure_le_form hw B)) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  rw [← he, mul_add]
  exact (abs_add_le _ _).trans (add_le_add (hbd u hu) (hbd v hv))

def EnergyFamily.withLocalEnergy {F : _root_.DirichletForm m} {U : Set X}
    (Gamma : EnergyFamily F U) (t : ℝ) (ht : 0 ≤ t) (B : Set X) (hB : MeasurableSet B) :
    ClosedForm m := by
  let E := F.toClosedForm

  refine {
    domain := E.domain
    form := fun u v => E.form u v + t * Gamma.cross u v B
    denseDomain := E.denseDomain
    form_symm := ?_
    form_add_left := ?_
    form_smul_left := ?_
    form_nonneg := ?_
    complete := ?_ }
  · intro u hu v hv
    rw [E.form_symm u hu v hv, Gamma.cross_symm u hu v hv]
  · intro u hu v hv w hw
    rw [E.form_add_left u hu v hv w hw, Gamma.cross_add_left hu hv hw,
      VectorMeasure.add_apply, mul_add]
    ring
  · intro c u hu v hv
    rw [E.form_smul_left c u hu v hv, Gamma.cross_smul_left c hu hv,
      VectorMeasure.smul_apply]
    simp only [smul_eq_mul]
    ring
  · intro u hu
    have hE := E.form_nonneg u hu
    have hGamma := Gamma.cross_self_nonneg hu hB
    exact add_nonneg hE (mul_nonneg ht hGamma)
  · intro u hu hCauchy
    have hECauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
        E.form (u p - u q) (u p - u q) + ‖u p - u q‖ ^ 2 < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hCauchy ε hε
      refine ⟨N, ?_⟩
      intro p hp q hq
      have hdiff : u p - u q ∈ E.domain := E.domain.sub_mem (hu p) (hu q)
      have hGamma := Gamma.cross_self_nonneg hdiff hB
      have hpenalty := mul_nonneg ht hGamma
      have hsmall := hN p hp q hq
      change (E.form (u p - u q) (u p - u q) +
        t * Gamma.cross (u p - u q) (u p - u q) B) +
        ‖u p - u q‖ ^ 2 < ε at hsmall
      linarith only [hpenalty, hsmall]
    obtain ⟨w, hw, hlim⟩ := E.complete u hu hECauchy
    refine ⟨w, hw, ?_⟩
    have hnonneg : ∀ n : ℕ, 0 ≤
        (E.form (u n - w) (u n - w) +
          t * Gamma.cross (u n - w) (u n - w) B) + ‖u n - w‖ ^ 2 := by
      intro n
      have hdiff : u n - w ∈ E.domain := E.domain.sub_mem (hu n) hw
      have hGamma := Gamma.cross_self_nonneg hdiff hB
      have hE := E.form_nonneg (u n - w) hdiff
      exact add_nonneg (add_nonneg hE (mul_nonneg ht hGamma)) (sq_nonneg _)
    have hbound : ∀ n : ℕ,
        (E.form (u n - w) (u n - w) +
          t * Gamma.cross (u n - w) (u n - w) B) + ‖u n - w‖ ^ 2 ≤
        (1 + t) * (E.form (u n - w) (u n - w) + ‖u n - w‖ ^ 2) := by
      intro n
      have hdiff : u n - w ∈ E.domain := E.domain.sub_mem (hu n) hw
      have hcross : Gamma.cross (u n - w) (u n - w) B ≤
          E.form (u n - w) (u n - w) := by
        rw [Gamma.cross_self (u n - w) hdiff B hB]
        exact Gamma.toReal_measure_le_form hdiff B
      have hform : E.form (u n - w) (u n - w) +
          t * Gamma.cross (u n - w) (u n - w) B ≤
          (1 + t) * E.form (u n - w) (u n - w) := by
        calc
          _ = t * Gamma.cross (u n - w) (u n - w) B +
              E.form (u n - w) (u n - w) := by ring
          _ ≤ t * E.form (u n - w) (u n - w) +
              E.form (u n - w) (u n - w) :=
                add_le_add_left (mul_le_mul_of_nonneg_left hcross ht) _
          _ = E.form (u n - w) (u n - w) +
              t * E.form (u n - w) (u n - w) := by ring
          _ = _ := by ring
      have hfactor : 1 ≤ 1 + t := by linarith only [ht]
      have hnorm : 0 ≤ ‖u n - w‖ ^ 2 := sq_nonneg _
      calc
        _ ≤ (1 + t) * E.form (u n - w) (u n - w) + ‖u n - w‖ ^ 2 :=
          add_le_add_left hform _
        _ = ‖u n - w‖ ^ 2 +
            (1 + t) * E.form (u n - w) (u n - w) := by ring
        _ ≤ (1 + t) * ‖u n - w‖ ^ 2 +
            (1 + t) * E.form (u n - w) (u n - w) := by
          simpa only [one_mul] using
            (add_le_add_left
              (mul_le_mul_of_nonneg_right hfactor hnorm)
              ((1 + t) * E.form (u n - w) (u n - w)))
        _ = _ := by ring
    have hscaled : Tendsto
        (fun n : ℕ => (1 + t) *
          (E.form (u n - w) (u n - w) + ‖u n - w‖ ^ 2)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlim.const_mul (1 + t)
    exact squeeze_zero hnonneg (fun n => hbound n) hscaled


theorem EnergyFamily.local_limsup [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.DirichletForm m} {U : Set X} (Γ : EnergyFamily F U)
    {u : ℕ → Lp ℝ 2 m} (hu : ∀ n, u n ∈ F.domain) {v : Lp ℝ 2 m}
    (hlim : Tendsto u atTop (𝓝 v)) {B : ℝ} (hB : ∀ n, F.form (u n) (u n) ≤ B)
    {A : Set X} (hA : MeasurableSet A) {K : ℝ}
    (hK : ∀ n, (Γ.measure (u n) A).toReal ≤ K) :
    v ∈ F.domain ∧ (Γ.measure v A).toReal ≤ K := by
  let E := F.toClosedForm
  let Gamma := Γ
  let un := u
  let u := v
  let E0 := B
  let B := A
  have hE0 := hB
  have hB := hA

  have hdomain := E.mem_domain_of_tendsto_of_form_le hu hlim hE0
  refine ⟨hdomain.1, ?_⟩
  have hE0nonneg : 0 ≤ E0 := le_trans (E.form_nonneg (un 0) (hu 0)) (hE0 0)
  apply le_of_forall_pos_le_add
  intro ε hε
  let t : ℝ := E0 / ε + 1
  have ht : 0 ≤ t := by
    dsimp [t]
    exact add_nonneg (div_nonneg hE0nonneg hε.le) zero_le_one
  have hEt : E0 ≤ t * ε := by
    dsimp [t]
    have hmul := (div_mul_cancel₀ E0 hε.ne')
    linarith only [hmul, hε]
  let F := Gamma.withLocalEnergy t ht B hB
  have hFbound : ∀ n, F.form (un n) (un n) ≤ E0 + t * K := by
    intro n
    have hcross : Gamma.cross (un n) (un n) B = (Gamma.measure (un n) B).toReal :=
      Gamma.cross_self (un n) (hu n) B hB
    change E.form (un n) (un n) + t * Gamma.cross (un n) (un n) B ≤ E0 + t * K
    rw [hcross]
    exact add_le_add (hE0 n) (mul_le_mul_of_nonneg_left (hK n) ht)
  have hFclosed := F.mem_domain_of_tendsto_of_form_le hu hlim hFbound
  have hFenergy : F.form u u ≤ E0 + t * K := hFclosed.2
  have htpos : 0 < t := by
    dsimp [t]
    have hdiv : 0 ≤ E0 / ε := div_nonneg hE0nonneg hε.le
    linarith only [hdiv]
  have hlocal : (Gamma.measure u B).toReal ≤ K + ε := by
    have hcross : Gamma.cross u u B = (Gamma.measure u B).toReal :=
      Gamma.cross_self u hdomain.1 B hB
    have hcompare : E.form u u + t * (Gamma.measure u B).toReal ≤ E0 + t * K := by
      change E.form u u + t * Gamma.cross u u B ≤ E0 + t * K at hFenergy
      rw [hcross] at hFenergy
      exact hFenergy
    have hEunonneg := E.form_nonneg u hdomain.1
    have htmul : t * (Gamma.measure u B).toReal ≤ E0 + t * K := by
      linarith only [hcompare, hEunonneg]
    have hratio : (Gamma.measure u B).toReal ≤ (E0 + t * K) / t :=
      (le_div_iff₀ htpos).2 (by simpa only [mul_comm] using htmul)
    have hEt' : E0 / t ≤ ε := (div_le_iff₀ htpos).2 (by simpa only [mul_comm] using hEt)
    have hratio' : (E0 + t * K) / t = E0 / t + K := by
      rw [add_div, mul_div_cancel_left₀ K htpos.ne']
    rw [hratio'] at hratio
    calc
      (Gamma.measure u B).toReal ≤ E0 / t + K := hratio
      _ ≤ ε + K := add_le_add_left hEt' K
      _ = K + ε := by ring
  exact hlocal



/-- Restriction of a domain family to the relative continuous core. -/
def EnergyFamily.toCoreMeasure {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) : CoreMeasure F U where
  measure := Γ.measure
  finite := fun u hu => Γ.finite u hu.1
  mass := fun u hu => Γ.mass u hu.1
  carried := fun u hu => Γ.carried u hu.1
  regular := fun u hu => Γ.regular u hu.1
  defining := Γ.defining

theorem EnergyFamily.zero_on_open_bounded [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U) (Γ : EnergyFamily F U)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {R : ℝ≥0}
    (huR : ∀ᵐ x ∂m, |u x| ≤ R) {O : Set X} (hO : IsOpen O)
    (hz : ∀ᵐ x ∂m, x ∈ O → u x = 0) : Γ.measure u O = 0 := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  letI : (Γ.measure u).Regular := Γ.regular u hu
  obtain ⟨C, hC⟩ := h.core
  obtain ⟨a, haR⟩ := hC.exists_bounded_coreApproximation F hu huR
  have hcompact : ∀ K : Set X, K ⊆ U ∩ O → IsCompact K → Γ.measure u K = 0 := by
    intro K hKU hK
    obtain ⟨β, f, V, hβ, hf, hfc, hfUO, hβae, hf01, hV, hKV, hfV⟩ :=
      hC.exists_cutoff F hK (h.isOpen.inter hO) hKU inter_subset_left
    have hfu : ∀ᵐ x ∂m, (0 - u x) * f x = 0 := by
      filter_upwards [hz] with x hx
      by_cases hxO : x ∈ O
      · rw [hx hxO, sub_self, zero_mul]
      · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hxf => hxO (hfUO hxf).2)
        rw [hf0, mul_zero]
    obtain ⟨b, hb⟩ := a.exists_plateau haR hβ.1 hf hfc
      (hfUO.trans inter_subset_left) hβae hf01 hfu
    have hb0 : ∀ n, Γ.measure (b.seq n) K = 0 := by
      intro n
      have hzV : ∀ᵐ x ∂m, x ∈ V → b.seq n x = 0 := by
        filter_upwards [b.ae_rep n] with x hx hxV
        rw [hx]
        exact hb n x (hfV x hxV)
      exact measure_mono_null hKV
        (Γ.toCoreMeasure.zero_on_open h (b.memCoreOn n) hV hzV)
    have hle := (Γ.local_limsup b.mem_domain b.tendsto b.energy_le hK.measurableSet
      (fun n => by rw [hb0 n, ENNReal.toReal_zero])).2
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hle ENNReal.toReal_nonneg) |>.resolve_right (Γ.measure_ne_top hu K)
  have hUO : Γ.measure u (U ∩ O) = 0 := by
    rw [(h.isOpen.inter hO).measure_eq_iSup_isCompact (Γ.measure u)]
    simp only [ENNReal.iSup_eq_zero]
    exact hcompact
  apply le_antisymm _ bot_le
  calc
    Γ.measure u O ≤ Γ.measure u (U ∩ O) + Γ.measure u Uᶜ :=
      (measure_mono (fun x hx => by
        by_cases hxU : x ∈ U
        · exact Or.inl ⟨hxU, hx⟩
        · exact Or.inr hxU)).trans (measure_union_le _ _)
    _ = 0 := by rw [hUO, Γ.carried u hu, zero_add]

theorem EnergyFamily.zero_on_open [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U) (Γ : EnergyFamily F U)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {O : Set X} (hO : IsOpen O)
    (hz : ∀ᵐ x ∂m, x ∈ O → u x = 0) : Γ.measure u O = 0 := by
  let un : ℕ → Lp ℝ 2 m := fun n => clipLp (n + 1) u
  have hun : ∀ n, un n ∈ F.domain := fun n => (clipLp_mem F (n + 1) hu).1
  have hE : ∀ n, F.form (un n) (un n) ≤ F.form u u := fun n =>
    (clipLp_mem F (n + 1) hu).2
  have hzero : ∀ n, Γ.measure (un n) O = 0 := by
    intro n
    have hR : ∀ᵐ x ∂m, |un n x| ≤ (n + 1 : ℝ≥0) := by
      filter_upwards [coeFn_clipLp (n + 1) u] with x hx
      rw [hx]
      exact abs_clip_le (by positivity) (u x)
    apply Γ.zero_on_open_bounded h (hun n) hR hO
    filter_upwards [coeFn_clipLp (n + 1) u, hz] with x hx hz' hxO
    rw [hx, hz' hxO]
    exact clip_zero (by positivity)
  have hle := (Γ.local_limsup hun (tendsto_clipLp u) hE hO.measurableSet
    (fun n => by rw [hzero n, ENNReal.toReal_zero])).2
  exact (ENNReal.toReal_eq_zero_iff _).mp
    (le_antisymm hle ENNReal.toReal_nonneg) |>.resolve_right (Γ.measure_ne_top hu O)

theorem EnergyFamily.locality [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U) (Γ : EnergyFamily F U)
    {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    {O : Set X} (hO : IsOpen O) (heq : ⇑u =ᵐ[m.restrict O] ⇑v) :
    (Γ.measure u).restrict O = (Γ.measure v).restrict O := by
  have hd : u - v ∈ F.domain := F.domain.sub_mem hu hv
  have hz : Γ.measure (u - v) O = 0 := by
    apply Γ.zero_on_open h hd hO
    filter_upwards [Lp.coeFn_sub u v, (ae_restrict_iff' hO.measurableSet).1 heq]
      with x hx hy hxO
    rw [hx, Pi.sub_apply, hy hxO, sub_self]
  ext B hB
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
  have hBO : MeasurableSet (B ∩ O) := hB.inter hO.measurableSet
  have hzB : Γ.measure (u - v) (B ∩ O) = 0 := measure_mono_null inter_subset_right hz
  have hcross : ∀ w ∈ F.domain, Γ.cross (u - v) w (B ∩ O) = 0 := by
    intro w hw
    have hb := Γ.cross_le (u - v) hd w hw (B ∩ O) hBO
    rw [hzB, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at hb
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  have he : Γ.cross (u - v) u (B ∩ O) + Γ.cross (u - v) v (B ∩ O) =
      (Γ.measure u (B ∩ O)).toReal - (Γ.measure v (B ∩ O)).toReal := by
    have hs : u - v = u + (-1 : ℝ) • v := by module
    rw [hs, Γ.cross_add_left hu (F.domain.smul_mem (-1) hv) hu,
      Γ.cross_add_left hu (F.domain.smul_mem (-1) hv) hv,
      Γ.cross_smul_left (-1) hv hu, Γ.cross_smul_left (-1) hv hv,
      VectorMeasure.add_apply, VectorMeasure.add_apply,
      VectorMeasure.smul_apply, VectorMeasure.smul_apply,
      Γ.cross_symm v hv u hu, Γ.cross_self u hu (B ∩ O) hBO,
      Γ.cross_self v hv (B ∩ O) hBO]
    simp only [smul_eq_mul]
    ring
  rw [hcross u hu, hcross v hv, zero_add] at he
  exact (ENNReal.toReal_eq_toReal_iff' (Γ.measure_ne_top hu _) (Γ.measure_ne_top hv _)).mp
    (sub_eq_zero.mp he.symm)

end DirichletForm.FOTConstruction
