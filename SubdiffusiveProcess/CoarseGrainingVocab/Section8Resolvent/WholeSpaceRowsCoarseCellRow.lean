
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsPriceCover
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellContraction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedExteriorL2

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## 1. The contraction on the `translatedCube` pair -/

/-- **The coarse-grained local `L²` contraction on a `translatedCube` pair.**

`massive_local_l2_coarse_contraction_of_energy_price_on` with

* `S = translatedCube d n c` the contracted cube,
* `W = translatedCube d (n+1) c` the contraction denominator,
* `V = Metric.ball c ((4/5) 3^n)` the intermediate set of the intermediate-ball geometry,

and the Dirichlet term of the conclusion dropped.  This is exactly the shape of
the `hcell` hypothesis of the repaired stopping partition's exterior row. -/
theorem massive_local_l2_translatedCube_coarse_contraction
    {a : Vec d → ℝ} {lam Lam t eta P R Sc Gam K : ℝ} {n : ℤ} {c : Vec d}
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) c)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam : 0 < Gam) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam + Sc)))
    (u : H1Function (translatedCube d (n + 1) c))
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) c) u (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi)
    (hchiBox : tsupport chi ⊆
      {x : Vec d | ∀ i, |x i - c i| ≤ 3 / 4 * (3 : ℝ) ^ n})
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hchi_one : ∀ x ∈ translatedCube d n c, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hprice : MesoscopicCrossPriceEnergyOn a (translatedCube d (n + 1) c)
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) u.toFun u.grad chi t P R Sc)
    (henergy : CoarseEnergyBoundOn a (translatedCube d (n + 1) c)
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) u.toFun u.grad t Gam)
    (hsmall : 81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) * t ≤ eta ^ 4) :
    (∫ x in translatedCube d n c, u.toFun x ^ 2 ∂volume) ≤
      eta * ∫ x in translatedCube d (n + 1) c, u.toFun x ^ 2 ∂volume := by
  have hchiS : tsupport chi ⊆ translatedCube d (n + 1) c :=
    hchiBox.trans ((box_subset_ball d n c).trans (ball_subset_translatedCube_succ d n c))
  have hbase := massive_local_l2_coarse_contraction_of_energy_price_on
    (isOpenBoundedConvexDomain_translatedCube (n + 1) c) hEll haNonneg ht heta
    hP hGam hR hSc hbeta1 (translatedCube_subset_succ d n c)
    (isOpenBoundedConvexDomain_translatedCube n c).isOpen.measurableSet u hu
    hchi hchiC hchiS hchi_le hchi_one hK hprice henergy hsmall
  have hgrad : 0 ≤ t * ∫ x in translatedCube d n c,
      a x * vecNormSq (u.grad x) ∂volume :=
    mul_nonneg ht.le (setIntegral_nonneg
      (isOpenBoundedConvexDomain_translatedCube n c).isOpen.measurableSet
      fun x _ ↦ mul_nonneg (haNonneg x) (vecNormSq_nonneg _))
  linarith only [hbase, hgrad]

/-! ## 2. The contraction from the per-cell mesoscopic inputs -/

/-- **The coarse per-cell contraction from the two mesoscopic legs.**

The energy leg is `coarseEnergyBoundOn_contraction_pair_of_mesoCells`
(constant `Gam0 * 27^d`, the `27^d` being the overlap of the mesoscopic lattice
cover) and the price leg is
`mesoscopicCrossPriceEnergyOn_contraction_pair_of_triadicCells` (constant `P`,
`R`, `Sc`, no multiplicity because the triadic price cells are disjoint).

The mesoscopic scale must be at least three triadic scales below the contraction
scale (`hkn`), which is what makes the price cells fit between the cutoff's
support box and the intermediate ball. -/
theorem massive_local_l2_translatedCube_coarse_contraction_of_cells
    {a : Vec d → ℝ} {lam Lam t eta P R Sc Gam0 K : ℝ} {k n : ℤ} {c : Vec d}
    (hkn : k ≤ n - 3)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) c)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam0 : 0 < Gam0) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam0 * 27 ^ d + Sc)))
    (u : H1Function (translatedCube d (n + 1) c))
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) c) u (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi)
    (hchiBox : tsupport chi ⊆
      {x : Vec d | ∀ i, |x i - c i| ≤ 3 / 4 * (3 : ℝ) ^ n})
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hchi_one : ∀ x ∈ translatedCube d n c, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hcrossInt : IntegrableOn (fun x => a x * chi x * u.toFun x *
      vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (n + 1) c) volume)
    (henergyInt : IntegrableOn (fun x => a x * vecNormSq (u.grad x))
      (translatedCube d (n + 1) c) volume)
    (hmassInt : IntegrableOn (fun x => u.toFun x ^ 2)
      (translatedCube d (n + 1) c) volume)
    (hpricecell : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) u.toFun u.grad chi t P R Sc)
    (henergycell : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) u.toFun u.grad
        t Gam0)
    (hsmall : 81 * (P * (Gam0 * 27 ^ d + Sc)) ^ 2 * R ^ 2 *
      (Gam0 * 27 ^ d + Sc) * t ≤ eta ^ 4) :
    (∫ x in translatedCube d n c, u.toFun x ^ 2 ∂volume) ≤
      eta * ∫ x in translatedCube d (n + 1) c, u.toFun x ^ 2 ∂volume := by
  have hprice := mesoscopicCrossPriceEnergyOn_contraction_pair_of_triadicCells
    hkn ht hP.le hR hSc haNonneg hchiBox hcrossInt henergyInt hmassInt hpricecell
  have henergy := coarseEnergyBoundOn_contraction_pair_of_mesoCells
    (by omega : k ≤ n) ht hGam0.le
    (fun x => mul_nonneg (haNonneg x) (vecNormSq_nonneg _)) henergyInt hmassInt
    henergycell
  have hGam : (0 : ℝ) < Gam0 * 27 ^ d := by positivity
  exact massive_local_l2_translatedCube_coarse_contraction hEll haNonneg ht heta
    hP hGam hR hSc hbeta1 u hu hchi hchiC hchiBox hchi_le hchi_one hK hprice
    henergy hsmall

/-! ## 3. The numerical obligation -/

/-- **The smallness hypothesis of §1 from the manuscript's condition.**

`mesoscopic_smallness_of_paper_condition_theta`  with the datum
coefficient absorbed into the coarse energy constant (`Ssmall = 0`,
`Gam = Gam0 27^d + Sc`, which is the constant the two legs of §2 actually
produce).  `hcond` is the manuscript's condition
`t Λ¹² λ⁻¹¹ ≤ C⁻¹ η⁴` at the arbitrary constant `C = 81 c³`, and `Theta` is the
coarse ellipticity ratio power carried by the Caccioppoli prefactor. -/
theorem coarse_contraction_smallness_of_paper_condition
    {t lam Lam eta cst P R Sc Gam0 Theta : ℝ} (ht : 0 < t) (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam) (hc : 0 < cst) (hTheta : 1 ≤ Theta)
    (hGamNonneg : 0 ≤ Gam0 * 27 ^ d + Sc)
    (hPS : (P * (Gam0 * 27 ^ d + Sc)) ^ 2 ≤ cst * Theta ^ 3)
    (hR : R ^ 2 ≤ cst * Lam) (hGam : Gam0 * 27 ^ d + Sc ≤ cst * Theta)
    (hdom : Theta ^ 4 * Lam ≤ Lam ^ 12 * lam⁻¹ ^ 11)
    (hcond : t * (Lam ^ 12 * lam⁻¹ ^ 11) ≤ (81 * cst ^ 3)⁻¹ * eta ^ 4) :
    81 * (P * (Gam0 * 27 ^ d + Sc)) ^ 2 * R ^ 2 * (Gam0 * 27 ^ d + Sc) * t ≤
      eta ^ 4 := by
  have h := mesoscopic_smallness_of_paper_condition_theta (t := t) (lam := lam)
    (Lam := Lam) (eta := eta) (c := cst) (P := P) (R := R) (Ssmall := 0)
    (Gam := Gam0 * 27 ^ d + Sc) (Theta := Theta) ht hlam hlamLam hc hGamNonneg
    hTheta (by simpa using hPS) hR hGam hdom hcond
  simpa using h

/-- Monotonicity of the per-cell contraction in the contraction factor: the
factor produced by §1 may be replaced by any larger one, in particular by the
repaired stopping partition's `repairedStoppingContractionFactor d`. -/
theorem translatedCube_mass_contraction_mono {w : Vec d → ℝ} {theta theta' : ℝ}
    {n : ℤ} {c : Vec d} (hmono : theta ≤ theta')
    (h : (∫ x in translatedCube d n c, w x ^ 2 ∂volume) ≤
      theta * ∫ x in translatedCube d (n + 1) c, w x ^ 2 ∂volume) :
    (∫ x in translatedCube d n c, w x ^ 2 ∂volume) ≤
      theta' * ∫ x in translatedCube d (n + 1) c, w x ^ 2 ∂volume := by
  have hnn : (0 : ℝ) ≤ ∫ x in translatedCube d (n + 1) c, w x ^ 2 ∂volume :=
    setIntegral_nonneg
      (isOpenBoundedConvexDomain_translatedCube (n + 1) c).isOpen.measurableSet
      fun x _ ↦ sq_nonneg _
  exact h.trans (mul_le_mul_of_nonneg_right hmono hnn)

/-- The repaired stopping partition's per-cell factor is at most `1`; with
`translatedCube_mass_contraction_mono` this is the only numerical comparison a
caller has to make between the contraction factor `eta` produced by §1 and the
factor the exterior row demands. -/
theorem repairedStoppingContractionFactor_le_one :
    repairedStoppingContractionFactor d ≤ 1 := by
  have hD : 0 < (repairedStoppingDegreeBound d : ℝ) :=
    Nat.cast_pos.mpr repairedStoppingDegreeBound_pos
  have h1 : (1 : ℝ) ≤ (repairedStoppingDegreeBound d : ℝ) :=
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr repairedStoppingDegreeBound_pos.ne')
  have hden : (1 : ℝ) ≤ 2 * (repairedStoppingDegreeBound d : ℝ) *
      (((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ)) := by
    have h2 : (1 : ℝ) ≤ ((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    nlinarith
  have hpos : (0 : ℝ) < 2 * (repairedStoppingDegreeBound d : ℝ) *
      (((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ)) :=
    lt_of_lt_of_le zero_lt_one hden
  rw [repairedStoppingContractionFactor]
  exact (div_le_one hpos).mpr hden

/-- Consequently the `hbeta1` hypothesis of §1 is automatic at
`eta = repairedStoppingContractionFactor d` as soon as the product of the price
constant and the coarse energy constant is at least one. -/
theorem repairedStopping_le_three_mul {P G : ℝ} (h : 1 ≤ P * G) :
    repairedStoppingContractionFactor d ≤ 3 * (P * G) := by
  have h1 := repairedStoppingContractionFactor_le_one (d := d)
  linarith [h, h1]

/-! ## 3b. Congruence of the two legs in the solution fields

The per-cell analytic inputs (energy and price estimates) are
proved for an `H¹` function **on the cell**, while the assembly of §2 consumes
them for the fields of the solution on the contraction cube — and ultimately for
the carrier's own global fields.  Both predicates only see set integrals
over subsets of their first argument, so they transfer along a pointwise
identification of the mass field and an almost-everywhere identification of the
gradient. -/

theorem coarseEnergyBoundOn_congr {a : Vec d → ℝ} {W V : Set (Vec d)}
    {w1 w2 : Vec d → ℝ} {G1 G2 : Vec d → Vec d} {T Gam : ℝ}
    (hWmeas : MeasurableSet W) (hVW : V ⊆ W)
    (hw : ∀ x ∈ W, w1 x = w2 x)
    (hG : G1 =ᵐ[volume.restrict W] G2)
    (h : CoarseEnergyBoundOn a W V w1 G1 T Gam) :
    CoarseEnergyBoundOn a W V w2 G2 T Gam := by
  have hGV : G1 =ᵐ[volume.restrict V] G2 :=
    ae_mono (Measure.restrict_mono hVW le_rfl) hG
  have hE : (∫ x in V, a x * vecNormSq (G1 x) ∂volume) =
      ∫ x in V, a x * vecNormSq (G2 x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hGV] with x hx
    rw [hx]
  have hM : (∫ x in W, w1 x ^ 2 ∂volume) = ∫ x in W, w2 x ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' hWmeas).2 (Filter.Eventually.of_forall hw)]
      with x hx
    rw [hx]
  have h' : T * ∫ x in V, a x * vecNormSq (G1 x) ∂volume ≤
      Gam * ∫ x in W, w1 x ^ 2 ∂volume := h
  rw [hE, hM] at h'
  exact h'

theorem mesoscopicCrossPriceEnergyOn_congr {a chi : Vec d → ℝ}
    {W V : Set (Vec d)} {w1 w2 : Vec d → ℝ} {G1 G2 : Vec d → Vec d}
    {t P R Sc : ℝ}
    (hWmeas : MeasurableSet W) (hVW : V ⊆ W)
    (hw : ∀ x ∈ W, w1 x = w2 x)
    (hG : G1 =ᵐ[volume.restrict W] G2)
    (h : MesoscopicCrossPriceEnergyOn a W V w1 G1 chi t P R Sc) :
    MesoscopicCrossPriceEnergyOn a W V w2 G2 chi t P R Sc := by
  have hWae : ∀ᵐ x ∂volume.restrict W, w1 x = w2 x :=
    (ae_restrict_iff' hWmeas).2 (Filter.Eventually.of_forall hw)
  have hGV : G1 =ᵐ[volume.restrict V] G2 :=
    ae_mono (Measure.restrict_mono hVW le_rfl) hG
  have hE : (∫ x in V, a x * vecNormSq (G1 x) ∂volume) =
      ∫ x in V, a x * vecNormSq (G2 x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hGV] with x hx
    rw [hx]
  have hM : (∫ x in W, w1 x ^ 2 ∂volume) = ∫ x in W, w2 x ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hWae] with x hx
    rw [hx]
  have hC : (∫ x in W, a x * chi x * w1 x *
        vecDot (G1 x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume) =
      ∫ x in W, a x * chi x * w2 x *
        vecDot (G2 x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hWae, hG] with x hx hgx
    rw [hx, hgx]
  intro beta hbeta hbeta1
  have hbase := h beta hbeta hbeta1
  rw [hC, hE, hM] at hbase
  exact hbase

/-! ## 4. From the local solution to the whole-space carrier, and the row -/

/-- **The whole-space carrier inherits the local contraction.**

The carrier only promises a local `H¹` solution on each open bounded
convex domain; this transports a contraction proved for *every* such local
solution on `translatedCube d (n+1) z` to the carrier's own fields.  The datum
must vanish on the enlargement, which is what makes the local equation
homogeneous. -/
theorem wholeSpaceSolution_translatedCube_mass_contraction_of_local
    {a f : Vec d → ℝ} {t theta : ℝ} {n : ℤ} {z : Vec d}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) z, f x = 0)
    (hlocal : ∀ v : H1Function (translatedCube d (n + 1) z),
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
        (translatedCube d (n + 1) z) v (fun _ ↦ (0 : ℝ)) →
      (∫ x in translatedCube d n z, v.toFun x ^ 2 ∂volume) ≤
        theta * ∫ x in translatedCube d (n + 1) z, v.toFun x ^ 2 ∂volume) :
    (∫ x in translatedCube d n z, u.toFun x ^ 2 ∂volume) ≤
      theta * ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := by
  classical
  have hWdom : IsOpenBoundedConvexDomain (translatedCube d (n + 1) z) :=
    isOpenBoundedConvexDomain_translatedCube (n + 1) z
  have hWmeas : MeasurableSet (translatedCube d (n + 1) z) :=
    hWdom.isOpen.measurableSet
  have hQmeas : MeasurableSet (translatedCube d n z) :=
    (isOpenBoundedConvexDomain_translatedCube n z).isOpen.measurableSet
  have hQW : translatedCube d n z ⊆ translatedCube d (n + 1) z :=
    translatedCube_subset_succ d n z
  obtain ⟨v, hval, _hgrad, hsol⟩ :=
    u.locally_weak_solution (translatedCube d (n + 1) z) hWdom
  have hsol0 : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) z) v (fun _ ↦ (0 : ℝ)) := by
    intro phi
    refine (hsol phi).trans ?_
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    simp [hf0 x hx]
  have hbase := hlocal v hsol0
  have hQval : (∫ x in translatedCube d n z, v.toFun x ^ 2 ∂volume) =
      ∫ x in translatedCube d n z, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hQmeas fun x hx ↦ ?_
    rw [hval x (hQW hx)]
  have hWval : (∫ x in translatedCube d (n + 1) z, v.toFun x ^ 2 ∂volume) =
      ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    rw [hval x hx]
  rwa [hQval, hWval] at hbase

/-- **The coarse per-cell contraction for the whole-space carrier.**

§2 for the carrier's own fields.  The carrier promises a local `H¹` solution on
the contraction cube which agrees with it there, so the two mesoscopic legs may
be assumed for `u.toFun`, `u.grad` — the form in which the cover lemmas and the
per-cell analytic theorems are stated — and are transported to the local
solution by the congruences of §3b. -/
theorem wholeSpaceSolution_translatedCube_coarse_mass_contraction_of_cells
    {a f : Vec d → ℝ} {lam Lam t eta P R Sc Gam0 K : ℝ} {k n : ℤ} {c : Vec d}
    (hkn : k ≤ n - 3)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) c)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam0 : 0 < Gam0) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam0 * 27 ^ d + Sc)))
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) c, f x = 0)
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi)
    (hchiBox : tsupport chi ⊆
      {x : Vec d | ∀ i, |x i - c i| ≤ 3 / 4 * (3 : ℝ) ^ n})
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hchi_one : ∀ x ∈ translatedCube d n c, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hcrossInt : IntegrableOn (fun x => a x * chi x * u.toFun x *
      vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (n + 1) c) volume)
    (hpricecell : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) u.toFun u.grad chi t P R Sc)
    (henergycell : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) u.toFun u.grad
        t Gam0)
    (hsmall : 81 * (P * (Gam0 * 27 ^ d + Sc)) ^ 2 * R ^ 2 *
      (Gam0 * 27 ^ d + Sc) * t ≤ eta ^ 4) :
    (∫ x in translatedCube d n c, u.toFun x ^ 2 ∂volume) ≤
      eta * ∫ x in translatedCube d (n + 1) c, u.toFun x ^ 2 ∂volume := by
  classical
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hrho1 : (0 : ℝ) < 4 / 5 * (3 : ℝ) ^ n := by positivity
  have hslack := price_slack_bound (k := k) (n := n) hkn
  have hWdom : IsOpenBoundedConvexDomain (translatedCube d (n + 1) c) :=
    isOpenBoundedConvexDomain_translatedCube (n + 1) c
  have hWmeas : MeasurableSet (translatedCube d (n + 1) c) :=
    hWdom.isOpen.measurableSet
  have hQmeas : MeasurableSet (translatedCube d n c) :=
    (isOpenBoundedConvexDomain_translatedCube n c).isOpen.measurableSet
  obtain ⟨v, hval, hgrad, hsol⟩ :=
    u.locally_weak_solution (translatedCube d (n + 1) c) hWdom
  have hsol0 : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) c) v (fun _ ↦ (0 : ℝ)) := by
    intro phi
    refine (hsol phi).trans ?_
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    simp [hf0 x hx]
  -- the carrier's fields and the local solution's agree on the contraction cube
  have huv : ∀ x ∈ translatedCube d (n + 1) c, u.toFun x = v.toFun x :=
    fun x hx => (hval x hx).symm
  have hguv : u.grad =ᵐ[volume.restrict (translatedCube d (n + 1) c)] v.grad :=
    hgrad.symm
  -- the price cells and the mesoscopic cells sit inside the contraction cube
  have hpriceSub : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      openCubeSet (priceCell d k m) ⊆ translatedCube d (n + 1) c := by
    intro m hm
    refine (openCubeSet_priceCell_subset k m).trans ?_
    exact (cubeSet_priceCell_subset_ball hrho1 hslack hm).trans
      (ball_subset_translatedCube_succ d n c)
  have hmesoSub : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      mesoCell d k m ⊆ translatedCube d (n + 1) c :=
    fun m hm => mesoCell_subset_translatedCube hm
  -- transport the two legs and the integrabilities to the local solution
  have hpricecell' : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) v.toFun v.grad chi t P R Sc := by
    intro m hm
    exact mesoscopicCrossPriceEnergyOn_congr (measurableSet_openCubeSet _)
      (subset_refl _) (fun x hx => huv x (hpriceSub m hm hx))
      (ae_mono (Measure.restrict_mono (hpriceSub m hm) le_rfl) hguv)
      (hpricecell m hm)
  have henergycell' : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) v.toFun v.grad
        t Gam0 := by
    intro m hm
    exact coarseEnergyBoundOn_congr (measurableSet_mesoCell k m)
      (mesoCore_subset_mesoCell k m) (fun x hx => huv x (hmesoSub m hm hx))
      (ae_mono (Measure.restrict_mono (hmesoSub m hm) le_rfl) hguv)
      (henergycell m hm)
  have henergyInt : IntegrableOn (fun x => a x * vecNormSq (v.grad x))
      (translatedCube d (n + 1) c) volume := by
    refine (u.integrable_energy.restrict (s := translatedCube d (n + 1) c)).congr ?_
    filter_upwards [hguv] with x hx
    rw [hx]
  have hmassInt : IntegrableOn (fun x => v.toFun x ^ 2)
      (translatedCube d (n + 1) c) volume := by
    refine (u.memL2_toFun.integrable_sq.restrict
      (s := translatedCube d (n + 1) c)).congr ?_
    filter_upwards [(ae_restrict_iff' hWmeas).2 (Filter.Eventually.of_forall huv)]
      with x hx
    rw [hx]
  have hcrossInt' : IntegrableOn (fun x => a x * chi x * v.toFun x *
      vecDot (v.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (n + 1) c) volume := by
    refine hcrossInt.congr ?_
    filter_upwards [(ae_restrict_iff' hWmeas).2 (Filter.Eventually.of_forall huv),
      hguv] with x hx hgx
    rw [hx, hgx]
  have hres := massive_local_l2_translatedCube_coarse_contraction_of_cells hkn
    hEll haNonneg ht heta hP hGam0 hR hSc hbeta1 v hsol0 hchi hchiC hchiBox
    hchi_le hchi_one hK hcrossInt' henergyInt hmassInt hpricecell' henergycell'
    hsmall
  have hQval : (∫ x in translatedCube d n c, v.toFun x ^ 2 ∂volume) =
      ∫ x in translatedCube d n c, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hQmeas fun x hx ↦ ?_
    rw [hval x (translatedCube_subset_succ d n c hx)]
  have hWval : (∫ x in translatedCube d (n + 1) c, v.toFun x ^ 2 ∂volume) =
      ∫ x in translatedCube d (n + 1) c, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    rw [hval x hx]
  rwa [hQval, hWval] at hres



theorem wholeSpaceSolution_exterior_decay_of_coarse_stopping_cells
    [NeZero d] {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsourceNonempty : source.Nonempty) (x0 : Vec d) (R epsilon : ℝ) (k : ℕ)
    (hgood : ¬ RepairedStoppingShortCrossing source hsourceNonempty
      x0 R epsilon k)
    (hquiet : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
        ∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q), f x = 0)
    (hlocal : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
        ∀ v : H1Function (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q)),
          IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
            (translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q)) v (fun _ ↦ (0 : ℝ)) →
          (∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), v.toFun x ^ 2 ∂volume) ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), v.toFun x ^ 2 ∂volume) :
    ∫ x in (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ, u.toFun x ^ 2 ∂volume ≤
      ((stoppingGraphLevelCells repairedStoppingGraph source
          hsourceNonempty 0).card : ℝ) *
        (∫ x, f x ^ 2 ∂volume) * (1 - (1 / 2 : ℝ))⁻¹ *
        Real.exp (Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k)) := by
  refine wholeSpaceSolution_exterior_decay_of_repaired_stopping_cells_of_l2
    u hL2 hinitial hrepair source hsourceNonempty x0 R epsilon k hgood ?_
  intro q hq
  exact wholeSpaceSolution_translatedCube_mass_contraction_of_local u
    (hquiet q hq) (hlocal q hq)

/-- **The exterior row from the mesoscopic per-cell data, end to end.**

The composition of §2/§4 with the assembly: for every stopping cell
at positive graph distance from the source the two mesoscopic legs are assumed
in their per-cell form — the price on the triadic price cells of scale `k q` and
the coarse energy bound on the mesoscopic cells of the same scale — together
with the cutoff, the ellipticity of the coefficient on the enlargement, the
integrability of the cross term, and the numerical smallness at
`eta = repairedStoppingContractionFactor d`; the conclusion is the exterior
decay of the `WholeSpaceRows` exterior row.

Nothing here is scale-uniform: `k`, the cutoff, the constants and the
ellipticities are all allowed to depend on the cell, which is what the stopping
partition needs (the mesoscopic scale is chosen cell by cell from the balance
`side² ≍ λ t`). -/
theorem wholeSpaceSolution_exterior_decay_of_coarse_mesoscopic_cells
    [NeZero d] {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {a f : Vec d → ℝ} {t : ℝ} (ht : 0 < t)
    (haNonneg : ∀ x, 0 ≤ a x)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsourceNonempty : source.Nonempty) (x0 : Vec d) (R0 epsilon : ℝ) (k0 : ℕ)
    (hgood : ¬ RepairedStoppingShortCrossing source hsourceNonempty
      x0 R0 epsilon k0)
    (scaleOf : RefinedStoppingCell failure omega base → ℤ)
    (lam Lam P R Sc Gam0 K : RefinedStoppingCell failure omega base → ℝ)
    (chi : RefinedStoppingCell failure omega base → Vec d → ℝ)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
      scaleOf q ≤ refinedStoppingScale q - 3 ∧
      IsEllipticFieldOn (lam q) (Lam q)
        (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q)) (scalarCoeffField a) ∧
      0 < P q ∧ 0 < Gam0 q ∧ 0 ≤ R q ∧ 0 ≤ Sc q ∧
      repairedStoppingContractionFactor d ≤
        3 * (P q * (Gam0 q * 27 ^ d + Sc q)) ∧
      (∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), f x = 0) ∧
      ContDiff ℝ (⊤ : ℕ∞) (chi q) ∧ HasCompactSupport (chi q) ∧
      tsupport (chi q) ⊆ {x : Vec d | ∀ i,
        |x i - refinedStoppingCenter q i| ≤
          3 / 4 * (3 : ℝ) ^ refinedStoppingScale q} ∧
      (∀ x, |chi q x| ≤ 1) ∧
      (∀ x ∈ translatedCube d (refinedStoppingScale q)
        (refinedStoppingCenter q), chi q x = 1) ∧
      (∀ x, vecNormSq (fun i ↦ (fderiv ℝ (chi q) x) (basisVec i)) ≤ K q) ∧
      IntegrableOn (fun x => a x * chi q x * u.toFun x *
        vecDot (u.grad x) (fun i ↦ (fderiv ℝ (chi q) x) (basisVec i)))
        (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q)) volume ∧
      (∀ m ∈ priceIndexBox d (scaleOf q) (refinedStoppingCenter q)
          (3 / 4 * (3 : ℝ) ^ refinedStoppingScale q),
        MesoscopicCrossPriceEnergyOn a
          (openCubeSet (priceCell d (scaleOf q) m))
          (openCubeSet (priceCell d (scaleOf q) m)) u.toFun u.grad (chi q)
          t (P q) (R q) (Sc q)) ∧
      (∀ m ∈ mesoIndexBox d (scaleOf q) (refinedStoppingScale q + 1)
          (refinedStoppingCenter q),
        CoarseEnergyBoundOn a (mesoCell d (scaleOf q) m)
          (mesoCore d (scaleOf q) m) u.toFun u.grad t (Gam0 q)) ∧
      81 * (P q * (Gam0 q * 27 ^ d + Sc q)) ^ 2 * R q ^ 2 *
        (Gam0 q * 27 ^ d + Sc q) * t ≤
          repairedStoppingContractionFactor d ^ 4) :
    ∫ x in (Metric.ball x0 ((3 : ℝ) ^ k0 * R0))ᶜ, u.toFun x ^ 2 ∂volume ≤
      ((stoppingGraphLevelCells repairedStoppingGraph source
          hsourceNonempty 0).card : ℝ) *
        (∫ x, f x ^ 2 ∂volume) * (1 - (1 / 2 : ℝ))⁻¹ *
        Real.exp (Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k0)) := by
  refine wholeSpaceSolution_exterior_decay_of_repaired_stopping_cells_of_l2
    u hL2 hinitial hrepair source hsourceNonempty x0 R0 epsilon k0 hgood ?_
  intro q hq
  obtain ⟨hkn, hEll, hP, hGam0, hR, hSc, hbeta1, hf0, hchi, hchiC, hchiBox,
    hchi_le, hchi_one, hK, hcrossInt, hpricecell, henergycell, hsmall⟩ :=
    hcell q hq
  exact wholeSpaceSolution_translatedCube_coarse_mass_contraction_of_cells
    hkn hEll haNonneg ht repairedStoppingContractionFactor_pos hP hGam0 hR hSc
    hbeta1 u hf0 hchi hchiC hchiBox hchi_le hchi_one hK hcrossInt hpricecell
    henergycell hsmall

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
