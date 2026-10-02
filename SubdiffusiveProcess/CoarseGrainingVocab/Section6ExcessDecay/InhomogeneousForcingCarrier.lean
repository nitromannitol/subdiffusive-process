import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.FractionalHolderBridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum

/-!
# From a Hölder forcing field to the inhomogeneous `H^s` carrier

The v5 harmonic-approximation anchor (D-048) and the v3 excess-decay anchor
(D-057) hypothesise the *inhomogeneous* fractional carrier

```text
  ∃ sOrder : FractionalOrder, sOrder.1 = s ∧
    MemCubeEuclideanFullWsp (originCube d m) sOrder FiniteLpExponent.two g
```

for the forcing field `g`, in place of the version-4 homogeneous
`MemFractionalOn (cube d m) s g`.  The Hölder ladder supplies its forcing field
as `MemHolder (cube d m) (1/2) g`, and version 4 was consumed from that datum by
`memFractionalOn_cube_of_memHolder`.  This file upgrades that step: a
`C^{0,1/2}` field on a cube lies in the full inhomogeneous carrier at every
order `s ∈ (0, 1/4]`.

Two halves are needed:

* the `L²` half `MemLp (fun x => HilbertVec.ofVec (g x)) 2
  (normalizedCubeMeasure (originCube d m))` — a Hölder field on a *bounded*
  window is continuous and bounded there, hence square-integrable for the
  finite normalized cube measure.  This half is exactly what the homogeneous
  seminorm cannot see, and it is the whole content of the D-048 delta;
* the Gagliardo half `MemCubeEuclideanWsp`, which is the version-4 datum
  transported through the normalization identity
  `Section6HarmonicApproximation.fractionalSeminormOn_openCubeSet_eq_sqrt_mul_cubeEuclideanWspESeminorm`
  and CoarseGraining's `memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Continuity and boundedness of a `C^{0,1/2}` field on a window -/

/-- A field with a Hölder-`1/2` seminorm bound on `W` is continuous on `W`,
after promotion to the Euclidean Hilbert carrier. -/
theorem continuousOn_ofVec_of_holderSeminormBoundOn {W : Set (Vec d)}
    {f : Vec d → Vec d} {K : ℝ} (hK : 0 ≤ K)
    (hf : HolderSeminormBoundOn W (1 / 2 : ℝ) K f) :
    ContinuousOn (fun x => HilbertVec.ofVec (f x)) W := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  refine ⟨(ε / (K + 1)) ^ 2 / ((d : ℝ) + 1), by positivity, ?_⟩
  intro a ha hab
  have hKb : euclideanNorm (f a - f b) ≤ K * euclideanNorm (a - b) ^ (1 / 2 : ℝ) :=
    hf a ha b hb
  have hcmp : euclideanNorm (a - b) ≤ (d : ℝ) * dist a b := by
    have h := HilbertVec.norm_ofVec_le_mul_norm (a - b)
    rw [euclideanNorm_eq_norm_ofVec]
    simpa [dist_eq_norm] using h
  have hdab : (d : ℝ) * dist a b ≤ (ε / (K + 1)) ^ 2 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hab' : dist a b ≤ (ε / (K + 1)) ^ 2 / ((d : ℝ) + 1) := le_of_lt hab
    have h1 : (d : ℝ) * dist a b ≤ (d : ℝ) * ((ε / (K + 1)) ^ 2 / ((d : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hab' hd0
    have h2 : (d : ℝ) * ((ε / (K + 1)) ^ 2 / ((d : ℝ) + 1)) ≤ (ε / (K + 1)) ^ 2 := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) + 1)]
      nlinarith [sq_nonneg (ε / (K + 1)), hd0]
    linarith only [h1, h2]
  have hpow : euclideanNorm (a - b) ^ (1 / 2 : ℝ) ≤ ε / (K + 1) := by
    have hchain : euclideanNorm (a - b) ≤ (ε / (K + 1)) ^ 2 :=
      le_trans hcmp hdab
    have hmono : euclideanNorm (a - b) ^ (1 / 2 : ℝ)
        ≤ ((ε / (K + 1)) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (euclideanNorm_nonneg _) hchain (by norm_num)
    have hsq : ((ε / (K + 1)) ^ 2 : ℝ) ^ (1 / 2 : ℝ) = ε / (K + 1) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    rwa [hsq] at hmono
  have hfinal : euclideanNorm (f a - f b) < ε := by
    have h1 : K * euclideanNorm (a - b) ^ (1 / 2 : ℝ) ≤ K * (ε / (K + 1)) :=
      mul_le_mul_of_nonneg_left hpow hK
    have h2 : K * (ε / (K + 1)) < ε := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K + 1)]
      nlinarith only [hε, hK]
    linarith only [hKb, h1, h2]
  have hsub : HilbertVec.ofVec (f a - f b)
      = HilbertVec.ofVec (f a) - HilbertVec.ofVec (f b) := by
    simp
  have hdist : dist (HilbertVec.ofVec (f a)) (HilbertVec.ofVec (f b))
      = euclideanNorm (f a - f b) := by
    rw [dist_eq_norm, euclideanNorm_eq_norm_ofVec, hsub]
  rw [hdist]
  exact hfinal

/-- A field with a Hölder-`1/2` seminorm bound on a window contained in a ball
about one of its own points is bounded on that window. -/
theorem norm_ofVec_le_of_holderSeminormBoundOn {W : Set (Vec d)}
    {f : Vec d → Vec d} {K R : ℝ} {p : Vec d} (hK : 0 ≤ K)
    (hp : p ∈ W) (hball : W ⊆ Metric.ball p R)
    (hf : HolderSeminormBoundOn W (1 / 2 : ℝ) K f) :
    ∀ x ∈ W, ‖HilbertVec.ofVec (f x)‖
      ≤ euclideanNorm (f p) + K * ((d : ℝ) * R) ^ (1 / 2 : ℝ) := by
  intro x hx
  have hKb : euclideanNorm (f x - f p) ≤ K * euclideanNorm (x - p) ^ (1 / 2 : ℝ) :=
    hf x hx p hp
  have hcmp : euclideanNorm (x - p) ≤ (d : ℝ) * R := by
    have h := HilbertVec.norm_ofVec_le_mul_norm (x - p)
    have hxp : ‖x - p‖ ≤ R := le_of_lt (by simpa [dist_eq_norm] using hball hx)
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    rw [euclideanNorm_eq_norm_ofVec]
    exact le_trans h (mul_le_mul_of_nonneg_left hxp hd0)
  have hpow : euclideanNorm (x - p) ^ (1 / 2 : ℝ) ≤ ((d : ℝ) * R) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (euclideanNorm_nonneg _) hcmp (by norm_num)
  have hsub : HilbertVec.ofVec (f x - f p)
      = HilbertVec.ofVec (f x) - HilbertVec.ofVec (f p) := by
    simp
  have htri : euclideanNorm (f x) ≤ euclideanNorm (f p) + euclideanNorm (f x - f p) := by
    rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
      euclideanNorm_eq_norm_ofVec, hsub]
    have hrw : HilbertVec.ofVec (f x)
        = (HilbertVec.ofVec (f x) - HilbertVec.ofVec (f p)) + HilbertVec.ofVec (f p) := by
      abel
    calc ‖HilbertVec.ofVec (f x)‖
        = ‖(HilbertVec.ofVec (f x) - HilbertVec.ofVec (f p)) + HilbertVec.ofVec (f p)‖ := by
          rw [← hrw]
      _ ≤ ‖HilbertVec.ofVec (f x) - HilbertVec.ofVec (f p)‖ + ‖HilbertVec.ofVec (f p)‖ :=
          norm_add_le _ _
      _ = ‖HilbertVec.ofVec (f p)‖ + ‖HilbertVec.ofVec (f x) - HilbertVec.ofVec (f p)‖ := by
          ring
  rw [← euclideanNorm_eq_norm_ofVec]
  have h1 : K * euclideanNorm (x - p) ^ (1 / 2 : ℝ) ≤ K * ((d : ℝ) * R) ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hpow hK
  linarith only [htri, hKb, h1]

/-! ### The `L²` half on a cube -/

/-- A `C^{0,1/2}` field on the cube `□_m` is square-integrable for the
normalized cube measure: the `L²` half of the inhomogeneous carrier. -/
theorem memLp_two_normalizedCubeMeasure_of_memHolder {m : ℤ} {f : Vec d → Vec d}
    (hf : MemHolder (cube d m) (1 / 2 : ℝ) f) :
    MemLp (fun x => HilbertVec.ofVec (f x)) 2
      (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨K, hK, hfK⟩ := hf
  haveI : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top (originCube d m)
  have hmeas : MeasurableSet (cube d m) :=
    (isOpenBoundedConvexDomain_cube d m).isOpen.measurableSet
  have hcont : ContinuousOn (fun x => HilbertVec.ofVec (f x)) (cube d m) :=
    continuousOn_ofVec_of_holderSeminormBoundOn hK hfK
  have hae : AEStronglyMeasurable (fun x => HilbertVec.ofVec (f x))
      (volume.restrict (openCubeSet (originCube d m))) :=
    hcont.aestronglyMeasurable hmeas
  have hbdd : ∀ x ∈ cube d m, ‖HilbertVec.ofVec (f x)‖
      ≤ euclideanNorm (f 0) + K * ((d : ℝ) * (3 : ℝ) ^ m) ^ (1 / 2 : ℝ) :=
    norm_ofVec_le_of_holderSeminormBoundOn hK
      (zero_mem_cube d m) (fun q hq => cube_subset_ball (zero_mem_cube d m) hq) hfK
  have hbase : MemLp (fun x => HilbertVec.ofVec (f x)) 2
      (volume.restrict (openCubeSet (originCube d m))) := by
    refine MemLp.of_bound hae (euclideanNorm (f 0) + K * ((d : ℝ) * (3 : ℝ) ^ m) ^ (1 / 2 : ℝ)) ?_
    refine (ae_restrict_iff' hmeas).2 ?_
    filter_upwards with x hx using hbdd x hx
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d m)]
  exact hbase.smul_measure ENNReal.ofReal_ne_top

/-! ### The full inhomogeneous carrier -/

/-- **The D-057 upgrade of `memFractionalOn_cube_of_memHolder`.**

A `C^{0,1/2}` field on `□_m` lies in the *inhomogeneous* Euclidean `W^{s,2}`
carrier of Chapter 3 at every order `s ∈ (0,1/4]` — the hypothesis shape the v5
harmonic anchor (D-048) and the v3 excess-decay anchor (D-057) take for the
forcing field. -/
theorem memCubeEuclideanFullWsp_cube_of_memHolder {m : ℤ} {f : Vec d → Vec d}
    (hd : 1 ≤ d) (sOrder : FractionalOrder) (hs : sOrder.1 ≤ 1 / 4)
    (hf : MemHolder (cube d m) (1 / 2 : ℝ) f) :
    Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d m) sOrder
      FiniteLpExponent.two f := by
  have hLp : MemLp (fun x => HilbertVec.ofVec (f x)) 2
      (normalizedCubeMeasure (originCube d m)) :=
    memLp_two_normalizedCubeMeasure_of_memHolder hf
  have hLp' : MemLp (fun x => HilbertVec.ofVec (f x)) FiniteLpExponent.two.exponent
      (normalizedCubeMeasure (originCube d m)) := hLp
  have hfrac : MemFractionalOn (cube d m) sOrder.1 f :=
    memFractionalOn_cube_of_memHolder hd sOrder.2.1 hs hf
  have hsemi : cubeEuclideanWspESeminorm (originCube d m) sOrder
      FiniteLpExponent.two f < ∞ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    apply hfrac
    have heq :=
      fractionalSeminormOn_openCubeSet_eq_sqrt_mul_cubeEuclideanWspESeminorm
        (originCube d m) sOrder f
    have hne : (ENNReal.ofReal sOrder.1) ^ (1 / 2 : ℝ) ≠ 0 :=
      ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr sOrder.2.1) ENNReal.ofReal_ne_top)
    have hcube : cube d m = openCubeSet (originCube d m) := rfl
    rw [hcube, heq, hcon, ENNReal.mul_top hne]
  exact ⟨hLp', memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top hLp' hsemi⟩

/-- The exact existential shape the v5/v3 anchors take for the forcing field,
produced from the Hölder datum the Hölder ladder carries. -/
theorem exists_fractionalOrder_memCubeEuclideanFullWsp_of_memHolder {m : ℤ}
    {f : Vec d → Vec d} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hs1 : s ≤ 1 / 4)
    (hf : MemHolder (cube d m) (1 / 2 : ℝ) f) :
    ∃ sOrder : FractionalOrder, sOrder.1 = s ∧
      Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d m) sOrder
        FiniteLpExponent.two f :=
  ⟨⟨s, hs0, by linarith⟩, rfl,
    memCubeEuclideanFullWsp_cube_of_memHolder hd ⟨s, hs0, by linarith⟩ hs1 hf⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
