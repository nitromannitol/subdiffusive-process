import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.EventIndependence
import SubdiffusiveProcess.Frozen.Assumptions.GMCModel
import Mathlib.Probability.Independence.ZeroOne




set_option autoImplicit false

open MeasureTheory ProbabilityTheory MeasurableSpace Set Homogenization MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-! ## Grouping an independent family into disjoint blocks -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- Independence is inherited by coarser σ-algebras. -/
theorem iIndep_mono {ι : Type*} {m m' : ι → MeasurableSpace Ω}
    (h : ∀ i, m' i ≤ m i) (hm : iIndep m μ) : iIndep m' μ := by
  rw [iIndep_iff]
  intro S f hf
  exact (iIndep_iff m μ).mp hm S fun i hi => h i _ (hf i hi)

/-- **Block grouping.**  If `c` is an independent family of sub-σ-algebras and
`kappa` picks pairwise disjoint blocks of indices, then the σ-algebras generated
by the blocks are independent.  This is the step `IndependentEventScales` needs:
the layer-zero event sees the shells up to `n`, every later layer sees one
shell, and the blocks are pairwise disjoint. -/
theorem iIndep_biSup_of_pairwise_disjoint {ι : Type*} [DecidableEq ι] {κ : Type*}
    {c : κ → MeasurableSpace Ω} (hle : ∀ k, c k ≤ mΩ) (hc : iIndep c μ)
    (block : ι → Set κ) (hdisj : Pairwise (Function.onFun Disjoint block)) :
    iIndep (fun j => ⨆ k ∈ block j, c k) μ := by
  rw [iIndep_iff]
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro f _
      haveI := hc.isProbabilityMeasure
      simp
  | insert j S hj ih =>
      intro f hf
      have hmono : ∀ i ∈ S, (⨆ k ∈ block i, c k) ≤ ⨆ k ∈ (block j)ᶜ, c k := by
        intro i hi
        refine iSup₂_le fun k hk => ?_
        refine le_iSup₂_of_le k ?_ le_rfl
        have hne : i ≠ j := fun h => hj (h ▸ hi)
        have := hdisj hne
        exact Set.disjoint_left.mp this hk
      have h1 : MeasurableSet[⨆ k ∈ block j, c k] (f j) :=
        hf j (Finset.mem_insert_self j S)
      have h2 : MeasurableSet[⨆ k ∈ (block j)ᶜ, c k] (⋂ i ∈ S, f i) := by
        refine Finset.measurableSet_biInter S fun i hi => ?_
        exact hmono i hi _ (hf i (Finset.mem_insert_of_mem hi))
      have hindep : Indep (⨆ k ∈ block j, c k) (⨆ k ∈ (block j)ᶜ, c k) μ :=
        indep_biSup_compl hle hc (block j)
      rw [Finset.set_biInter_insert, Finset.prod_insert hj,
        (Indep_iff _ _ μ).mp hindep _ _ h1 h2,
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **Clause 7d.**  Scale independence of the event field, from the locality of
each layer in a block of shells and the independence of the shells
(`SubdiffusiveProcess.Frozen.Assumptions.ShellLawPrefix.independent`). -/
theorem independentEventScales_of_blocks {d : ℕ}
    {mu : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)}
    (hind : iIndepFun
      (fun k => fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k) mu)
    (block : ℕ → Set ℕ) (hdisj : Pairwise (Function.onFun Disjoint block))
    {E : ℕ → Lattice d → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)}
    (hE : ∀ j, eventFieldSigma (E j) Set.univ ≤
      ⨆ k ∈ block j, MeasurableSpace.comap
        (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k) inferInstance) :
    IndependentEventScales mu E := by
  have hle : ∀ k : ℕ, MeasurableSpace.comap
      (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k) inferInstance ≤
      (inferInstance : MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) :=
    fun k => (measurable_pi_apply k).comap_le
  exact iIndep_mono hE
    (iIndep_biSup_of_pairwise_disjoint hle ((iIndepFun_iff_iIndep _ _ _).mp hind) block hdisj)

/-! ## Locality of the layer events -/

/-- The carrier local σ-algebra is monotone in the observation set. -/
theorem localSigmaR_mono {d : ℕ} {U V : Set (Vec d)} (h : U ⊆ V) :
    LocalSigmaR U ≤ LocalSigmaR V := by
  refine MeasurableSpace.generateFrom_mono ?_
  rintro s ⟨i, j, phi, hprobe, hsupp, t, ht, rfl⟩
  exact ⟨i, j, phi, hprobe, hsupp.trans h, t, ht, rfl⟩

theorem potentialLocalSigma_mono {d : ℕ} {U V : Set (Vec d)} (h : U ⊆ V) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U ≤
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V :=
  MeasurableSpace.comap_mono (localSigmaR_mono h)

theorem shellLocalSigma_mono {d : ℕ} (k : ℕ) {U V : Set (Vec d)} (h : U ⊆ V) :
    shellLocalSigma (d := d) k U ≤ shellLocalSigma k V :=
  MeasurableSpace.comap_mono (potentialLocalSigma_mono h)

/-- **The domination clause 7e reduces to.**  If every layer-`j` event at a site
is measurable for shell `n + j` on that site's dependence box, then the whole
event field over a set `S` of sites is measurable for shell `n + j` on the union
of those boxes; the finite-range clause then follows from
`SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1.range_dependence` at that shell. -/
theorem eventFieldSigma_le_shellLocalSigma {d k : ℕ}
    {E : Lattice d → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)}
    {box : Lattice d → Set (Vec d)}
    (hE : ∀ z, MeasurableSet[shellLocalSigma k (box z)] (E z)) (S : Set (Lattice d)) :
    eventFieldSigma E S ≤ shellLocalSigma k (⋃ z ∈ S, box z) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro A ⟨z, hz, rfl⟩
  exact shellLocalSigma_mono k (Set.subset_biUnion_of_mem hz) _ (hE z)




/-- **Clause 7f.**  If the construction of the event field is equivariant under
a family of law-preserving maps indexed by the lattice, then the joint law of
all event indicators is translation invariant. -/
theorem translationInvariantEventLaw_of_covariant {d : ℕ}
    {E : ℕ → Lattice d → Set Ω} (hmeas : ∀ j z, MeasurableSet (E j z))
    (T : Lattice d → Ω → Ω) (hT : ∀ a, Measurable (T a))
    (hTmp : ∀ a, Measure.map (T a) μ = μ)
    (hcov : ∀ (j : ℕ) (z a : Lattice d), E j (z + a) = (T a) ⁻¹' (E j z)) :
    TranslationInvariantEventLaw μ E := by
  refine ⟨hmeas, fun a => ?_⟩
  have hfun : translateEventFieldConfiguration E a = eventFieldConfiguration E ∘ (T a) := by
    funext omega p
    have hset := hcov p.1 p.2 a
    simp only [translateEventFieldConfiguration, eventFieldConfiguration, Function.comp_apply,
      hset]
    by_cases hmem : omega ∈ (T a) ⁻¹' (E p.1 p.2)
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_preimage.mp hmem)]
    · rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (fun h => hmem (Set.mem_preimage.mpr h))]
  rw [hfun, ← Measure.map_map (measurable_eventFieldConfiguration hmeas) (hT a), hTmp a]

/-! ## The analytic package -/



theorem localHarmonicOscillation_of_depthDecay {d : ℕ} (a : Vec d → ℝ)
    (eps0 C cdec : ℝ) (j2 : ℕ) (Pfam : Set (Cube d × Cube d))
    (hdecay : ∀ p ∈ Pfam, ∀ h : Vec d → ℝ, WeakHarmonic a (cubeSet p.2) h →
      oscillation (cubeSet p.1) h ≤
        ENNReal.ofReal (C * (3 : ℝ) ^ (-cdec * (j2 : ℝ))) * oscillation (cubeSet p.2) h)
    (hchoice : C * (3 : ℝ) ^ (-cdec * (j2 : ℝ)) ≤ eps0) :
    LocalHarmonicOscillation a eps0 Pfam := by
  refine ⟨fun p hp h hharm => ?_⟩
  refine le_trans (hdecay p hp h hharm) ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hchoice) le_rfl



theorem goodCubeAnalyticPackage_of_supportInputs {d : ℕ} (a : Vec d → ℝ)
    (law : Kernel (Vec d) (Path d)) (clock : ℝ → ℝ) (p0 cc CC eps0 : ℝ)
    (U : Cube d) (Pfam : Set (Cube d × Cube d)) (Qfam Afam : Set (Cube d))
    (hexit_lower : ∀ x ∈ middleQuarter U,
      ENNReal.ofReal (cc * clock U.2) ≤ meanExit law (cubeSet U) x)
    (hexit_upper : ∀ x ∈ cubeSet U,
      meanExit law (cubeSet U) x ≤ ENNReal.ofReal (CC * clock U.2))
    (hdescendant : ∀ B' ∈ Qfam, ∀ B ∈ Qfam, CompactlyInside B' B →
      (∀ x ∈ cubeSet B', ENNReal.ofReal (cc * clock B.2) ≤ meanExit law (cubeSet B) x) ∧
      (∀ x ∈ cubeSet B, meanExit law (cubeSet B) x ≤ ENNReal.ofReal (CC * clock B.2)))
    (hmass_quarter :
      ENNReal.ofReal cc * weightedMeasure a (cubeSet U) ≤ weightedMeasure a (middleQuarter U))
    (hmass_descendant : ∀ B' ∈ Qfam, ∀ B ∈ Qfam, CompactlyInside B' B →
      ENNReal.ofReal cc * weightedMeasure a (cubeSet B) ≤ weightedMeasure a (cubeSet B'))
    (hmass_overlap : ∀ A ∈ Afam,
      ENNReal.ofReal cc * weightedMeasure a (cubeSet U) ≤ weightedMeasure a (cubeSet A))
    (hsobolev : ∀ Q ∈ Qfam, ∀ f : H10Function (cubeSet Q),
      lpSq a (cubeSet Q) p0 f.toH1Function.toFun ≤
        ENNReal.ofReal CC * weightedMeasure a (cubeSet Q) ^ (-(1 - 2 / p0)) *
          ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function))
    (hoscillation : LocalHarmonicOscillation a eps0 Pfam) :
    LocalTorsionEstimates a law clock p0 cc CC U Qfam Afam ∧
      LocalHarmonicOscillation a eps0 Pfam :=
  ⟨⟨hexit_lower, hexit_upper, hdescendant, hmass_quarter, hmass_descendant,
      hmass_overlap, hsobolev⟩, hoscillation⟩

/-! ## The deterministic half of the finite-range clause -/

theorem coord_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  have h : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  calc |v i| = Real.sqrt (v i * v i) := (Real.sqrt_mul_self_eq_abs (v i)).symm
    _ ≤ Real.sqrt (∑ j, v j * v j) := Real.sqrt_le_sqrt h
    _ = euclideanNorm v := rfl



theorem euclidean_separation_of_latticeDist {d n j Cdep : ℕ} {C : ℝ}
    (hCdep : C + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ))
    {z z' : Lattice d} (hsep : Cdep * 3 ^ j < latticeDist z z')
    {p q : Vec d}
    (hp : p ∈ SubdiffusiveProcess.Section9.centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j)))
    (hq : q ∈ SubdiffusiveProcess.Section9.centeredAxisCube (goodCubeCentre n z') (C * (3 : ℝ) ^ (n + j))) :
    Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + j) ≤ euclideanNorm (p - q) := by
  obtain ⟨i, -, hi⟩ := Finset.lt_sup_iff.mp hsep
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hpow : (3 : ℝ) ^ (n + j) = (3 : ℝ) ^ n * (3 : ℝ) ^ j := pow_add _ _ _
  -- the coordinate gap of the two centres
  have hgap : ((Cdep : ℝ) * (3 : ℝ) ^ j) < |(z i : ℝ) - (z' i : ℝ)| := by
    have hnat : (Cdep * 3 ^ j : ℕ) < (z i - z' i).natAbs := hi
    have hcast : ((Cdep * 3 ^ j : ℕ) : ℝ) < (((z i - z' i).natAbs : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have habs : (((z i - z' i).natAbs : ℕ) : ℝ) = |(z i : ℝ) - (z' i : ℝ)| := by
      rw [Nat.cast_natAbs]
      push_cast
      ring_nf
    rw [habs] at hcast
    calc ((Cdep : ℝ) * (3 : ℝ) ^ j) = ((Cdep * 3 ^ j : ℕ) : ℝ) := by push_cast; ring
      _ < _ := hcast
  -- the two points stay within half a side of their centres
  have hpi : |p i - (z i : ℝ) * (3 : ℝ) ^ n| < C * (3 : ℝ) ^ (n + j) / 2 :=
    (mem_centeredAxisCube.mp hp) i
  have hqi : |q i - (z' i : ℝ) * (3 : ℝ) ^ n| < C * (3 : ℝ) ^ (n + j) / 2 :=
    (mem_centeredAxisCube.mp hq) i
  have hcoord : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + j) ≤ |p i - q i| := by
    have hlow : |(z i : ℝ) * (3 : ℝ) ^ n - (z' i : ℝ) * (3 : ℝ) ^ n|
        ≤ |p i - q i| + (C * (3 : ℝ) ^ (n + j) / 2 + C * (3 : ℝ) ^ (n + j) / 2) := by
      have hsplit : (z i : ℝ) * (3 : ℝ) ^ n - (z' i : ℝ) * (3 : ℝ) ^ n
          = (p i - q i) + (((z i : ℝ) * (3 : ℝ) ^ n - p i) + (q i - (z' i : ℝ) * (3 : ℝ) ^ n)) := by
        ring
      have h1 : |((z i : ℝ) * (3 : ℝ) ^ n - p i)| < C * (3 : ℝ) ^ (n + j) / 2 := by
        rwa [abs_sub_comm]
      have h2 : |(q i - (z' i : ℝ) * (3 : ℝ) ^ n)| < C * (3 : ℝ) ^ (n + j) / 2 := hqi
      calc |(z i : ℝ) * (3 : ℝ) ^ n - (z' i : ℝ) * (3 : ℝ) ^ n|
          = |(p i - q i) + (((z i : ℝ) * (3 : ℝ) ^ n - p i)
              + (q i - (z' i : ℝ) * (3 : ℝ) ^ n))| := by rw [hsplit]
        _ ≤ |p i - q i| + |((z i : ℝ) * (3 : ℝ) ^ n - p i)
              + (q i - (z' i : ℝ) * (3 : ℝ) ^ n)| := abs_add_le _ _
        _ ≤ |p i - q i| + (|((z i : ℝ) * (3 : ℝ) ^ n - p i)|
              + |(q i - (z' i : ℝ) * (3 : ℝ) ^ n)|) := by
            have := abs_add_le ((z i : ℝ) * (3 : ℝ) ^ n - p i)
              (q i - (z' i : ℝ) * (3 : ℝ) ^ n)
            linarith
        _ ≤ |p i - q i| + (C * (3 : ℝ) ^ (n + j) / 2 + C * (3 : ℝ) ^ (n + j) / 2) := by
            linarith
    have hfac : |(z i : ℝ) * (3 : ℝ) ^ n - (z' i : ℝ) * (3 : ℝ) ^ n|
        = |(z i : ℝ) - (z' i : ℝ)| * (3 : ℝ) ^ n := by
      rw [← sub_mul, abs_mul, abs_of_pos h3n]
    rw [hfac] at hlow
    have hbig : (Cdep : ℝ) * (3 : ℝ) ^ j * (3 : ℝ) ^ n
        < |(z i : ℝ) - (z' i : ℝ)| * (3 : ℝ) ^ n :=
      by exact mul_lt_mul_of_pos_right hgap h3n
    have hCdep' : (C + Real.sqrt (d : ℝ)) * (3 : ℝ) ^ j * (3 : ℝ) ^ n
        ≤ (Cdep : ℝ) * (3 : ℝ) ^ j * (3 : ℝ) ^ n := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCdep (le_of_lt h3j)) (le_of_lt h3n)
      exact this
    rw [hpow]
    rw [hpow] at hlow
    linarith [hlow, hbig, hCdep']
  have hcoordq : |(p - q) i| = |p i - q i| := by simp [Pi.sub_apply]
  calc Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + j) ≤ |p i - q i| := hcoord
    _ = |(p - q) i| := hcoordq.symm
    _ ≤ euclideanNorm (p - q) := coord_le_euclideanNorm _ _

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
