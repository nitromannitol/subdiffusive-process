import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarExterior
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimar




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## Elementary conversions -/

/-- A site of the unit-radius-zero ball is the centre. -/
theorem eq_of_inLatticeBallReal_zero {z v : Lattice d}
    (h : InLatticeBallReal z v (0 : ℝ)) : v = z := by
  funext i
  have hi := h i
  have h0 : (|v i - z i| : ℤ) ≤ 0 := by exact_mod_cast hi
  have hnn := abs_nonneg (v i - z i : ℤ)
  have hz : (|v i - z i| : ℤ) = 0 := by omega
  have : v i - z i = 0 := abs_eq_zero.mp hz
  omega

/-- A lattice-distance bound gives membership in the real-radius ball. -/
theorem inLatticeBallReal_of_latticeDist_le {z v : Lattice d} {n : ℕ} {R : ℝ}
    (h : latticeDist z v ≤ n) (hR : (n : ℝ) ≤ R) : InLatticeBallReal z v R := by
  intro i
  have h1 : (z i - v i).natAbs ≤ n := (coord_le_latticeDist z v i).trans h
  have h2 : (v i - z i).natAbs ≤ n := by omega
  have h3 : (|v i - z i| : ℤ) = ((v i - z i).natAbs : ℤ) := Int.abs_eq_natAbs _
  rw [h3]
  have h4 : (((v i - z i).natAbs : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
  linarith

/-- Membership in the real-radius ball of integer radius gives a lattice-distance bound. -/
theorem latticeDist_le_of_inLatticeBallReal_natRadius {z v : Lattice d} {n : ℕ}
    (h : InLatticeBallReal z v (n : ℝ)) : latticeDist z v ≤ n := by
  refine latticeDist_le_iff.mpr fun i => ?_
  have hi := h i
  have h1 : (|v i - z i| : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi
  rw [Int.abs_eq_natAbs] at h1
  have h2 : (v i - z i).natAbs ≤ n := by exact_mod_cast h1
  omega

/-- A diameter bound in the manuscript's normalization is a lattice-distance bound. -/
theorem latticeDist_le_div_of_hasLatticeDiameterAtMost {S : Set (Lattice d)} {L : ℕ}
    (h : HasLatticeDiameterAtMost S ((L : ℝ) / 100)) {v w : Lattice d}
    (hv : v ∈ S) (hw : w ∈ S) : latticeDist v w ≤ L / 100 := by
  refine latticeDist_le_iff.mpr fun i => ?_
  have hi := h v hv w hw i
  have hz : (100 : ℝ) * ((|v i - w i| : ℤ) : ℝ) ≤ (L : ℝ) := by linarith
  have hz' : (100 : ℤ) * (|v i - w i| : ℤ) ≤ (L : ℤ) := by exact_mod_cast hz
  rw [Int.abs_eq_natAbs] at hz'
  omega

/-- The greatest index below a bound at which a property holds. -/
theorem exists_greatest_index (P : ℕ → Prop) (m k : ℕ) (hk : k ≤ m) (hPk : P k) :
    ∃ b, k ≤ b ∧ b ≤ m ∧ P b ∧ ∀ j, b < j → j ≤ m → ¬ P j := by
  classical
  refine ⟨Nat.findGreatest P m, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_findGreatest hk hPk
  · exact Nat.findGreatest_le m
  · exact Nat.findGreatest_spec hk hPk
  · intro j hj hjm
    exact Nat.findGreatest_is_greatest hj hjm

/-! ## Components and boundaries -/

/-- A site of a set lies in its own component. -/
theorem self_mem_jStepComponent {J : ℕ} {S : Set (Lattice d)} {v : Lattice d} (hv : v ∈ S) :
    v ∈ jStepComponent J S v :=
  jStepReachableIn_of_dist hv hv (by rw [latticeDist_self]; exact Nat.zero_le J)

/-- One admissible step out of a component stays in it. -/
theorem mem_jStepComponent_of_dist_le {J : ℕ} {S : Set (Lattice d)} {c x y : Lattice d}
    (hx : x ∈ jStepComponent J S c) (hy : y ∈ S) (h : latticeDist x y ≤ J) :
    y ∈ jStepComponent J S c :=
  hx.trans (jStepReachableIn_of_dist (mem_of_jStepReachableIn hx) hy h)

/-- **A path inside a set stays inside the component of its source.** -/
theorem jStepReachableIn_jStepComponent {J : ℕ} {S : Set (Lattice d)} {u w : Lattice d}
    (hu : u ∈ S) (h : JStepReachableIn J S u w) :
    JStepReachableIn J (jStepComponent J S u) u w := by
  have hself : u ∈ jStepComponent J S u := self_mem_jStepComponent hu
  refine jStepReachableIn_induction h ?_ ?_
  · exact jStepReachableIn_of_dist hself hself (by rw [latticeDist_self]; exact Nat.zero_le J)
  · intro x hx y hy hP hxy
    have hx' : x ∈ jStepComponent J S u := mem_of_jStepReachableIn hP
    have hy' : y ∈ jStepComponent J S u := mem_jStepComponent_of_dist_le hx' hy hxy
    exact hP.trans (jStepReachableIn_of_dist hx' hy' hxy)

/-- Every component is `1`-step connected inside itself. -/
theorem jStepReachableIn_within_jStepComponent {J : ℕ} {S : Set (Lattice d)} {c : Lattice d}
    {a b : Lattice d} (ha : a ∈ jStepComponent J S c) (hb : b ∈ jStepComponent J S c) :
    JStepReachableIn J (jStepComponent J S c) a b := by
  have hab : JStepReachableIn J S a b := ha.symm.trans hb
  have h := jStepReachableIn_jStepComponent (mem_of_jStepReachableIn ha) hab
  rwa [jStepComponent_eq_of_mem ha] at h

/-- A site adjacent to a set and off it lies on the outer boundary. -/
theorem mem_outerBoundary_of_step {K : Set (Lattice d)} {x y : Lattice d}
    (hx : x ∈ K) (hy : y ∉ K) (h : latticeDist x y ≤ 1) : y ∈ outerBoundary K :=
  ⟨hy, x, hx, h⟩

/-- The outer boundary of a set inside a ball sits in the ball of radius one more. -/
theorem latticeDist_le_of_outerBoundary {K : Set (Lattice d)} {c y : Lattice d} {r : ℕ}
    (hK : ∀ u ∈ K, latticeDist c u ≤ r) (hy : y ∈ outerBoundary K) :
    latticeDist c y ≤ r + 1 := by
  obtain ⟨-, u, hu, hd⟩ := hy
  exact le_trans (latticeDist_triangle c u y) (Nat.add_le_add (hK u hu) hd)

/-- A set all of whose sites are within a fixed distance of a centre is finite. -/
theorem finite_of_forall_latticeDist_le {K : Set (Lattice d)} {c : Lattice d} {r : ℕ}
    (h : ∀ u ∈ K, latticeDist c u ≤ r) : K.Finite :=
  Set.Finite.subset (finite_setOf_latticeDist_le c r) fun _ hx => h _ hx

/-! ## A large good component reaches outside every small box -/

/-- **A good component of diameter at least `R` leaves every box of radius `r < R / 2`.**  This
is the quantitative form of "a small bad component cannot enclose a large good component". -/
theorem exists_mem_boxExterior_of_inGoodComponentOfDiameterAtLeast
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω} {R : ℝ} {c p : Lattice d} {r : ℕ}
    (hp : InGoodComponentOfDiameterAtLeast E Cbox 1 ω R p) (hr : 2 * (r : ℝ) < R) :
    ∃ q, JStepReachableIn 1 {u | IsPercolationGoodSite E Cbox ω u} p q ∧ q ∈ boxExterior c r := by
  obtain ⟨-, u1, u2, h1, h2, hdist⟩ := hp
  by_contra hcon
  push_neg at hcon
  have hu1 : latticeDist c u1 ≤ r := by
    have := hcon u1 h1
    simpa [boxExterior, Nat.not_lt] using this
  have hu2 : latticeDist c u2 ≤ r := by
    have := hcon u2 h2
    simpa [boxExterior, Nat.not_lt] using this
  have htri : latticeDist u1 u2 ≤ r + r := by
    refine le_trans (latticeDist_triangle u1 c u2) ?_
    have : latticeDist u1 c = latticeDist c u1 := latticeDist_comm u1 c
    omega
  have hreal : ((latticeDist u1 u2 : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by
    have : ((latticeDist u1 u2 : ℕ) : ℝ) ≤ ((r + r : ℕ) : ℝ) := by exact_mod_cast htri
    push_cast at this ⊢
    linarith
  linarith

/-! ## The separation step -/



theorem goodConnectedInDoubleBallAt_of_timarBoundaryComponentConnectivity
    (hd : 2 ≤ d) (htimar : TimarBoundaryComponentConnectivity d)
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} (hJ : 1 ≤ J) (ω : Ω) (z : Lattice d) (L : ℕ)
    {D : ℝ} (hD : (L : ℝ) / 20 ≤ D)
    (hbad : ∀ v : Lattice d, InLatticeBallReal z v (2 * L : ℝ) →
      ¬ IsPercolationGoodSite E Cbox ω v →
      HasLatticeDiameterAtMost
        (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox ω u} v) ((L : ℝ) / 100)) :
    GoodConnectedInDoubleBallAt E Cbox ω z L D := by
  classical
  intro v w hv hw hvcomp hwcomp
  have hL2 : (L : ℝ) ≤ (2 * L : ℝ) := by
    have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith
  -- the geodesic and its ball bounds
  have hgball : ∀ k : ℕ, InLatticeBallReal z (latticeGeodesic v w k) (L : ℝ) := fun k =>
    inLatticeBallReal_latticeGeodesic hv hw k
  have hgball2 : ∀ k : ℕ, InLatticeBallReal z (latticeGeodesic v w k) (2 * L : ℝ) := fun k =>
    inLatticeBallReal_mono hL2 (hgball k)
  have hgm : latticeGeodesic v w (latticeDist v w) = w :=
    latticeGeodesic_of_latticeDist_le le_rfl
  have hg0 : latticeGeodesic v w 0 = v := latticeGeodesic_zero v w
  have hvT : v ∈ {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} :=
    ⟨hvcomp.1, inLatticeBallReal_mono hL2 hv⟩
  -- the walk
  have key : ∀ n k : ℕ, latticeDist v w - k ≤ n → k ≤ latticeDist v w →
      IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
      JStepReachableIn 1
        {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} v
        (latticeGeodesic v w k) →
      JStepReachableIn 1
        {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} v w := by
    intro n
    induction n with
    | zero =>
      intro k hkn hkm _ hreach
      have hk : k = latticeDist v w := by omega
      subst hk
      rwa [hgm] at hreach
    | succ n ih =>
      intro k hkn hkm hgood hreach
      by_cases hkeq : k = latticeDist v w
      · subst hkeq
        rwa [hgm] at hreach
      have hklt : k < latticeDist v w := lt_of_le_of_ne hkm hkeq
      by_cases hnext : IsPercolationGoodSite E Cbox ω (latticeGeodesic v w (k + 1))
      · have hstep : JStepReachableIn 1
            {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)}
            (latticeGeodesic v w k) (latticeGeodesic v w (k + 1)) :=
          jStepReachableIn_of_dist ⟨hgood, hgball2 k⟩ ⟨hnext, hgball2 (k + 1)⟩
            (latticeDist_latticeGeodesic_succ v w k)
        exact ih (k + 1) (by omega) (by omega) hnext (hreach.trans hstep)
      -- the obstructed case
      · -- the bad `1`-step component of the next site
        have hbadmem : latticeGeodesic v w (k + 1) ∈
            {u | ¬ IsPercolationGoodSite E Cbox ω u} := hnext
        have hKmem : latticeGeodesic v w (k + 1) ∈
            jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)) := self_mem_jStepComponent hbadmem
        have hKJ : jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)) ⊆
            jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)) := fun u hu => jStepReachableIn_mono_step hJ hu
        have hdiam := hbad (latticeGeodesic v w (k + 1)) (hgball2 (k + 1)) hnext
        have hdiamK : HasLatticeDiameterAtMost
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1))) ((L : ℝ) / 100) :=
          fun a ha b hb i => hdiam a (hKJ ha) b (hKJ hb) i
        have hKball : ∀ u ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)),
            latticeDist (latticeGeodesic v w (k + 1)) u ≤ L / 100 := fun u hu =>
          latticeDist_le_div_of_hasLatticeDiameterAtMost hdiamK hKmem hu
        -- `L` is positive
        have hLpos : 0 < L := by
          rcases Nat.eq_zero_or_pos L with hL0 | hL0
          · exfalso
            subst hL0
            have h1 : v = z := eq_of_inLatticeBallReal_zero (by simpa using hv)
            have h2 : w = z := eq_of_inLatticeBallReal_zero (by simpa using hw)
            rw [h1, h2, latticeDist_self] at hklt
            omega
          · exact hL0
        have hKbad : jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
            (latticeGeodesic v w (k + 1)) ⊆ {u | ¬ IsPercolationGoodSite E Cbox ω u} :=
          jStepComponent_subset
        have hgoodK : ∀ {p : Lattice d}, IsPercolationGoodSite E Cbox ω p →
            p ∈ (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)))ᶜ := fun {p} hp hmem => (hKbad hmem) hp
        have hvK := hgoodK hvcomp.1
        have hwK := hgoodK hwcomp.1
        -- the component of `v` in the complement of the bad component
        have hvC : v ∈ jStepComponent 1
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)))ᶜ v := self_mem_jStepComponent hvK
        have hTK : {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} ⊆
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)))ᶜ := fun u hu => hgoodK hu.1
        have hgkC : latticeGeodesic v w k ∈ jStepComponent 1
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)))ᶜ v := jStepReachableIn_mono_set hTK hreach
        -- both endpoints reach outside the box that contains the bad component
        have hrlt : 2 * ((L / 100 : ℕ) : ℝ) < D := by
          have h1 : L / 100 * 100 ≤ L := Nat.div_mul_le_self L 100
          have h1' : ((L / 100 : ℕ) : ℝ) * 100 ≤ (L : ℝ) := by exact_mod_cast h1
          have h2 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
          linarith
        obtain ⟨qv, hqv, hqvE⟩ :=
          exists_mem_boxExterior_of_inGoodComponentOfDiameterAtLeast
            (c := latticeGeodesic v w (k + 1)) hvcomp hrlt
        obtain ⟨qw, hqw, hqwE⟩ :=
          exists_mem_boxExterior_of_inGoodComponentOfDiameterAtLeast
            (c := latticeGeodesic v w (k + 1)) hwcomp hrlt
        have hExtK : boxExterior (latticeGeodesic v w (k + 1)) (L / 100) ⊆
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)))ᶜ := by
          intro u hu hmem
          exact absurd (hKball u hmem) (Nat.not_le.mpr hu)
        have hgoodsubK : {u | IsPercolationGoodSite E Cbox ω u} ⊆
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)))ᶜ := fun u hu => hgoodK hu
        have hwC : w ∈ jStepComponent 1
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)))ᶜ v := by
          have h1 := jStepReachableIn_mono_set hgoodsubK hqv
          have h2 := jStepReachableIn_mono_set hgoodsubK hqw
          have h3 := jStepReachableIn_mono_set hExtK
            (jStepReachableIn_boxExterior hd (latticeGeodesic v w (k + 1)) (L / 100) hqvE hqwE)
          exact (h1.trans h3).trans h2.symm
        -- the last geodesic index outside that component
        obtain ⟨b, hbk, hbm, hbC, hbmax⟩ :=
          exists_greatest_index
            (fun j => latticeGeodesic v w j ∉ jStepComponent 1
              (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
                (latticeGeodesic v w (k + 1)))ᶜ v)
            (latticeDist v w) (k + 1) (by omega)
            (fun hmem => (jStepComponent_subset hmem) hKmem)
        have hbne : b ≠ latticeDist v w := by
          intro hbeq
          exact hbC (by rw [hbeq, hgm]; exact hwC)
        have hblt : b < latticeDist v w := lt_of_le_of_ne hbm hbne
        have hb1C : latticeGeodesic v w (b + 1) ∈ jStepComponent 1
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)))ᶜ v :=
          not_not.mp (hbmax (b + 1) (by omega) (by omega))
        -- the site before the exit is in the bad component
        have hbK : latticeGeodesic v w b ∈
            jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)) := by
          by_contra hnotK
          refine hbC (mem_jStepComponent_of_dist_le hb1C hnotK ?_)
          rw [latticeDist_comm]
          exact latticeDist_latticeGeodesic_succ v w b
        -- both ends of the detour are on the visible boundary
        have hb1out : latticeGeodesic v w (b + 1) ∈ outerBoundary
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1))) :=
          mem_outerBoundary_of_step hbK (jStepComponent_subset hb1C)
            (latticeDist_latticeGeodesic_succ v w b)
        have hgkout : latticeGeodesic v w k ∈ outerBoundary
            (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1))) := by
          refine mem_outerBoundary_of_step hKmem (hgoodK hgood) ?_
          rw [latticeDist_comm]
          exact latticeDist_latticeGeodesic_succ v w k
        -- the corrected `[Timár]` joins them inside the visible boundary
        have hKfin : (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
            (latticeGeodesic v w (k + 1))).Finite := finite_of_forall_latticeDist_le hKball
        have hKne : (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
            (latticeGeodesic v w (k + 1))).Nonempty := ⟨_, hKmem⟩
        have hKconn : ∀ a ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)),
            ∀ b' ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1)),
            JStepReachableIn 1 (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1))) a b' := fun a ha b' hb' =>
          jStepReachableIn_within_jStepComponent ha hb'
        have hpath := htimar _ hKfin hKne hKconn v hvK
          (latticeGeodesic v w k) ⟨hgkout, hgkC⟩
          (latticeGeodesic v w (b + 1)) ⟨hb1out, hb1C⟩
        -- the visible boundary consists of good sites of the double ball
        have hvisT : visibleBoundary (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u}
              (latticeGeodesic v w (k + 1))) v ⊆
            {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} := by
          intro u hu
          refine ⟨isPercolationGoodSite_of_mem_outerBoundary_badComponent le_rfl hu.1, ?_⟩
          have hcentre : latticeDist z (latticeGeodesic v w (k + 1)) ≤ L :=
            latticeDist_le_of_inLatticeBallReal_natRadius (hgball (k + 1))
          have hbnd : latticeDist (latticeGeodesic v w (k + 1)) u ≤ L / 100 + 1 :=
            latticeDist_le_of_outerBoundary hKball hu.1
          have htri : latticeDist z u ≤ 2 * L := by
            have := latticeDist_triangle z (latticeGeodesic v w (k + 1)) u
            omega
          refine inLatticeBallReal_of_latticeDist_le htri ?_
          push_cast
          linarith
        have hdetour := jStepReachableIn_mono_set hvisT hpath
        have hb1good : IsPercolationGoodSite E Cbox ω (latticeGeodesic v w (b + 1)) :=
          (hvisT ⟨hb1out, hb1C⟩).1
        exact ih (b + 1) (by omega) (by omega) hb1good (hreach.trans hdetour)
  refine key (latticeDist v w) 0 (by omega) (by omega) ?_ ?_
  · rw [hg0]; exact hvcomp.1
  · rw [hg0]
    exact jStepReachableIn_of_dist hvT hvT (by rw [latticeDist_self]; exact Nat.zero_le 1)

/-- **`TimarBoundaryInput`, the recorded external of S1**, is the case
`D = L / 10` of the free-diameter separation step. -/
theorem timarBoundaryInput_of_timarBoundaryComponentConnectivity
    (hd : 2 ≤ d) (htimar : TimarBoundaryComponentConnectivity d)
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} (hJ : 1 ≤ J) (ω : Ω) (z : Lattice d) (L : ℕ) :
    TimarBoundaryInput E Cbox J ω z L := fun hbad =>
  goodConnectedInDoubleBallAt_of_timarBoundaryComponentConnectivity hd htimar hJ ω z L
    (by have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L; linarith) hbad


/-- The visible boundary is exactly the **inner** boundary of the complementary component it is
seen from.  This is the cleanest form of the remaining external: *the inner boundary of a
`1`-step component of the complement of a finite `1`-step connected set is `1`-step connected*. -/
theorem visibleBoundary_eq_innerBoundary (S : Set (Lattice d)) (c : Lattice d) :
    visibleBoundary S c = innerBoundary (jStepComponent 1 Sᶜ c) := by
  ext x
  constructor
  · rintro ⟨⟨hxS, u, huS, hux⟩, hxC⟩
    refine ⟨hxC, u, ?_, hux⟩
    exact fun hu => (jStepComponent_subset hu) huS
  · rintro ⟨hxC, u, huC, hux⟩
    have hxS : x ∉ S := jStepComponent_subset hxC
    refine ⟨⟨hxS, u, ?_, hux⟩, hxC⟩
    by_contra huS
    refine huC (mem_jStepComponent_of_dist_le hxC huS ?_)
    rw [latticeDist_comm]
    exact hux



theorem goodConnectedInDoubleBall_of_timarBoundaryComponentConnectivity
    (hd : 2 ≤ d) (htimar : TimarBoundaryComponentConnectivity d)
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} (hJ : 1 ≤ J) {ω : Ω} {z : Lattice d} {C q : ℝ}
    {h L : ℕ} (hbad : BadComponentDiameterBound E Cbox J ω z C q h)
    (hsmall : C * (1 + h + q⁻¹ * Real.log (2 + (2 * L : ℝ))) ^ 2 ≤ (L : ℝ) / 100) :
    GoodConnectedInDoubleBall E Cbox ω z L :=
  goodConnectedInDoubleBall_of_badComponentDiameterBound hbad hsmall
    (timarBoundaryInput_of_timarBoundaryComponentConnectivity hd htimar hJ ω z L)


namespace DimensionOne

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

/-! ## `2 ≤ d` is necessary: the separation step is FALSE on the line

The `2 ≤ d` hypothesis of `timarBoundaryInput_of_timarBoundaryComponentConnectivity` is not an
artefact of the proof.  On `ℤ` a single bad site disconnects the lattice, so
`TimarBoundaryInput` itself fails, however strong the boundary-connectivity input:  the two
good half-lines have infinite diameter, every bad component is a single site (diameter `0`), and
yet no good path joins `-L` to `L`.  The witness field makes exactly the origin bad. -/

/-- The event field whose only bad site is the origin: `E 0 0 = univ` and `E j u = ∅` otherwise,
with influence-box constant `Cbox = 0`. -/
def singletonBadField (d : ℕ) (Ω : Type*) : ℕ → Lattice d → Set Ω :=
  fun j u => if j = 0 ∧ u = 0 then Set.univ else ∅

/-- The good sites of `singletonBadField` are exactly the sites other than the origin. -/
theorem isPercolationGoodSite_singletonBadField_iff {d : ℕ} {Ω : Type*} (ω : Ω)
    (z : Lattice d) :
    IsPercolationGoodSite (singletonBadField d Ω) 0 ω z ↔ z ≠ 0 := by
  constructor
  · intro h hz
    apply h 0 z
    · simp [InInfluenceBox, latticeDist_self]
    · simp [singletonBadField, hz]
  · intro hz j u hu
    have hu0 : latticeDist u z = 0 := by
      simpa [InInfluenceBox] using hu
    have huz : u = z := eq_of_latticeDist_eq_zero hu0
    subst huz
    simp [singletonBadField, hz]

/-- A set of diameter zero has any nonnegative diameter bound. -/
theorem hasLatticeDiameterAtMost_of_subset_singleton {d : ℕ} {S : Set (Lattice d)}
    {c : Lattice d} {R : ℝ} (hR : 0 ≤ R) (h : S ⊆ {c}) : HasLatticeDiameterAtMost S R := by
  intro v hv w hw i
  have hv' : v = c := h hv
  have hw' : w = c := h hw
  subst hv'
  subst hw'
  simpa using hR

/-- On the line, updating the only coordinate produces the constant site. -/
theorem update_one_const (x : Lattice 1) (a : ℤ) :
    Function.update x (0 : Fin 1) a = fun _ => a := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp

theorem latticeDist_one_const (a b : ℤ) :
    latticeDist (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) = (a - b).natAbs := by
  simp [latticeDist]

theorem inLatticeBallReal_one_const {a : ℤ} {R : ℝ} (h : ((|a| : ℤ) : ℝ) ≤ R) :
    InLatticeBallReal (0 : Lattice 1) (fun _ : Fin 1 => a) R := by
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [Pi.zero_apply, sub_zero]
  exact h

/-- **The separation step fails in dimension one.**  For every `L ≥ 1` the recorded S1 input
`TimarBoundaryInput` is false for the one-bad-site field, so no boundary-connectivity statement
can discharge S1 on the line: the `2 ≤ d` hypothesis of
`timarBoundaryInput_of_timarBoundaryComponentConnectivity` is necessary. -/
theorem not_timarBoundaryInput_one {Ω : Type*} (ω : Ω) (J L : ℕ) (hL : 1 ≤ L) :
    ¬ TimarBoundaryInput (singletonBadField 1 Ω) 0 J ω (0 : Lattice 1) L := by
  intro h
  have hgood : ∀ z : Lattice 1,
      IsPercolationGoodSite (singletonBadField 1 Ω) 0 ω z ↔ z ≠ 0 :=
    fun z => isPercolationGoodSite_singletonBadField_iff ω z
  have hmemgood : ∀ t : ℤ, t ≠ 0 →
      (fun _ : Fin 1 => t) ∈
        {u : Lattice 1 | IsPercolationGoodSite (singletonBadField 1 Ω) 0 ω u} := by
    intro t ht
    have : (fun _ : Fin 1 => t) ≠ 0 := by
      intro hcon
      exact ht (by simpa using congrFun hcon (0 : Fin 1))
    exact (hgood _).mpr this
  -- every bad component is the single site `0`
  have hbadsub : ∀ p : Lattice 1,
      jStepComponent J {u : Lattice 1 | ¬ IsPercolationGoodSite (singletonBadField 1 Ω) 0 ω u} p
        ⊆ {(0 : Lattice 1)} := by
    intro p x hx
    have hx' := jStepComponent_subset hx
    simp only [Set.mem_setOf_eq, hgood, not_not] at hx'
    exact hx'
  have hbad : ∀ p : Lattice 1, InLatticeBallReal (0 : Lattice 1) p (2 * L : ℝ) →
      ¬ IsPercolationGoodSite (singletonBadField 1 Ω) 0 ω p →
      HasLatticeDiameterAtMost
        (jStepComponent J {u : Lattice 1 | ¬ IsPercolationGoodSite (singletonBadField 1 Ω) 0 ω u}
          p) ((L : ℝ) / 100) := fun p _ _ =>
    hasLatticeDiameterAtMost_of_subset_singleton (by positivity) (hbadsub p)
  -- the two endpoints and their large good components
  have hray : ∀ a b : ℤ, (∀ t : ℤ, min a b ≤ t → t ≤ max a b → t ≠ 0) →
      JStepReachableIn 1 {u : Lattice 1 | IsPercolationGoodSite (singletonBadField 1 Ω) 0 ω u}
        (fun _ => a) (fun _ => b) := by
    intro a b hab
    have hupd := jStepReachableIn_update
      (S := {u : Lattice 1 | IsPercolationGoodSite (singletonBadField 1 Ω) 0 ω u})
      (fun _ : Fin 1 => (0 : ℤ)) (0 : Fin 1) a b
      (fun t h1 h2 => by
        rw [update_one_const]
        exact hmemgood t (hab t h1 h2))
    rwa [update_one_const, update_one_const] at hupd
  have hvgood : IsPercolationGoodSite (singletonBadField 1 Ω) 0 ω (fun _ => -(L : ℤ)) :=
    hmemgood _ (by omega)
  have hwgood : IsPercolationGoodSite (singletonBadField 1 Ω) 0 ω (fun _ => (L : ℤ)) :=
    hmemgood _ (by omega)
  have hvcomp : InGoodComponentOfDiameterAtLeast (singletonBadField 1 Ω) 0 1 ω ((L : ℝ) / 10)
      (fun _ => -(L : ℤ)) := by
    refine ⟨hvgood, (fun _ => -(L : ℤ)), (fun _ => -(2 * L : ℤ)), ?_, ?_, ?_⟩
    · exact jStepReachableIn_of_dist hvgood hvgood (by rw [latticeDist_self]; exact Nat.zero_le 1)
    · exact hray _ _ (fun t h1 h2 => by omega)
    · rw [latticeDist_one_const]
      have : ((-(L : ℤ) - -(2 * L : ℤ)).natAbs : ℝ) = (L : ℝ) := by
        have hn : (-(L : ℤ) - -(2 * L : ℤ)).natAbs = L := by omega
        rw [hn]
      rw [this]
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith
  have hwcomp : InGoodComponentOfDiameterAtLeast (singletonBadField 1 Ω) 0 1 ω ((L : ℝ) / 10)
      (fun _ => (L : ℤ)) := by
    refine ⟨hwgood, (fun _ => (L : ℤ)), (fun _ => (2 * L : ℤ)), ?_, ?_, ?_⟩
    · exact jStepReachableIn_of_dist hwgood hwgood (by rw [latticeDist_self]; exact Nat.zero_le 1)
    · exact hray _ _ (fun t h1 h2 => by omega)
    · rw [latticeDist_one_const]
      have : (((L : ℤ) - (2 * L : ℤ)).natAbs : ℝ) = (L : ℝ) := by
        have hn : ((L : ℤ) - (2 * L : ℤ)).natAbs = L := by omega
        rw [hn]
      rw [this]
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith
  have hvball : InLatticeBallReal (0 : Lattice 1) (fun _ => -(L : ℤ)) (L : ℝ) := by
    refine inLatticeBallReal_one_const ?_
    have : |(-(L : ℤ))| = (L : ℤ) := by
      rw [abs_neg]
      exact abs_of_nonneg (Int.natCast_nonneg L)
    rw [this]
    exact le_rfl
  have hwball : InLatticeBallReal (0 : Lattice 1) (fun _ => (L : ℤ)) (L : ℝ) := by
    refine inLatticeBallReal_one_const ?_
    have : |((L : ℤ))| = (L : ℤ) := abs_of_nonneg (Int.natCast_nonneg L)
    rw [this]
    exact le_rfl
  have hres := h hbad (fun _ => -(L : ℤ)) (fun _ => (L : ℤ)) hvball hwball hvcomp hwcomp
  obtain ⟨x, hx, hx0⟩ :=
    exists_mem_eq_of_jStepReachableIn_one (c := 0) hres (by simp) (by simp)
  have hxz : x = 0 := lattice_one_ext (by rw [hx0]; simp)
  exact ((hgood x).mp hx.1) hxz

end DimensionOne

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
