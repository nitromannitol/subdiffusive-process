module

public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_iteration_twelve
public import SubdiffusiveProcess.Paper.lem_as_regularity_rooted_iteration
public import SubdiffusiveProcess.Analysis.ScoreBudget
public import SubdiffusiveProcess.Analysis.ScoreIterationParameters
public import SubdiffusiveProcess.Analysis.DirichletIterationCost
public import SubdiffusiveProcess.Analysis.DirichletForcingRow

@[expose] public section

/-! Raw score sums and reference ratios supply a deterministic Dirichlet oscillation estimate for
the cutoff field on the threshold-12 good events. The stochastic prefix and physical scaling
statements are separate inputs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- Small score budgets pay the entire boundary excess iteration for the cutoff field
`aCutoff M L ω` (threshold-12 events, sample-based coefficient error). -/
theorem lem_as_regularity_dirichlet_budget_twelve (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (Cg kap rho : ℝ) (hCg : 0 < Cg) (hkap : 0 < kap) (hrho : 0 < rho) :
    ∃ lam tau C : ℝ, 0 < lam ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < C ∧
    ∀ base : ℝ, 0 ≤ base → base ≤ min (2*lam) tau →
    ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, 2048 * M.delta ^ 2 ≤ 1 → 32 * M.delta ^ 2 ≤ tau →
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ ((1 / 4 : ℝ) / 8) * Real.log 3 / 16 →
    ∀ L m n : ℕ, n+26 ≤ m → ∀ z ∈ cube d m, ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
    ∀ ref Z score : ℕ → ℝ,
      (∀ j,0 < ref j) → (∀ j,0 ≤ Z j) → (∀ j,0 ≤ score j) →
      (∑ j ∈ Finset.Icc n m,Z j) ≤ (lam*tau/2)*((m:ℝ)-n) →
      (∑ j ∈ Finset.Icc n m,score j) ≤ (lam*tau/2)*((m:ℝ)-n) →
      (∀ e : ℝ, tau ≤ e → e ≤ 1 → ∀ j : ℕ, j+2 ≤ m → Z (j+2) < 1 →
        ω ∈ Paper.product_threshold_good_scale d M 12 (some L) (j + 2) z e (1 / 32)) →
      (∀ j : ℕ, j+2 ≤ m → Z (j+2) < 1 →
        section6HomogenizationError M (1 / 32) L (j + 2) ω z ≤ Cg*(base+score (j+2))) →
      (∀ j : ℕ, j+2 ≤ m → Z (j+2) < 1 →
        kap * ref j ≤ tailAverage M L (j + 2) ω (translatedCube d ((j : ℤ) + 2) z)) →
      (∀ j : ℕ,n ≤ j → j+5 ≤ m →
        ref (m-2)/ref j ≤ Real.exp (4*(lam*((m:ℝ)-n)))) →
    ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
      IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
      (∃ sOrder : FractionalOrder,sOrder.1 = (1/4:ℝ) ∧
        Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d m) sOrder FiniteLpExponent.two g) →
      MemHolder (cube d m) (1/2) g → MemHolder (cube d m) (1/2) h.grad →
      (3:ℝ)^(-((n+2:ℕ):ℤ))*normalizedL2On (truncatedCube d m (n+2:ℕ) z)
        (fun x => u.toFun x-averageOn (truncatedCube d m (n+2:ℕ) z) u.toFun)  ≤
      C*(3:ℝ)^(rho*((m:ℝ)-n))*
        ((3:ℝ)^(-((m-5:ℕ):ℤ))*normalizedL2On (truncatedCube d m (m-5:ℕ) z)
          (fun x => u.toFun x-averageOn (truncatedCube d m (m-5:ℕ) z) u.toFun) +
          vectorSupNormOn (cube d m) h.grad +
          (ref (m-2))⁻¹*(3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) g +
          (3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) h.grad) := by
  classical
  obtain ⟨A,CI,hA,hCI,hiter⟩ := lem_as_regularity_dirichlet_iteration_twelve d hd
  obtain ⟨k,hk,htheta,hthetak,hpure⟩ := exists_score_iteration_block A
  obtain ⟨B,hB,hiter⟩ := hiter k hk
  obtain ⟨eta,heta,hcontract⟩ := exists_score_iteration_cap A B _ _ hB hthetak.1 hpure
  let B1 := B * max 1 kap⁻¹
  have hB1 : B ≤ B1 := le_mul_of_one_le_right hB.le (le_max_left _ _)
  have hB10 : 0 < B1 := lt_of_lt_of_le hB hB1
  obtain ⟨lam,C,hlam,hC,hcost⟩ := exists_dirichlet_iteration_cost CI B1 (3*B*Cg) rho k
    hCI hB10.le (by positivity) hrho
  let tau := eta/2
  have htau : 0 < tau := half_pos heta.1
  have htau1 : tau  ≤  1 := by dsimp only [tau]; linarith only [heta.2]
  refine ⟨lam,tau,C,hlam,htau,htau1,hC,?_⟩
  intro base hb0 hb M hM2048 hM32 hMtau L m n hnm z hz ω ref Z score href hZ hsc hZsum hscsum
    hev herr htail hrat u h g hsol hg hgh hhh
  have hlen : 0  ≤  (m:ℝ)-n := sub_nonneg.mpr (by exact_mod_cast (show n ≤ m by omega))
  obtain ⟨hscore,hcount⟩ := score_budget_rescale (Finset.Icc n m) Z score tau lam
    ((m:ℝ)-n) htau htau1 hlam.le hlen (fun j _ => hZ j) (fun j _ => hsc j) hZsum hscsum
  let good := fun j => Z j < 1 ∧ score j  ≤  tau
  obtain ⟨bad,hbad,hgood,hbadcard⟩ := aux_lem_as_regularity_rooted_iteration_bad
    good n m n (m-7) k le_rfl (by omega)
  have hend : m-7+2 = m-5 := by omega
  simp only [hend] at hbad hgood
  let err := fun j : ℕ => section6HomogenizationError M (1 / 32) L (j + 2) ω z
  let epsRow := fun j : ℤ => if j ∈ bad then 0 else B*err j.toNat
  let R := Real.exp (4*(lam*((m:ℝ)-n)))
  let Hmean := vectorSupNormOn (cube d m) h.grad
  let T := (ref (m-2))⁻¹*(3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) g +
    (3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) h.grad
  let defect := fun j : ℤ => epsRow j*Hmean+B1*R*T*(3:ℝ)^(-((((m:ℤ)-j:ℤ):ℝ)/2))
  have hH : 0  ≤  Hmean := Section6Holder.vectorSupNormOn_cube_nonneg hhh
  have hT : 0  ≤  T := by
    have h1 := holderSeminormOn_nonneg hgh
    have h2 := holderSeminormOn_nonneg hhh
    have hr0 := href (m-2)
    dsimp only [T]
    positivity
  have hR : 1  ≤  R := Real.one_le_exp_iff.mpr (by positivity)
  have hErr0 : ∀ j : ℕ, 0 ≤ err j := fun j => ENNReal.toReal_nonneg
  have heps (j : ℤ) : 0  ≤  epsRow j := by
    dsimp only [epsRow]; split_ifs
    · exact le_rfl
    · exact mul_nonneg hB.le (hErr0 _)
  have he_good (j : ℕ) (hj : j+2 ≤ m) (hjbad : (j:ℤ) ∉ bad)
      (hjn : n+2 ≤ j) (hjt : j ≤ m-5) :
      k ≤ j ∧ ω ∈ Paper.product_threshold_good_scale d M 12 (some L) (j + 2) z eta (1 / 32) ∧
        err j ≤ Cg*(base+score (j+2)) := by
    obtain ⟨hkj,hgj⟩ := hgood j hjn hjt hjbad
    have he := herr j hj hgj.1
    have hbnd : base+score (j+2)  ≤  eta := by
      have hbt := hb.trans (min_le_right _ _)
      dsimp only [good,tau] at hgj
      dsimp only [tau] at hbt
      linarith only [hbt,hgj.2]
    refine ⟨hkj,hev eta (by dsimp only [tau]; linarith only [heta.1]) heta.2 j hj hgj.1, he⟩
  have hsum := aux_prop_folded_iteration_eps_sum (n+2) (m-5) n m (by omega) (by omega)
    (by omega) bad (fun j => err j) score B Cg base hB.le hCg.le hb0 hsc
    (fun j hjn hjt hjbad => (he_good j (by omega) hjbad hjn hjt).2.2)
  have hesum : (∑ j ∈ Finset.Icc ((n+2:ℕ):ℤ) ((m-5:ℕ):ℤ),epsRow j)  ≤ 
      (3*B*Cg)*lam*((m:ℝ)-n) := by
    have hbL := mul_le_mul_of_nonneg_right (hb.trans (min_le_left _ _)) hlen
    have hinner : base*((m:ℝ)-n)+(∑ j ∈ Finset.Icc n m,score j)  ≤  3*lam*((m:ℝ)-n) := by
      linarith only [hbL,hscore]
    have hh := mul_le_mul_of_nonneg_left hinner (mul_nonneg hB.le hCg.le)
    exact hsum.trans (by nlinarith only [hh])
  have hM' : 2048 * M.delta ^ 2 ≤ 1 := hM2048
  have hetaI : eta ∈ Icc (32 * M.delta ^ 2) 1 :=
    ⟨by dsimp only [tau] at hM32; linarith only [hM32, heta.1], heta.2⟩
  have hrec := hiter M hM' hMtau eta hetaI _ htheta hthetak hcontract L m (n+2) (m-5)
    (by omega) (by omega) z hz ω bad hbad (by
      intro j hj hjbad
      have hjb := Finset.mem_Icc.mp hj
      have hj0 : 0 ≤ j := (Int.natCast_nonneg (n+2)).trans (Finset.mem_Icc.mp hj).1
      have hc : (j.toNat:ℤ)=j := Int.toNat_of_nonneg hj0
      have hh := he_good j.toNat (by omega) (by simpa only [hc] using hjbad) (by omega) (by omega)
      exact ⟨hh.1,hh.2.1⟩) u h g hsol hg hgh hhh epsRow defect
    (fun j _ => ⟨heps j,by
      dsimp only [defect]
      exact add_nonneg (mul_nonneg (heps j) hH)
        (mul_nonneg (mul_nonneg (mul_nonneg hB10.le (by linarith only [hR])) hT) (by positivity))⟩) (by
      intro j hj hjbad
      have hjb := Finset.mem_Icc.mp hj
      have hj0 : 0 ≤ j := (Int.natCast_nonneg (n+2)).trans (Finset.mem_Icc.mp hj).1
      have hc : (j.toNat:ℤ)=j := Int.toNat_of_nonneg hj0
      have hcr : (j.toNat:ℝ)=(j:ℝ) := by exact_mod_cast hc
      have hjn : j.toNat + 2 ≤ m := by omega
      have hfr := dirichlet_forcing_row_le j m (ref j.toNat) (ref (m-2)) R
        (holderSeminormOn (cube d m) (1/2) g) (holderSeminormOn (cube d m) (1/2) h.grad)
        (href _) (href _) hR (holderSeminormOn_nonneg hgh) (holderSeminormOn_nonneg hhh)
        (hrat j.toNat (by omega) (by omega))
      obtain ⟨_, hgjZ⟩ := hgood j.toNat (by omega) (by omega) (by simpa only [hc] using hjbad)
      have hti := htail j.toNat hjn hgjZ.1
      have hTa : 0 < tailAverage M L (j.toNat + 2) ω (translatedCube d ((j.toNat : ℤ) + 2) z) :=
        lt_of_lt_of_le (mul_pos hkap (href _)) hti
      have hinv : (tailAverage M L (j.toNat + 2) ω (translatedCube d ((j.toNat : ℤ) + 2) z))⁻¹ ≤
          max 1 kap⁻¹ * (ref j.toNat)⁻¹ := by
        calc _ ≤ (kap * ref j.toNat)⁻¹ := inv_anti₀ (mul_pos hkap (href _)) hti
          _ = kap⁻¹ * (ref j.toNat)⁻¹ := by rw [mul_inv]
          _ ≤ max 1 kap⁻¹ * (ref j.toNat)⁻¹ :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.2 (href _).le)
      refine ⟨by simp only [epsRow,if_neg hjbad,err]; exact le_rfl,?_⟩
      dsimp only [defect,epsRow]
      rw [if_neg hjbad]
      have hG := holderSeminormOn_nonneg hgh
      have hHh := holderSeminormOn_nonneg hhh
      have hp3 : (0:ℝ) ≤ (3:ℝ)^((j.toNat:ℝ)/2) := by positivity
      have hK1 : 0 ≤ max 1 kap⁻¹ := le_trans zero_le_one (le_max_left _ _)
      have hrowT : (tailAverage M L (j.toNat + 2) ω (translatedCube d ((j.toNat : ℤ) + 2) z))⁻¹ *
            (3:ℝ)^((j.toNat:ℝ)/2) * holderSeminormOn (cube d m) (1/2) g +
          (3:ℝ)^((j.toNat:ℝ)/2) * holderSeminormOn (cube d m) (1/2) h.grad ≤
          max 1 kap⁻¹ * ((ref j.toNat)⁻¹ * (3:ℝ)^((j.toNat:ℝ)/2) *
            holderSeminormOn (cube d m) (1/2) g +
          (3:ℝ)^((j.toNat:ℝ)/2) * holderSeminormOn (cube d m) (1/2) h.grad) := by
        have h1 := mul_le_mul_of_nonneg_right hinv (mul_nonneg hp3 hG)
        have h2 : (3:ℝ)^((j.toNat:ℝ)/2) * holderSeminormOn (cube d m) (1/2) h.grad ≤
            max 1 kap⁻¹ * ((3:ℝ)^((j.toNat:ℝ)/2) * holderSeminormOn (cube d m) (1/2) h.grad) :=
          le_mul_of_one_le_left (mul_nonneg hp3 hHh) (le_max_left _ _)
        nlinarith only [h1, h2]
      simp only [Int.cast_natCast] at hfr
      rw [hcr] at hrowT
      have hfr' := mul_le_mul_of_nonneg_left hfr (mul_nonneg hB.le hK1)
      have hcmb := mul_le_mul_of_nonneg_left hrowT hB.le
      dsimp only [T,Hmean, B1]
      nlinarith only [hfr', hcmb])
  have hdSum := dirichlet_defect_sum_le ((n+2:ℕ):ℤ) ((m-5:ℕ):ℤ) m (by omega) (by omega)
    epsRow Hmean B1 R T _ hH hB10.le (by positivity) hT (le_refl _)
  have hnb : (bad.card:ℝ)  ≤  k+1+lam*((m:ℝ)-n) := by
    dsimp only [good] at hbadcard
    linarith only [hbadcard,hcount]
  have htop : 0  ≤  (3:ℝ)^(-((m-5:ℕ):ℤ))*normalizedL2On (truncatedCube d m (m-5:ℕ) z)
      (fun x => u.toFun x-averageOn (truncatedCube d m (m-5:ℕ) z) u.toFun) :=
    mul_nonneg (by positivity) (Section6Iteration.normalizedL2On_nonneg _ _)
  have hout := hcost ((m:ℝ)-n) bad.card _ _ Hmean T _ hlen htop hH hT hnb hesum
    (hrec.trans (by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      dsimp only [defect,R] at hdSum ⊢
      linarith only [hdSum]))
  dsimp only [T,Hmean] at hout
  convert hout using 1 <;> ring

end Paper
