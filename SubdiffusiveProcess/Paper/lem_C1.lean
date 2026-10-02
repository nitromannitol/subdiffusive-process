import Homogenization.Book.Ch02.MultiscaleEllipticity
import Homogenization.Book.Ch02.Matrices
import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Sobolev.ContinuousCubeL2
import SubdiffusiveProcess.Sobolev.NormalizedDualRatio
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Homogenization hiding sigmaStarInvCoarse
open Homogenization.Book.Ch02
open scoped BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open MeasureTheory Set TopologicalSpace

def aux_lem_C1_testSet (d : Nat) (Q : TriadicCube d) :
    Set (Homogenization.Vec d → Homogenization.Vec d) :=
  {phi : Homogenization.Vec d → Homogenization.Vec d |
    ContDiff Real ∞ phi ∧
    (∃ x ∈ openCubeSet Q, phi x ≠ 0)}

def aux_lem_C1_ratio (d : Nat) (Q : TriadicCube d)
    (F phi : Homogenization.Vec d → Homogenization.Vec d) : Real :=
  |average (cubeDomain Q) (fun x => vecDot (F x) (phi x))| /
    (Real.sqrt (average (cubeDomain Q) (fun x =>
        ∑ i : Fin d, ∑ j : Fin d,
          (fderiv Real (fun y => phi y i) x (Pi.single j 1)) ^ 2)) +
      (3 : Real) ^ (-(Q.scale : Real)) *
        Real.sqrt (average (cubeDomain Q) (fun x =>
          ∑ i : Fin d, (phi x i) ^ 2)))

def aux_lem_C1_weakSet (d : Nat) (Q : TriadicCube d)
    (F : Homogenization.Vec d → Homogenization.Vec d) : Set Real :=
  aux_lem_C1_ratio d Q F '' aux_lem_C1_testSet d Q

lemma aux_lem_C1_weak_bound (d : Nat) (m : Int)
    (F : Homogenization.Vec d → Homogenization.Vec d)
    (hF : Homogenization.MemVectorL2 (openCubeSet (originCube d m)) F) :
    BddAbove (aux_lem_C1_weakSet d (originCube d m) F) ∧
    sSup (aux_lem_C1_weakSet d (originCube d m) F) ≤
      (3 : Real) ^ (m : Real) *
        (Real.sqrt (∑ i : Fin d,
          ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hF i).toLp
            (fun x => F x i)‖ ^ 2) /
          Real.sqrt (volume.real (openCubeSet (originCube d m)))) := by
  let hr : (0 : Real) < (3 : Real) ^ m := by positivity
  let z : SubdiffusiveProcess.SpatialCoordinates d := 0
  let U : Set (SubdiffusiveProcess.SpatialCoordinates d) :=
    (SubdiffusiveProcess.centeredCube z ((3 : Real) ^ m) hr : Set _)
  have hUeq : U = openCubeSet (originCube d m) := by
    dsimp [U, z]
    exact SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube m hr
  have hF' : Homogenization.MemVectorL2 U F := by
    rw [hUeq]
    exact hF
  have hbound : ∀ r : Real, r ∈ aux_lem_C1_weakSet d (originCube d m) F →
      r ≤ (3 : Real) ^ (m : Real) *
        (Real.sqrt (∑ i : Fin d,
          ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hF i).toLp
            (fun x => F x i)‖ ^ 2) /
          Real.sqrt (volume.real (openCubeSet (originCube d m)))) := by
    intro r hrset
    rcases hrset with ⟨phi, ⟨hphi, hnonzero⟩, rfl⟩
    obtain ⟨hmem, hmem_spec⟩ :=
      SubdiffusiveProcess.continuousOn_cube_memLp_and_nonzero
        z ((3 : Real) ^ m) hr phi hphi.continuous.continuousOn
    let fdom : Fin d → SubdiffusiveProcess.DomainL2
        (SubdiffusiveProcess.centeredCube z ((3 : Real) ^ m) hr) :=
      fun i => (Homogenization.memScalarL2_coord_of_memVectorL2 hF' i).toLp
        (fun x => F x i)
    let pdom : Fin d → SubdiffusiveProcess.DomainL2
        (SubdiffusiveProcess.centeredCube z ((3 : Real) ^ m) hr) :=
      fun i => (hmem i).toLp (fun x => phi x i)
    have hnonzero' : ∃ x ∈ (SubdiffusiveProcess.centeredCube z ((3 : Real) ^ m) hr : Set _),
        phi x ≠ 0 := by
      change ∃ x ∈ U, phi x ≠ 0
      rw [hUeq]
      exact hnonzero
    have hsumpos : 0 < ∑ i : Fin d, ‖pdom i‖ ^ 2 := by
      exact hmem_spec.mp hnonzero'
    have hV : 0 < volume.real U := by
      dsimp [U]
      exact SubdiffusiveProcess.centeredCube_volume_pos z hr
    have hdenpos : 0 < Real.sqrt (∑ i : Fin d, ‖pdom i‖ ^ 2) /
          Real.sqrt (volume.real U) := by positivity
    have hnormF (i : Fin d) : ‖fdom i‖ ^ 2 =
        ∫ x in U, (F x i) ^ 2 := by
      rw [show fdom i =
          (Homogenization.memScalarL2_coord_of_memVectorL2 hF' i).toLp
            (fun x => F x i) by rfl, MeasureTheory.Lp.norm_toLp]
      exact Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq
        (Homogenization.memScalarL2_coord_of_memVectorL2 hF' i)
    have hnormp (i : Fin d) : ‖pdom i‖ ^ 2 =
        ∫ x in U, (phi x i) ^ 2 := by
      rw [show pdom i = (hmem i).toLp (fun x => phi x i) by rfl,
        MeasureTheory.Lp.norm_toLp]
      exact Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq (hmem i)
    have hnormpsum : ∑ i : Fin d, ‖pdom i‖ ^ 2 =
        ∫ x in U, ∑ i : Fin d, (phi x i) ^ 2 := by
      calc
        _ = ∑ i : Fin d, ∫ x in U, (phi x i) ^ 2 :=
          Finset.sum_congr rfl (fun i hi => hnormp i)
        _ = ∫ x in U, ∑ i : Fin d, (phi x i) ^ 2 := by
          symm
          exact MeasureTheory.integral_finset_sum Finset.univ
            (fun i hi => by
              simpa [U, pow_two] using (hmem i).integrable_mul (hmem i))
    have hpair (i : Fin d) :
        ∫ x in U, (fdom i) x * (pdom i) x =
          ∫ x in U, F x i * phi x i := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [
        (Homogenization.memScalarL2_coord_of_memVectorL2 hF' i).coeFn_toLp,
        (hmem i).coeFn_toLp] with x hxF hxphi
      rw [hxF, hxphi]
    have hnum : (volume.real U)⁻¹ *
        ∫ x in U, vecDot (F x) (phi x) =
        (volume.real U)⁻¹ *
          ∫ x in U, ∑ i : Fin d, (fdom i) x * (pdom i) x := by
      calc
        _ = (volume.real U)⁻¹ *
            ∫ x in U, ∑ i : Fin d, F x i * phi x i := by
          congr 2
          
        _ = (volume.real U)⁻¹ *
            ∑ i : Fin d, ∫ x in U, F x i * phi x i := by
          congr 1
          exact MeasureTheory.integral_finset_sum Finset.univ
            (fun i hi =>
              (Homogenization.memScalarL2_coord_of_memVectorL2 hF' i).integrable_mul
                (hmem i))
        _ = (volume.real U)⁻¹ *
            ∑ i : Fin d, ∫ x in U, (fdom i) x * (pdom i) x := by
          congr 2
          funext i
          exact (hpair i).symm
        _ = (volume.real U)⁻¹ *
            ∫ x in U, ∑ i : Fin d, (fdom i) x * (pdom i) x := by
          congr 1
          have hprod : ∀ i : Fin d, MeasureTheory.Integrable
              (fun x => F x i * phi x i) (volume.restrict U) := by
            intro i
            exact (Homogenization.memScalarL2_coord_of_memVectorL2 hF' i).integrable_mul
              (hmem i)
          have hprod' : ∀ i : Fin d, MeasureTheory.Integrable
              (fun x => (fdom i) x * (pdom i) x) (volume.restrict U) := by
            intro i
            apply (hprod i).congr
            filter_upwards [
              (Homogenization.memScalarL2_coord_of_memVectorL2 hF' i).coeFn_toLp,
              (hmem i).coeFn_toLp] with x hxF hxphi
            rw [hxF, hxphi]
          exact (MeasureTheory.integral_finset_sum Finset.univ
            (fun i hi => hprod' i)).symm
    have hmain :=
      (SubdiffusiveProcess.normalized_coordinate_pairing_div_bound
        z ((3 : Real) ^ m) hr (1 : Real) fdom pdom 0 (by positivity)).2
    have hmain' :
        |(volume.real U)⁻¹ * ∫ x in U, vecDot (F x) (phi x)| /
            ((3 : Real) ^ (-(m : Real)) *
              Real.sqrt (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) /
                Real.sqrt (volume.real U)) ≤
          (3 : Real) ^ (m : Real) *
            (Real.sqrt (∑ i : Fin d, ‖fdom i‖ ^ 2) /
              Real.sqrt (volume.real U)) := by
      rw [hnormpsum] at hmain
      rw [← hnum] at hmain
      have hzpow : (3 : Real) ^ m = (3 : Real) ^ (m : Real) := by
        rw [Real.rpow_intCast]
      have hneg : ((3 : Real) ^ m) ^ (-1 : Real) =
          (3 : Real) ^ (-(m : Real)) := by
        rw [hzpow, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 3)]
        ring_nf
      have hpos : ((3 : Real) ^ m) ^ (1 : Real) =
          (3 : Real) ^ (m : Real) := by
        rw [Real.rpow_one, hzpow]
      rw [hneg, hpos, zero_add] at hmain
      convert hmain using 1 <;> ring
    have hsumint : 0 ≤ ∫ x in U, ∑ i : Fin d, (phi x i) ^ 2 := by
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [] with x
      positivity
    have havg : Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
          (fun x => ∑ i : Fin d, (phi x i) ^ 2) =
        (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) / volume.real U := by
      unfold Homogenization.Book.Ch02.average
      change (volume.real (openCubeSet (originCube d m)))⁻¹ *
          ∫ x in openCubeSet (originCube d m), ∑ i : Fin d, (phi x i) ^ 2 = _
      rw [← hUeq]
      field_simp
    have hExtra :
        (3 : Real) ^ (-(m : Real)) *
            Real.sqrt (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) /
              Real.sqrt (volume.real U) =
        (3 : Real) ^ (-((originCube d m).scale : Real)) *
          Real.sqrt (average (cubeDomain (originCube d m))
            (fun x => ∑ i : Fin d, (phi x i) ^ 2)) := by
      rw [show (originCube d m).scale = m by rfl, havg,
        Real.sqrt_div hsumint]
      have hzpow : (3 : Real) ^ m = (3 : Real) ^ (m : Real) := by
        rw [Real.rpow_intCast]
      have hscale : (3 : Real) ^ (-(m : Real)) =
          ((3 : Real) ^ m) ^ (-1 : Real) := by
        rw [hzpow, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 3)]
        ring_nf
      rw [hscale]
      ring
    have hdenpos' : 0 < (3 : Real) ^ (-(m : Real)) *
          Real.sqrt (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) /
            Real.sqrt (volume.real U) := by
      rw [← hnormpsum]
      positivity
    have hdenle :
        (3 : Real) ^ (-(m : Real)) *
              Real.sqrt (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) /
                Real.sqrt (volume.real U) ≤
        Real.sqrt (average (cubeDomain (originCube d m)) (fun x =>
              ∑ i : Fin d, ∑ j : Fin d,
                (fderiv Real (fun y => phi y i) x (Pi.single j 1)) ^ 2)) +
            (3 : Real) ^ (-((originCube d m).scale : Real)) *
              Real.sqrt (average (cubeDomain (originCube d m)) (fun x =>
                ∑ i : Fin d, (phi x i) ^ 2)) := by
      rw [← hExtra]
      exact le_add_of_nonneg_left (by positivity)
    have hdiv :
        |average (cubeDomain (originCube d m)) (fun x => vecDot (F x) (phi x))| /
          (Real.sqrt (average (cubeDomain (originCube d m)) (fun x =>
              ∑ i : Fin d, ∑ j : Fin d,
                (fderiv Real (fun y => phi y i) x (Pi.single j 1)) ^ 2)) +
            (3 : Real) ^ (-((originCube d m).scale : Real)) *
              Real.sqrt (average (cubeDomain (originCube d m)) (fun x =>
                ∑ i : Fin d, (phi x i) ^ 2))) ≤
        |average (cubeDomain (originCube d m)) (fun x => vecDot (F x) (phi x))| /
          ((3 : Real) ^ (-(m : Real)) *
              Real.sqrt (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) /
                Real.sqrt (volume.real U)) := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) hdenpos' hdenle
    calc
      _ ≤ |average (cubeDomain (originCube d m))
          (fun x => vecDot (F x) (phi x))| /
          ((3 : Real) ^ (-(m : Real)) *
              Real.sqrt (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) /
                Real.sqrt (volume.real U)) := hdiv
      _ ≤ (3 : Real) ^ (m : Real) *
        (Real.sqrt (∑ i : Fin d, ‖fdom i‖ ^ 2) /
          Real.sqrt (volume.real U)) := by
        rw [show Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
              (fun x => vecDot (F x) (phi x)) =
            (volume.real U)⁻¹ * ∫ x in U, vecDot (F x) (phi x) by
          unfold Homogenization.Book.Ch02.average
          rw [hUeq]
          rfl]
        exact hmain'
      _ ≤ (3 : Real) ^ (m : Real) *
          (Real.sqrt (∑ i : Fin d,
            ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hF i).toLp
              (fun x => F x i)‖ ^ 2) /
            Real.sqrt (volume.real (openCubeSet (originCube d m)))) := by
        have hnormfeq (i : Fin d) : ‖fdom i‖ =
            ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hF i).toLp
              (fun x => F x i)‖ := by
          rw [show fdom i =
              (Homogenization.memScalarL2_coord_of_memVectorL2 hF' i).toLp
                (fun x => F x i) by rfl,
            MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
          rw [← hUeq]
        have hnormeq : ∑ i : Fin d, ‖fdom i‖ ^ 2 =
            ∑ i : Fin d, ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hF i).toLp
              (fun x => F x i)‖ ^ 2 := by
          exact Finset.sum_congr rfl (fun i hi => by rw [hnormfeq i])
        rw [hnormeq, hUeq]
  have hBdd : BddAbove (aux_lem_C1_weakSet d (originCube d m) F) :=
    ⟨(3 : Real) ^ (m : Real) *
        (Real.sqrt (∑ i : Fin d,
          ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hF i).toLp
            (fun x => F x i)‖ ^ 2) /
          Real.sqrt (volume.real (openCubeSet (originCube d m)))), hbound⟩
  refine ⟨hBdd, ?_⟩
  by_cases hne : (aux_lem_C1_weakSet d (originCube d m) F).Nonempty
  · exact csSup_le hne hbound
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    positivity

lemma aux_lem_C1_weak_triangle (d : Nat) (m : Int)
    (F G : Homogenization.Vec d → Homogenization.Vec d)
    (hF : Homogenization.MemVectorL2 (openCubeSet (originCube d m)) F)
    (hG : Homogenization.MemVectorL2 (openCubeSet (originCube d m)) G) :
    sSup (aux_lem_C1_weakSet d (originCube d m) (fun x => F x + G x)) ≤
      sSup (aux_lem_C1_weakSet d (originCube d m) F) +
        sSup (aux_lem_C1_weakSet d (originCube d m) G) := by
  obtain ⟨hFBdd, _⟩ := aux_lem_C1_weak_bound d m F hF
  obtain ⟨hGBdd, _⟩ := aux_lem_C1_weak_bound d m G hG
  let hr : (0 : Real) < (3 : Real) ^ m := by positivity
  let z : SubdiffusiveProcess.SpatialCoordinates d := 0
  let U : Set (SubdiffusiveProcess.SpatialCoordinates d) :=
    (SubdiffusiveProcess.centeredCube z ((3 : Real) ^ m) hr : Set _)
  have hUeq : U = openCubeSet (originCube d m) := by
    dsimp [U, z]
    exact SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube m hr
  have hF' : Homogenization.MemVectorL2 U F := by rw [hUeq]; exact hF
  have hG' : Homogenization.MemVectorL2 U G := by rw [hUeq]; exact hG
  have hpoint : ∀ phi ∈ aux_lem_C1_testSet d (originCube d m),
      aux_lem_C1_ratio d (originCube d m) (fun x => F x + G x) phi ≤
        aux_lem_C1_ratio d (originCube d m) F phi +
          aux_lem_C1_ratio d (originCube d m) G phi := by
    intro phi hphi
    obtain ⟨hphi, hnonzero⟩ := hphi
    obtain ⟨hmem, hmem_spec⟩ :=
      SubdiffusiveProcess.continuousOn_cube_memLp_and_nonzero
        z ((3 : Real) ^ m) hr phi hphi.continuous.continuousOn
    have hphiVec : Homogenization.MemVectorL2 U phi := by
      rw [Homogenization.MemVectorL2, MeasureTheory.memLp_pi_iff]
      exact hmem
    have hnonzero' : ∃ x ∈ U, phi x ≠ 0 := by
      change ∃ x ∈ U, phi x ≠ 0
      rw [hUeq]
      exact hnonzero
    have hsumpos : 0 < ∑ i : Fin d,
        ‖(hmem i).toLp (fun x => phi x i)‖ ^ 2 :=
      hmem_spec.mp hnonzero'
    have hV : 0 < volume.real U := by
      dsimp [U]
      exact SubdiffusiveProcess.centeredCube_volume_pos z hr
    have hden : 0 <
        Real.sqrt (average (cubeDomain (originCube d m)) (fun x =>
          ∑ i : Fin d, ∑ j : Fin d,
            (fderiv Real (fun y => phi y i) x (Pi.single j 1)) ^ 2)) +
          (3 : Real) ^ (-((originCube d m).scale : Real)) *
            Real.sqrt (average (cubeDomain (originCube d m)) (fun x =>
              ∑ i : Fin d, (phi x i) ^ 2)) := by
      have hextra : 0 < (3 : Real) ^ (-(m : Real)) *
          Real.sqrt (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) /
            Real.sqrt (volume.real U) := by
        have hnorm : ∑ i : Fin d,
            ‖(hmem i).toLp (fun x => phi x i)‖ ^ 2 =
            ∫ x in U, ∑ i : Fin d, (phi x i) ^ 2 := by
          calc
            _ = ∑ i : Fin d, ∫ x in U, (phi x i) ^ 2 :=
              Finset.sum_congr rfl (fun i hi => by
                rw [MeasureTheory.Lp.norm_toLp]
                exact Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq (hmem i))
            _ = _ := by
              symm
              exact MeasureTheory.integral_finset_sum Finset.univ
                (fun i hi => by
                  simpa [U, pow_two] using (hmem i).integrable_mul (hmem i))
        rw [← hnorm]
        positivity
      have hnonnegA : 0 ≤ Real.sqrt (average (cubeDomain (originCube d m))
          (fun x => ∑ i : Fin d, ∑ j : Fin d,
            (fderiv Real (fun y => phi y i) x (Pi.single j 1)) ^ 2)) :=
        Real.sqrt_nonneg _
      have hextra_eq : (3 : Real) ^ (-(m : Real)) *
          Real.sqrt (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) /
            Real.sqrt (volume.real U) =
          (3 : Real) ^ (-((originCube d m).scale : Real)) *
            Real.sqrt (average (cubeDomain (originCube d m))
              (fun x => ∑ i : Fin d, (phi x i) ^ 2)) := by
        have hsum : 0 ≤ ∫ x in U, ∑ i : Fin d, (phi x i) ^ 2 := by
          apply MeasureTheory.integral_nonneg_of_ae
          filter_upwards [] with x
          positivity
        have havg : Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
              (fun x => ∑ i : Fin d, (phi x i) ^ 2) =
            (∫ x in U, ∑ i : Fin d, (phi x i) ^ 2) / volume.real U := by
          unfold Homogenization.Book.Ch02.average
          change (volume.real (openCubeSet (originCube d m)))⁻¹ *
              ∫ x in openCubeSet (originCube d m), ∑ i : Fin d, (phi x i) ^ 2 = _
          rw [← hUeq]
          field_simp
        rw [show (originCube d m).scale = m by rfl, havg,
          Real.sqrt_div hsum]
        ring
      rw [← hextra_eq]
      exact lt_of_lt_of_le hextra (le_add_of_nonneg_left hnonnegA)
    have hlin :
        Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
            (fun x => vecDot ((F x) + (G x)) (phi x)) =
          Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
            (fun x => vecDot (F x) (phi x)) +
          Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
            (fun x => vecDot (G x) (phi x)) := by
      unfold Homogenization.Book.Ch02.average
      simp only [Homogenization.Book.Ch02.cubeDomain_coe]
      rw [← hUeq]
      rw [show (fun x => vecDot (F x + G x) (phi x)) =
          (fun x => vecDot (F x) (phi x) + vecDot (G x) (phi x)) by
            funext x
            simp only [Homogenization.vecDot]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Pi.add_apply]
            ring]
      rw [MeasureTheory.integral_add
        (Homogenization.integrableOn_vecDot_of_memVectorL2 hF' hphiVec)
        (Homogenization.integrableOn_vecDot_of_memVectorL2 hG' hphiVec)]
      ring
    unfold aux_lem_C1_ratio
    rw [hlin]
    calc
      |Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
            (fun x => vecDot (F x) (phi x)) +
          Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
            (fun x => vecDot (G x) (phi x))| / _ ≤
          (|Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
            (fun x => vecDot (F x) (phi x))| +
            |Homogenization.Book.Ch02.average (cubeDomain (originCube d m))
            (fun x => vecDot (G x) (phi x))|) / _ :=
        div_le_div_of_nonneg_right (abs_add_le _ _) hden.le
      _ = _ := by rw [add_div]
  by_cases hne : (aux_lem_C1_weakSet d (originCube d m)
      (fun x => F x + G x)).Nonempty
  · apply csSup_le hne
    rintro r ⟨phi, hphi, rfl⟩
    have hFmem : aux_lem_C1_ratio d (originCube d m) F phi ∈
        aux_lem_C1_weakSet d (originCube d m) F := ⟨phi, hphi, rfl⟩
    have hGmem : aux_lem_C1_ratio d (originCube d m) G phi ∈
        aux_lem_C1_weakSet d (originCube d m) G := ⟨phi, hphi, rfl⟩
    exact (hpoint phi hphi).trans (add_le_add
      (le_csSup hFBdd hFmem) (le_csSup hGBdd hGmem))
  · have htestempty : (aux_lem_C1_testSet d (originCube d m)).Nonempty →
        (aux_lem_C1_weakSet d (originCube d m)
          (fun x => F x + G x)).Nonempty := by
      rintro ⟨phi, hphi⟩
      exact ⟨aux_lem_C1_ratio d (originCube d m) (fun x => F x + G x) phi,
        ⟨phi, hphi, rfl⟩⟩
    have htest : ¬(aux_lem_C1_testSet d (originCube d m)).Nonempty := by
      intro ht
      exact hne (htestempty ht)
    have hFempty : aux_lem_C1_weakSet d (originCube d m) F = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro r hr
      rcases hr with ⟨phi, hphi, rfl⟩
      exact htest ⟨phi, hphi⟩
    have hGempty : aux_lem_C1_weakSet d (originCube d m) G = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro r hr
      rcases hr with ⟨phi, hphi, rfl⟩
      exact htest ⟨phi, hphi⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hne, hFempty, hGempty,
      Real.sSup_empty, add_zero]

lemma aux_lem_C1_weak_const_bound (d : Nat) (m : Int)
    (b : Homogenization.Vec d) :
    sSup (aux_lem_C1_weakSet d (originCube d m) (fun _ => b)) ≤
      (3 : Real) ^ (m : Real) * Real.sqrt (∑ i : Fin d, (b i) ^ 2) := by
  let U := openCubeSet (originCube d m)
  have hU : 0 < volume.real U := by
    let hr : (0 : Real) < (3 : Real) ^ m := by positivity
    change 0 < volume.real (openCubeSet (originCube d m))
    rw [← SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube m hr]
    exact SubdiffusiveProcess.centeredCube_volume_pos 0 hr
  have hconst : Homogenization.MemVectorL2 U (fun _ => b) := by
    exact Homogenization.memVectorL2_const b
  obtain ⟨hBdd, hbound⟩ := aux_lem_C1_weak_bound d m (fun _ => b) hconst
  have hnorm (i : Fin d) :
      ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hconst i).toLp
          (fun _ => b i)‖ ^ 2 = volume.real U * (b i) ^ 2 := by
    rw [MeasureTheory.Lp.norm_toLp]
    rw [Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq
      (Homogenization.memScalarL2_coord_of_memVectorL2 hconst i)]
    simp only [MeasureTheory.integral_const, volumeMeasureOn,
      MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul]
  have hsum :
      ∑ i : Fin d,
        ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hconst i).toLp
            (fun _ => b i)‖ ^ 2 =
        volume.real U * ∑ i : Fin d, (b i) ^ 2 := by
    calc
      _ = ∑ i : Fin d, volume.real U * (b i) ^ 2 :=
        Finset.sum_congr rfl (fun i hi => hnorm i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hquot :
      Real.sqrt
          (∑ i : Fin d,
            ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hconst i).toLp
                (fun _ => b i)‖ ^ 2) /
          Real.sqrt (volume.real U) =
        Real.sqrt (∑ i : Fin d, (b i) ^ 2) := by
    rw [hsum, Real.sqrt_mul (hU.le)]
    field_simp [ne_of_gt hU]
  calc
    sSup (aux_lem_C1_weakSet d (originCube d m) (fun _ => b)) ≤
        (3 : Real) ^ (m : Real) *
          (Real.sqrt (∑ i : Fin d,
            ‖(Homogenization.memScalarL2_coord_of_memVectorL2 hconst i).toLp
                (fun _ => b i)‖ ^ 2) /
            Real.sqrt (volume.real U)) := by
      simpa [U] using hbound
    _ = (3 : Real) ^ (m : Real) * Real.sqrt (∑ i : Fin d, (b i) ^ 2) := by
      rw [hquot]

lemma aux_lem_C1_defect_nonneg (d : Nat)
    (a : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (m n : Int) (hnm : n ≤ m) (p q : Homogenization.Vec d) :
    0 ≤
      (3 : Real) ^ (-(d : Real) * ((m : Real) - (n : Real))) *
          (∑ Q ∈ descendantsAtScale (originCube d m) n,
            responseJ (cubeDomain Q) (a.coeffOn Q) p q) -
        responseJ (cubeDomain (originCube d m))
          (a.coeffOn (originCube d m)) p q := by
  let Q := originCube d m
  let j := Int.toNat (m - n)
  let ap : Homogenization.Book.Ch02.CoeffOn (cubeDomain Q) :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn
      (cubeDomain Q) (a.coeffOn Q)
  have hEll : IsEllipticFieldOn ap.lam ap.Lam (openCubeSet Q) ap.toCoeffField := by
    simpa [ap] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hOld :
      Homogenization.ResponseJ (openCubeSet Q) p q ap.toCoeffField ≤
        descendantsAverage Q j
          (fun R => Homogenization.ResponseJ (openCubeSet R) p q ap.toCoeffField) :=
    responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
      j Q ap.toCoeffField hEll p q
  have hLeft :
      responseJ (cubeDomain Q) (a.coeffOn Q) p q =
        Homogenization.ResponseJ (openCubeSet Q) p q ap.toCoeffField := by
    calc
      responseJ (cubeDomain Q) (a.coeffOn Q) p q =
          responseJ (cubeDomain Q) ap p q := by
            rw [Homogenization.Book.Ch02.responseJ_eq_ofAEEq]
            simpa [ap] using
              (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq
                (cubeDomain Q) (a.coeffOn Q)).symm
      _ = Homogenization.ResponseJ (openCubeSet Q) p q ap.toCoeffField := by
            rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
            rfl
  have hRespCell :
      ∀ R ∈ descendantsAtDepth Q j,
        responseJ (cubeDomain R) (a.coeffOn R) p q =
          Homogenization.ResponseJ (openCubeSet R) p q ap.toCoeffField := by
    intro R hR
    have hsub : (openCubeSet R : Set (Homogenization.Vec d)) ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllCell :
        IsEllipticFieldOn ap.lam ap.Lam (openCubeSet R) ap.toCoeffField :=
      IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet R) hsub
    let apCell : Homogenization.Book.Ch02.CoeffOn (cubeDomain R) := {
      toCoeffField := ap.toCoeffField
      lam := ap.lam
      Lam := ap.Lam
      lam_pos := ap.lam_pos
      lam_le_Lam := ap.lam_le_Lam
      aeStronglyMeasurable := by
        intro i k
        have hentry : Measurable (fun x : Homogenization.Vec d =>
            restrictCoeffField (openCubeSet R) ap.toCoeffField x i k) := by
          have hik := (measurable_pi_iff.1 (measurable_pi_iff.1 hEllCell.1 i) k)
          convert hik using 1
          funext x
          by_cases hx : x ∈ openCubeSet R <;>
            simp [restrictCoeffField, hx]
        exact hentry.aestronglyMeasurable
      aeElliptic := by
        filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet R)]
          with x hx
        exact hEllCell.2 x hx }
    have hrestrict : CoeffOn.RestrictsTo (a.coeffOn Q) (a.coeffOn R) := by
      have : R ∈ descendantsAtScale Q n := by
        rw [descendantsAtScale_eq_descendantsAtDepth Q hnm]
        simpa [Q, j] using hR
      exact a.restrictsTo_descendant (Q := Q) (R := R) (k := n)
        (by simpa [Q] using hnm) this
    have hapaCell : CoeffOn.AEEq apCell (a.coeffOn R) := by
      have hpoint :
          ap.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)]
            (a.coeffOn Q).toCoeffField := by
        simpa [ap, volumeMeasureOn] using
          (MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub
            (by
              simpa [ap, volumeMeasureOn] using
                (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq
                  (cubeDomain Q) (a.coeffOn Q))))
      change ap.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)]
        (a.coeffOn R).toCoeffField
      exact hpoint.trans hrestrict.symm
    calc
      responseJ (cubeDomain R) (a.coeffOn R) p q =
          responseJ (cubeDomain R) apCell p q := by
            rw [Homogenization.Book.Ch02.responseJ_eq_ofAEEq hapaCell]
      _ = Homogenization.ResponseJ (openCubeSet R) p q ap.toCoeffField := by
            rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
            rfl
  have hscale : descendantsAtScale Q n = descendantsAtDepth Q j := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hnm]
    rfl
  have havg :
      responseJ (cubeDomain Q) (a.coeffOn Q) p q ≤
        ((descendantsAtDepth Q j).card : Real)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j,
            responseJ (cubeDomain R) (a.coeffOn R) p q := by
    rw [hLeft]
    calc
      Homogenization.ResponseJ (openCubeSet Q) p q ap.toCoeffField ≤
          descendantsAverage Q j
            (fun R => Homogenization.ResponseJ (openCubeSet R) p q ap.toCoeffField) := hOld
      _ = _ := by
        unfold descendantsAverage
        dsimp
        congr 1
        apply Finset.sum_congr rfl
        intro R hR
        rw [← hRespCell R hR]
  have hcard : (descendantsAtDepth Q j).card = (3 ^ d) ^ j :=
    descendantsAtDepth_card Q j
  have hpow :
      ((descendantsAtDepth Q j).card : Real)⁻¹ =
        (3 : Real) ^ (-(d : Real) * ((m : Real) - (n : Real))) := by
    have hcardR : ((descendantsAtDepth Q j).card : Real) =
        (((3 ^ d) ^ j : Nat) : Real) := by
      rw [hcard]
    rw [hcardR]
    have htoNat : (Int.toNat (m - n) : Int) = m - n := by
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hnm)
    rw [show j = Int.toNat (m - n) by rfl]
    norm_num
    rw [show ((3 ^ d) ^ Int.toNat (m - n) : Real) =
        (3 : Real) ^ ((d : Real) * ((m : Real) - (n : Real))) by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : Real) ≤ 3)]
      congr 1
      have htoNatR : (Int.toNat (m - n) : Real) =
          (m : Real) - (n : Real) := by
        exact_mod_cast htoNat
      rw [htoNatR]]
    rw [← Real.rpow_neg (by norm_num : (0 : Real) ≤ 3)]
  rw [hscale]
  calc
    0 ≤ ((descendantsAtDepth Q j).card : Real)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          responseJ (cubeDomain R) (a.coeffOn R) p q -
        responseJ (cubeDomain Q) (a.coeffOn Q) p q :=
      sub_nonneg.mpr havg
    _ = (3 : Real) ^ (-(d : Real) * ((m : Real) - (n : Real))) *
          ∑ R ∈ descendantsAtDepth Q j,
            responseJ (cubeDomain R) (a.coeffOn R) p q -
        responseJ (cubeDomain Q) (a.coeffOn Q) p q := by rw [hpow]

lemma aux_lem_C1_geom_sum (ell m : Int) (r : Real)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ell ≤ m) :
    ∑ n ∈ Finset.Icc ell m, r ^ (Int.toNat (m - n)) ≤ (1 - r)⁻¹ := by
  let k : Nat := Int.toNat (m - ell)
  have hk : (k : Int) = m - ell := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr h)
  have hsum :
      ∑ n ∈ Finset.Icc ell m, r ^ (Int.toNat (m - n)) =
        ∑ z ∈ Finset.range (k + 1), r ^ z := by
    apply Finset.sum_bij' (fun n _ => Int.toNat (m - n))
      (fun z _ => m - (z : Int))
    · intro n hn
      simp only [Finset.mem_range]
      have hnle : n ≤ m := (Finset.mem_Icc.mp hn).2
      have hnge : ell ≤ n := (Finset.mem_Icc.mp hn).1
      have hnon : 0 ≤ m - n := sub_nonneg.mpr hnle
      apply (Int.toNat_lt_of_ne_zero (n := k + 1) (by omega)).2
      norm_num [Int.ofNat_add]
      rw [hk]
      omega
    · intro z hz
      simp only [Finset.mem_Icc]
      have hz0 : 0 ≤ (z : Int) := by omega
      have hzlt : z < k + 1 := Finset.mem_range.mp hz
      have hzkNat : z ≤ k := by omega
      have hzk : (z : Int) ≤ (k : Int) := by exact_mod_cast hzkNat
      omega
    · intro n hn
      have hnle : n ≤ m := (Finset.mem_Icc.mp hn).2
      have hnon : 0 ≤ m - n := sub_nonneg.mpr hnle
      rw [Int.toNat_of_nonneg hnon]
      omega
    · intro z hz
      have hz0 : 0 ≤ (z : Int) := by omega
      rw [show m - (m - (z : Int)) = (z : Int) by ring]
      have hcast : (Int.toNat (z : Int) : Int) = (z : Int) :=
        Int.toNat_of_nonneg hz0
      exact_mod_cast hcast
    · intro n hn
      rfl
  rw [hsum]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (sub_pos.mpr hr1)).2
  have hgeom := geom_sum_mul_of_le_one (x := r) hr1.le (k + 1)
  have hpow : 0 ≤ r ^ (k + 1) := pow_nonneg hr0 _
  nlinarith

lemma aux_lem_C1_four_square (x₁ x₂ x₃ x₄ : Real) :
    (x₁ + x₂ + x₃ + x₄) ^ 2 ≤
      4 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) := by
  nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃),
    sq_nonneg (x₁ - x₄), sq_nonneg (x₂ - x₃),
    sq_nonneg (x₂ - x₄), sq_nonneg (x₃ - x₄)]

lemma aux_lem_C1_weighted_square (s : Finset Int) (w x : Int → Real)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hsum : ∑ i ∈ s, w i ≤ 2) :
    (∑ i ∈ s, w i * Real.sqrt (x i)) ^ 2 ≤
      2 * ∑ i ∈ s, w i * x i := by
  have hc :
      (∑ i ∈ s, w i * Real.sqrt (x i)) ^ 2 ≤
        (∑ i ∈ s, w i) * ∑ i ∈ s, w i * x i := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s hw
      (fun i hi => mul_nonneg (hw i hi) (hx i hi))
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hx i hi)]
    ring
  have hnon : 0 ≤ ∑ i ∈ s, w i * x i := by
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hx i hi))
  nlinarith

lemma aux_lem_C1_square_le (x y z : Real) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hxy : x ≤ y + z) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * z ^ 2 := by
  have hsq : x ^ 2 ≤ (y + z) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (y - z)]

lemma aux_lem_C1_weight_one (m n : Int) (h : n ≤ m) :
    (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) =
      ((3 : Real) ^ (-(3 / 4 : Real))) ^ Int.toNat (m - n) := by
  have hto : (Int.toNat (m - n) : Int) = m - n :=
    Int.toNat_of_nonneg (sub_nonneg.mpr h)
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : Real) ≤ 3)]
  congr 1
  have htoR : (Int.toNat (m - n) : Real) =
      (m : Real) - (n : Real) := by
    exact_mod_cast hto
  rw [htoR]
  ring

lemma aux_lem_C1_weight_two (m n : Int) (h : n ≤ m) :
    (3 : Real) ^ (-((m : Real) - (n : Real))) =
      ((3 : Real) ^ (-1 : Real)) ^ Int.toNat (m - n) := by
  have hto : (Int.toNat (m - n) : Int) = m - n :=
    Int.toNat_of_nonneg (sub_nonneg.mpr h)
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : Real) ≤ 3)]
  congr 1
  have htoR : (Int.toNat (m - n) : Real) =
      (m : Real) - (n : Real) := by
    exact_mod_cast hto
  rw [htoR]
  ring

lemma aux_lem_C1_rpow_three_quarter :
    (2 : Real) ≤ (3 : Real) ^ (3 / 4 : Real) := by
  have hpow : ((3 : Real) ^ (3 / 4 : Real)) ^ 4 = 27 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 3)]
    norm_num
  by_contra hnot
  have hlt : (3 : Real) ^ (3 / 4 : Real) < 2 := lt_of_not_ge hnot
  have hpowlt := pow_lt_pow_left₀ hlt (by positivity : 0 ≤ (3 : Real) ^ (3 / 4 : Real))
    (by norm_num : 4 ≠ 0)
  nlinarith

lemma aux_lem_C1_inv_le_half_of_two_le (x : Real) (hx : 0 < x)
    (h : 2 ≤ x) : x⁻¹ ≤ (1 / 2 : Real) := by
  apply (inv_le_iff_one_le_mul₀' hx).2
  nlinarith

lemma aux_lem_C1_inv_sub_le_two (r : Real) (hr : r < 1)
    (hrhalf : r ≤ (1 / 2 : Real)) : (1 - r)⁻¹ ≤ 2 := by
  apply (inv_le_iff_one_le_mul₀' (sub_pos.mpr hr)).2
  nlinarith

lemma aux_lem_C1_square_mono (x y : Real) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  nlinarith

lemma aux_lem_C1_constant_base (x y z u : Real)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hu : 0 ≤ u) :
    64 * x * y ^ 2 ≤
      100000 * (1 + x) * (1 + y) ^ 2 * (1 + z) * (1 + u) := by
  have hxy : x ≤ 1 + x := le_add_of_nonneg_left (by norm_num)
  have hysq : y ^ 2 ≤ (1 + y) ^ 2 :=
    aux_lem_C1_square_mono y (1 + y) hy
      (add_nonneg (by norm_num) hy)
      (le_add_of_nonneg_left (by norm_num))
  have hA : 0 ≤ (1 + x) * (1 + y) ^ 2 :=
    mul_nonneg (add_nonneg (by norm_num) hx) (sq_nonneg _)
  have hfactor : 1 ≤ (1 + z) * (1 + u) := by
    have hz1 : 1 ≤ 1 + z := le_add_of_nonneg_right hz
    have hu1 : 1 ≤ 1 + u := le_add_of_nonneg_right hu
    calc
      1 = 1 * 1 := by ring
      _ ≤ (1 + z) * 1 :=
        mul_le_mul_of_nonneg_right hz1 (by norm_num)
      _ ≤ (1 + z) * (1 + u) :=
        mul_le_mul_of_nonneg_left hu1 (by positivity)
  calc
    64 * x * y ^ 2 ≤ 64 * (1 + x) * (1 + y) ^ 2 := by
      calc
        64 * x * y ^ 2 = (64 * x) * y ^ 2 := by ring
        _ ≤ (64 * (1 + x)) * y ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hxy (by norm_num)) (sq_nonneg _)
        _ ≤ (64 * (1 + x)) * (1 + y) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hysq (by positivity)
        _ = 64 * (1 + x) * (1 + y) ^ 2 := by ring
    _ ≤ 100000 * (1 + x) * (1 + y) ^ 2 * (1 + z) * (1 + u) := by
      have hscale : 64 * ((1 + x) * (1 + y) ^ 2) ≤
          100000 * ((1 + x) * (1 + y) ^ 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) hA
      have htail : 100000 * ((1 + x) * (1 + y) ^ 2) ≤
          (100000 * ((1 + x) * (1 + y) ^ 2)) *
            ((1 + z) * (1 + u)) :=
        le_mul_of_one_le_right (by positivity) hfactor
      calc
        64 * (1 + x) * (1 + y) ^ 2 ≤
            100000 * (1 + x) * (1 + y) ^ 2 := by
              simpa only [mul_assoc] using hscale
        _ ≤ (100000 * ((1 + x) * (1 + y) ^ 2)) *
              ((1 + z) * (1 + u)) := by
                simpa only [mul_assoc] using htail
        _ = 100000 * (1 + x) * (1 + y) ^ 2 * (1 + z) * (1 + u) := by
          ring

lemma aux_lem_C1_constant_base_U (x y z u : Real)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hu : 0 ≤ u) :
    10 * x * (1 + y) ^ 2 ≤
      100000 * (1 + x) * (1 + y) ^ 2 * (1 + z) * (1 + u) := by
  have hxy : x ≤ 1 + x := le_add_of_nonneg_left (by norm_num)
  have hA : 0 ≤ (1 + x) * (1 + y) ^ 2 :=
    mul_nonneg (add_nonneg (by norm_num) hx) (sq_nonneg _)
  have hfactor : 1 ≤ (1 + z) * (1 + u) := by
    have hz1 : 1 ≤ 1 + z := le_add_of_nonneg_right hz
    have hu1 : 1 ≤ 1 + u := le_add_of_nonneg_right hu
    calc
      1 = 1 * 1 := by ring
      _ ≤ (1 + z) * 1 :=
        mul_le_mul_of_nonneg_right hz1 (by norm_num)
      _ ≤ (1 + z) * (1 + u) :=
        mul_le_mul_of_nonneg_left hu1 (by positivity)
  calc
    10 * x * (1 + y) ^ 2 ≤ 10 * (1 + x) * (1 + y) ^ 2 := by
      calc
        10 * x * (1 + y) ^ 2 = (10 * x) * (1 + y) ^ 2 := by ring
        _ ≤ (10 * (1 + x)) * (1 + y) ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hxy (by norm_num)) (sq_nonneg _)
        _ = 10 * (1 + x) * (1 + y) ^ 2 := by ring
    _ ≤ 100000 * (1 + x) * (1 + y) ^ 2 * (1 + z) * (1 + u) := by
      have hscale : 10 * ((1 + x) * (1 + y) ^ 2) ≤
          100000 * ((1 + x) * (1 + y) ^ 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) hA
      have htail : 100000 * ((1 + x) * (1 + y) ^ 2) ≤
          (100000 * ((1 + x) * (1 + y) ^ 2)) *
            ((1 + z) * (1 + u)) :=
        le_mul_of_one_le_right (by positivity) hfactor
      calc
        10 * (1 + x) * (1 + y) ^ 2 ≤
            100000 * (1 + x) * (1 + y) ^ 2 := by
              simpa only [mul_assoc] using hscale
        _ ≤ (100000 * ((1 + x) * (1 + y) ^ 2)) *
              ((1 + z) * (1 + u)) := by
                simpa only [mul_assoc] using htail
        _ = 100000 * (1 + x) * (1 + y) ^ 2 * (1 + z) * (1 + u) := by
          ring

lemma aux_lem_C1_ratio_le_square (x y : Real) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ≤ (1 + x + y) ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (1 + x + y)]

lemma aux_lem_C1_nonneg_eight_sq (x : Real) :
    0 ≤ 8 * x ^ 2 + 2 := by positivity

lemma aux_lem_C1_nonneg_ten_sq (x : Real) :
    0 ≤ 10 * (1 + x) ^ 2 := by positivity

lemma aux_lem_C1_nonneg_sq_mul (x y : Real) (hy : 0 ≤ y) :
    0 ≤ x ^ 2 * y := by
  exact mul_nonneg (sq_nonneg x) hy

lemma aux_lem_C1_fin_sum_sq_nonneg (d : Nat) (b : Fin d → Real) :
    0 ≤ ∑ i : Fin d, (b i) ^ 2 := by
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (b i))

lemma aux_lem_C1_three_rpow_nonneg (x : Real) :
    0 ≤ (3 : Real) ^ x := by
  exact Real.rpow_nonneg (by norm_num) x

lemma aux_lem_C1_pow_two_le_pow_three (x : Real) (hx : 1 ≤ x) :
    x ^ 2 ≤ x ^ 3 := by
  have h := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)
  nlinarith

lemma aux_lem_C1_scalar_u (x : Real) (hx : 0 ≤ x) :
    8 * x ^ 2 + 2 ≤ 10 * (1 + x) ^ 2 := by
  nlinarith [sq_nonneg x]

lemma aux_lem_C1_add_four {a b c e x y z t : Real}
    (ha : a ≤ x) (hb : b ≤ y) (hc : c ≤ z) (he : e ≤ t) :
    a + b + c + e ≤ x + y + z + t := by
  linarith

lemma aux_lem_C1_last_factor (x a : Real) (hx : 0 ≤ x) (ha : 1 ≤ a) :
    2 * x ≤ 100000 * a * (1 + x) := by
  have h0 : 0 ≤ 1 + x := by linarith
  have hfirst : 2 * x ≤ 100000 * (1 + x) := by
    calc
      2 * x ≤ 100000 * x :=
        mul_le_mul_of_nonneg_right (by norm_num) hx
      _ ≤ 100000 * x + 100000 := by
        exact le_add_of_nonneg_right (by norm_num)
      _ = 100000 * (1 + x) := by ring
  have ha' : 100000 ≤ 100000 * a :=
    by simpa using (mul_le_mul_of_nonneg_left ha (by norm_num : (0 : Real) ≤ 100000))
  exact hfirst.trans (mul_le_mul_of_nonneg_right ha' h0)

lemma aux_lem_C1_product_one (x y z w : Real)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    1 ≤ (1 + x) * (1 + y) ^ 2 * (1 + z + w) := by
  have h₁ : 1 ≤ 1 + x := by linarith
  have h₂ : 1 ≤ (1 + y) ^ 2 := by
    nlinarith [sq_nonneg y]
  have h₃ : 1 ≤ 1 + z + w := by linarith
  have h₁₂ : 1 ≤ (1 + x) * (1 + y) ^ 2 := by
    have h := mul_le_mul h₁ h₂ (by norm_num : (0 : Real) ≤ 1)
      (by positivity : (0 : Real) ≤ 1 + x)
    simpa using h
  have h := mul_le_mul h₁₂ h₃ (by norm_num : (0 : Real) ≤ 1)
    (by positivity : (0 : Real) ≤ (1 + x) * (1 + y) ^ 2)
  simpa [mul_assoc] using h

lemma aux_lem_C1_collect
    (d : Nat) (ell m : Int)
    (Cweak Cbesov Lam lam K C G₁ G₂ : Real)
    (D S : Int → Real) (b : Fin d → Real)
    (Jm1 Dm1 JQm SD SS EJ BU : Real)
    (hCweak : 0 < Cweak) (hCbesov : 0 < Cbesov)
    (hLam : 0 < Lam) (hlam : 0 < lam) (hK : 0 < K)
    (hG₁ : 0 ≤ G₁) (hG₂ : 0 ≤ G₂)
    (hDm1 : 0 ≤ Dm1) (hJQm : 0 ≤ JQm)
    (hSD : 0 ≤ SD) (hSS : 0 ≤ SS) (hEJ : 0 ≤ EJ) (hBU : 0 ≤ BU)
    (hC : C = 100000 * (1 + Cweak) * (1 + Cbesov) ^ 2 *
      (1 + (3 : Real) ^ d) * (1 + G₁ + G₂))
    (hKdef : K = 1 + Lam + lam ^ (-1 : Real))
    (hJbound : Jm1 ≤
      Cweak * Lam * Real.sqrt (Lam / lam) *
        (32 * Cbesov ^ 2 * lam⁻¹ * SD +
          32 * Cbesov ^ 2 * SS +
          64 * Cbesov ^ 2 * lam⁻¹ * EJ +
          (8 * Cbesov ^ 2 + 2) * BU) +
        2 * (3 : Real) ^ d * Dm1)
    (hSDSS : SD + SS =
      ∑ n ∈ Finset.Icc ell m,
        (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) *
          (D n + S n))
    (hEJdef : EJ =
      ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * JQm)
    (hBUdef : BU = ∑ i : Fin d, (b i) ^ 2) :
    Jm1 ≤ C * K ^ 3 *
        ((∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) *
              (D n + S n)) +
          (∑ i : Fin d, (b i) ^ 2) +
          (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 2)) * JQm) +
      C * Dm1 := by
  have hlam_inv_nonneg : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  have hlam_inv_le_K : lam⁻¹ ≤ K := by
    rw [hKdef, Real.rpow_neg_one]
    linarith only [hLam.le]
  have hLam_le_K : Lam ≤ K := by
    rw [hKdef, Real.rpow_neg_one]
    linarith only [hlam_inv_nonneg]
  have hratio_nonneg : 0 ≤ Lam / lam := div_nonneg hLam.le hlam.le
  have hratio_le : Lam / lam ≤ K ^ 2 := by
    rw [div_eq_mul_inv, hKdef, Real.rpow_neg_one]
    exact aux_lem_C1_ratio_le_square Lam lam⁻¹ hLam.le hlam_inv_nonneg
  have hsqrt_ratio_le : Real.sqrt (Lam / lam) ≤ K := by
    have hs := Real.sq_sqrt hratio_nonneg
    nlinarith only [hs, hratio_le, hK.le]
  have hP_le : Cweak * Lam * Real.sqrt (Lam / lam) ≤ Cweak * K ^ 2 := by
    have hp := mul_le_mul_of_nonneg_right hLam_le_K
      (Real.sqrt_nonneg (Lam / lam))
    have hp' : Lam * Real.sqrt (Lam / lam) ≤ K * K := by
      calc
        Lam * Real.sqrt (Lam / lam) ≤ K * Real.sqrt (Lam / lam) := hp
        _ ≤ K * K := mul_le_mul_of_nonneg_left hsqrt_ratio_le hK.le
    have hh := mul_le_mul_of_nonneg_left hp' hCweak.le
    simpa only [mul_assoc, pow_two] using hh
  have hCbase : 64 * Cweak * Cbesov ^ 2 ≤ C := by
    rw [hC]
    simpa only [mul_assoc, add_assoc] using
      (aux_lem_C1_constant_base Cweak Cbesov ((3 : Real) ^ d)
        (G₁ + G₂) hCweak.le hCbesov.le (by positivity)
        (add_nonneg hG₁ hG₂))
  have hCbaseU : 10 * Cweak * (1 + Cbesov) ^ 2 ≤ C := by
    rw [hC]
    simpa only [mul_assoc, add_assoc] using
      (aux_lem_C1_constant_base_U Cweak Cbesov ((3 : Real) ^ d)
        (G₁ + G₂) hCweak.le hCbesov.le (by positivity)
        (add_nonneg hG₁ hG₂))
  have hK_one : 1 ≤ K := by
    rw [hKdef, Real.rpow_neg_one]
    calc
      1 ≤ 1 + Lam := le_add_of_nonneg_right hLam.le
      _ ≤ 1 + Lam + lam⁻¹ := le_add_of_nonneg_right hlam_inv_nonneg
  have hcoefD :
      (Cweak * Lam * Real.sqrt (Lam / lam)) *
          (32 * Cbesov ^ 2 * lam⁻¹) ≤ C * K ^ 3 := by
    have hfac : 0 ≤ 32 * Cbesov ^ 2 * lam⁻¹ := by positivity
    have hfac_le : 32 * Cbesov ^ 2 * lam⁻¹ ≤ 64 * Cbesov ^ 2 * K := by
      calc
        32 * Cbesov ^ 2 * lam⁻¹ = (32 * Cbesov ^ 2) * lam⁻¹ := by ring
        _ ≤ (32 * Cbesov ^ 2) * K :=
          mul_le_mul_of_nonneg_left hlam_inv_le_K (by positivity)
        _ ≤ (64 * Cbesov ^ 2) * K := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg Cbesov)) hK.le
        _ = 64 * Cbesov ^ 2 * K := by ring
    calc
      _ ≤ (Cweak * K ^ 2) * (32 * Cbesov ^ 2 * lam⁻¹) :=
        mul_le_mul_of_nonneg_right hP_le hfac
      _ ≤ (Cweak * K ^ 2) * (64 * Cbesov ^ 2 * K) :=
        mul_le_mul_of_nonneg_left hfac_le (mul_nonneg hCweak.le (sq_nonneg K))
      _ = (64 * Cweak * Cbesov ^ 2) * K ^ 3 := by ring
      _ ≤ C * K ^ 3 :=
        mul_le_mul_of_nonneg_right hCbase (pow_nonneg hK.le 3)
  have hcoefS :
      (Cweak * Lam * Real.sqrt (Lam / lam)) *
          (32 * Cbesov ^ 2) ≤ C * K ^ 3 := by
    have hfac : 0 ≤ 32 * Cbesov ^ 2 := by positivity
    have hKsq_le : K ^ 2 ≤ K ^ 3 := aux_lem_C1_pow_two_le_pow_three K hK_one
    calc
      _ ≤ (Cweak * K ^ 2) * (32 * Cbesov ^ 2) :=
        mul_le_mul_of_nonneg_right hP_le hfac
      _ ≤ (Cweak * K ^ 2) * (64 * Cbesov ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg Cbesov))
          (mul_nonneg hCweak.le (sq_nonneg K))
      _ ≤ (Cweak * K ^ 3) * (64 * Cbesov ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKsq_le hCweak.le) (by positivity)
      _ = (64 * Cweak * Cbesov ^ 2) * K ^ 3 := by ring
      _ ≤ C * K ^ 3 :=
        mul_le_mul_of_nonneg_right hCbase (pow_nonneg hK.le 3)
  have hcoefJ :
      (Cweak * Lam * Real.sqrt (Lam / lam)) *
          (64 * Cbesov ^ 2 * lam⁻¹) ≤ C * K ^ 3 := by
    have hfac : 0 ≤ 64 * Cbesov ^ 2 * lam⁻¹ := by positivity
    have hfac_le : 64 * Cbesov ^ 2 * lam⁻¹ ≤ 64 * Cbesov ^ 2 * K :=
      mul_le_mul_of_nonneg_left hlam_inv_le_K (by positivity)
    calc
      _ ≤ (Cweak * K ^ 2) * (64 * Cbesov ^ 2 * lam⁻¹) :=
        mul_le_mul_of_nonneg_right hP_le hfac
      _ ≤ (Cweak * K ^ 2) * (64 * Cbesov ^ 2 * K) :=
        mul_le_mul_of_nonneg_left hfac_le (mul_nonneg hCweak.le (sq_nonneg K))
      _ = (64 * Cweak * Cbesov ^ 2) * K ^ 3 := by ring
      _ ≤ C * K ^ 3 :=
        mul_le_mul_of_nonneg_right hCbase (pow_nonneg hK.le 3)
  have hscalarU : 8 * Cbesov ^ 2 + 2 ≤ 10 * (1 + Cbesov) ^ 2 :=
    aux_lem_C1_scalar_u Cbesov hCbesov.le
  have hcoefU :
      (Cweak * Lam * Real.sqrt (Lam / lam)) *
          (8 * Cbesov ^ 2 + 2) ≤ C * K ^ 3 := by
    have hfac : 0 ≤ 8 * Cbesov ^ 2 + 2 := aux_lem_C1_nonneg_eight_sq _
    have hfac' : 0 ≤ 10 * (1 + Cbesov) ^ 2 := aux_lem_C1_nonneg_ten_sq _
    have hKsq_le : K ^ 2 ≤ K ^ 3 := aux_lem_C1_pow_two_le_pow_three K hK_one
    calc
      _ ≤ (Cweak * K ^ 2) * (8 * Cbesov ^ 2 + 2) :=
        mul_le_mul_of_nonneg_right hP_le hfac
      _ ≤ (Cweak * K ^ 2) * (10 * (1 + Cbesov) ^ 2) :=
        mul_le_mul_of_nonneg_left hscalarU (mul_nonneg hCweak.le (sq_nonneg K))
      _ ≤ (Cweak * K ^ 3) * (10 * (1 + Cbesov) ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKsq_le hCweak.le) hfac'
      _ = (10 * Cweak * (1 + Cbesov) ^ 2) * K ^ 3 := by ring
      _ ≤ C * K ^ 3 :=
        mul_le_mul_of_nonneg_right hCbaseU (pow_nonneg hK.le 3)
  have hpart :
      (Cweak * Lam * Real.sqrt (Lam / lam)) *
          (32 * Cbesov ^ 2 * lam⁻¹ * SD +
            32 * Cbesov ^ 2 * SS +
            64 * Cbesov ^ 2 * lam⁻¹ * EJ +
            (8 * Cbesov ^ 2 + 2) * BU) ≤
        C * K ^ 3 * (SD + SS + EJ + BU) := by
    have h1 := mul_le_mul_of_nonneg_right hcoefD hSD
    have h2 := mul_le_mul_of_nonneg_right hcoefS hSS
    have h3 := mul_le_mul_of_nonneg_right hcoefJ hEJ
    have h4 := mul_le_mul_of_nonneg_right hcoefU hBU
    calc
      _ = ((Cweak * Lam * Real.sqrt (Lam / lam)) *
              (32 * Cbesov ^ 2 * lam⁻¹)) * SD +
            ((Cweak * Lam * Real.sqrt (Lam / lam)) *
              (32 * Cbesov ^ 2)) * SS +
            ((Cweak * Lam * Real.sqrt (Lam / lam)) *
              (64 * Cbesov ^ 2 * lam⁻¹)) * EJ +
            ((Cweak * Lam * Real.sqrt (Lam / lam)) *
              (8 * Cbesov ^ 2 + 2)) * BU := by ring
      _ ≤ C * K ^ 3 * SD + C * K ^ 3 * SS +
          C * K ^ 3 * EJ + C * K ^ 3 * BU :=
            aux_lem_C1_add_four h1 h2 h3 h4
      _ = C * K ^ 3 * (SD + SS + EJ + BU) := by ring
  have hJbound' :
      Jm1 ≤ C * K ^ 3 * (SD + SS + EJ + BU) +
          2 * (3 : Real) ^ d * Dm1 := by
    exact le_trans hJbound (add_le_add hpart (le_refl _))
  have hClast : 2 * (3 : Real) ^ d ≤ C := by
    rw [hC]
    have hA : 1 ≤ (1 + Cweak) * (1 + Cbesov) ^ 2 *
        (1 + G₁ + G₂) :=
      aux_lem_C1_product_one Cweak Cbesov G₁ G₂
        hCweak.le hCbesov.le hG₁ hG₂
    have hh := aux_lem_C1_last_factor ((3 : Real) ^ d)
      ((1 + Cweak) * (1 + Cbesov) ^ 2 * (1 + G₁ + G₂))
      (by positivity) hA
    convert hh using 1 <;> ring
  have hlast : 2 * (3 : Real) ^ d * Dm1 ≤ C * Dm1 :=
    mul_le_mul_of_nonneg_right hClast hDm1
  have htarget :
      C * K ^ 3 * (SD + SS + EJ + BU) + C * Dm1 ≤
        C * K ^ 3 *
            ((∑ n ∈ Finset.Icc ell m,
                (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) *
                  (D n + S n)) +
              (∑ i : Fin d, (b i) ^ 2) +
              (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 2)) * JQm) +
          C * Dm1 := by
    have hweight :
        ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 =
          (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 3)]
      congr 1
      ring
    rw [hSDSS, hBUdef, hEJdef]
    rw [hweight]
    ring_nf
    exact le_rfl
  exact le_trans (le_trans hJbound' (add_le_add le_rfl hlast)) htarget



theorem lem_C1 (d : Nat) (hd : 2 ≤ d) (hJ : in_J d) :
    let weakNorm : TriadicCube d → (Homogenization.Vec d → Homogenization.Vec d) → Real :=
      fun Q F => sSup {r : Real | ∃ phi : Homogenization.Vec d → Homogenization.Vec d,
        ContDiff Real ∞ phi ∧
        (∃ x ∈ openCubeSet Q, phi x ≠ 0) ∧
        r = |average (cubeDomain Q) (fun x => vecDot (F x) (phi x))| /
          (Real.sqrt (average (cubeDomain Q) (fun x =>
              ∑ i : Fin d, ∑ j : Fin d,
                (fderiv Real (fun y => phi y i) x (Pi.single j 1)) ^ 2)) +
            (3 : Real) ^ (-(Q.scale : Real)) *
              Real.sqrt (average (cubeDomain Q) (fun x =>
                ∑ i : Fin d, (phi x i) ^ 2)))}
    let maximizer := fun (a : TriadicCoeffFamily d) (Q : TriadicCube d) (p q : Homogenization.Vec d) =>
      (canonicalMaximizer (responseExistenceTheory (cubeDomain Q) (a.coeffOn Q)) p q).toSolution
    ∀ (hJWeak : ∃ Cweak : Real, 0 < Cweak ∧
        ∀ a : TriadicCoeffFamily d,
          (∀ Q : TriadicCube d, CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ (m : Int) (p q : Homogenization.Vec d),
            let Qm := originCube d m
            let J := fun Q => responseJ (cubeDomain Q) (a.coeffOn Q) p q
            let Lam := LambdaSq Qm (1 / 4) (.finite 1) a
            let lam := lambdaSq Qm (1 / 4) (.finite 1) a
            J (originCube d (m - 1)) ≤
              Cweak * Lam * Real.sqrt (Lam / lam) *
                  (3 : Real) ^ (-2 * (m : Real)) *
                    (weakNorm Qm (maximizer a Qm p q).toH1.grad) ^ 2 +
                2 * (3 : Real) ^ d *
                  ((3 : Real) ^ (-(d : Real) * ((m : Real) - ((m - 1 : Int) : Real))) *
                    (∑ Q ∈ descendantsAtScale Qm (m - 1), J Q) - J Qm))
      (hBesov : ∃ Cbesov : Real, 0 < Cbesov ∧
        ∀ a : TriadicCoeffFamily d,
          (∀ Q : TriadicCube d, CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ m ell : Int, ell ≤ m → ∀ p q : Homogenization.Vec d,
            let Qm := originCube d m
            let J := fun Q => responseJ (cubeDomain Q) (a.coeffOn Q) p q
            let R := fun Q => sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)
            let D := fun n : Int =>
              (3 : Real) ^ (-(d : Real) * ((m : Real) - (n : Real))) *
                (∑ Q ∈ descendantsAtScale Qm n, J Q) - J Qm
            let S := fun n : Int =>
              (3 : Real) ^ (-(d : Real) * ((m : Real) - (n : Real))) *
                (∑ Q ∈ descendantsAtScale Qm n,
                  ∑ i : Fin d, (matVecMul (R Q - R Qm) q i) ^ 2)
            let b := matVecMul (R Qm) q - p
            let lam := lambdaSq Qm (1 / 4) (.finite 1) a
            let v := maximizer a Qm p q
            (3 : Real) ^ (-(m : Real)) *
                weakNorm Qm (fun x => v.toH1.grad x - b) ≤
              Cbesov * Real.sqrt (lam⁻¹) *
                  (∑ n ∈ Finset.Icc ell m,
                    (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * Real.sqrt (D n)) +
                Cbesov * (∑ n ∈ Finset.Icc ell m,
                  (3 : Real) ^ (-((m : Real) - (n : Real))) * Real.sqrt (S n)) +
                Cbesov * Real.sqrt (lam⁻¹) / (1 - (1 / 4 : Real)) *
                  (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4)) *
                  Real.sqrt (variationEnergyValue (cubeDomain Qm) (a.coeffOn Qm) v) +
                Cbesov * (3 : Real) ^ (-((m : Real) - (ell : Real))) *
                  Real.sqrt (∑ i : Fin d, (b i) ^ 2))
      (hEnergy : ∀ (a : TriadicCoeffFamily d) (Q : TriadicCube d) (p q : Homogenization.Vec d),
        responseJ (cubeDomain Q) (a.coeffOn Q) p q =
          (1 / 2 : Real) * variationEnergyValue (cubeDomain Q) (a.coeffOn Q)
            (maximizer a Q p q)),
    ∃ C : Real, 0 < C ∧
      ∀ a : Homogenization.Book.Ch02.TriadicCoeffFamily d,
        (∀ Q : TriadicCube d, CoeffOn.IsSymmetric (a.coeffOn Q)) →
        ∀ m ell : Int, ell < m →
        ∀ p q : Homogenization.Vec d,
          let Qm : TriadicCube d := originCube d m
          let J : TriadicCube d → Real :=
            fun Q => responseJ (cubeDomain Q) (a.coeffOn Q) p q
          let R : TriadicCube d → Mat d :=
            fun Q => sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)
          let D : Int → Real := fun n =>
            (3 : Real) ^ (-(d : Real) * ((m : Real) - (n : Real))) *
                (∑ Q ∈ descendantsAtScale Qm n, J Q) - J Qm
          let S : Int → Real := fun n =>
            (3 : Real) ^ (-(d : Real) * ((m : Real) - (n : Real))) *
                (∑ Q ∈ descendantsAtScale Qm n,
                  ∑ i : Fin d, (matVecMul (R Q - R Qm) q i) ^ 2)
          let b : Homogenization.Vec d := matVecMul (R Qm) q - p
          let K : Real :=
            1 + LambdaSq Qm (1 / 4) (.finite 1) a +
              (lambdaSq Qm (1 / 4) (.finite 1) a) ^ (-1 : Real)
          J (originCube d (m - 1)) ≤
            C * K ^ 3 *
                ((∑ n ∈ Finset.Icc ell m,
                    (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) *
                      (D n + S n)) +
                  (∑ i : Fin d, (b i) ^ 2) +
                  (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 2)) * J Qm) +
              C * D (m - 1) := by
  dsimp
  let W : TriadicCube d → (Homogenization.Vec d → Homogenization.Vec d) → Real :=
    fun Q F => sSup {r : Real | ∃ phi : Homogenization.Vec d → Homogenization.Vec d,
      ContDiff Real ∞ phi ∧
      (∃ x ∈ openCubeSet Q, phi x ≠ 0) ∧
      r = |average (cubeDomain Q) (fun x => vecDot (F x) (phi x))| /
        (Real.sqrt (average (cubeDomain Q) (fun x =>
            ∑ i : Fin d, ∑ j : Fin d,
              (fderiv Real (fun y => phi y i) x (Pi.single j 1)) ^ 2)) +
          (3 : Real) ^ (-(Q.scale : Real)) *
            Real.sqrt (average (cubeDomain Q) (fun x =>
              ∑ i : Fin d, (phi x i) ^ 2)))}
  rintro hJWeak hBesov hEnergy
  clear hJ
  letI : NeZero d := ⟨by omega⟩
  rcases hJWeak with ⟨Cweak, hCweak, hJWeak⟩
  rcases hBesov with ⟨Cbesov, hCbesov, hBesov⟩
  let r₁ : Real := (3 : Real) ^ (-(3 / 4 : Real))
  let r₂ : Real := (3 : Real) ^ (-1 : Real)
  let G₁ : Real := (1 - r₁)⁻¹
  let G₂ : Real := (1 - r₂)⁻¹
  let C : Real := 100000 * (1 + Cweak) * (1 + Cbesov) ^ 2 *
    (1 + (3 : Real) ^ d) * (1 + G₁ + G₂)
  have hr₁C : r₁ < 1 := by
    dsimp [r₁]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr₂C : r₂ < 1 := by
    dsimp [r₂]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hG₁C : 0 < G₁ := by
    dsimp [G₁]
    exact inv_pos.mpr (sub_pos.mpr hr₁C)
  have hG₂C : 0 < G₂ := by
    dsimp [G₂]
    exact inv_pos.mpr (sub_pos.mpr hr₂C)
  refine ⟨C, by positivity, ?_⟩
  intro a ha m ell hℓm p q
  let Qm : TriadicCube d := originCube d m
  let J : TriadicCube d → Real :=
    fun Q => responseJ (cubeDomain Q) (a.coeffOn Q) p q
  let R : TriadicCube d → Mat d :=
    fun Q => sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)
  let D : Int → Real := fun n =>
    (3 : Real) ^ (-(d : Real) * ((m : Real) - (n : Real))) *
        (∑ Q ∈ descendantsAtScale Qm n, J Q) - J Qm
  let S : Int → Real := fun n =>
    (3 : Real) ^ (-(d : Real) * ((m : Real) - (n : Real))) *
        (∑ Q ∈ descendantsAtScale Qm n,
          ∑ i : Fin d, (matVecMul (R Q - R Qm) q i) ^ 2)
  let b : Homogenization.Vec d := matVecMul (R Qm) q - p
  let lam : Real := lambdaSq Qm (1 / 4) (.finite 1) a
  let Lam : Real := LambdaSq Qm (1 / 4) (.finite 1) a
  let K : Real := 1 + Lam + lam ^ (-1 : Real)
  let v := (canonicalMaximizer
    (responseExistenceTheory (cubeDomain Qm) (a.coeffOn Qm)) p q).toSolution
  change J (originCube d (m - 1)) ≤
    C * K ^ 3 *
        ((∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) *
              (D n + S n)) +
          (∑ i : Fin d, (b i) ^ 2) +
          (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 2)) * J Qm) +
      C * D (m - 1)
  have hJ1 := hJWeak a ha m p q
  have hBes1 := hBesov a ha m ell (le_of_lt hℓm) p q
  have hJ1' : J (originCube d (m - 1)) ≤
      Cweak * Lam * Real.sqrt (Lam / lam) *
          (3 : Real) ^ (-2 * (m : Real)) *
            (W Qm (fun x => v.toH1.grad x)) ^ 2 +
        2 * (3 : Real) ^ d * D (m - 1) := by
    change J (originCube d (m - 1)) ≤
      Cweak * Lam * Real.sqrt (Lam / lam) *
          (3 : Real) ^ (-2 * (m : Real)) *
            (W Qm (fun x => v.toH1.grad x)) ^ 2 +
        2 * (3 : Real) ^ d * D (m - 1) at hJ1
    exact hJ1
  have hBes1' :
      (3 : Real) ^ (-(m : Real)) *
          W Qm (fun x => v.toH1.grad x - b) ≤
        Cbesov * Real.sqrt (lam⁻¹) *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) *
                Real.sqrt (D n)) +
          Cbesov *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-((m : Real) - (n : Real))) *
                Real.sqrt (S n)) +
          Cbesov * Real.sqrt (lam⁻¹) / (1 - (1 / 4 : Real)) *
              (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4)) *
                Real.sqrt (variationEnergyValue (cubeDomain Qm)
                  (a.coeffOn Qm) v) +
          Cbesov * (3 : Real) ^ (-((m : Real) - (ell : Real))) *
            Real.sqrt (∑ i : Fin d, (b i) ^ 2) := by
    change (3 : Real) ^ (-(m : Real)) *
          W Qm (fun x => v.toH1.grad x - b) ≤
        Cbesov * Real.sqrt (lam⁻¹) *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) *
                Real.sqrt (D n)) +
          Cbesov *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-((m : Real) - (n : Real))) *
                Real.sqrt (S n)) +
          Cbesov * Real.sqrt (lam⁻¹) / (1 - (1 / 4 : Real)) *
              (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4)) *
                Real.sqrt (variationEnergyValue (cubeDomain Qm)
                  (a.coeffOn Qm) v) +
          Cbesov * (3 : Real) ^ (-((m : Real) - (ell : Real))) *
            Real.sqrt (∑ i : Fin d, (b i) ^ 2) at hBes1
    exact hBes1
  clear hJWeak hBesov hJ1 hBes1
  have hgrad_mem :
      Homogenization.MemVectorL2 (openCubeSet Qm)
        (fun x => v.toH1.grad x - b) := by
    exact v.toH1.grad_memVectorL2.sub (Homogenization.memVectorL2_const b)
  have hb_mem :
      Homogenization.MemVectorL2 (openCubeSet Qm) (fun _ => b) :=
    Homogenization.memVectorL2_const b
  have hWtri_eq (F : Homogenization.Vec d → Homogenization.Vec d) :
      W Qm F = sSup (aux_lem_C1_weakSet d (originCube d m) F) := by
    dsimp [W, Qm]
    congr 1
    ext r
    constructor
    · rintro ⟨phi, hphi, hnonzero, hr⟩
      exact ⟨phi, ⟨hphi, hnonzero⟩,
        by simpa [aux_lem_C1_ratio] using hr.symm⟩
    · rintro ⟨phi, ⟨hphi, hnonzero⟩, hr⟩
      exact ⟨phi, hphi, hnonzero,
        by simpa [aux_lem_C1_ratio] using hr.symm⟩
  have htri := aux_lem_C1_weak_triangle d m
    (fun x => v.toH1.grad x - b) (fun _ => b) hgrad_mem hb_mem
  have htri' : W Qm (fun x => v.toH1.grad x) ≤
      W Qm (fun x => v.toH1.grad x - b) + W Qm (fun _ => b) := by
    rw [hWtri_eq, hWtri_eq, hWtri_eq]
    have hfun : (fun x => (v.toH1.grad x - b) + b) =
        (fun x => v.toH1.grad x) := by
      funext x
      simp
    rw [hfun] at htri
    exact htri
  have hconst := aux_lem_C1_weak_const_bound d m b
  have hconst' : W Qm (fun _ => b) ≤
      (3 : Real) ^ (m : Real) * Real.sqrt (∑ i : Fin d, (b i) ^ 2) := by
    rw [hWtri_eq]
    exact hconst
  have hWnon (F : Homogenization.Vec d → Homogenization.Vec d) :
      0 ≤ W Qm F := by
    apply Real.sSup_nonneg
    intro r hr
    rcases hr with ⟨phi, hphi, hnonzero, hr⟩
    rw [hr]
    apply div_nonneg (abs_nonneg _)
    positivity
  have hscaled :
      (3 : Real) ^ (-(m : Real)) * W Qm (fun x => v.toH1.grad x) ≤
        (3 : Real) ^ (-(m : Real)) *
            W Qm (fun x => v.toH1.grad x - b) +
          Real.sqrt (∑ i : Fin d, (b i) ^ 2) := by
    have hpow : (3 : Real) ^ (-(m : Real)) * (3 : Real) ^ (m : Real) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : Real) < 3)]
      norm_num
    have ht := mul_le_mul_of_nonneg_left htri' (by positivity :
      0 ≤ (3 : Real) ^ (-(m : Real)))
    have hc := mul_le_mul_of_nonneg_left hconst' (by positivity :
      0 ≤ (3 : Real) ^ (-(m : Real)))
    have hc' : (3 : Real) ^ (-(m : Real)) * W Qm (fun _ => b) ≤
        Real.sqrt (∑ i : Fin d, (b i) ^ 2) := by
      calc
        (3 : Real) ^ (-(m : Real)) * W Qm (fun _ => b) ≤
            (3 : Real) ^ (-(m : Real)) *
              ((3 : Real) ^ (m : Real) *
                Real.sqrt (∑ i : Fin d, (b i) ^ 2)) := hc
        _ = Real.sqrt (∑ i : Fin d, (b i) ^ 2) := by
          rw [← mul_assoc, hpow, one_mul]
    rw [mul_add] at ht
    calc
      (3 : Real) ^ (-(m : Real)) * W Qm (fun x => v.toH1.grad x) ≤
          (3 : Real) ^ (-(m : Real)) * W Qm (fun x => v.toH1.grad x - b) +
            (3 : Real) ^ (-(m : Real)) * W Qm (fun _ => b) := ht
      _ ≤ _ := by
        convert (add_le_add_left hc'
          ((3 : Real) ^ (-(m : Real)) * W Qm
            (fun x => v.toH1.grad x - b))) using 1 <;> ring
  have hscaled_sq :
      ((3 : Real) ^ (-(m : Real)) * W Qm (fun x => v.toH1.grad x)) ^ 2 ≤
        2 * ((3 : Real) ^ (-(m : Real)) *
            W Qm (fun x => v.toH1.grad x - b)) ^ 2 +
          2 * (∑ i : Fin d, (b i) ^ 2) := by
    have hnonx : 0 ≤ (3 : Real) ^ (-(m : Real)) *
        W Qm (fun x => v.toH1.grad x) :=
      mul_nonneg (by positivity) (hWnon _)
    have hnony : 0 ≤ (3 : Real) ^ (-(m : Real)) *
        W Qm (fun x => v.toH1.grad x - b) :=
      mul_nonneg (by positivity) (hWnon _)
    have hnonb : 0 ≤ Real.sqrt (∑ i : Fin d, (b i) ^ 2) := by positivity
    have hh := aux_lem_C1_square_le
      ((3 : Real) ^ (-(m : Real)) * W Qm (fun x => v.toH1.grad x))
      ((3 : Real) ^ (-(m : Real)) *
        W Qm (fun x => v.toH1.grad x - b))
      (Real.sqrt (∑ i : Fin d, (b i) ^ 2)) hnonx hnony hnonb hscaled
    simpa [Real.sq_sqrt (by positivity : 0 ≤ ∑ i : Fin d, (b i) ^ 2)] using hh
  have hD_nonneg (n : Int) (hn : n ∈ Finset.Icc ell m) : 0 ≤ D n := by
    apply aux_lem_C1_defect_nonneg d a m n
      (Finset.mem_Icc.mp hn).2 p q
  have hDm1 : 0 ≤ D (m - 1) := by
    apply aux_lem_C1_defect_nonneg d a m (m - 1) (by omega) p q
  have hS_nonneg (n : Int) : 0 ≤ S n := by
    dsimp [S]
    positivity
  have hJ_nonneg (Q : TriadicCube d) : 0 ≤ J Q := by
    dsimp [J]
    exact Homogenization.Book.Ch02.responseJ_nonneg
      (cubeDomain Q) (a.coeffOn Q) p q
  have hJQm : 0 ≤ J Qm := hJ_nonneg Qm
  have hr₁0 : 0 ≤ r₁ := by
    dsimp [r₁]
    positivity
  have hr₁1 : r₁ < 1 := by
    dsimp [r₁]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr₂0 : 0 ≤ r₂ := by
    dsimp [r₂]
    positivity
  have hr₂1 : r₂ < 1 := by
    dsimp [r₂]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsum₁ :
      ∑ n ∈ Finset.Icc ell m,
        (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) ≤ G₁ := by
    calc
      _ = ∑ n ∈ Finset.Icc ell m, r₁ ^ Int.toNat (m - n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [aux_lem_C1_weight_one m n (Finset.mem_Icc.mp hn).2]
      _ ≤ (1 - r₁)⁻¹ := aux_lem_C1_geom_sum ell m r₁ hr₁0 hr₁1 (le_of_lt hℓm)
      _ = G₁ := by rfl
  have hsum₂ :
      ∑ n ∈ Finset.Icc ell m,
        (3 : Real) ^ (-((m : Real) - (n : Real))) ≤ G₂ := by
    calc
      _ = ∑ n ∈ Finset.Icc ell m, r₂ ^ Int.toNat (m - n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [aux_lem_C1_weight_two m n (Finset.mem_Icc.mp hn).2]
      _ ≤ (1 - r₂)⁻¹ := aux_lem_C1_geom_sum ell m r₂ hr₂0 hr₂1 (le_of_lt hℓm)
      _ = G₂ := by rfl
  have hG₁two : G₁ ≤ 2 := by
    have hr₁half : r₁ ≤ (1 / 2 : Real) := by
      dsimp [r₁]
      rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 3)]
      exact aux_lem_C1_inv_le_half_of_two_le _
        (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 3) _)
        aux_lem_C1_rpow_three_quarter
    dsimp [G₁]
    exact aux_lem_C1_inv_sub_le_two r₁ hr₁C hr₁half
  have hG₂two : G₂ ≤ 2 := by
    have hr₂half : r₂ ≤ (1 / 2 : Real) := by
      dsimp [r₂]
      have heq : (3 : Real) ^ (-1 : Real) = (3 : Real)⁻¹ := by
        rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 3), Real.rpow_one]
      rw [heq]
      norm_num
    dsimp [G₂]
    exact aux_lem_C1_inv_sub_le_two r₂ hr₂C hr₂half
  have henergy :
      variationEnergyValue (cubeDomain Qm) (a.coeffOn Qm) v = 2 * J Qm := by
    have hh := hEnergy a Qm p q
    dsimp [J, v] at hh ⊢
    linarith
  clear hEnergy
  have hsqD :
      (∑ n ∈ Finset.Icc ell m,
        (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) *
          Real.sqrt (D n)) ^ 2 ≤
        2 * ∑ n ∈ Finset.Icc ell m,
          (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n := by
    apply aux_lem_C1_weighted_square (s := Finset.Icc ell m)
      (w := fun n => (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)))
      (x := D)
    · intro n hn
      exact Real.rpow_nonneg (show (0 : Real) ≤ 3 by norm_num) _
    · intro n hn
      exact hD_nonneg n hn
    · exact hsum₁.trans hG₁two
  have hsqS :
      (∑ n ∈ Finset.Icc ell m,
        (3 : Real) ^ (-((m : Real) - (n : Real))) *
          Real.sqrt (S n)) ^ 2 ≤
        2 * ∑ n ∈ Finset.Icc ell m,
          (3 : Real) ^ (-((m : Real) - (n : Real))) * S n := by
    apply aux_lem_C1_weighted_square (s := Finset.Icc ell m)
      (w := fun n => (3 : Real) ^ (-((m : Real) - (n : Real))))
      (x := S)
    · intro n hn
      exact Real.rpow_nonneg (show (0 : Real) ≤ 3 by norm_num) _
    · intro n hn
      exact hS_nonneg n
    · exact hsum₂.trans hG₂two
  let X : Real := (3 : Real) ^ (-(m : Real)) *
    W Qm (fun x => v.toH1.grad x - b)
  let A : Real := ∑ n ∈ Finset.Icc ell m,
    (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * Real.sqrt (D n)
  let B : Real := ∑ n ∈ Finset.Icc ell m,
    (3 : Real) ^ (-((m : Real) - (n : Real))) * Real.sqrt (S n)
  let E : Real := Real.sqrt (variationEnergyValue (cubeDomain Qm)
    (a.coeffOn Qm) v)
  let U : Real := Real.sqrt (∑ i : Fin d, (b i) ^ 2)
  let T₁ : Real := Cbesov * Real.sqrt (lam⁻¹) * A
  let T₂ : Real := Cbesov * B
  let T₃ : Real := Cbesov * Real.sqrt (lam⁻¹) / (1 - (1 / 4 : Real)) *
    (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4)) * E
  let T₄ : Real := Cbesov * (3 : Real) ^ (-((m : Real) - (ell : Real))) * U
  have hBesAbbrev : X ≤ T₁ + T₂ + T₃ + T₄ := by
    simpa [X, A, B, E, U, T₁, T₂, T₃, T₄] using hBes1'
  have hlam_pos' : 0 < lam := by
    dsimp [lam]
    exact lambdaSq_pos (q := .finite 1) Qm a (by norm_num) (by norm_num)
  have hLam_pos' : 0 < Lam := by
    dsimp [Lam]
    exact LambdaSq_pos (q := .finite 1) Qm a (by norm_num) (by norm_num)
  have hK_pos : 0 < K := by
    dsimp [K]
    rw [Real.rpow_neg_one]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg zero_lt_one hLam_pos'.le)
      (inv_pos.mpr hlam_pos').le
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun n hn => mul_nonneg
      (Real.rpow_nonneg (show (0 : Real) ≤ 3 by norm_num) _)
      (Real.sqrt_nonneg _))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun n hn => mul_nonneg
      (Real.rpow_nonneg (show (0 : Real) ≤ 3 by norm_num) _)
      (Real.sqrt_nonneg _))
  have hE_nonneg : 0 ≤ E := by dsimp [E]; exact Real.sqrt_nonneg _
  have hU_nonneg : 0 ≤ U := by dsimp [U]; exact Real.sqrt_nonneg _
  have hT₁_nonneg : 0 ≤ T₁ := by
    dsimp [T₁]
    exact mul_nonneg (mul_nonneg hCbesov.le (Real.sqrt_nonneg _)) hA_nonneg
  have hT₂_nonneg : 0 ≤ T₂ := by
    dsimp [T₂]
    exact mul_nonneg hCbesov.le hB_nonneg
  have hT₃_nonneg : 0 ≤ T₃ := by
    dsimp [T₃]
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (mul_nonneg hCbesov.le (Real.sqrt_nonneg _)) (by norm_num))
        (Real.rpow_nonneg (show (0 : Real) ≤ 3 by norm_num) _)) hE_nonneg
  have hT₄_nonneg : 0 ≤ T₄ := by
    dsimp [T₄]
    exact mul_nonneg
      (mul_nonneg hCbesov.le
        (Real.rpow_nonneg (show (0 : Real) ≤ 3 by norm_num) _)) hU_nonneg
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (Real.rpow_nonneg (show (0 : Real) ≤ 3 by norm_num) _) (hWnon _)
  have hsqBes : X ^ 2 ≤ 4 * (T₁ ^ 2 + T₂ ^ 2 + T₃ ^ 2 + T₄ ^ 2) := by
    have hsumT : 0 ≤ T₁ + T₂ + T₃ + T₄ := by
      exact add_nonneg (add_nonneg (add_nonneg hT₁_nonneg hT₂_nonneg) hT₃_nonneg)
        hT₄_nonneg
    have hsq : X ^ 2 ≤ (T₁ + T₂ + T₃ + T₄) ^ 2 :=
      aux_lem_C1_square_mono X (T₁ + T₂ + T₃ + T₄) hX_nonneg hsumT hBesAbbrev
    have hfour := aux_lem_C1_four_square T₁ T₂ T₃ T₄
    exact hsq.trans hfour
  have hlam_inv_nonneg : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam_pos'.le
  have hT₁sq : T₁ ^ 2 ≤
      2 * Cbesov ^ 2 * lam⁻¹ *
        (∑ n ∈ Finset.Icc ell m,
          (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n) := by
    have hh := hsqD
    have hc : 0 ≤ Cbesov ^ 2 * lam⁻¹ :=
      mul_nonneg (sq_nonneg _) hlam_inv_nonneg
    have hh' := mul_le_mul_of_nonneg_left hh hc
    have hsqrt : (Real.sqrt (lam⁻¹)) ^ 2 = lam⁻¹ :=
      Real.sq_sqrt hlam_inv_nonneg
    dsimp [T₁]
    calc
      (Cbesov * Real.sqrt (lam⁻¹) * A) ^ 2 =
          Cbesov ^ 2 * (Real.sqrt (lam⁻¹)) ^ 2 * A ^ 2 := by ring
      _ = Cbesov ^ 2 * lam⁻¹ * A ^ 2 := by rw [hsqrt]
      _ ≤ Cbesov ^ 2 * lam⁻¹ *
          (2 * ∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n) := hh'
      _ = 2 * Cbesov ^ 2 * lam⁻¹ *
          (∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n) := by ring
  have hT₂sq : T₂ ^ 2 ≤
      2 * Cbesov ^ 2 *
        (∑ n ∈ Finset.Icc ell m,
          (3 : Real) ^ (-((m : Real) - (n : Real))) * S n) := by
    have hh := hsqS
    have hc : 0 ≤ Cbesov ^ 2 := sq_nonneg _
    have hh' := mul_le_mul_of_nonneg_left hh hc
    dsimp [T₂]
    calc
      (Cbesov * B) ^ 2 = Cbesov ^ 2 * B ^ 2 := by ring
      _ ≤ Cbesov ^ 2 *
          (2 * ∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-((m : Real) - (n : Real))) * S n) := hh'
      _ = 2 * Cbesov ^ 2 *
          (∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-((m : Real) - (n : Real))) * S n) := by ring
  have hw₂ell : 0 ≤ (3 : Real) ^ (-((m : Real) - (ell : Real))) := by
    positivity
  have hw₂ell_le : (3 : Real) ^ (-((m : Real) - (ell : Real))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (ell : Real) ≤ (m : Real) := by exact_mod_cast (le_of_lt hℓm)
    linarith
  have hT₄sq : T₄ ^ 2 ≤ Cbesov ^ 2 * U ^ 2 := by
    have hwu : ((3 : Real) ^ (-((m : Real) - (ell : Real)))) ^ 2 ≤ 1 := by
      simpa using (aux_lem_C1_square_mono _ 1 hw₂ell (by norm_num) hw₂ell_le)
    dsimp [T₄]
    calc
      (Cbesov * (3 : Real) ^ (-((m : Real) - (ell : Real))) * U) ^ 2 =
          (Cbesov * U) ^ 2 * ((3 : Real) ^ (-((m : Real) - (ell : Real)))) ^ 2 := by ring
      _ ≤ (Cbesov * U) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hwu (sq_nonneg (Cbesov * U))
      _ = Cbesov ^ 2 * U ^ 2 := by ring
  have hEnergy_nonneg :
      0 ≤ variationEnergyValue (cubeDomain Qm) (a.coeffOn Qm) v := by
    rw [henergy]
    exact mul_nonneg (by norm_num) (hJ_nonneg Qm)
  have hEsq : E ^ 2 = 2 * J Qm := by
    dsimp [E]
    rw [Real.sq_sqrt hEnergy_nonneg, henergy]
  have hw₁ell_nonneg :
      0 ≤ (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4)) := by
    positivity
  have hT₃sq : T₃ ^ 2 ≤
      4 * Cbesov ^ 2 * lam⁻¹ *
        ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 *
          J Qm := by
    have hsqrt : (Real.sqrt (lam⁻¹)) ^ 2 = lam⁻¹ :=
      Real.sq_sqrt hlam_inv_nonneg
    have hcalc : T₃ ^ 2 =
        (32 / 9 : Real) * Cbesov ^ 2 * lam⁻¹ *
          ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 *
            J Qm := by
      dsimp [T₃]
      calc
        (Cbesov * Real.sqrt (lam⁻¹) / (1 - (1 / 4 : Real)) *
            (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4)) * E) ^ 2 =
            Cbesov ^ 2 * (Real.sqrt (lam⁻¹)) ^ 2 /
              (1 - (1 / 4 : Real)) ^ 2 *
              ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * E ^ 2 := by ring
        _ = (32 / 9 : Real) * Cbesov ^ 2 * lam⁻¹ *
            ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * J Qm := by
          rw [hsqrt, hEsq]
          ring
    rw [hcalc]
    have hnon : 0 ≤ Cbesov ^ 2 * lam⁻¹ *
        ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * J Qm := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (sq_nonneg _) hlam_inv_nonneg) (sq_nonneg _))
        (hJ_nonneg Qm)
    convert mul_le_mul_of_nonneg_right (by norm_num : (32 / 9 : Real) ≤ 4) hnon using 1 <;>
      ring
  have hweight_compare (n : Int) (hn : n ∈ Finset.Icc ell m) :
      (3 : Real) ^ (-((m : Real) - (n : Real))) ≤
        (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hnm : (n : Real) ≤ (m : Real) := by
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    linarith
  have hSsum_compare :
      ∑ n ∈ Finset.Icc ell m,
        (3 : Real) ^ (-((m : Real) - (n : Real))) * S n ≤
      ∑ n ∈ Finset.Icc ell m,
        (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (hweight_compare n hn) (hS_nonneg n)
  have hweight_one_sq :
      ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 =
        (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 3)]
    congr 1
    ring
  let SD : Real := ∑ n ∈ Finset.Icc ell m,
    (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n
  let SS : Real := ∑ n ∈ Finset.Icc ell m,
    (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n
  let BU : Real := ∑ i : Fin d, (b i) ^ 2
  let w : Real :=
    (3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))
  let EJ : Real :=
    w ^ 2 * J Qm
  have hXfinal : X ^ 2 ≤
      8 * Cbesov ^ 2 * lam⁻¹ *
          (∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n) +
        8 * Cbesov ^ 2 *
          (∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n) +
        16 * Cbesov ^ 2 * lam⁻¹ *
          ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * J Qm +
        4 * Cbesov ^ 2 * ∑ i : Fin d, (b i) ^ 2 := by
    have hT₂sq' : T₂ ^ 2 ≤
        2 * Cbesov ^ 2 *
          (∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n) := by
      exact le_trans hT₂sq
        (mul_le_mul_of_nonneg_left hSsum_compare
          (mul_nonneg (by norm_num) (sq_nonneg Cbesov)))
    have hsum_inner : T₁ ^ 2 + T₂ ^ 2 + T₃ ^ 2 + T₄ ^ 2 ≤
        (2 * Cbesov ^ 2 *
            lam⁻¹ *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n)) +
          (2 * Cbesov ^ 2 *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n)) +
          (4 * Cbesov ^ 2 *
            lam⁻¹ *
            ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * J Qm) +
          Cbesov ^ 2 * U ^ 2 := by
      have h12 := add_le_add hT₁sq hT₂sq'
      have h34 := add_le_add hT₃sq hT₄sq
      calc
        T₁ ^ 2 + T₂ ^ 2 + T₃ ^ 2 + T₄ ^ 2 =
            (T₁ ^ 2 + T₂ ^ 2) + (T₃ ^ 2 + T₄ ^ 2) := by ring
        _ ≤
            (2 * Cbesov ^ 2 * lam⁻¹ *
                (∑ n ∈ Finset.Icc ell m,
                  (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n) +
              2 * Cbesov ^ 2 *
                (∑ n ∈ Finset.Icc ell m,
                  (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n)) +
              (4 * Cbesov ^ 2 *
                lam⁻¹ *
                ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * J Qm +
                Cbesov ^ 2 * U ^ 2) := add_le_add h12 h34
        _ = _ := by ring
    have hsum_bound := mul_le_mul_of_nonneg_left hsum_inner
      (by norm_num : (0 : Real) ≤ 4)
    have hU2 : U ^ 2 = ∑ i : Fin d, (b i) ^ 2 := by
      dsimp [U]
      rw [Real.sq_sqrt]
      positivity
    rw [hU2] at hsum_bound
    calc
      X ^ 2 ≤ 4 * (T₁ ^ 2 + T₂ ^ 2 + T₃ ^ 2 + T₄ ^ 2) := hsqBes
      _ ≤ 4 * ((2 * Cbesov ^ 2 *
            lam⁻¹ *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n)) +
          (2 * Cbesov ^ 2 *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n)) +
          (4 * Cbesov ^ 2 *
            lam⁻¹ *
            ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * J Qm) +
          Cbesov ^ 2 * ∑ i : Fin d, (b i) ^ 2) := hsum_bound
      _ = _ := by ring
  have hgrad_final :
      ((3 : Real) ^ (-(m : Real)) * W Qm
          (fun x => v.toH1.grad x)) ^ 2 ≤
        32 * Cbesov ^ 2 * lam⁻¹ * SD +
          32 * Cbesov ^ 2 * SS +
          64 * Cbesov ^ 2 * lam⁻¹ * EJ +
          (8 * Cbesov ^ 2 + 2) * BU := by
    dsimp [SD, SS, BU, EJ]
    have hh := hscaled_sq
    have hx := hXfinal
    have hU2 : U ^ 2 = ∑ i : Fin d, (b i) ^ 2 := by
      dsimp [U]
      rw [Real.sq_sqrt]
      positivity
    have h2x := mul_le_mul_of_nonneg_left hx (by norm_num : (0 : Real) ≤ 2)
    calc
      _ ≤ 2 * (3 ^ (- (m : Real)) * W Qm
          (fun x => v.toH1.grad x - b)) ^ 2 +
          2 * ∑ i : Fin d, (b i) ^ 2 := hh
      _ ≤ 2 * (8 * Cbesov ^ 2 * lam⁻¹ *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n) +
          8 * Cbesov ^ 2 *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n) +
          16 * Cbesov ^ 2 * lam⁻¹ *
            ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * J Qm +
          4 * Cbesov ^ 2 * ∑ i : Fin d, (b i) ^ 2) +
          2 * ∑ i : Fin d, (b i) ^ 2 := by
            exact add_le_add h2x (le_refl _)
      _ ≤ _ := by
        have hSD0 : 0 ≤
            ∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n := by
          exact Finset.sum_nonneg (fun n hn =>
            mul_nonneg (Real.rpow_nonneg (show (0 : Real) ≤ 3 by norm_num) _)
              (hD_nonneg n hn))
        have hSS0 : 0 ≤
            ∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n := by
          exact Finset.sum_nonneg (fun n hn =>
              mul_nonneg (Real.rpow_nonneg (show (0 : Real) ≤ 3 by norm_num) _)
              (hS_nonneg n))
        have hC0 : 0 ≤ Cbesov ^ 2 * lam⁻¹ :=
          mul_nonneg (sq_nonneg _) hlam_inv_nonneg
        have hW0 : 0 ≤
            ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 := by
          positivity
        have hJ0 : 0 ≤ J Qm := hJ_nonneg Qm
        have hCD : 0 ≤ Cbesov ^ 2 * lam⁻¹ *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n) :=
          mul_nonneg hC0 hSD0
        have hCS : 0 ≤ Cbesov ^ 2 *
            (∑ n ∈ Finset.Icc ell m,
              (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n) :=
          mul_nonneg (sq_nonneg _) hSS0
        have hCJ : 0 ≤ Cbesov ^ 2 * lam⁻¹ *
            ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * J Qm :=
          mul_nonneg (mul_nonneg hC0 hW0) hJ0
        nlinarith only [hCD, hCS, hCJ, hU2]
  have hscale_eq :
      (3 : Real) ^ (-2 * (m : Real)) *
          (W Qm (fun x => v.toH1.grad x)) ^ 2 =
        ((3 : Real) ^ (-(m : Real)) *
          W Qm (fun x => v.toH1.grad x)) ^ 2 := by
    have hpow : (3 : Real) ^ (-2 * (m : Real)) =
        ((3 : Real) ^ (-(m : Real))) ^ 2 := by
      calc
        (3 : Real) ^ (-2 * (m : Real)) =
            (3 : Real) ^ (-(m : Real) * (2 : Real)) := by
              congr 1
              ring
        _ = ((3 : Real) ^ (-(m : Real))) ^ (2 : Real) := by
              rw [Real.rpow_mul (show (0 : Real) ≤ 3 by norm_num)]
        _ = ((3 : Real) ^ (-(m : Real))) ^ 2 := by
              exact Real.rpow_natCast _ 2
    rw [mul_pow, hpow]
  have hcoef_nonneg : 0 ≤ Cweak * Lam * Real.sqrt (Lam / lam) := by
    exact mul_nonneg (mul_nonneg hCweak.le hLam_pos'.le) (Real.sqrt_nonneg _)
  have hJbound : J (originCube d (m - 1)) ≤
      Cweak * Lam * Real.sqrt (Lam / lam) *
        (32 * Cbesov ^ 2 * lam⁻¹ * SD +
          32 * Cbesov ^ 2 * SS +
          64 * Cbesov ^ 2 * lam⁻¹ * EJ +
          (8 * Cbesov ^ 2 + 2) * BU) +
        2 * (3 : Real) ^ d * D (m - 1) := by
    have hscale_le := hgrad_final
    rw [← hscale_eq] at hscale_le
    have hfirst : J (originCube d (m - 1)) ≤
        Cweak * Lam * Real.sqrt (Lam / lam) *
            ((3 : Real) ^ (-2 * (m : Real)) *
              (W Qm (fun x => v.toH1.grad x)) ^ 2) +
          2 * (3 : Real) ^ d * D (m - 1) := by
      simpa only [mul_assoc] using hJ1'
    have hmul := mul_le_mul_of_nonneg_left hscale_le hcoef_nonneg
    exact le_trans hfirst (add_le_add hmul (le_refl _))
  have hSD_nonneg : 0 ≤ SD := by
    dsimp [SD]
    exact Finset.sum_nonneg (fun n hn => mul_nonneg
      (aux_lem_C1_three_rpow_nonneg _)
      (hD_nonneg n hn))
  have hSS_nonneg : 0 ≤ SS := by
    dsimp [SS]
    exact Finset.sum_nonneg (fun n hn => mul_nonneg
      (aux_lem_C1_three_rpow_nonneg _)
      (hS_nonneg n))
  have hBU_nonneg : 0 ≤ BU := by
    change 0 ≤ ∑ i : Fin d, (b i) ^ 2
    exact aux_lem_C1_fin_sum_sq_nonneg d b
  have hEJ_nonneg : 0 ≤ EJ := by
    dsimp [EJ]
    exact mul_nonneg (sq_nonneg w) hJQm
  have hSDSS : SD + SS =
      ∑ n ∈ Finset.Icc ell m,
        (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) *
          (D n + S n) := by
    dsimp [SD, SS]
    calc
      (∑ n ∈ Finset.Icc ell m,
          (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n) +
          ∑ n ∈ Finset.Icc ell m,
            (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n =
        ∑ n ∈ Finset.Icc ell m,
          ((3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * D n +
            (3 : Real) ^ (-(3 * ((m : Real) - (n : Real)) / 4)) * S n) := by
              rw [Finset.sum_add_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hEJdef : EJ =
      ((3 : Real) ^ (-(3 * ((m : Real) - (ell : Real)) / 4))) ^ 2 * J Qm := by
    dsimp [EJ, w]
  have hBUdef : BU = ∑ i : Fin d, (b i) ^ 2 := by
    rfl
  exact aux_lem_C1_collect d ell m Cweak Cbesov Lam lam K C G₁ G₂ D S b
    (J (originCube d (m - 1))) (D (m - 1)) (J Qm) SD SS EJ BU
    hCweak hCbesov hLam_pos' hlam_pos' hK_pos hG₁C.le hG₂C.le
    hDm1 (hJ_nonneg Qm)
    hSD_nonneg hSS_nonneg hEJ_nonneg hBU_nonneg
    (by rfl) (by rfl) hJbound hSDSS hEJdef hBUdef
end Paper


