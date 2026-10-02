import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.MeanZero
import SubdiffusiveProcess.Sobolev.AffineData
import SubdiffusiveProcess.Sobolev.GradientRange




open MeasureTheory Set TopologicalSpace
namespace SubdiffusiveProcess

variable {d : ℕ}

/-- `u` restricted to `qp` and re-centred by its own mean on `qp` lies in `meanZeroSobolevGraph
qp`, agrees a.e. with the mean-centred restriction, and has the same weak gradient as the plain
restriction (subtracting a constant leaves the gradient unchanged). -/
theorem exists_meanZero_restrict_of_weakSobolevGraph
    {Q qp : Opens (SpatialCoordinates d)} (hV : qp ≤ Q)
    (hbdd : Bornology.IsBounded (qp : Set (SpatialCoordinates d)))
    [IsFiniteMeasure (volume.restrict (qp : Set (SpatialCoordinates d)))]
    (hqpvol : volume.real (qp : Set (SpatialCoordinates d)) ≠ 0)
    (u : SobolevData Q) (hu : u ∈ weakSobolevGraph Q) :
    ∃ w : meanZeroSobolevGraph qp,
      ((w : SobolevData qp).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (qp : Set (SpatialCoordinates d))]
        (fun x => (sobolevDataRestrict hV u).1 x -
          (volume.real (qp : Set (SpatialCoordinates d)))⁻¹ *
            ∫ y in (qp : Set (SpatialCoordinates d)), (sobolevDataRestrict hV u).1 y) ∧
      sobolevGradient ((w : meanZeroSobolevGraph qp) : SobolevData qp) =
        sobolevGradient (sobolevDataRestrict hV u) := by
  set avg : ℝ := (volume.real (qp : Set (SpatialCoordinates d)))⁻¹ *
    ∫ y in (qp : Set (SpatialCoordinates d)), (sobolevDataRestrict hV u).1 y with havg
  set z : SobolevData qp :=
    sobolevDataRestrict hV u - affineSobolevData hbdd (fun _ : Fin d => (0 : ℝ)) avg with hz
  have hz1 : (z.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (qp : Set (SpatialCoordinates d))]
      (fun x => (sobolevDataRestrict hV u).1 x - avg) := by
    have hconst : ((affineSobolevData hbdd (fun _ : Fin d => (0 : ℝ)) avg).1 :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (qp : Set (SpatialCoordinates d))]
        fun _ => avg := by
      simpa [affineSlope_apply] using affineL2_coeFn hbdd (fun _ : Fin d => (0 : ℝ)) avg
    filter_upwards [Lp.coeFn_sub (sobolevDataRestrict hV u).1
      (affineSobolevData hbdd (fun _ : Fin d => (0 : ℝ)) avg).1, hconst] with x hx1 hx2
    show z.1 x = _
    rw [hz]
    simp only [Prod.fst_sub]
    rw [hx1]
    simp [hx2]
  have hz2 : (z.2 : Fin d → DomainL2 qp) = (sobolevDataRestrict hV u).2 := by
    have hzero : (affineSobolevData hbdd (fun _ : Fin d => (0 : ℝ)) avg).2 =
        (0 : Fin d → DomainL2 qp) := by
      funext i
      show domainConstantL2 (Ω := qp) (0 : ℝ) = 0
      rw [Lp.eq_zero_iff_ae_eq_zero]
      simpa using domainConstantL2_coeFn (Ω := qp) (0 : ℝ)
    rw [hz]
    simp only [Prod.snd_sub, hzero, sub_zero]
  have hzmem : z ∈ weakSobolevGraph qp :=
    (weakSobolevGraph qp).sub_mem (sobolevDataRestrict_mem_weak hV hu)
      (affineSobolevData_mem hbdd (fun _ : Fin d => (0 : ℝ)) avg)
  have hint1 : IntegrableOn (fun x => (sobolevDataRestrict hV u).1 x)
      (qp : Set (SpatialCoordinates d)) volume :=
    (Lp.memLp (sobolevDataRestrict hV u).1).integrable (by norm_num)
  have hvolqp : volume (qp : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [← Measure.restrict_apply_univ (qp : Set (SpatialCoordinates d))]
    exact measure_ne_top _ _
  have hzavg : (∫ x in (qp : Set (SpatialCoordinates d)), z.1 x) = 0 := by
    rw [integral_congr_ae hz1, integral_sub hint1 (integrableOn_const hvolqp), integral_const,
      smul_eq_mul, measureReal_restrict_apply_univ, havg]
    field_simp
    ring
  refine ⟨⟨z, ?_⟩, ?_, ?_⟩
  · rw [mem_meanZeroSobolevGraph_iff]; exact ⟨hzmem, hzavg⟩
  · exact hz1
  · show sobolevGradient z = sobolevGradient (sobolevDataRestrict hV u)
    unfold sobolevGradient
    simp only [ContinuousLinearMap.comp_apply]
    congr 1

end SubdiffusiveProcess
