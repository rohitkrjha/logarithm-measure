import LogarithmExtension.BoundedJetMatrix
import LogarithmExtension.AnalyticTranslation
import OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge

/-! # The bounded jet matrix is the matrix used in the determinant estimates -/

noncomputable section
namespace LogarithmExtension.MatrixIdentification

open OAI OAI.PiExponent OAI.PiExponentApprox
open CoordinateScaling NormalizedTruncation InterpolationMatrix
open scoped BigOperators

theorem scaleY_monomial {m : ℕ} (y : ℂ) (e : Fin (m+1) → ℕ) :
    scaleY y (MvPolynomial.monomial (exponentVector e) (1 : ℂ)) =
      MvPolynomial.C (y ^ e 0) * MvPolynomial.monomial (exponentVector e) 1 := by
  rw [scaleY, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ,
    exponentVector_apply, map_one, one_mul, mul_pow, ← map_pow]
  ring

theorem entry_eq_coeff {m : ℕ} (base : ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (j : ℕ) (b e : Fin (m+1) → ℕ) :
    AnalyticTranslation.matrixEntry base r T j (b 0) (fun i => b i.succ)
      (e 0) (fun i => e i.succ) =
      MvPowerSeries.coeff (exponentVector b)
        (truncatedJet (base ^ j) (fun i => (j : ℂ) * r i) T
          (MvPolynomial.monomial (exponentVector e) 1)) := by
  change base ^ (j * e 0) * InterpolationMatrix.entry r
    (fun i => InterpolationMatrix.truncatedLog (T i)) j (b 0) (fun i => b i.succ)
      (e 0) (fun i => e i.succ) =
    MvPowerSeries.coeff (exponentVector b)
      (FormalLogTruncation.truncatedFormalJet (fun i => (j : ℂ) * r i) T
        (scaleY (base ^ j) (MvPolynomial.monomial (exponentVector e) 1)))
  rw [scaleY_monomial, map_mul]
  have hc : FormalLogTruncation.truncatedFormalJet (fun i => (j : ℂ) * r i) T
      (MvPolynomial.C ((base ^ j) ^ e 0)) = MvPowerSeries.C ((base ^ j) ^ e 0) :=
    (FormalLogTruncation.truncatedFormalJet _ _).commutes _
  rw [hc, MvPowerSeries.coeff_C_mul, ← pow_mul,
    FormalMatrixBridge.entry_eq_coeff_truncatedFormalJet]

def actualMatrix (d : GeometryData) (base : ℂ) (r : Fin d.m → ℂ)
    (T : Fin d.m → ℕ) (H : ℚ) :
    Matrix (BoundedJetMatrix.Row d H) (BoundedJetMatrix.Column d H) ℂ :=
  fun row col => AnalyticTranslation.matrixEntry base r T row.1.val
    (row.2.val 0) (fun i => row.2.val i.succ) (col.val 0) (fun i => col.val i.succ)

theorem actualMatrix_eq (d : GeometryData) (base : ℂ) (r : Fin d.m → ℂ)
    (hy : ∀ j, d.centerY j = base ^ j.val)
    (hc : ∀ j i, d.curveCenters j i = (j.val : ℂ) * r i)
    (T : Fin d.m → ℕ) (H : ℚ) :
    actualMatrix d base r T H = BoundedJetMatrix.matrix d T H := by
  funext row col
  change AnalyticTranslation.matrixEntry base r T _ _ _ _ _ =
    MvPowerSeries.coeff _ (truncatedJet (d.centerY row.1) (d.curveCenters row.1) T _)
  rw [hy, funext (hc row.1)]
  exact entry_eq_coeff base r T row.1.val row.2.val col.val

theorem eventually_nonzero_minor (d : GeometryData) (base : ℂ) (r : Fin d.m → ℂ)
    (hy : ∀ j, d.centerY j = base ^ j.val)
    (hc : ∀ j i, d.curveCenters j i = (j.val : ℂ) * r i)
    (T : Fin d.m → ℕ)
    (hT : ∀ i, d.curveJetWeights i.succ ≤ (T i : ℚ) * d.curveJetWeights 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ selection : BoundedJetMatrix.Row d ((n : ℚ) * (BlowupGeometry.scale d).radius) →
          BoundedJetMatrix.Column d ((n : ℚ) * (BlowupGeometry.scale d).radius),
        Function.Injective selection ∧
          ((actualMatrix d base r T ((n : ℚ) * (BlowupGeometry.scale d).radius)).submatrix
            id selection).det ≠ 0 := by
  simpa only [actualMatrix_eq d base r hy hc] using BoundedJetMatrix.eventually_nonzero_minor d T hT

end LogarithmExtension.MatrixIdentification
