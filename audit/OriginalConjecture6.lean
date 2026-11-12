import AaronsonAmbainis.Main

/-!
# Independent bridge to Aaronson–Ambainis Conjecture 6

This is a separate formulation of Conjecture 6 in Aaronson and Ambainis,
"The Need for Structure in Quantum Speedups" (arXiv:0911.0996v3), also
Conjecture 1.7 of the journal version.

The historical `(ε/d)^{O(1)}` is interpreted here as the existence of one
*uniform positive natural exponent* for all instances, with no prefactor.
This implies a formulation allowing some fixed positive prefactor (take 1).
For nondegenerate instances under the range [0,1], variance is at most 1/4
and d is positive, hence ε/d ≤ 1/4. Thus any fixed positive prefactor can
also be absorbed into a sufficiently larger uniform natural exponent.
Whether this formalization matches the intended informal interpretation
remains a separate mathematical judgment.

The definitions below use Mathlib primitives, not PSI's `PrintedConjecture`.
The cube is {0,1}^N and the squared flip difference is *not* divided by 4.
On {-1,1}^N, the usual Fourier influence uses a half-difference squared;
the change of range g(x) = 2p((x+1)/2) - 1 identifies these influences
while multiplying the variance by 4.
The one-way bridge imports PSI's theorem only as its premise. This file does
not establish equivalence of informal formulations or the quantum reduction.

From the repository root, after setting up pinned Lean and Mathlib:

  lake build AaronsonAmbainis.Main
  lake env lean audit/OriginalConjecture6.lean

The proof body below was separately checked against the released source at
commit `2a6ceaef872ae993708950f951989134084b851a` in CI run
https://github.com/heathsanchez/test/actions/runs/42485073471 .
-/

namespace IndependentAAAudit

private noncomputable def cubeValue (N : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p

private noncomputable def cubeMean (N : ℕ) (p : MvPolynomial (Fin N) ℝ) : ℝ :=
  (∑ X : Fin N → Bool, cubeValue N p X) / 2 ^ N

private noncomputable def cubeVariance (N : ℕ) (p : MvPolynomial (Fin N) ℝ) : ℝ :=
  (∑ X : Fin N → Bool, (cubeValue N p X - cubeMean N p) ^ 2) / 2 ^ N

private noncomputable def cubeInfluence (N : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (i : Fin N) : ℝ :=
  (∑ X : Fin N → Bool,
    (cubeValue N p X - cubeValue N p (Function.update X i (!X i))) ^ 2) / 2 ^ N

/-! ## Normalization across the two Boolean-cube conventions -/

/-- The ±1 coordinate corresponding to a Boolean coordinate. -/
private def signedCoordinate {N : ℕ} (X : Fin N → Bool) (i : Fin N) : ℝ :=
  if X i then 1 else -1

/-- The value of `f(x) = 2 p((x + 1)/2) - 1` on the signed cube. -/
private noncomputable def signedValue (N : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (X : Fin N → Bool) : ℝ :=
  2 * cubeValue N p X - 1

private noncomputable def signedMean (N : ℕ) (p : MvPolynomial (Fin N) ℝ) : ℝ :=
  (∑ X : Fin N → Bool, signedValue N p X) / 2 ^ N

private noncomputable def signedVariance (N : ℕ) (p : MvPolynomial (Fin N) ℝ) : ℝ :=
  (∑ X : Fin N → Bool, (signedValue N p X - signedMean N p) ^ 2) / 2 ^ N

/-- Fourier normalization on the signed cube uses a half flip difference. -/
private noncomputable def signedInfluence (N : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (i : Fin N) : ℝ :=
  (∑ X : Fin N → Bool,
    ((signedValue N p X - signedValue N p (Function.update X i (!X i))) / 2) ^ 2)
    / 2 ^ N

private theorem signed_value_transform (N : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (X : Fin N → Bool) :
    signedValue N p X =
      2 * MvPolynomial.eval (fun i => (signedCoordinate X i + 1) / 2) p - 1 := by
  have hcoords : (fun i : Fin N => (signedCoordinate X i + 1) / 2) =
      (fun i => if X i then (1 : ℝ) else 0) := by
    funext i
    cases h : X i <;> simp [signedCoordinate, h]
  simp only [signedValue, cubeValue, hcoords]

private theorem signed_mean_eq (N : ℕ) (p : MvPolynomial (Fin N) ℝ) :
    signedMean N p = 2 * cubeMean N p - 1 := by
  have hcard : (∑ _X : Fin N → Bool, (1 : ℝ)) = (2 : ℝ) ^ N := by
    simp
  simp only [signedMean, signedValue, cubeMean, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hcard]
  have hne : (2 : ℝ) ^ N ≠ 0 := by positivity
  field_simp

/-- The affine rescaling quadruples variance. -/
theorem signed_variance_eq (N : ℕ) (p : MvPolynomial (Fin N) ℝ) :
    signedVariance N p = 4 * cubeVariance N p := by
  have h : ∀ X : Fin N → Bool,
      (2 * cubeValue N p X - 1 - (2 * cubeMean N p - 1)) ^ 2 =
        4 * (cubeValue N p X - cubeMean N p) ^ 2 := fun X => by ring
  simp only [signedVariance, cubeVariance, signed_mean_eq, signedValue, h]
  rw [← Finset.mul_sum, mul_div_assoc]

/-- The half-difference convention cancels the affine rescaling in influence. -/
theorem signed_influence_eq (N : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (i : Fin N) :
    signedInfluence N p i = cubeInfluence N p i := by
  have h : ∀ X : Fin N → Bool,
      ((2 * cubeValue N p X - 1 -
        (2 * cubeValue N p (Function.update X i (!X i)) - 1)) / 2) ^ 2 =
        (cubeValue N p X - cubeValue N p (Function.update X i (!X i))) ^ 2 :=
    fun X => by ring
  simp only [signedInfluence, cubeInfluence, signedValue, h]

/-- Original exact-degree premise; `O(1)` means an existential uniform positive exponent.
    No PSI-defined proposition occurs in the specification. -/
def OriginalConjecture6 : Prop :=
  ∃ k : ℕ, 0 < k ∧
    ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree = d →
      (∀ X : Fin N → Bool, 0 ≤ cubeValue N p X ∧ cubeValue N p X ≤ 1) →
      ∀ ε : ℝ, 0 < ε → cubeVariance N p ≥ ε →
        ∃ i : Fin N, cubeInfluence N p i ≥ (ε / (d : ℝ)) ^ k

/-- PSI's exponent `7` supplies a uniform historical exponent; exact degree
    implies the at-most-degree premise. -/
theorem printed_implies_original
    (h : AaronsonAmbainis.PrintedConjecture) : OriginalConjecture6 := by
  refine ⟨7, by norm_num, ?_⟩
  intro N d p hDegree hBound ε hε hVar
  have hBound' :
      ∀ X : Fin N → Bool,
        0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
          MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1 := by
    simpa only [cubeValue] using hBound
  have hVar' :
      (∑ X : Fin N → Bool,
        (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
          - (∑ Y : Fin N → Bool,
              MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p) / 2 ^ N) ^ 2)
        / 2 ^ N ≥ ε := by
    simpa only [cubeVariance, cubeMean, cubeValue] using hVar
  obtain ⟨i, hi⟩ := h N d p (le_of_eq hDegree) hBound' ε hε hVar'
  refine ⟨i, ?_⟩
  simpa only [cubeInfluence, cubeValue] using hi

/-- A non-vacuous 0/1-cube witness: coordinate projection has mean 1/2,
variance 1/4 and unscaled squared bit-flip influence 1. -/
private theorem coordinate_sanity :
    ∃ p : MvPolynomial (Fin 1) ℝ,
      p.totalDegree = 1 ∧
      (∀ X : Fin 1 → Bool, 0 ≤ cubeValue 1 p X ∧ cubeValue 1 p X ≤ 1) ∧
      cubeMean 1 p = (1 : ℝ) / 2 ∧
      cubeVariance 1 p = (1 : ℝ) / 4 ∧
      cubeInfluence 1 p 0 = 1 := by
  let p : MvPolynomial (Fin 1) ℝ := MvPolynomial.X 0
  let x0 : Fin 1 → Bool := fun _ => false
  let x1 : Fin 1 → Bool := fun _ => true
  have h_univ : (Finset.univ : Finset (Fin 1 → Bool)) = {x0, x1} := by decide
  have h_ne : x0 ≠ x1 := by decide
  have hsum (F : (Fin 1 → Bool) → ℝ) :
      (∑ X : Fin 1 → Bool, F X) = F x0 + F x1 := by
    rw [h_univ]
    simp [h_ne]
  have hm : cubeMean 1 p = (1 : ℝ) / 2 := by
    unfold cubeMean
    rw [hsum]
    norm_num [cubeValue, p, x0, x1]
  have hv : cubeVariance 1 p = (1 : ℝ) / 4 := by
    unfold cubeVariance
    rw [hsum]
    norm_num [cubeValue, p, x0, x1, hm]
  have hi : cubeInfluence 1 p 0 = 1 := by
    unfold cubeInfluence
    rw [hsum]
    norm_num [cubeValue, p, x0, x1]
  refine ⟨p, by simp [p], ?_, hm, hv, hi⟩
  intro X
  cases h : X 0 <;> simp [cubeValue, p, h]

/-- A consumer of the original-form statement, without assuming the PSI theorem. -/
theorem historical_conjecture : OriginalConjecture6 :=
  printed_implies_original AaronsonAmbainis.aaronson_ambainis

end IndependentAAAudit

#print axioms IndependentAAAudit.historical_conjecture
#print axioms IndependentAAAudit.signed_variance_eq
#print axioms IndependentAAAudit.signed_influence_eq
