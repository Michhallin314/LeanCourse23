import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Minpoly.Basic
set_option linter.unusedVariables false
noncomputable section
open Real Function BigOperators
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 17.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


section LinearMap

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
  [Module R M₁] [Module R M₂] [Module R N]

/- Define the coproduct of two linear maps that send (x, y) ↦ f x + g y. -/

def exercise5_1 (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun := fun (m₁, m₂) ↦ f m₁ + g m₂
  map_add' := by
    simp
    exact fun a b a_1 b_1 ↦ add_add_add_comm (f a) (f a_1) (g b) (g b_1)
  map_smul' := by
    simp
example (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  exercise5_1 f g (x, y) = f x + g y := by rfl -- should be rfl


end LinearMap

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
  prove that the units of a ring form a group.
  Hint: I recommend that you first prove that the product of two units is again a unit,
  and that you define the inverse of a unit separately using `Exists.choose`.
  Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
  (`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

instance exercise5_2 : Group {x : R // IsAUnit x} := by
  have h {x y : R} (h₁ : IsAUnit x) (h₂ : IsAUnit y) : IsAUnit (x * y) := by
    rw [IsAUnit]
    rw [IsAUnit] at h₁ h₂
    obtain ⟨t₁, h₁⟩ := h₁
    obtain ⟨t₂, h₂⟩ := h₂
    use (t₁*t₂)
    rw[mul_comm t₁ t₂, mul_assoc, mul_comm, ← mul_assoc, mul_assoc, mul_comm y t₂, h₁, h₂]
    simp
  --let y := Exists.choose_spec IsAUnit
  --let x := Exists.choose.{x : R // IsAUnit x}
  --let y := (IsAUnit x)^(-1)
  sorry

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by sorry

end Ring



/- The Frobenius morphism in a field of characteristic p is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. -/
#check CharP.cast_eq_zero_iff
#check Finset.sum_congr
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] in
open Nat Finset in
lemma exercise5_3 (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have h2 : p.Prime := hp.out
  have h3 : 0 < p := h2.pos
  have h4 : range p = insert 0 (Ioo 0 p)
  · ext (_|_) <;> simp [h3]
  have h5 : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    intro i h_t
    rw [Ioo, LocallyFiniteOrder.finsetIoo, instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring] at h_t
    have hyp : i ≠ 0 := by
      sorry
    have hyp2 : i < p := by
      sorry
    exact Prime.dvd_choose_self h2 hyp hyp2
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
    calc ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i
     _ = ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by sorry
     _ = 0 := by sorry
  rw[sum_range_succ, h4, insert_eq]
  simp
  rw[sum_eq_add_sum_diff_singleton]
  sorry
  sorry
  sorry


/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).
-/
#check exists_ne
lemma exercise5_4 {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by
  have hₜ : exists_ne M := by sorry
  sorry
