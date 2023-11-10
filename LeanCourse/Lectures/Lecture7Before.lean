import LeanCourse.Common
open Set Function Real
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)


/- # Today: Numbers and induction

We cover chapter 5 from Mathematics in Lean, and some material about `norm_cast`/`push_cast`
that is not covered in MiL. -/

/-
Last time we discussed sets:
* Set-builder notation: `{ x : X | p x}`;
* Unions/intersections: `⋃ i : ι, C i`, `⋃ i ∈ s, C i` or `⋃₀ C`;
* Images and preimages: `f ⁻¹' s` or `f '' s`;

We also defined the inverse of a function.
-/

/- # Recursion and induction

Let's start by defining our own factorial function.
Note that there is no `:=` -/

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

lemma fac_zero : fac 0 = 1 := by rfl

lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rfl

example : fac 4 = 24 := by rfl

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction n
  case zero =>
    rw [fac]
    norm_num
  case succ n ih =>
    rw [fac]
    sorry

/-
Two useful tactics:
`norm_num`: compute equalities and inequalities involving numerals
`positivity`: can show that something is positive/non-negative from using that its components are positive/non-negative.
-/

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by
  induction n
  case zero =>
    norm_num
  case succ k ih =>
    rw [fac, pow_add, mul_comm]
    gcongr
    exact Nat.le_add_left (2 ^ 1) k


open BigOperators Finset

/- We can use `∑ i in range (n + 1), f i` to take the sum `f 0 + f 1 + ⋯ + f n`. -/

example (f : ℕ → ℝ) : ∑ i in range 0, f i = 0 :=
  sum_range_zero f

example (f : ℕ → ℝ) (n : ℕ) : ∑ i in range (n + 1), f i = (∑ i in range n, f i) + f n :=
  sum_range_succ f n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction n
  · case zero => simp
  · case succ k ih =>
      rw [fac, prod_range_succ, ← ih, mul_comm]

/- The following result is denoted using division of natural numbers.
This is defined as division, rounded down.
This makes it harder to prove things about it, so we generally avoid using it
(unless you actually want to round down sometimes). -/

theorem sum_id (n : ℕ) : (∑ i in range (n + 1), i) = n * (n + 1) / 2 := by
  symm
  rw [Nat.div_eq_of_eq_mul_left]
  norm_num
  symm
  induction n
  · case zero => simp
  · case succ k ih =>
      rw [sum_range_succ, add_mul, ih]
      ring






/- When using division, it is better to do the calculation in the rationals or reals.
Note that we write `(... : ℚ)` in the left hand side to *coerce* the value to the rationals.
In the infoview (right half of your screen), these coercions are denoted with `↑`.

Some tactics that are useful when working with coercions:
* `norm_cast`: pull coercions out of an expression.
  E.g. turn `↑n * ↑m + ↑k` into `↑(n * m + k)`
* `push_cast`: push coercions into an expression.
  E.g. turn `↑(n * m + k)` into `↑n * ↑m + ↑k`

Note: when coercing from `ℕ` to e.g. `ℚ` these tactics will not push/pull casts along `-` or `/`,
since `↑n - ↑m = ↑(n - m)` and `↑n / ↑m = ↑(n / m)` are not always true.
-/

example : (∑ i in range (n + 1), i : ℚ) = n * (n + 1) / 2 := by
  induction n
  case zero => simp
  case succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring



/- Let's define the Fibonacci sequence -/

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib (n + 1) + fib n

/- ## Exercises -/

example : ∑ i in range n, fib (2 * i + 1) = fib (2 * n) := by
  induction n
  case zero => simp
  case succ k ih =>
    rw[sum_range_succ, ih]
    symm
    rw [mul_add]
    symm
    rw [add_comm]
    rfl

example : (∑ i in range n, fib i : ℤ) = fib (n + 1) - 1 := by
  induction n
  case zero => simp
  case succ k ih =>
    rw[sum_range_succ, ih]
    calc ↑(fib (k + 1)) - 1 + ↑(fib k)
     _ = ↑(fib (k + 1)) + (- 1) + ↑(fib k) := by rw [Int.add_neg_one]
     _ = ↑(fib (k + 1)) + ((- 1) + ↑(fib k)) := by rw [Int.add_assoc]
     _ = (- 1) + ↑(fib k) + ↑(fib (k + 1)) := by rw [Int.add_comm]
     _ = (- 1) + (↑(fib k) + ↑(fib (k + 1))) := by rw [Int.add_assoc]
     _ = ↑(fib k) + ↑(fib (k + 1)) + (-1) := by rw [Int.add_comm]
     _ = ↑(fib k) + ↑(fib (k + 1)) - 1 := by rw [Int.add_neg_one]
     _ = ↑((fib k) + (fib (k + 1))) - 1 := by norm_cast
     _ = ↑((fib (k + 1)) + (fib k)) - 1 := by rw [Nat.add_comm]
     _ = ↑(fib (k + 1 + 1)) - 1 := by rfl

example : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n
  case zero => simp
  case succ k ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

example : (∑ i in range (n + 1), i ^ 3 : ℚ) = (n * (n + 1) / 2 : ℚ) ^ 2 := by
  induction n
  case zero => simp
  case succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by
  induction n
  case zero => simp
  case succ k ih =>
    symm
    have h₁ : 2 ^ (k+1) = 2 * 2 ^ k := by rw [Nat.pow_succ']
    have h₂ : fac (k+1) = (k+1) * fac k := by rfl
    --calc fac (k + 1) * 2 ^ (k + 1) * ∏ i in Finset.range (k + 1), (2 * i + 1)
    -- _ = fac (k + 1) * 2 ^ (k + 1) * ∏ i in Finset.range (k + 1), (2 * i + 1)
    rw[prod_range_succ, h₁, h₂, ← mul_assoc, ← mul_assoc, ]
    sorry





/- Let's prove an explicit formula for the Fibonacci sequence.
Along the way, we will want to write and use some lemmas about `ϕ` and `ψ`
  -/

def ϕ : ℝ := (1 + sqrt 5) / 2
def ψ : ℝ := (1 - sqrt 5) / 2

/- `Nat.two_step_induction` can be used to do an induction with 2 induction hypotheses, i.e.
`P n → P (n + 1) → P (n + 2)`. -/

#check Nat.two_step_induction

lemma coe_fib_eq (n : ℕ) : (fib n : ℝ) = (ϕ ^ n - ψ ^ n) / (ϕ - ψ) := by sorry

/- The following lemmas will be useful for this.
`field_simp` is a useful tactic that can often cancel denominators. -/

-- @[simp] lemma ϕ_sub_ψ_ne_zero : ϕ - ψ ≠ 0 := by sorry sorry
-- @[simp] lemma ϕ_sq : ϕ ^ 2 = ϕ + 1 := by sorry sorry
-- @[simp] lemma ψ_sq : ψ ^ 2 = ψ + 1 := by sorry sorry

/- `Nat.strongRec` is used for strong induction-/
#check Nat.strongRec





/- ## A warning on casts
* (in)equalities in different types are not the same statement.
* you can use `norm_cast` to simplify (in)equalities involving casts. -/

example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by
  norm_cast at h
  exact h.symm

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by
  gcongr
  norm_cast

example (n : ℤ) (h : 0 < n) : 0 < sqrt n := by
  rw [sqrt_pos]
  norm_cast

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by
  norm_cast

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by
  norm_cast

/- We can also induct on various other inductively defined types.

`Nat.le_induction` is used to induct in equalities of the natural numbers. -/
theorem fac_dvd_fac (n m : ℕ) (h : n ≤ m) : fac n ∣ fac m := by sorry



open Topology Filter

/- `TopologicalSpace.generateFrom` is the smallest topology containing
a specific collection of sets. It is defined inductively. -/
#check TopologicalSpace.generateFrom

open TopologicalSpace
theorem le_generateFrom_iff_subset_isOpen {α : Type*} {t : TopologicalSpace α}
    {g : Set (Set α)} (h : g ⊆ { s | IsOpen[t] s }) :
    { s | IsOpen[generateFrom g] s } ⊆ { s | IsOpen[t] s } := by sorry





/- One can also state, prove and use induction principle for objects whose definition
is not inductive. -/

#check IsCompact.induction_on

#check Submodule.span_induction

#check IntermediateField.induction_on_adjoin
