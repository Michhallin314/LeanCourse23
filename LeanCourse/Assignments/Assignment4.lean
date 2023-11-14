import LeanCourse.Common
set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.

* You can use any lemmas or tactics from mathlib.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ i in range (n + 1), i : ℚ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    symm
    rw [sum_range_succ]
    symm
    rw [ih]
    simp
    symm
    rw [add_sq]
    have h : (∑ i in range (n + 1), i : ℚ) = n*(n+1)/2 := by
      clear ih
      induction n with
      | zero => simp
      | succ n ih₂ =>
        rw [sum_range_succ, ih₂]
        push_cast
        ring
    rw [h]
    ring

open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by
  have h := wf.wf.has_min
  rw[Pairwise]
  constructor
  · intro i j h₁
    intro X h₂ h₃
    simp at h₂ h₃
    simp
    by_contra hyp
    push_neg at hyp
    sorry
  · ext x
    simp
    constructor
    · intro h₁
      obtain ⟨i, hi⟩ := h₁
      specialize hC i
      use i
      have hyp1 : A i \ ⋃ j < i, A j ⊆ A i := by exact diff_subset (A i) (⋃ j, ⋃ (_ : j < i), A j)
      have hyp2 : C i ⊆ A i := by exact Eq.trans_subset hC hyp1
      exact hyp2 hi
    · intro h₁
      obtain ⟨i, hi⟩ := h₁
      by_cases x ∈ A i \ ⋃ j < i, A j
      · use i
        specialize hC i
        rw[hC]
        exact h
      · have hyp : x ∈ ⋃ j < i, A j := by
          simp
          -- combination of hi and h and the fact that it is a linear order
          sorry
        /-
        rw [mem_iUnion₂] at hyp
        obtain ⟨k, hk⟩ := hyp
        obtain ⟨l, hl⟩ := hk
        use k
        specialize hC k
        have hyp1 : A k \ ⋃ j < k, A j ⊆ C k := by exact Eq.subset (id hC.symm)
        -/
        sorry


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers.

Note: any field mentioning `div`, `npow` or `zpow` are fields that you don't have to give when
defining a group. These are operations defined in terms of the group structure. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h

lemma exercise4_3 : Group PosReal := by
  have  h : Monoid PosReal := by
    have h₁ : Semigroup PosReal := by
      sorry
    have h_temp : One PosReal := by
      sorry
    have h₂ : ∀ (a : PosReal), (One PosReal) * a = a := by
      sorry
    have h₃ : ∀ (a : PosReal), a * (One PosReal) = a := by
      sorry
    have h₄ : ℕ → PosReal → PosReal := by
      exact fun a a => a
    --apply?
    sorry
  refine groupOfIsUnit ?h
  intro a
  --use
  sorry

/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
  constructor
  · intro h₁
    rw [Nat.prime_def_lt] at h₁
    push_neg at h₁
    by_cases 2 ≤ n
    · specialize h₁ h
      right
      right
      obtain ⟨m, hm1, hm2, hm3⟩ := h₁
      have hyp : m ≠ 0 := by sorry
      have hyp2 : 2 ≤ m := by sorry
      use m
      let m₂ := n/m
      use m₂
      sorry
    · push_neg at h
      --left
      sorry
  · intro h
    obtain h₁|h₂|h₃ := h
    · rw [h₁]
      exact Nat.not_prime_zero
    · rw [h₂]
      exact Nat.not_prime_one
    · obtain ⟨a, b, h₁, h₂, h₃⟩ := h₃
      by_contra h
      rw[Nat.Prime] at h
      have hyp : IsUnit a ∨ IsUnit b := by exact Irreducible.isUnit_or_isUnit h h₃
      obtain hyp1|hyp2 := hyp
      · simp at hyp1
        rw [hyp1] at h₁
        simp at h₁
      · simp at hyp2
        rw [hyp2] at h₂
        simp at h₂


lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp at hn
  · simp at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [pow_mul]
      _ ≡ ((2 : ℤ) ^ a - 1 + 1) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [Int.sub_add_cancel]
      _ ≡ (0 + 1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [Int.zero_add]
      _ ≡ 1 - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw[one_pow]
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by rw[Int.sub_self]
  have h2 : 2 ^ 2 ≤ 2 ^ a := by
    gcongr
    linarith
  have h3 : 1 ≤ 2 ^ a := by linarith
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    rw [Nat.pow_mul, Nat.pow_right_comm]
    have h_temp : 2 < 2 ^ b := by
      calc 2
       _ = 2 ^ 1 := by rfl
       _ < 2 ^ 2 := by linarith
       _ ≤ 2 ^ b := by {gcongr; linarith}
    gcongr
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by
    gcongr
    · linarith
    · calc 0
       _ ≤ 4 := by linarith
       _ = 2 * 2 := by rfl
       _ ≤ a * b := by exact Nat.mul_le_mul ha hb
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  obtain ⟨hn1, hn2⟩ := hn
  specialize hn2 (2^a-1) h5 h'
  exact h4 hn2


/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/
lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by
  by_contra h
  push_neg at h
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨x, h₁⟩ := h₁
  obtain ⟨y, h₂⟩ := h₂
  sorry
