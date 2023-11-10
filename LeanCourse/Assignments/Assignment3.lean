import LeanCourse.Common
import LeanCourse.MIL.C03_Logic.solutions.Solutions_S06_Sequences_and_Convergence
set_option linter.unusedVariables false
open Nat Real Function Set

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 3 and 6
  Read chapter 4, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 3.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


/- Prove the law of excluded middle without using `by_cases` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by
  by_contra h
  push_neg at h
  exact (not_and_self_iff p).1 h




/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_2 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by
  rw [SequentialLimit]
  rw [SequentialLimit] at hs
  intro ε hε
  rcases hs ε hε with ⟨N₁, hN₁⟩
  specialize hr N₁
  obtain ⟨N₂, hN₂⟩ := hr
  use N₂
  intro n hn
  have h : (s ∘ r) n = s (r n) := by simp
  rw [h]
  exact hN₁ (r n) (hN₂ n hn)


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma exercise3_3 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by
  rw [SequentialLimit]
  rw [SequentialLimit] at hs₁ hs₃
  intro ε hε
  specialize hs₁ ε hε
  specialize hs₃ ε hε
  obtain ⟨N₁, hN₁⟩ := hs₁
  obtain ⟨N₂, hN₂⟩ := hs₃
  let N := max N₁ N₂
  use N
  intro n hn
  rw [abs_lt]
  have h : n ≥ max N₁ N₂ ↔ n ≥ N₁ ∧ n ≥ N₂ := by simp
  have hn' : n ≥ N₁ ∧ n ≥ N₂ := by exact Nat.max_le.mp hn
  obtain ⟨hn₁, hn₂⟩ := hn'
  specialize hN₁ n hn₁
  specialize hN₂ n hn₂
  rw [abs_lt] at hN₁ hN₂
  specialize hs₁s₂ n
  specialize hs₂s₃ n
  constructor
  · calc -ε
     _ < s₁ n - a := by exact hN₁.1
     _ ≤ s₂ n - a := by exact sub_le_sub_right hs₁s₂ a
  · calc s₂ n - a
     _ ≤ s₃ n - a := by exact sub_le_sub_right hs₂s₃ a
     _ < ε := by exact hN₂.2


/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)

lemma exercise3_4 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by
  rw [SequentialLimit]
  intro ε hε
  use ⌈1/ε⌉₊
  intro n hn
  rw [abs_lt]
  constructor
  · calc -ε
     _ < 0 := by exact neg_lt_zero.mpr hε
     _ < 1 / (↑n + 1) := by exact one_div_pos_of_nat
     _ = 1 / (↑n + 1) - 0 := by rw [sub_zero]
  · rw [sub_zero]
    have h (h : 1/ε < (↑n + 1)) : 1 / (↑n + 1) < ε := by
      have h₀ : 0 < n + 1 := by exact succ_pos n
      have hε₂ : 0 < 1 / ε := by exact one_div_pos.mpr hε
      simp
      simp at h
      have h₀₀ : 0 < ((n+1) : ℝ) := by exact cast_add_one_pos n
      simp only [one_div] at hε₂
      exact (inv_lt h₀₀ hε).mpr h
    apply h
    calc 1 / ε
     _ ≤ ⌈1 / ε⌉₊ := by exact le_ceil (1 / ε)
     _ ≤ n := by exact cast_le.mpr hn
     _ < n + 1 := by norm_num


/- Use the previous exercises to prove that `n ↦ sin n / (n + 1)` converges to 0.
  I will prove for you that `n ↦ -1 / (n + 1)` also converges to `0`. -/

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel' ε ?hb; positivity

lemma use_me : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by
  have : SequentialLimit (fun n ↦ (-1) * (1 / (n+1))) (-1 * 0) :=
    convergesTo_mul_const (-1) exercise3_4
  simp at this
  simp [neg_div, this]

lemma exercise3_5 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by
  have h₁ : ∀ (n : ℕ), -1 / (↑n + 1) ≤ sin ↑n / (↑n + 1) := by
    intro n
    gcongr
    exact neg_one_le_sin ↑n
  have h₂ : ∀ (n : ℕ), sin ↑n / (↑n + 1) ≤ 1 / (↑n + 1) := by
    intro n
    gcongr
    exact sin_le_one ↑n
  have h₃ : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by exact exercise3_4
  have h₄ : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by exact use_me
  exact exercise3_3 h₄ h₃ h₁ h₂

/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_6 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by
  rw [SequentialLimit] at h1
  rw [NondecreasingSequence] at h2
  by_contra h3
  push_neg at h3
  obtain ⟨n, hn⟩ := h3
  have hn₂ : u n - l > 0 := by exact sub_pos.mpr hn
  rcases h1 (u n - l) hn₂ with ⟨N, hN⟩
  specialize h2 n
  rcases lt_trichotomy n N with h₁|h₂|h₃
  · specialize hN N
    specialize h2 N
    have hyp1 : n ≤ N := by exact Nat.le_of_lt h₁
    simp at hN
    have hyp2 : u N - l ≥ u n - l := by exact sub_le_sub_right (h2 hyp1) l
    have hyp3 : u N - l > 0 := by exact LT.lt.trans_le hn₂ hyp2
    have hyp4 : |u N - l| = u N - l := by exact abs_of_pos hyp3
    rw [hyp4] at hN
    linarith
  · let m := N + 1
    have hyp : n + 1 ≥ N := by exact le.intro (congrFun (congrArg HAdd.hAdd (id h₂.symm)) 1)
    specialize hN (n+1) hyp
    specialize h2 (n+1) (le_add_right n 1)
    have hyp2 : u (n+1) - l ≥ u n - l := by exact sub_le_sub_right h2 l
    have hyp3 : u (n+1) - l > 0 := by exact LT.lt.trans_le hn₂ hyp2
    have hyp4 : |u (n+1) - l| = u (n+1) - l := by exact abs_of_pos hyp3
    rw [hyp4] at hN
    linarith
  · have hyp : n + 1 > N := by exact Nat.lt_add_right N n 1 h₃
    have hyp' : n + 1 ≥ N := by exact Nat.le_of_lt hyp
    specialize hN (n+1) hyp'
    specialize h2 (n+1) (le_add_right n 1)
    have hyp2 : u (n+1) - l ≥ u n - l := by exact sub_le_sub_right h2 l
    have hyp3 : u (n+1) - l > 0 := by exact LT.lt.trans_le hn₂ hyp2
    have hyp4 : |u (n+1) - l| = u (n+1) - l := by exact abs_of_pos hyp3
    rw [hyp4] at hN
    linarith


/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/


lemma exercise3_7 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  rw [image_inter_preimage]

lemma exercise3_8 :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by
  rw [preimage_setOf_eq]
  refine ext ?h
  intro x
  constructor
  · rw [@mem_union]
    intro h
    rw [@mem_setOf] at h
    rw [mem_setOf]
    rw [mem_setOf]
    have h₁ : 4 ≤ x ^ 2 := by exact h
    have h₂ : 2 ^ 2 ≤ x ^ 2 := by
      /-calc (2 ^ 2)
       _ = 2 * 2 := by rw[sq]
       _ = 2 + 2 := by rw[two_add]
      -/
      --Why can't I prove that 4 is 2^2?
      sorry
    have h₃ : |2| ≤ |x| := by exact sq_le_sq.mp h₂
    rw [le_abs] at h₃
    obtain h₃₁|h₃₂ := h₃
    · right
      simp at h₃₁
      exact h₃₁
    · left
      simp at h₃₂
      exact le_neg.mpr h₃₂
  · intro h
    rw [mem_union] at h
    rw [@mem_setOf] at h
    rw [mem_setOf] at h
    rw [mem_setOf]
    have h₁ : 4 ≤ x ^ 2 → x ^ 2 ≥ 4 := by exact fun a => a
    have h₂ : 2 ^ 2 ≤ x ^ 2 → 4 ≤ x ^ 2 := by
      intro h₂
      /-
      calc 4
       _ = 2 + 2 := by exact?
       _ = 2 * 2 := by rw[two_add]
      -/
      --Why can't I prove that 4 is 2^2?
      sorry
    have h₃ : |2| ≤ |x| → 2 ^ 2 ≤ x ^ 2 := by
      --exact fun a => (fun {R} [LinearOrderedRing R] {x y} => sq_le_sq.mpr) a
      --Why does exact? give incorrect hint?
      sorry
    apply h₁
    apply h₂
    apply h₃
    rw [le_abs]
    obtain ha|hb := h
    · right
      simp
      exact le_neg.mpr ha
    · left
      simp
      exact hb

/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses.
  Remember: you can use `simp [hyp]` to simplify using hypothesis `hyp`. -/
lemma exercise3_9 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
  have h1' : ∀ x y, f x ≠ g y
  · intro x y h
    apply h1.subset
    exact ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
  have h1'' : ∀ y x, g y ≠ f x
  · intro x y
    symm
    apply h1'
  have h2' : ∀ x, x ∈ range f ∪ range g := eq_univ_iff_forall.1 h2
  have hf' : ∀ x x', f x = f x' ↔ x = x' := fun x x' ↦ hf.eq_iff
  let L : Set α × Set β → Set γ :=
    fun (s, t) ↦ sorry
  let R : Set γ → Set α × Set β :=
    fun s ↦ sorry
  sorry
