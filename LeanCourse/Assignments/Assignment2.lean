import LeanCourse.Common
set_option linter.unusedVariables false
open Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 3, 4 and 5
  Read chapter 3, sections 1, 2, 4, 5.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 27.10.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/

lemma exercise2_1 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    obtain hx1|hx2 := hx
    · left
      use x
    · right
      use x
  · intro h
    obtain ⟨x, hp⟩|h := h
    · use x
      left
      assumption
    · obtain ⟨x, hq⟩ := h
      use x
      right
      assumption
section Surjectivity

/- Lean's mathematical library knows what a surjective function is, but let's define it here
ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
  `simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma exercise2_2 (h : SurjectiveFunction (g ∘ f)) : SurjectiveFunction g := by
  rw [SurjectiveFunction]
  rw [SurjectiveFunction] at h
  intro y
  rcases h y with ⟨x₂, hx₂⟩
  use f x₂
  have h₁ : (g ∘ f) x₂ = g (f x₂) := by simp
  rw [← h₁]
  assumption

/- Hint: you are allowed to use the previous exercise in this exercise! -/
lemma exercise2_3 (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  constructor
  · have h : (h : SurjectiveFunction (g ∘ f)) → SurjectiveFunction g := by exact fun h => exercise2_2 h
    exact h
  · intro hg
    rw [SurjectiveFunction]
    rw [SurjectiveFunction] at hf
    rw [SurjectiveFunction] at hg
    intro y
    rcases hg y with ⟨x₁, hx₁⟩
    rcases hf x₁ with ⟨x₂, hx₂⟩
    use x₂
    have h₁ : (g ∘ f) x₂ = g (f x₂) := by simp
    rw [h₁, hx₂, hx₁]

/- Composing a surjective function by a linear function to the left and the right will still result
in a surjective function. The `ring` tactic will be very useful here! -/
lemma exercise2_4 (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  intro y
  rw [SurjectiveFunction] at hf
  rcases hf ((y-1)/2) with ⟨x₁, hx₁⟩
  use (x₁/3-4)
  have h : (fun x => 2 * f (3 * (x + 4)) + 1) (x₁/3-4) = 2 * f (3 * ((x₁/3-4) + 4)) + 1 := by simp
  rw [h]
  calc 2 * f (3 * (x₁ / 3 - 4 + 4)) + 1
   _ = 2 * f (3 * (x₁ / 3)) + 1 := by simp
   _ = 2 * f (3 * x₁ / 3) + 1 := by rw [mul_div]
   _ = 2 * f (3 / 3 * x₁) + 1 := by rw [mul_div_right_comm]
   _ = 2 * f (1 * x₁) + 1 := by rw [div_self_of_invertible]
   _ = 2 * f x₁ + 1 := by rw [one_mul]
   _ = 2 * ((y-1)/2) + 1 := by rw [hx₁]
   _ = 2 * (y - 1) / 2 + 1 := by rw [mul_div]
   _ = 2 / 2 * (y - 1) + 1 := by rw [mul_div_right_comm]
   _ = 1 * (y - 1) + 1 := by rw [div_self_of_invertible]
   _ = y - 1 + 1 := by rw [one_mul]
   _ = y := by rw [sub_add_cancel]

end Surjectivity





section Growth

/- Given two sequences of natural numbers `s` and `t`. We say that `s` eventually grows faster than
  `t` if for all `k : ℕ`, `s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

variable {s t : ℕ → ℕ} {k : ℕ}

/- Hint: `simp` can help you simplify expressions like the following.
  Furthermore, `gcongr` will be helpful! -/
example : (fun n ↦ n * s n) k = k * s k := by simp

lemma exercise2_5 : EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  rw [EventuallyGrowsFaster]
  intro j
  use j
  simp
  intro n
  intro h
  exact mul_le_mul_right (s n) h

/- For the following exercise, it will be useful to know that you can write `max a b`
  to take the maximum of `a` and `b`, and that this lemma holds  -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

lemma exercise2_6 {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  rw [EventuallyGrowsFaster]
  rw [EventuallyGrowsFaster] at h₁
  rw [EventuallyGrowsFaster] at h₂
  intro j
  rcases h₁ j with ⟨N₁, hN₁⟩
  rcases h₂ j with ⟨N₂, hN₂⟩
  let N := max N₁ N₂
  use N
  intro n hn
  have h : n ≥ N₁ ∧ n ≥ N₂ := by exact (useful_fact N₁ N₂ n).mp hn
  obtain ⟨hn₁, hn₂⟩ := h
  specialize hN₁ n hn₁
  specialize hN₂ n hn₂
  calc j * (t₁ + t₂) n
   _ = j * (t₁ n + t₂ n) := by rw [Pi.add_apply]
   _ = j * t₁ n + j * t₂ n := by rw [mul_add]
   _ ≤ s₁ n + j * t₂ n := by exact Nat.add_le_add_right hN₁ (j * t₂ n)
   _ ≤ s₁ n + s₂ n := by exact Nat.add_le_add_left hN₂ (s₁ n)
   _ = (s₁ + s₂) n := by rw [Pi.add_apply]


/- Optional hard exercise 1:
Find a function that is nowhere zero and grows faster than itself when shifted by one. -/
lemma exercise2_7 : ∃ (s : ℕ → ℕ), EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  use fun n ↦ 2^(n^2)
  constructor
  · rw [EventuallyGrowsFaster]
    intro j
    use j
    intro n hn

    have h (h : j ≤ 2 ^ (2*n + 1)) : j * 2 ^ n ^ 2 ≤ 2 ^ (n + 1) ^ 2 := by
      sorry
    apply h
    have h₁ : j ≤ 2 ^ (2*j + 1) := by
      sorry
    have h₂ : 2 ^ (2*j + 1) ≤ 2 ^ (2*n + 1) := by
      gcongr
      simp
    calc j
     _ ≤ 2 ^ (2*j + 1) := h₁
     _ ≤ 2 ^ (2*n + 1) := h₂
  · intro n
    -- wrong ↓
    /-have h {f : ℕ → ℕ} (h₁ : 2^(n^2) ≠ 0) : (∃ n₀ : ℕ, 2^(n₀^2) ≠ 0) ∧ (∀ n₁ : ℕ, ∀ n₂ : ℕ, 2^((n₁+n₂)^2) = 2^(n₁^2) * 2^(n₂^2)) := by
      constructor
      · exact Exists.intro n h₁
      ·
        sorry
    -/
    --specialize h (fun n ↦ 2^(n^2))
    sorry


/- Optional hard exercise 2:
Show that a function that satisfies the conditions of the last
exercise, then it must necessarily tend to infinity.
The following fact will be useful. Also, the first step of the proof is already given. -/

lemma useful_fact2 {n m : ℕ} (hn : n ≥ m + 1) : ∃ k ≥ m, k + 1 = n := by
  use n - 1
  constructor
  · exact le_pred_of_lt hn
  · have : 1 ≤ n := by exact one_le_of_lt hn
    exact Nat.sub_add_cancel this

lemma exercise2_8 (hs : EventuallyGrowsFaster (fun n ↦ s (n+1)) s) (h2s : ∀ n, s n ≠ 0) :
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, s n ≥ k := by
  have h3s : ∀ n, 1 ≤ s n := by
    intro n
    exact one_le_iff_ne_zero.mpr (h2s n)

  sorry



end Growth
