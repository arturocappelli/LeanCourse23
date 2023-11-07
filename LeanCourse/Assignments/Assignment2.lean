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
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
    constructor
    · intro h
      rcases h with ⟨x, h'⟩
      obtain hp|hq := h'
      left
      use x
      right
      use x
    · intro h
      obtain hp|hq := h
      rcases hp with ⟨x, hpx⟩
      use x
      left
      apply hpx
      rcases hq with ⟨x, hqx⟩
      use x
      right
      apply hqx
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is, but let's define it here
ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
  `simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma exercise2_2 (h : SurjectiveFunction (g ∘ f)) : SurjectiveFunction g := by {
  intro y
  rw [SurjectiveFunction] at h
  specialize h y
  rcases h with ⟨x₁, hx₁⟩
  use f x₁
  have h' :  (g ∘ f) x₁ = g (f x₁) := by simp
  rw [← h', hx₁]
  }


/- Hint: you are allowed to use the previous exercise in this exercise! -/
lemma exercise2_3 (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  constructor
  · apply exercise2_2
  intro hg
  rw [SurjectiveFunction] at hf hg
  rw [SurjectiveFunction]
  intro y₁
  specialize hg y₁
  rcases hg with ⟨y₂, hy₂⟩
  specialize hf y₂
  rcases hf with ⟨x, hx⟩
  use x
  have h' :  (g ∘ f) x = g (f x) := by simp
  rw [h', hx, hy₂]
  }


/- Composing a surjective function by a linear function to the left and the right will still result
in a surjective function. The `ring` tactic will be very useful here! -/
lemma exercise2_4 (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  rw [SurjectiveFunction] at hf
  intro y
  set y₁ := (y - 1)/2 with hy₁
  specialize hf y₁
  rcases hf with ⟨x₁, hx₁⟩
  use (x₁ / 3) - 4
  ring
  rw [hx₁]
  ring
  }

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
  intro k
  use k
  simp
  exact fun n a => Nat.mul_le_mul_right (s n) a

/- For the following exercise, it will be useful to know that you can write `max a b`
  to take the maximum of `a` and `b`, and that this lemma holds  -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp


lemma exercise2_6 {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
      rw [EventuallyGrowsFaster] at h₁ h₂
      intro k
      specialize h₁ k
      specialize h₂ k
      obtain ⟨N₁, hN₁⟩ := h₁
      obtain ⟨N₂, hN₂⟩ := h₂
      use max N₁ N₂
      intro n hn
      specialize hN₁ n
      specialize hN₂ n
      have hn₁ : n ≥ N₁ :=
      calc n ≥ max N₁ N₂ := by apply hn
       _ ≥ N₁ := by exact le_max_left N₁ N₂
      have hn₂ : n ≥ N₂ :=
      calc n ≥ max N₁ N₂ := by apply hn
       _ ≥ N₂ := by exact le_max_right N₁ N₂
      specialize hN₁ hn₁
      specialize hN₂ hn₂
      simp [add_def]
      rw [mul_add]
      linarith
    }

/- Optional hard exercise 1:
Find a function that is nowhere zero and grows faster than itself when shifted by one. -/
lemma exercise2_7 : ∃ (s : ℕ → ℕ), EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by sorry



/- Optional hard exercise 2:
Show that a function that satisfies the conditions of the last
exercise, then it must necessarily tend to infinity.
The following fact will be useful. Also, the first step of the proof is already given. -/

lemma useful_fact2 {n m : ℕ} (hn : n ≥ m + 1) : ∃ k ≥ m, k + 1 = n := by sorry

lemma exercise2_8 (hs : EventuallyGrowsFaster (fun n ↦ s (n+1)) s) (h2s : ∀ n, s n ≠ 0) := by  sorry
end Growth
