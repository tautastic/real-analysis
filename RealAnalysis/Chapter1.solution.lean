import Mathlib.tactic

namespace chapter1
universe u
variable (α : Type u)

/-Exercise 1.5 a-/
theorem union_eq_left (A B : Set α) : A ∪ B = A ↔ B ⊆ A := by
  constructor
  -- Forward direction
  · intro h
    intro x hB
    have : x ∈ A ∪ B := Or.inr hB
    rw [h] at this
    exact this
  -- Backward direction
  · intro h
    ext x
    constructor
    · intro hAB
      cases hAB with
      | inl hA => exact hA
      | inr hB => exact h hB
    · intro hA
      exact Or.inl hA

/-Exercise 1.5 b-/
theorem inter_eq_left (A B : Set α) : A ∩ B = A ↔ A ⊆ B := by
  constructor
  -- Forward direction
  · intro h
    intro x hA
    rw [← h] at hA
    exact hA.right
  -- Backward direction
  · intro h
    ext x
    constructor
    · intro hAB
      exact hAB.left
    · intro hA
      exact ⟨hA, (h hA)⟩

/-Lemmas needed for Exercise 1.5 c-/
lemma diff_eq_inter_compl (A B : Set α) : A \ B = A ∩ Bᶜ := by rfl
lemma inter_assoc (A B C: Set α) : A ∩ B ∩ C = A ∩ (B ∩ C) := Set.ext fun _ => and_assoc
lemma mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := by rfl

/-Exercise 1.5 c-/
theorem diff_eq_left (A B : Set α) : A \ B = A ↔ A ∩ B = ∅ := by
  constructor
  -- Forward direction
  · intro h
    rw [← h, diff_eq_inter_compl, inter_assoc]
    simp
  -- Backward direction
  · intro h
    ext x
    constructor
    · rw [mem_diff]
      apply And.left
    · intro hA
      rw [mem_diff]
      constructor
      exact hA
      · intro hB
        have hAB : x ∈ A ∩ B := ⟨hA, hB⟩
        rw [h] at hAB
        contradiction

/-Exercise 1.5 d-/
theorem diff_eq_empty (A B : Set α) : A \ B = ∅ ↔ A ⊆ B := by
  constructor
  -- Forward direction
  . intros h x hA
    by_contra hB
    have : x ∈ A \ B := ⟨hA, hB⟩
    rw [h] at this
    exact this
  -- Backward direction
  . intro h
    ext x
    constructor
    . intro hx
      cases hx with
      | intro hA hB =>
        have : x ∈ B := h hA
        contradiction
    . intro hx
      contradiction

/-Exercise 1.7 a-/
theorem id_injective {f : X → Y} {g : Y → X}
(hId : ∀ x, (g ∘ f) x = x) : Function.Injective (g ∘ f) := by
  unfold Function.Injective
  by_contra h
  push_neg at h
  choose x1 x2 h using h
  have hNeq : x1 ≠ x2 := h.2
  have hEq : x1 = x2 := by rw [←hId x1, ←hId x2, h.1]
  contradiction

/-Exercise 1.7 b-/
theorem id_surjective {f : X → Y} {g : Y → X}
(hId : ∀ x, (g ∘ f) x = x) : Function.Surjective (g ∘ f) := by
  unfold Function.Surjective
  by_contra h
  push_neg at h
  choose x1 h using h
  revert h
  simp at hId ⊢
  rw [← hId x1]
  use x1

/-Extra Exercise-/
theorem id_bijective {f : X → Y} {g : Y → X}
(hId : ∀ x, (g ∘ f) x = x) : Function.Bijective (g ∘ f)  := by
  unfold Function.Bijective
  exact ⟨id_injective hId, (id_surjective hId)⟩

/-Exercise 1.8 a-/
theorem compl_inter (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  constructor
  -- Forward direction
  · intro h
    cases Classical.em (x ∈ A) with
    | inl hA => right; intro hB; exact h ⟨hA, hB⟩
    | inr hNA => left; exact hNA
  -- Backward direction
  · intro h hAB
    cases h with
    | inl hNA => exact hNA hAB.left
    | inr hNB => exact hNB hAB.right

/-Exercise 1.8 b-/
theorem compl_union (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  -- Forward direction
  · intro h
    exact ⟨fun hA => h (Or.inl hA), fun hB => h (Or.inr hB)⟩
  -- Backward direction
  · intro h hAB
    cases hAB with
    | inl hA => exact h.left hA
    | inr hB => exact h.right hB

/-Exercise 1.10-/
theorem mul_id_unique {F : Type*} [Field F] {e1 e2 : F}
(h1 : ∀ x : F, e1 * x = x) (h2 : ∀ x : F, e2 * x = x) : e1 = e2 := by
  rw [← h1 e2]
  nth_rewrite 1 [← h2 e1]
  rw [mul_comm e2 e1]

/-Exercise 1.12 a-/
theorem lt_add_trans {F : Type*} [LinearOrderedField F] {a b c d : F}
(h1: a < b) (h2: c < d) : a + c < b + d := by
  linarith -- Mega lame :/

/-Exercise 1.12 b-/
theorem not_necessarily_lt_mul {F : Type*} [LinearOrderedField F] :
(∃ a b c d : F, a < b ∧ c < d ∧ b * d ≤ a * c) := by
  use -1, 0, -1, 0
  refine ⟨?_, ?_, ?_⟩
  all_goals norm_num

/-Exercise 1.14-/
theorem abs_mul_eq_mul_abs {a b : ℝ} : |a * b| = |a| * |b| := by
  sorry

/-Exercise 1.17-/
theorem pow_lt {a b : ℝ} (h1: 0 < a) (h2: a < b) : ∀ n : ℕ+, a ^ (n: ℕ) < b ^ (n: ℕ) := by
  intro n
  induction n with
    | mk k h3 =>
      · simp
        refine pow_lt_pow_left h2 h1.le h3.ne'

end chapter1
