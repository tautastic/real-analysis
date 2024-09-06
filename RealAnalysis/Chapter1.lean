import Mathlib.tactic

namespace chapter1
universe u
variable (α : Type u)

/-Exercise 1.5 a-/
theorem union_eq_left (A B : Set α) : A ∪ B = A ↔ B ⊆ A := by
  sorry

/-Exercise 1.5 b-/
theorem inter_eq_left (A B : Set α) : A ∩ B = A ↔ A ⊆ B := by
  sorry

/-Lemmas needed for Exercise 1.5 c-/
lemma diff_eq_inter_compl (A B : Set α) : A \ B = A ∩ Bᶜ := by rfl
lemma inter_assoc (A B C: Set α) : A ∩ B ∩ C = A ∩ (B ∩ C) := Set.ext fun _ => and_assoc
lemma mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := by rfl

/-Exercise 1.5 c-/
theorem diff_eq_left (A B : Set α) : A \ B = A ↔ A ∩ B = ∅ := by
  sorry

/-Exercise 1.5 d-/
theorem diff_eq_empty (A B : Set α) : A \ B = ∅ ↔ A ⊆ B := by
  sorry

/-Exercise 1.7 a-/
theorem id_injective {f : X → Y} {g : Y → X}
(hId : ∀ x, (g ∘ f) x = x) : Function.Injective (g ∘ f) := by
  sorry

/-Exercise 1.7 b-/
theorem id_surjective {f : X → Y} {g : Y → X}
(hId : ∀ x, (g ∘ f) x = x) : Function.Surjective (g ∘ f) := by
  sorry

/-Extra Exercise-/
theorem id_bijective {f : X → Y} {g : Y → X}
(hId : ∀ x, (g ∘ f) x = x) : Function.Bijective (g ∘ f)  := by
  sorry

/-Exercise 1.8 a-/
theorem compl_inter (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  sorry

/-Exercise 1.8 b-/
theorem compl_union (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  sorry

/-Exercise 1.10-/
theorem mul_id_unique {F : Type*} [Field F] {e1 e2 : F}
(h1 : ∀ x : F, e1 * x = x) (h2 : ∀ x : F, e2 * x = x) : e1 = e2 := by
  sorry

/-Exercise 1.12 a-/
theorem lt_add_trans {F : Type*} [LinearOrderedField F] {a b c d : F}
(h1: a < b) (h2: c < d) : a + c < b + d := by
  sorry

/-Exercise 1.12 b-/
theorem not_necessarily_lt_mul {F : Type*} [LinearOrderedField F] :
(∃ a b c d : F, a < b ∧ c < d ∧ b * d ≤ a * c) := by
  sorry

/-Exercise 1.14-/
theorem abs_mul_eq_mul_abs {a b : ℝ} : |a * b| = |a| * |b| := by
  sorry

/-Exercise 1.17-/
theorem pow_lt {a b : ℝ} (h1: 0 < a) (h2: a < b) : ∀ n : ℕ+, a ^ (n: ℕ) < b ^ (n: ℕ) := by
  sorry

end chapter1
