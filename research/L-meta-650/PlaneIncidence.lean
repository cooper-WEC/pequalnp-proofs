import Mathlib
import PEqualNP.Defs

namespace PlaneIncidence650

open PEqualNP.CircuitLowerBounds

private lemma edgeCons650 (x : Fin 26 → Bool) (a b : ℕ) (ha : a < 26) (hb : b < 26) (es : List (ℕ × ℕ)) :
    (∃ u v : Fin 26, (u.val, v.val) ∈ (a, b) :: es ∧ x u = true ∧ x v = true) ↔
    (x ⟨a, ha⟩ = true ∧ x ⟨b, hb⟩ = true) ∨
      ∃ u v : Fin 26, (u.val, v.val) ∈ es ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Or.inl ⟨(show u = ⟨a, ha⟩ from Fin.ext h1) ▸ hu, (show v = ⟨b, hb⟩ from Fin.ext h2) ▸ hv⟩
    · exact Or.inr ⟨u, v, h, hu, hv⟩
  · rintro (⟨h1, h2⟩ | ⟨u, v, h, hu, hv⟩)
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, List.mem_cons_self, h1, h2⟩
    · exact ⟨u, v, List.mem_cons_of_mem _ h, hu, hv⟩

def circuit : Circuit where
  gates := [
    ⟨.or, [13, 14]⟩,
    ⟨.or, [16, 22]⟩,
    ⟨.or, [26, 27]⟩,
    ⟨.and, [0, 28]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [21, 25]⟩,
    ⟨.or, [30, 31]⟩,
    ⟨.and, [1, 32]⟩,
    ⟨.or, [14, 20]⟩,
    ⟨.or, [24, 25]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.and, [2, 36]⟩,
    ⟨.or, [13, 19]⟩,
    ⟨.or, [23, 24]⟩,
    ⟨.or, [38, 39]⟩,
    ⟨.and, [3, 40]⟩,
    ⟨.or, [18, 22]⟩,
    ⟨.or, [23, 25]⟩,
    ⟨.or, [42, 43]⟩,
    ⟨.and, [4, 44]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.or, [46, 47]⟩,
    ⟨.and, [5, 48]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.or, [50, 51]⟩,
    ⟨.and, [6, 52]⟩,
    ⟨.or, [15, 19]⟩,
    ⟨.or, [20, 22]⟩,
    ⟨.or, [54, 55]⟩,
    ⟨.and, [7, 56]⟩,
    ⟨.or, [14, 18]⟩,
    ⟨.or, [19, 21]⟩,
    ⟨.or, [58, 59]⟩,
    ⟨.and, [8, 60]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.or, [62, 63]⟩,
    ⟨.and, [9, 64]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [19, 25]⟩,
    ⟨.or, [66, 67]⟩,
    ⟨.and, [10, 68]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [18, 24]⟩,
    ⟨.or, [70, 71]⟩,
    ⟨.and, [11, 72]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [17, 23]⟩,
    ⟨.or, [74, 75]⟩,
    ⟨.and, [12, 76]⟩,
    ⟨.or, [29, 33]⟩,
    ⟨.or, [37, 41]⟩,
    ⟨.or, [45, 49]⟩,
    ⟨.or, [53, 57]⟩,
    ⟨.or, [61, 65]⟩,
    ⟨.or, [69, 73]⟩,
    ⟨.or, [78, 79]⟩,
    ⟨.or, [80, 81]⟩,
    ⟨.or, [82, 83]⟩,
    ⟨.or, [84, 85]⟩,
    ⟨.or, [86, 77]⟩,
    ⟨.or, [87, 88]⟩]
  output := 89

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem size64 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 64 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  refine ⟨circuit, ?_, rfl, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := rfl
    rw [hx]
    simp only [circuit, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [edgeCons650 x 0 13 (by decide) (by decide)]
    rw [edgeCons650 x 0 14 (by decide) (by decide)]
    rw [edgeCons650 x 0 16 (by decide) (by decide)]
    rw [edgeCons650 x 0 22 (by decide) (by decide)]
    rw [edgeCons650 x 1 13 (by decide) (by decide)]
    rw [edgeCons650 x 1 15 (by decide) (by decide)]
    rw [edgeCons650 x 1 21 (by decide) (by decide)]
    rw [edgeCons650 x 1 25 (by decide) (by decide)]
    rw [edgeCons650 x 2 14 (by decide) (by decide)]
    rw [edgeCons650 x 2 20 (by decide) (by decide)]
    rw [edgeCons650 x 2 24 (by decide) (by decide)]
    rw [edgeCons650 x 2 25 (by decide) (by decide)]
    rw [edgeCons650 x 3 13 (by decide) (by decide)]
    rw [edgeCons650 x 3 19 (by decide) (by decide)]
    rw [edgeCons650 x 3 23 (by decide) (by decide)]
    rw [edgeCons650 x 3 24 (by decide) (by decide)]
    rw [edgeCons650 x 4 18 (by decide) (by decide)]
    rw [edgeCons650 x 4 22 (by decide) (by decide)]
    rw [edgeCons650 x 4 23 (by decide) (by decide)]
    rw [edgeCons650 x 4 25 (by decide) (by decide)]
    rw [edgeCons650 x 5 17 (by decide) (by decide)]
    rw [edgeCons650 x 5 21 (by decide) (by decide)]
    rw [edgeCons650 x 5 22 (by decide) (by decide)]
    rw [edgeCons650 x 5 24 (by decide) (by decide)]
    rw [edgeCons650 x 6 16 (by decide) (by decide)]
    rw [edgeCons650 x 6 20 (by decide) (by decide)]
    rw [edgeCons650 x 6 21 (by decide) (by decide)]
    rw [edgeCons650 x 6 23 (by decide) (by decide)]
    rw [edgeCons650 x 7 15 (by decide) (by decide)]
    rw [edgeCons650 x 7 19 (by decide) (by decide)]
    rw [edgeCons650 x 7 20 (by decide) (by decide)]
    rw [edgeCons650 x 7 22 (by decide) (by decide)]
    rw [edgeCons650 x 8 14 (by decide) (by decide)]
    rw [edgeCons650 x 8 18 (by decide) (by decide)]
    rw [edgeCons650 x 8 19 (by decide) (by decide)]
    rw [edgeCons650 x 8 21 (by decide) (by decide)]
    rw [edgeCons650 x 9 13 (by decide) (by decide)]
    rw [edgeCons650 x 9 17 (by decide) (by decide)]
    rw [edgeCons650 x 9 18 (by decide) (by decide)]
    rw [edgeCons650 x 9 20 (by decide) (by decide)]
    rw [edgeCons650 x 10 16 (by decide) (by decide)]
    rw [edgeCons650 x 10 17 (by decide) (by decide)]
    rw [edgeCons650 x 10 19 (by decide) (by decide)]
    rw [edgeCons650 x 10 25 (by decide) (by decide)]
    rw [edgeCons650 x 11 15 (by decide) (by decide)]
    rw [edgeCons650 x 11 16 (by decide) (by decide)]
    rw [edgeCons650 x 11 18 (by decide) (by decide)]
    rw [edgeCons650 x 11 24 (by decide) (by decide)]
    rw [edgeCons650 x 12 14 (by decide) (by decide)]
    rw [edgeCons650 x 12 15 (by decide) (by decide)]
    rw [edgeCons650 x 12 17 (by decide) (by decide)]
    rw [edgeCons650 x 12 23 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true_iff, Bool.and_eq_true_iff, and_or_left, or_and_right]
    apply Iff.of_eq
    ac_rfl

end PlaneIncidence650
