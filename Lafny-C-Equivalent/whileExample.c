/*
// Without pretty syntax

def whileExample' (f : ℕ → ℕ) (hf : ∀ x, Even x → Even (f x)) (n : ℕ) :
    {p : ℕ × ℕ // Even p.2 ∧ p.1 = 0} :=
  let ⟨p, even_p, npos_p⟩ := while_loop_with_invariant'
    (invariant := fun p : ℕ × ℕ => Even p.2)
    (cond := fun p => 0 < p.1)
    (meas := fun p => p.1)
    (init := ⟨(n, 0), by norm_num⟩)
    (next := fun p inv_p p1_gt =>
      have p1_pos : 0 < p.1 := by simpa using p1_gt
      have : p.1 - 2 < p.1 := tsub_lt_self p1_pos (by norm_num)
      ⟨(p.1 - 2, f p.2), ⟨hf _ inv_p, this⟩⟩)
  have : p.1 = 0 := by simpa using npos_p
  ⟨p, even_p, this⟩
*/

#include <stdio.h>

typedef struct {
    int p1;
    int p2;
} state_t;

int foo(int x) {
    return 2 * x + 4;
}

state_t ex(int n, int (*f)(int)) {
    state_t state;
    state.p1 = n;
    state.p2 = 0;

    while (state.p1 > 0) {
        state.p2 = (*f)(state.p2);
        state.p1 -= 2;
    }
    return state;
}

int main() {
    printf("%d\n", ex(12, &foo).p2);
    return 0;
}
