import data.polynomial.ring_division
import data.real.sign

noncomputable theory
open_locale classical


open polynomial
open multiset
open real


def proots (f : polynomial ℝ) := filter (λ x: ℝ, x > 0) (f.roots)
def nproots (f : polynomial ℝ) := (proots f).card

variable (f : polynomial ℝ)

def nonzero_coeff_list (f : polynomial ℝ) := 
list.map f.coeff ( finset.sort nat.le f.support)

noncomputable def list.num_sign_changes : list ℝ → ℕ
| [] := 0
| [h0] := 0
| (h0 :: h1 :: tail) := bool.to_nat (h0 * h1 < 0) + list.num_sign_changes (h1 :: tail)

def num_sign_changes (f : polynomial ℝ) := list.num_sign_changes (nonzero_coeff_list f)

lemma list.parity_sign (S : list ℝ) (h: S ≠ []) : even (S.num_sign_changes - bool.to_nat (S.head * (S.last h) < 0)) :=
begin
  sorry
end


theorem rule_of_signs (f : polynomial ℝ): num_sign_changes f ≥ nproots f ∧ even (num_sign_changes f - nproots f) :=
begin
  sorry
end