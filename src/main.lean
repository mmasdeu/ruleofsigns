import data.polynomial.ring_division
import data.real.sign

noncomputable theory
open_locale classical


open polynomial
open multiset
open real

-- def sign_changes (f : polynomial ℝ) := sorry

def proots (f : polynomial ℝ) := filter (λ x: ℝ, x > 0) (f.roots)
def nproots (f : polynomial ℝ) := (proots f).card

variable (f : polynomial ℝ)
#check f.coeff
def nonzero_coeff_list (f : polynomial ℝ) := 
list.map f.coeff ( finset.sort nat.le f.support)

def sign_change : (option ℝ) → (option ℝ) → Prop
| none a := false
| b none := false
| (some a) (some b) := a * b < 0

def changes_sign (f : polynomial ℝ) (i : ℕ) :=
sign_change ((nonzero_coeff_list f).nth i)  ((nonzero_coeff_list f).nth (i+1))

theorem rule_of_signs (f : polynomial ℝ): :=
begin
  sorry
end