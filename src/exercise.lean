import data.polynomial.ring_division
import data.real.sign

noncomputable theory
open_locale classical


open polynomial
open multiset
open real

def proots (f : polynomial ℝ) := filter (λ x: ℝ, x > 0) (f.roots)

def inv_p_proots (f : polynomial ℝ) := multiset.map (λ (x : ℝ), 1/x) (proots f)

variables {f g : polynomial ℝ} [ f ≠ 0 ] [ g ≠ 0 ]
 [↑(multiset.card (proots f)) = polynomial.degree f]
 [multiset.card (proots f) = multiset.card (proots g)]
 [ polynomial.monic f ] [ polynomial.monic g ]


lemma a_formula 
  (h : ↑(multiset.card (proots f)) = polynomial.degree f) 
  (H : f.leading_coeff = 1)
  (n: ℕ) (hn: f.degree = ↑n) (n > 1) :
  f.coeff (n-1) = sum(proots f) :=
begin
  sorry
end

lemma roots_proots : proots f = f.roots :=
begin
  sorry
end

lemma card_inv (hgf : inv_p_proots f = proots g) : multiset.card (proots g) = 3 :=
begin
  sorry
end

example (hgf : inv_p_proots f = proots g) : f.coeff 2 * g.coeff 2 ≥ 3 :=
begin
  sorry
end
