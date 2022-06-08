import data.polynomial.ring_division
import data.polynomial.field_division
import ring_theory.localization.fraction_ring
import data.real.sign

noncomputable theory
open_locale classical big_operators polynomial


open polynomial
open multiset
open real

def proots (f : polynomial ℝ) := filter (λ x: ℝ, x > 0) (f.roots)

def inv_p_proots (f : polynomial ℝ) := multiset.map (λ (x : ℝ), 1/x) (proots f)

variables {f g : polynomial ℝ} [ f ≠ 0 ] [ g ≠ 0 ]
 [↑(multiset.card (proots f)) = polynomial.degree f]
 [multiset.card (proots f) = multiset.card (proots g)]
 [ polynomial.monic f ] [ polynomial.monic g ] {α : ℝ}

    
--   [comm_ring R] [is_domain R]

def ι {R : Type*} [comm_ring R] [is_domain R]:  R →+* fraction_ring R :=
⟨λ x, localization.mk x 1, localization.mk_one, by norm_num,
by norm_num, by norm_num⟩

lemma factor_iff {R : Type*} [comm_ring R] [is_domain R]
[cancel_comm_monoid_with_zero R]
[unique_factorization_monoid R]
( r : R[X]) (p q: (fraction_ring R)[X])
(h : p * q = (map ι r)) : ∃ p' : R[X], p = (map ι p')
:=
begin
  sorry
end

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
lemma prod_multiset_X_sub_C_dvd' {R : Type*}
[comm_ring R] [is_domain R] [cancel_comm_monoid_with_zero R]
[unique_factorization_monoid R] (p : R[X]) :
  (multiset.map (λ (a : R), X - C a) p.roots).prod ∣ p :=
begin
  let Q := fraction_ring R,
  let p' := map (algebra_map R Q) p,
  have h1 := prod_multiset_X_sub_C_dvd p',
  have h2 : map (algebra_map R Q) (map (λ (a : R), X - C a) p.roots).prod ∣ 
  (map (λ (a : Q), X - C a) p'.roots).prod,
  {
    -- use something about prod of subsets
    sorry
  },
  have h3 : map (algebra_map R Q) (map (λ (a : R), X - C a) p.roots).prod ∣ p',
  {
    exact dvd_trans h2 h1,
  },
  clear h1 h2,
  obtain ⟨r, hr⟩ := h3,
  have : ∃ r1, polynomial.map (algebra_map R Q) r1 = r,
  {
    -- apply Gauss' lemma
    sorry,
  },
  obtain ⟨r1, hr1⟩ := this,
  use r1,
  -- use injectivity of localization map
  sorry
end

lemma pol_factor {R : Type*} [field R] (f : polynomial R) :
multiset.prod (multiset.map (λ (α : R), (X - C α)) f.roots) ∣ f :=
begin
  exact prod_multiset_X_sub_C_dvd' f,
end

lemma a_formula 
  (h : polynomial.degree f = multiset.card (f.roots))
  (H : f.leading_coeff = 1)
  (n: ℕ) (hn: f.degree = ↑n) (n > 1) :
  f.coeff (n-1) = sum f.roots :=
begin
  sorry
end

lemma card_inv (hgf : inv_p_proots f = g.roots) : multiset.card (proots g) = 3 :=
begin
  sorry
end

example (hgf : inv_p_proots f = proots g) : f.coeff 2 * g.coeff 2 ≥ 3 :=
begin
  sorry
end
