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

example {R : Type*}  [comm_ring R] [is_domain R] (p : R[X]) (a : R):
root_multiplicity a p = count a p.roots :=
begin
sorry
end

example {R : Type*} {α β : multiset R} (h : α ≤ β)
(a : R) : count a α ≤ count a β :=
begin
refine le_iff_count.mp h a,
end

example {R S : Type*} [comm_ring R] [comm_ring S]
[is_domain R] [is_domain S]
(f : R →+* S) (h : function.injective f) (p : R[X]) :
map f p.roots ≤ 
((polynomial.map_ring_hom f) p).roots :=
begin
simp,
rw le_iff_count,
intro a,
apply polynomial.count_map_roots h a,
end

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
lemma prod_multiset_X_sub_C_dvd' {R : Type*}
[comm_ring R] [is_domain R] [cancel_comm_monoid_with_zero R]
[unique_factorization_monoid R] (p : R[X]) :
  (multiset.map (λ (a : R), X - C a) p.roots).prod ∣ p :=
begin
  let Q := fraction_ring R,
  let ι := algebra_map R Q,
  let ι' : R[X] →+* Q[X] := polynomial.map_ring_hom ι,
  let p' := map ι p,
  have h1 := prod_multiset_X_sub_C_dvd p',
  have h2 : ι' (map (λ (a : R), X - C a) p.roots).prod ∣ 
  (map (λ (a : Q), X - C a) p'.roots).prod,
  {
    have haux : ∀ a : R,
    ι' (X - C a) = X - C (ι a),
    {
      intro a,
      norm_num,
    },
    rw map_multiset_prod,
    have :
    (map ι' ((map (λ (a : R), X - C a) p.roots))).prod
    = (((map (λ (a : R), X - C (ι a)) p.roots))).prod,
    {
      apply congr_arg multiset.prod,
      simp only [←haux],
      apply multiset.map_map,
    },
    rw this,
    clear this,
    have : (map ι p.roots) ≤ p'.roots,
    {
      

    },
    -- (map (λ (a : R), X - C ((algebra_map R Q) a)) p.roots).prod
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
  have : map (algebra_map R Q) p = map (algebra_map R Q) ((map (λ (a : R), X - C a) p.roots).prod * r1),
  {
    rwa [polynomial.map_mul, hr1],
  },
  have map_inj : function.injective (algebra_map R Q),
  {
    exact is_fraction_ring.injective R Q,
  },
  obtain pol_map_inj := polynomial.map_injective (algebra_map R Q) map_inj,
  exact pol_map_inj this,
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

