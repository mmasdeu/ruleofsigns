import data.polynomial.ring_division
import data.polynomial.field_division
import data.polynomial.inductions
import ring_theory.polynomial.basic
import data.real.sign
import data.quot
import order.hom.basic
import data.fin.tuple.basic
import tactic


noncomputable theory
open_locale classical


open multiset

variables {R : Type*} [linear_ordered_field R]

def polynomial.positive_roots (f : polynomial R) :=
f.roots.filter (λ x, 0 < x)

def polynomial.number_positive_roots (f : polynomial R) :=
f.positive_roots.card


variables {p q f : polynomial R}

open polynomial

@[simp] lemma smul_eq {a : R} : C a * p = a • p :=
begin
rw smul_eq_C_mul,
end

lemma mem_positive_roots {x : R} :
x ∈ p.positive_roots ↔ x ∈ p.roots ∧ 0 < x :=
by rw [positive_roots, mem_filter]

/--
The set of positive roots of X-a is {a} when 0 < a
-/
lemma positive_roots_X_sub_C_of_zero_lt {a : R} (h : 0 < a) :
(X - C a).positive_roots = {a} :=
begin
  rw positive_roots,
  rw roots_X_sub_C,
  rw filter_eq_self,
  simp [h],
end

lemma positive_roots_X : polynomial.positive_roots (@X R _) = ∅ :=
begin
  rw polynomial.positive_roots,
  rw roots_X,
  simp,
  rw filter_eq_nil,
  intros a ha,
  simp at ha,
  subst ha,
  exact irrefl 0,
end


/--
The positive roots of the monic normalization of f
-/
lemma positive_roots_normalize_eq_positive_roots :
  (normalize f).positive_roots = f.positive_roots :=
begin
  rw [positive_roots, roots_normalize],
  refl,
end

/--
The positive roots of the product of two polinomials
-/
lemma positive_roots_mul {p q : polynomial R}
(hpq : p * q ≠ 0):
  (p * q).positive_roots = p.positive_roots + q.positive_roots :=
begin
  rw [positive_roots, roots_mul hpq, filter_add],
  refl,
end

lemma positive_roots_X_pow (i : ℕ):
polynomial.positive_roots ((@X R _)^i) = ∅ :=
begin
  rw positive_roots,
  rw roots_pow,
  simp [filter_eq_nil],
  intros a ha,
  replace ha := mem_of_mem_nsmul ha,
  simp at ha,
  linarith [ha],
end
/--
The positive roots don't change when multiplying by X
-/
lemma positive_roots_mul_X (hp : p ≠ 0) :
  p.positive_roots = (p * X).positive_roots :=
begin
  have hnz : p * X ≠ 0 := mul_ne_zero hp X_ne_zero,
  rw [positive_roots_mul hnz, positive_roots_X],
  simp only [empty_eq_zero, add_zero],
end


lemma X_pow_ne_zero {i : ℕ} : (X : polynomial R)^i ≠ 0 :=
begin
  induction i with d hd,
  { simp only [pow_zero, ne.def, one_ne_zero, not_false_iff] },
  { apply mul_ne_zero X_ne_zero hd }
end

lemma positive_roots_mul_X_pow {i : ℕ} (hp : p ≠ 0) :
  (p * X^i).positive_roots = p.positive_roots :=
begin
rw positive_roots_mul (mul_ne_zero hp X_pow_ne_zero),
rw positive_roots_X_pow,
simp only [empty_eq_zero, add_zero],
end

-- Proposition 1 of Levin
/--
If all coefficients of p are non-negative, then p has no positive roots.
-/
lemma positive_roots_empty_of_positive_coeffs (h : ∀ n ∈ p.support, 0 < p.coeff n) :
  p.positive_roots = ∅ :=
begin
  by_contra he,
  have hp : p ≠ 0,
  {
    intro hp,
    apply he,
    rw [positive_roots, hp, roots_zero, empty_eq_zero, filter_zero]
  },
  --cases exists_mem_of_ne_zero he with x hx,
  obtain ⟨x, hx⟩ := exists_mem_of_ne_zero he,
  cases mem_positive_roots.mp hx with hxr hxp,
  rw [mem_roots hp, is_root.def, eval_eq_sum] at hxr,
  apply lt_irrefl (0 : R),
  nth_rewrite_rhs 0 ← hxr,
  convert finset.sum_lt_sum_of_nonempty _ _,
  swap,
  exact 0,
  simp only [pi.zero_apply, finset.sum_const_zero],
  exact nonempty_support_iff.mpr hp,
  intros n hn,
  specialize h n hn,
  rw [pi.zero_apply],
  exact mul_pos h (pow_pos hxp n),
end



/--
The list of nonzero coefficients of a polynomial
-/
def polynomial.nonzero_coeff_list
(f : polynomial R) := (f.support.sort (≤)).map f.coeff

open list

lemma list.sorted_of_monotone (l : list R) (hl : sorted (≤) l)
(g : R →o R) : sorted (≤) (map g l) :=
list.pairwise.map g.1 g.2 hl

lemma list.sort_commutes_monotone (S : list ℕ)
(g : ℕ →o ℕ) : (S.merge_sort (≤)).map g = (S.map g).merge_sort (≤)
:=
begin
  apply @eq_of_perm_of_sorted ℕ (≤),
  {
    calc
    map ⇑g (merge_sort has_le.le S) ~ map g.1 S : by {
      apply list.perm.map,
      apply perm_merge_sort,
    }
    ... ~ merge_sort has_le.le (map ⇑g S) : by {
      symmetry,
      apply perm_merge_sort,
    }
  },
  {
    apply pairwise.map g.1 g.2,
    apply sorted_merge_sort,
  },
  apply sorted_merge_sort,
end

lemma multiset.sort_commutes_monotone (S : multiset ℕ)
(g : ℕ ↪o ℕ) : (sort (≤) S).map g = sort (≤)
(multiset.map g S)
:=
begin
  set l : list ℕ := S.to_list,
  rw show S = (l : multiset ℕ), by simp only [coe_to_list],
  rw (show (sort has_le.le ↑l) = merge_sort (≤) l, by exact multiset.coe_sort (≤) l),
  rw (show (sort has_le.le (map ⇑g ↑l)) = merge_sort (≤) (map g l), by exact multiset.coe_sort (≤) _),
  apply list.sort_commutes_monotone l g,
end

/--
The support doesn't change when scaling by a nonzero constant
-/
lemma polynomial.support_smul_of_ne_zero (f : polynomial R) {a : R} (h : a ≠ 0) : (a • f).support = f.support :=
begin
  ext,
  simp [h],
end

lemma polynomial.nonzero_coeff_list_smul (f : polynomial R) {a : R} (hc : a ≠ 0) :
(a • f).nonzero_coeff_list = f.nonzero_coeff_list.map (λ x, a * x) :=
begin
  simp only [polynomial.nonzero_coeff_list],
  rw polynomial.support_smul_of_ne_zero f hc,
  have : (a• f).coeff = λ n, a * (f.coeff n),
  {
    ext n,
    simp [coeff_smul],
  },
  simp [this],
end

/--
The number of sign changes in a list
-/
def list.num_sign_changes : list R → ℕ
| [] := 0
| [a] := 0
| (a :: b :: tail) :=
bool.to_nat (a * b < 0) + list.num_sign_changes (b :: tail)

lemma list.num_sign_changes_smul (l : list R) (c : R) (hc : c ≠ 0) :
l.num_sign_changes = (l.map (λ x, c * x)).num_sign_changes :=
begin
induction l with a tail HI,
{
  refl,
},
{
  induction tail with b tail HI2,
  {
    refl,
  },
  {
    simp at *,
    rw list.num_sign_changes,
    rw list.num_sign_changes,
    rw HI,
    simp_rw show (a * b < 0) = (c * a * (c * b) < 0), by
    {
      ext,
      rw show (c * a * ( c * b) = c^2 * (a * b)), by ring,
      have hc' : 0 < c^2 := pow_two_pos_of_ne_zero c hc,
      split;
      {
        intro H,
        nlinarith [H],
      },
    },
  }
}

end

/--
The number of sign changes of a  polynomial
-/
def polynomial.num_sign_changes (f : polynomial R) :=
f.nonzero_coeff_list.num_sign_changes


lemma polynomial.num_sign_changes_smul (f : polynomial R) (c : R) (hc : c ≠ 0) :
(c • f).num_sign_changes = f.num_sign_changes :=
begin
  rw polynomial.num_sign_changes,
  rw polynomial.num_sign_changes,
  rw f.nonzero_coeff_list_smul hc,
  rw ← list.num_sign_changes_smul _  _ hc,
end

lemma polynomial.support_mul_X (f : polynomial R) :
(f * X).support = f.support.map ⟨nat.succ, nat.succ_injective⟩ :=
begin
  ext i,
  cases i with i i,
  {
    simp only [mem_support_iff, mul_coeff_zero, coeff_X_zero, mul_zero,
    ne.def, eq_self_iff_true, not_true, finset.mem_map,
    function.embedding.coe_fn_mk, exists_false],
  },
  split;
  {
    intro hi,
    simpa using hi,
  },
end


lemma polynomial.support_mul_X_pow {i : ℕ} (f : polynomial R) :
(f * X^i).support = f.support.map ⟨nat.add i, add_right_injective i⟩ :=
begin
  induction i with i hi,
  {
    ext,
    simp,
  },
  {
    sorry
  }
end

lemma polynomial.nonzero_coeff_list_mul_X (f : polynomial R) :
  (f * X).nonzero_coeff_list = f.nonzero_coeff_list :=
begin
  repeat {rw polynomial.nonzero_coeff_list},
  rw polynomial.support_mul_X,
  ext i a,
  simp [coeff_mul_X],
  split,
  {
    intro ha,
    obtain ⟨j, ⟨hj1, hj2⟩⟩ := ha,
    cases j,
    {
      simp at hj2,
      subst hj2,
      simp at hj1,
      sorry
    },
    rw coeff_mul_X at hj2,
    use j,
    split,
    {
      sorry
    },
    exact hj2,
  },
  {
    sorry
  }
end

lemma polynomial.num_sign_changes_mul_X (f : polynomial R):
(f * X).num_sign_changes = f.num_sign_changes :=
begin
  rw polynomial.num_sign_changes,
  rw polynomial.num_sign_changes,
  congr' 1,
  apply polynomial.nonzero_coeff_list_mul_X,
end

lemma polynomial.num_sign_changes_mul_X_pow (f : polynomial R) (i : ℕ):
(f * X^i).num_sign_changes = f.num_sign_changes :=
begin
  induction i with n hn,
  {
    simp only [pow_zero, mul_one],    
  },
  {
    rw show f * X ^ n.succ = (f * X^n) * X, by ring_nf,
    rw polynomial.num_sign_changes_mul_X,
    exact hn,
  }
end

/--
The number of sign changes can be computed on the monic normalization
-/
lemma num_sign_changes_normalize_eq_num_sign_changes :
  (normalize p).num_sign_changes = p.num_sign_changes :=
begin
  have hnz := (norm_unit (leading_coeff p)).ne_zero,
  simp only [coe_norm_unit, coeff_mul_C, normalize_apply],
  rw ← p.num_sign_changes_smul (norm_unit p.leading_coeff) hnz,
  congr' 1,
  rw smul_eq_C_mul,
  ring,
end

lemma coeff_mul_X_sub_C' {p : polynomial R} {r : R} {a : ℕ} :
  coeff (p * (X - C r)) a = (if 0 < a then coeff p (a - 1) else 0) - coeff p a * r :=
begin
  split_ifs,
  { have : a = (a - 1) + 1 := by omega,
    rw [this, coeff_mul_X_sub_C],
    simp, },
  { have : a = 0 := by omega, simp [this], },
end

-- Lemma 2 of Levin
/--
For all α > 0, the polynomial (X-α) * p has at least one more sign change than p
-/
lemma num_sign_changes_X_sub_C_mul' {x : R} (hx : 0 < x) (hp : coeff p 0 ≠ 0) :
  p.num_sign_changes + 1 ≤ ((X - C x : polynomial R) * p).num_sign_changes :=
begin
  sorry
end

lemma num_sign_changes_X_sub_C_mul {x : R} (hx : 0 < x) :
  p.num_sign_changes + 1 ≤ ((X - C x : polynomial R) * p).num_sign_changes :=
begin
  have : ∃ q, ∃ (i : ℕ), p = q * X^i ∧ q.coeff 0 ≠ 0,
  {
    sorry
  },
  obtain ⟨q, ⟨i, ⟨rfl, hnz⟩⟩⟩ := this,
  rw polynomial.num_sign_changes_mul_X_pow,
  rw show (X - C x) * (q * X^i) = ((X - C x) * q) * X^i, by ring,
  rw polynomial.num_sign_changes_mul_X_pow,
  exact num_sign_changes_X_sub_C_mul' hx hnz,
end

theorem descartes_sign_rule_1'  (hp : p ≠ 0) : p.number_positive_roots ≤ p.num_sign_changes :=
begin
  rw number_positive_roots,
  induction h : p.positive_roots.card generalizing p hp,
  { exact zero_le (p.num_sign_changes), },
  { obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp (by rw h; exact nat.succ_pos n),
    rw mem_positive_roots at hx,
    rw ← h,
    have := mul_div_eq_iff_is_root.mpr ((mem_roots hp).mp hx.1),
    rw ← this at hp,
    have hkey : (p / (X - C x)).positive_roots.card = n,
    {
      rw [← this, positive_roots_mul hp] at h,
      simp [card_add, positive_roots_X_sub_C_of_zero_lt hx.2] at h,
      exact nat.succ.inj h
    },
    rw [← this, positive_roots_mul, card_add],
    {
    calc (X - C x).positive_roots.card + (p / (X - C x)).positive_roots.card = 1 + (p / (X - C x)).positive_roots.card : by simp [positive_roots_X_sub_C_of_zero_lt hx.2]
      ... ≤ 1 + (p / (X - C x)).num_sign_changes : nat.add_le_add_left _ 1
      ... = (p / (X - C x)).num_sign_changes + 1 : add_comm _ _
      ... ≤ ((X - C x) * (p / (X - C x))).num_sign_changes : num_sign_changes_X_sub_C_mul hx.2,
      rw hkey,
      apply ih (right_ne_zero_of_mul hp),
      exact hkey,
    },
    exact hp,
  },
end

theorem descartes_sign_rule_1 (hp : p ≠ 0) : p.number_positive_roots ≤ p.num_sign_changes :=
begin
  by_cases hp0 :  p.coeff 0 = 0,
  {
    sorry
  },
  {
    exact descartes_sign_rule_1' hp,
  }
end

lemma list.parity_sign (S : list ℝ) (h: S ≠ []) : even (S.num_sign_changes - bool.to_nat (S.head * (S.last h) < 0)) :=
begin
  sorry
end

theorem descartes_sign_rule_2' {f : polynomial R} (hf : f.monic) : even (f.num_sign_changes - f.number_positive_roots) :=
begin
  sorry
end

theorem descartes_sign_rule_2 {f : polynomial R} (hf : f ≠ 0) : even (f.num_sign_changes - f.number_positive_roots) :=
begin
  rw ← num_sign_changes_normalize_eq_num_sign_changes,
  rw number_positive_roots,
  rw ←positive_roots_normalize_eq_positive_roots,
  exact descartes_sign_rule_2' (polynomial.monic_normalize hf),
end