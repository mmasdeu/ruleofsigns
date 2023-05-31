import data.polynomial.ring_division
import data.polynomial.field_division
import data.polynomial.inductions
import data.polynomial.coeff
import ring_theory.polynomial.basic
import data.real.sign
import data.quot
import order.hom.basic
import data.fin.tuple.basic
import tactic


noncomputable theory
open_locale classical big_operators


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
(multiset.map g S) :=
begin
  set l : list ℕ := S.to_list,
  rw show S = (l : multiset ℕ), by simp only [coe_to_list],
  rw (show (sort has_le.le ↑l) = merge_sort (≤) l, by exact multiset.coe_sort (≤) l),
  rw (show (sort has_le.le (map ⇑g ↑l)) = merge_sort (≤) (map g l), by exact multiset.coe_sort (≤) _),
  apply list.sort_commutes_monotone l g,
end

lemma finset.sort_commutes_monotone (S : finset ℕ)
(g : ℕ ↪o ℕ) : (finset.sort (≤) S).map g = finset.sort (≤) (finset.map g.1 S) :=
begin
  repeat {rw finset.sort},
  apply multiset.sort_commutes_monotone,
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
@[simp]
noncomputable def list.num_sign_changes : list R → ℕ
| [] := 0
| [a] := 0
| (a :: b :: tail) :=
ite (b = 0) (list.num_sign_changes (a :: tail))
(bool.to_nat (a * b < 0) + list.num_sign_changes (b :: tail))

@[simp]
lemma tt_to_nat_eq_one : tt.to_nat = 1 := rfl

@[simp]
lemma ff_to_nat_eq_zero : ff.to_nat = 0 := rfl

@[simp]
lemma list.num_sign_changes_of_eq_signs (a b : R) (tail : list R) (h : 0 < a * b): 
list.num_sign_changes (a :: b :: tail) = 
list.num_sign_changes (b :: tail) :=
begin
  have hb : b ≠ 0,
  {
    intro hc,
    simpa [hc] using h,
  },
  simp [hb,asymm h],
end

@[simp]
lemma list.num_sign_changes_of_neq_signs {a b : R} (h : a * b < 0) (l : list R) :
list.num_sign_changes (a :: b :: l) = 1 + list.num_sign_changes (b :: l) :=
begin
  have hb : b ≠ 0,
  {
    intro hc,
    simpa [hc] using h,
  },
  simp [h, hb],
end

@[simp]
lemma list.num_sign_changes_zero {a : R} (ha : a = 0) (l : list R) :
list.num_sign_changes (a :: l) = list.num_sign_changes l :=
begin
  rw ha,
  induction l with b tail,
  {
    simp,
  },
  by_cases hb : b = 0;
  {
    simp [hb],
    try {refl},
  },
end

@[simp]
lemma list.num_sign_changes_zero' {a b : R} (ha : b = 0) (l : list R) :
list.num_sign_changes (a :: b :: l) = list.num_sign_changes (a :: l) :=
begin
  simpa using ha,
end

lemma list.num_sign_changes_drop_while (l : list R) :
list.num_sign_changes l = list.num_sign_changes (drop_while (eq 0) l) :=
begin
  induction l with a tail,
  {
    simp [drop_while],
  },
  simp [drop_while],
  by_cases h : a = 0,
  {
    subst h,
    simpa using l_ih,
  },
  {
    simp [show ¬ (0 = a), by exact ne_comm.mp h],
  }
end


@[simp]
lemma list.num_sign_changes_eq_sign'
{l : list R} {a : R} (ha : 0 < a) :
list.num_sign_changes (a :: l) =
list.num_sign_changes (1 :: l) :=
begin
  have h : 0 < a * (1 : R),
  {
    simp [ha],
  },
  induction l with b l HI,
  --cases l with b l,
  {
    simp,
  },
  rcases (@trichotomous _ (<) _ b 0) with hb|hb|hb,
  {
    have hab : a * b < 0,
    {
      nlinarith [ha, hb],
    },
    sorry

  },
  {
    simp [hb, HI],
  },
  {
    sorry
  }
end


@[simp]
lemma list.num_sign_changes_eq_sign''
{a : R} (ha : a < 0) (l : list R) :
list.num_sign_changes (a :: l) =
list.num_sign_changes (-1 :: l) :=
begin
  sorry,
end


notation `V` := list.num_sign_changes

example (tail : list R):
V ((1 :: 2 :: -1 :: 3 :: 2 :: tail) : list R)
=
V ((1 :: 2 :: -1 :: 3 :: 5 :: tail) : list R)
:=
begin
norm_num,
end

lemma list.num_sign_changes_smul (l : list R) {c : R}
(hc : c ≠ 0) :
l.num_sign_changes = (l.map (λ x, c * x)).num_sign_changes :=
begin
induction l with a tail HI,
{
  refl,
},
{
  induction tail with b tail HI2,
  {
    simp,
  },
  {
    have hc : (a * b < 0) = (c * a * (c * b) < 0), by
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
    simp at *,
    rw HI,
    by_cases b = 0;
      simp [*] at *,
  }
}
end

lemma list.num_sign_changes_neg (l : list R) :
l.num_sign_changes = (l.map (λ x, -x)).num_sign_changes :=
begin
have h : -(1:R) ≠ 0, by linarith,
rw list.num_sign_changes_smul _ h,
simp,
end


lemma list.filter_zero_num_sign_changes (l : list R) :
(filter (not ∘ (eq 0)) l).num_sign_changes =
l.num_sign_changes :=
begin
induction l with a tail,
{
  simp,
},
by_cases h : a = 0,
{
  subst h,
  simpa using l_ih,
},
replace h := ne_comm.mp h,
simp [list.filter, h] at l_ih ⊢,
sorry
end

@[simp]
def list.integral : list R → list R
| [] := []
| (a :: tail) := a :: list.map (λ x, a+x) (tail.integral)

@[simp] lemma list.aux_integral (a₀ a₁ : R) (t : list R) :
(a₀ :: a₁ :: t).integral.tail = ((a₀ + a₁) :: t).integral := by norm_num

lemma list.integral_smul  (t : list R) (c : R):
t.integral.map (λ x, c * x) = (t.map (λ x, c * x)).integral :=
begin
  sorry
end

lemma list.integral_neg  (t : list R) :
t.integral.map (has_neg.neg) = (t.map (has_neg.neg)).integral :=
begin
  have : has_neg.neg =  (λ x, -(1:R) * x), by simp,
  rw this,
  rw list.integral_smul,
end

@[simp]
lemma list.integral_num_sign_changes_zero  (t : list R) :
(0 :: t).integral.num_sign_changes = t.integral.num_sign_changes :=
begin
simp only [list.integral, zero_add, map_id'', list.num_sign_changes_zero],
end

@[simp]
lemma list.integral_num_sign_changes_zero' (a : R)
(ha : a = 0)  (t : list R) :
(a :: t).integral.num_sign_changes = 
t.integral.num_sign_changes :=
begin
simp only [ha, list.integral, zero_add, map_id'', list.num_sign_changes_zero],
end

lemma list.integral_filter_zero_num_sign_changes (l : list R) :
(filter (not ∘ (eq 0)) l).integral.num_sign_changes =
(l.integral).num_sign_changes :=
begin
induction l with a tail,
{
  simp,
},
by_cases h : a = 0,
{
  subst h,
  simpa using l_ih,
},
replace h := ne_comm.mp h,
simp [list.filter, h] at l_ih ⊢,
sorry
end


lemma list.ilast_simp1 [inhabited R]
  (tail : list R) : ∀ a b : R,
  (a :: b :: tail).ilast = (b :: tail).ilast :=
begin
  induction tail with c t,
  {
    simp [ilast],
  },
  {
    simp [ilast],
    intros b,
    specialize tail_ih b c,
    rw tail_ih,
  }
end

lemma list.ilast_simp2 [inhabited R]
  {tail : list R} (h : tail ≠ list.nil) : ∀ a b : R,
  (a :: b :: tail).ilast = (a :: tail).ilast :=
begin
  induction tail with c t,
  {
    contradiction,
  },
  {
    simp [ilast],
    intros b,
    rw list.ilast_simp1,
  }
end

lemma key_lemma_aux [inhabited R]
(a₀ a₁ : R) (h : a₁ ≠ 0) (h1 : a₀ + a₁ = 0):
  ∃ (m : ℕ), V (a₀ :: a₁ :: []) =
  V ((a₀ :: a₁ :: []).integral) + 2*m+1 :=
begin
use 0,
rw show a₀ = -a₁, by linarith [h1],
simp [h],
end

/-
lemma key_lemma' [inhabited R] (a₀ a₁ a₂ : R) (t : list R) (h2 : a₂ ≠ 0):
  ∃ (m : ℕ), V (a₀ :: a₁ :: a₂ :: t) = V ((a₀ :: a₁ :: a₂ :: t).integral) + 2*m+1 :=
begin
  induction t with a₃ tail,
  {
    sorry,
  },
  {
    rcases (@trichotomous _ (<) _ a₀ 0) with h0|h0|h0,
    work_on_goal 2
    {
      subst h0,
      rw list.integral_num_sign_changes_zero at ⊢ t_ih,
      rw @list.num_sign_changes_zero _ _ (0 : R) (by refl) at ⊢ t_ih,
      sorry
    },
    all_goals {rcases (@trichotomous _ (<) _ a₁ 0) with h1|h1|h1};
    sorry,
    sorry,
  }
end
-/

@[simp]
lemma list.ilast_singleton [inhabited R] (a : R) : [a].ilast = a := rfl

lemma list.nil_of_length_zero {l : list R} : l.length = 0 → l = nil :=
begin
intro h,
cases l, refl, simpa using h,
end

lemma aux_1'
{t : list R} (a₀ a₁ : R) (h0 : 0 < a₀)
  (h : 0 ≤ a₀ * a₁) :
  (a₀ :: a₁ :: t).num_sign_changes =
  ((a₀ + a₁) :: t).num_sign_changes :=
begin
  by_cases h1 : a₁ = 0,
  {
    simp [h1],
  },
  {
    have h2 : 0 < a₁,
    {
      have : 0 ≤ a₁,
      { nlinarith,},
      exact (ne.symm h1).lt_of_le this,
    },
    have h' : ¬ a₀ * a₁ < 0,
    { nlinarith,},
    have h'' : 0 < a₀ + a₁,
    { nlinarith,},
    calc
    (a₀ :: a₁ :: t).num_sign_changes =
      (a₁ :: t).num_sign_changes : by {
        simp [h',h1],
      }
    ... = (1 :: t).num_sign_changes  : by {
      rw list.num_sign_changes_eq_sign' h2,
    }
    ... = _ : by {
      rw list.num_sign_changes_eq_sign' h'',
    }
  }
end

lemma aux_1
{t : list R} (a₀ a₁ : R)
  (h : 0 ≤ a₀ * a₁) :
  (a₀ :: a₁ :: t).num_sign_changes =
  ((a₀ + a₁) :: t).num_sign_changes :=
begin
  rcases (@trichotomous _ (<) _ a₀ 0) with h0|h0|h0,
  {
    calc
    (a₀ :: a₁ :: t).num_sign_changes =
    ((a₀ :: a₁ :: t).map has_neg.neg).num_sign_changes :
    by { rw list.num_sign_changes_neg,
    }
    ... = (-a₀ :: -a₁ :: t.map has_neg.neg).num_sign_changes : by {sorry}
    ... = ((-a₀ + -a₁) :: t.map has_neg.neg).num_sign_changes : by {
      apply aux_1'; linarith,
    }
    ... = (((a₀ + a₁) :: t).map has_neg.neg).num_sign_changes : by {
      simp,
      rw show -a₀ + -a₁ = -a₁ + -a₀, by ring,
    }
    ... = _ : by {
      rw ←list.num_sign_changes_neg,
      }
  },
  {
    simp [h0],
  },
  {
    exact aux_1' a₀ a₁ h0 h,
  }
end

@[simp] lemma aux_2
{t : list R} (a₀ a₁: R) [inhabited R] : 
(a₀ :: a₁ :: t).ilast = (a₁ :: t).ilast :=
begin
sorry
end


lemma aux_3'
{t : list R} {a₀ a₁ : R} (h0 : 0 < a₀)
  (h : 0 ≤ a₀ * a₁) :
  (a₀ :: a₁ :: t).integral.num_sign_changes =
  ((a₀ + a₁) :: t).integral.num_sign_changes :=
begin
  by_cases h0 : a₀ = 0,
  {
    simp [h0],
  },
  {
    sorry
  }
end

lemma aux_3
{t : list R} {a₀ a₁ : R}
  (h : 0 ≤ a₀ * a₁) :
  (a₀ :: a₁ :: t).integral.num_sign_changes =
  ((a₀ + a₁) :: t).integral.num_sign_changes :=
begin
  rcases (@trichotomous _ (<) _ a₀ 0) with h0|h0|h0,
  {
    calc
    (a₀ :: a₁ :: t).integral.num_sign_changes
    = ((a₀ :: a₁ :: t).integral.map(has_neg.neg)).num_sign_changes : by {
      rw list.num_sign_changes_neg,
    }
    ... = (-a₀ :: -a₁ :: t.map(has_neg.neg)).integral.num_sign_changes :
    by {
      rw list.integral_neg,
      simp,
    }
    ... = _ : by {
      sorry
    }
  },
  {
    simp [h0],
  },
  {
    apply aux_3' h0 h,
  }
end

lemma key_lemma [inhabited R] (t : list R)
:   ∀ (a₀ a₁ : R),  a₀ + a₁ + t.sum = 0 →  
(a₁ :: t).ilast ≠ 0 →
  ∃ m,  V (a₀ :: a₁ :: t) 
  = V ((a₀ :: a₁ :: t).integral) + 2*m + 1:=
begin
  induction t with t_head t_tail,
  {
    intros a₀ a₁ hsum hlast,
    simp at hsum hlast,
    simp [show a₀ = -a₁, by linarith, hlast],
  },
  {
    set t := t_head :: t_tail with ht,
    intros a₀ a₁ hsum hlast,
    specialize t_ih (a₀ + a₁) t_head,
    have H0 : a₀ + a₁ + t_head + t_tail.sum = 0,
    {
      rw ht at hsum,
      simp at hsum,
      linarith [hsum],
    },
    specialize t_ih H0,
    have H1: (t_head :: t_tail).ilast ≠ 0,
    {
      rw ht at hlast,
      simpa using hlast,
    },
    specialize t_ih H1,
    clear H0 H1,
    obtain ⟨m, hm⟩ := t_ih,
    by_cases h01 : 0 ≤ a₀ * a₁,
    {
      rw show (a₀ :: a₁ :: t).num_sign_changes
      = ((a₀+a₁) :: t).num_sign_changes, by exact aux_1 a₀ a₁ h01,
      use m,
      rw show (a₀ :: a₁ :: t).integral.num_sign_changes
      = ((a₀ + a₁) :: t).integral.num_sign_changes,
      by apply aux_3 h01,
      exact hm,
    },
    {
      replace h01 : a₀ * a₁ < 0, by linarith [h01],
      simp [h01],
      by_cases h0 : 0 < a₀,
      {
        have  h1: a₁ < 0, sorry,
        sorry
      },
      {
        -- replace h0 : a₀ < 0, by linarith [h0],
        sorry -- this is done exactly as the above case, swapping signs. Use wlog tactic?
      }
    }
  }
  
end


/--
The number of sign changes of a  polynomial
-/
def polynomial.num_sign_changes (f : polynomial R) :=
f.nonzero_coeff_list.num_sign_changes


lemma polynomial.num_sign_changes_smul (f : polynomial R) {c : R} (hc : c ≠ 0) :
(c • f).num_sign_changes = f.num_sign_changes :=
begin
  rw [polynomial.num_sign_changes, polynomial.num_sign_changes,
  f.nonzero_coeff_list_smul hc,←list.num_sign_changes_smul _ hc],
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
    rw pow_succ,
    rw [show f * (X * X^i) = (f*X^i) * X, by ring],
    rw [polynomial.support_mul_X, hi, finset.map_map],
    ext r,
    simp only [finset.mem_map, mem_support_iff,
    ne.def, function.embedding.trans_apply, function.embedding.coe_fn_mk,
    nat.add_def, exists_prop],
    simp_rw show ∀ (a : ℕ), (i+a).succ = i.succ + a,
    by {intro a, rw nat.succ_eq_add_one, rw nat.succ_eq_add_one, ring_nf},
  }
end

lemma polynomial.nonzero_coeff_list_mul_X_pow (f : polynomial R) (i : ℕ) :
  (f * X^i).nonzero_coeff_list = f.nonzero_coeff_list :=
begin
  repeat {rw polynomial.nonzero_coeff_list},
  rw polynomial.support_mul_X_pow,
  set addi : ℕ ↪o ℕ := ⟨⟨i.add, λ a b hab, (add_right_inj i).mp hab⟩, λ a b, by simp⟩ with haddi,
  rw (show function.embedding.mk i.add (add_right_injective i)  = addi.to_embedding, by refl),
  rw ←finset.sort_commutes_monotone f.support addi,
  simp only [function.embedding.coe_fn_mk, rel_embedding.coe_fn_mk, list.map_map],
  rw show (f * X^i).coeff ∘ i.add = f.coeff, by {ext,
  simp,
  rw [add_comm , coeff_mul_X_pow],
  },
end

lemma polynomial.nonzero_coeff_list_mul_X (f : polynomial R) :
  (f * X).nonzero_coeff_list = f.nonzero_coeff_list :=
begin
  rw [←pow_one X, polynomial.nonzero_coeff_list_mul_X_pow f 1],
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
  rw ← p.num_sign_changes_smul  hnz,
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

lemma finset.range_succ_succ (i : ℕ) :
finset.range i.succ.succ = insert 0  (insert 1 (finset.filter (λ j, 1 < j) (finset.range i.succ.succ))):=
begin
  ext,
  simp,
  cases a,
  {finish},
  cases a,
  {finish},
  finish,
end

lemma aux_lemma (a : ℕ) (f : ℕ → R): ite (1 < a)  ((ite (0 = a) (1 : R) 0 - ite (1 = a) 1 0) * f a) (0 : R) = 0 :=
begin
  cases a with a a,
  { simp },
  cases a with a a,
  { simp },
  have h0 : ¬ 0 = a.succ.succ,
  { 
    exact ne_zero.ne' (nat.succ a).succ,
  },
  have h1 : ¬ 1 = a.succ.succ,
  { 
    intro hc,
    have hh : 0 = a.succ := nat.succ.inj hc,
    finish,   
  },
  simp [h0, h1],
end

lemma coeff_X_sub_C_mul (i : ℕ):
  p.coeff i = ∑ j in finset.range (i+1), ((C (1 : R) - X) * p).coeff j :=
begin
  induction i with i hi,
    { simp },
  rw finset.range_succ,
  rw finset.sum_insert finset.not_mem_range_self,
  rw ← hi,
  rw coeff_mul,
  rw finset.nat.sum_antidiagonal_eq_sum_range_succ (λ x y, (C (1:R)- X).coeff x * p.coeff y) (i.succ),
  simp,
  rw finset.range_succ_succ,
  rw finset.sum_insert,
  {
    rw finset.sum_insert,
    {
      repeat {simp_rw coeff_one},
      repeat {simp_rw coeff_X},
      simp_rw [finset.sum_filter, aux_lemma],
      simp,
    },
    {
      simp,
    }
  },
  {
    simp,
  }
end

-- Arthan's version
lemma arthan (hp : coeff p 0 ≠ 0) :
 ∃ (m : ℕ), ((X - C 1 : polynomial R) * p).num_sign_changes  =
 p.num_sign_changes + 2*m + 1:=
begin
sorry
end

@[simp]
lemma num_sign_changes_cX {c : R} (hc : 0 < c) : (p.comp (c • X)).num_sign_changes = p.num_sign_changes :=
begin
sorry
end

lemma num_sign_changes_X_sub_C_mul'' {a : R} (ha: 0 < a) (hp : coeff p 0 ≠ 0) :
 ∃ (m : ℕ), ((X - C a : polynomial R) * p).num_sign_changes  = p.num_sign_changes + 2*m + 1:=
begin
have hp' : coeff (p.comp (a•X)) 0 ≠ 0, by sorry,
obtain ⟨m, hm⟩ := arthan hp',
have ha' : a ≠ 0 := ne_of_gt ha,
have ha'' : a⁻¹ ≠ 0 := inv_ne_zero ha',
use m,
-- reduce to Arthan's lemma by using that p(cx) has the same number of sign changes as p(x)
calc
((X - C a) * p).num_sign_changes  = (C a⁻¹ * ((X - C a) * p)).num_sign_changes : by {
  rw show C a⁻¹ * ((X - C a) * p) = C a⁻¹ • ((X - C a) * p), by simp,
  rw ← polynomial.num_sign_changes_smul _ ha'',
  simp,
}
... = (C a⁻¹ * ((C a * X - C a) * p.comp(a•X))).num_sign_changes : by {rw ← num_sign_changes_cX ha, simp}
... = ((C a⁻¹ * (C a * X - C a)) * p.comp(a•X)).num_sign_changes : by {simp}
... = ((X - C 1) * p.comp(a•X)).num_sign_changes : by {
  rw show C a * X - C a = C a * (X - C 1), by ring_nf,
  simp [ha'],
  }
... = (p.comp (a•X)).num_sign_changes + 2 * m + 1 : hm
... = p.num_sign_changes + 2 * m + 1 : by {rw num_sign_changes_cX ha}
end


-- Lemma 2 of Levin
/--
For all α > 0, the polynomial (X-α) * p has at least one more sign change than p
-/
lemma num_sign_changes_X_sub_C_mul' {x : R} (hx : 0 < x) (hp : coeff p 0 ≠ 0) :
  p.num_sign_changes + 1 ≤ ((X - C x : polynomial R) * p).num_sign_changes :=
begin
  obtain ⟨m,hm⟩ := num_sign_changes_X_sub_C_mul'' hx hp,
  rw hm,
  linarith,
end

lemma polynomial.root_iff_divides_X_sub_C {p : polynomial R} (hp : p ≠ 0) (α : R) :
∃ (q : polynomial R), p = (X-C α)^(p.root_multiplicity α) * q ∧ q.eval α ≠ 0 :=
begin
have H1 := @le_root_multiplicity_iff  _ _ _ hp α (p.root_multiplicity α),
simp at H1,
have H2 := @root_multiplicity_le_iff  _ _ _ hp α (p.root_multiplicity α),
simp at H2,
obtain ⟨q, hq⟩ := H1,
use q,
split,
  { exact hq },
intro hc,
replace hc : is_root q α := is_root.def.mpr hc,
obtain ⟨r, hr⟩ := dvd_iff_is_root.mpr hc,
apply H2,
rw hr at hq,
use r,
generalize hj : root_multiplicity α p = j,
rw hj at hq,
rw hq,
ring_exp,
end

lemma polynomial.root_zero_iff_divides_X  {p : polynomial R} (hp : p ≠ 0)  :
∃ q,  p = X^(p.root_multiplicity 0)  * q ∧ (q.coeff 0 ≠ 0) :=
begin
  obtain ⟨q, hq⟩ := polynomial.root_iff_divides_X_sub_C hp 0,
  use q,
  simp at hq,
  have H : q.coeff 0 = q.eval 0,
  { simp only [eval, eval₂_at_zero, ring_hom.id_apply] },
  rw H,
  exact hq,
end

lemma num_sign_changes_X_sub_C_mul (hp : p ≠ 0) {x : R} (hx : 0 < x) :
  p.num_sign_changes + 1 ≤ ((X - C x : polynomial R) * p).num_sign_changes :=
begin
  obtain ⟨q, ⟨h, hnz⟩⟩ := polynomial.root_zero_iff_divides_X hp,
  have h' : (X - C x) * (q * X^(p.root_multiplicity 0)) = ((X - C x) * q) * X^(p.root_multiplicity 0),
  { ring },
  rw [h, mul_comm, polynomial.num_sign_changes_mul_X_pow, h', polynomial.num_sign_changes_mul_X_pow],
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
    have hp' : p / (X - C x) ≠ 0,
    {
      intro hc,
      apply hp,
      rw hc,
      ring,
    },
    rw [← this, positive_roots_mul, card_add],
    {
    calc (X - C x).positive_roots.card + (p / (X - C x)).positive_roots.card = 1 + (p / (X - C x)).positive_roots.card : by simp [positive_roots_X_sub_C_of_zero_lt hx.2]
      ... ≤ 1 + (p / (X - C x)).num_sign_changes : nat.add_le_add_left _ 1
      ... = (p / (X - C x)).num_sign_changes + 1 : add_comm _ _
      ... ≤ ((X - C x) * (p / (X - C x))).num_sign_changes : num_sign_changes_X_sub_C_mul hp' hx.2,
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