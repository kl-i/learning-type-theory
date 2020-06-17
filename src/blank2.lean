#check list
-- list : Type u_1 → Type u_1
#check @list.rec

namespace hidden

inductive list : Type → Type 
| nil : Π A : Type, list A
| append : Π A : Type, Π a : A, Π l : list A, list A

/-
universe level of type_of(arg #1) of 'hidden.list.nil' is 
too big for the corresponding inductive datatype
-/

end hidden

universe u

inductive mylist (α : Sort u) : Sort u 
| nil : mylist
| append : Π a : α, Π l : mylist, mylist

#check @mylist
#check @mylist.rec -- Not large eliminating

inductive mylist2 (α : Type u) : Type u 
| nil : mylist2
| append : Π a : α, Π l : mylist2, mylist2

#check @mylist2
#check @mylist2.rec -- Large eliminating, since Type u = Sort (u + 1), 1 ≤ u + 1

#check list false

def len (α : Type u) : mylist2 α → ℕ := 
let C : Π l : mylist2 α, Type := λ l : mylist2 α, ℕ in 
@mylist2.rec α C 0 (λ a : α, λ l : mylist2 α, λ v : C l, v + 1)

#reduce len _ (@mylist2.append _ _ (@mylist2.nil _))

#check @eq.subst
#check @congr_arg
#print eq
#check @eq.rec
#check @eq.drec

inductive myeq (α : Sort u) : α → α → Sort 0
| refl : Π a : α, myeq a a

theorem imp_of_eq : Π P : Sort 0, Π Q : Sort 0, myeq (Sort 0) P Q → P → Q := 
@myeq.drec (Sort 0) (λ P Q : Sort 0, λ h : myeq (Sort 0) P Q, P → Q) 
(λ P : Sort 0, λ h : P, h)

#check @myeq.drec -- this is the recursor in Mario's paper
#check @myeq.rec -- this is the one in Lean. Seems stronger. 

inductive myle : ℕ → ℕ → Prop 
| min : Π a b : ℕ, a = 0 → myle a b
| diag : Π a b : ℕ, myle a b → myle (a + 1) (b + 1)
#reduce myle 0 1
#reduce myle 1 0
#check @myle.drec

#check @nat.rec
def myle2 : ℕ → ℕ → Prop := 
@nat.rec (λ a : ℕ, Π b : ℕ, Prop) 
(λ n : ℕ, true)
(λ k : ℕ, λ v, @nat.rec (λ b : ℕ, Prop) (false) (λ l : ℕ, λ w, v l))

#reduce myle2 0 1
#reduce myle2 1 0

#print eq.subst
theorem not_myle_one_zero : myle 1 0 → false := 
λ h : myle 1 0, @myle.drec (λ a b : ℕ, λ hab, myle2 a b) 
(λ a b : ℕ, λ ha : a = 0, 
  -- eq.subst ha.symm trivial -- doesn't work for some reason
  by {apply eq.subst ha.symm, exact trivial}
) 
(λ a b : ℕ, λ hab : myle a b, λ v, v)
1 0 h 

#print nat.lt
#print nat.less_than_or_equal
#reduce nat.less_than_or_equal 0 1
#check @has_le.le
#reduce @has_le.le ℕ _


#check @nat.less_than_or_equal.drec
theorem nat_eq_or_succ_le_of : Π a b : ℕ, a ≤ b → a = b ∨ nat.succ a ≤ b := 
λ a : ℕ, 
@nat.less_than_or_equal.drec a (λ b : ℕ, λ a_le_b, a = b ∨ nat.succ a ≤ b) 
(or.inl (eq.refl a))
(λ b : ℕ, λ a_le_b, λ a_eq_b_or_suc_a_le_b, 
  or.inr $ or.elim a_eq_b_or_suc_a_le_b 
  (λ a_eq_b, a_eq_b ▸ nat.less_than_or_equal.refl) 
  (λ suc_a_le_b, nat.less_than_or_equal.step suc_a_le_b)
)

theorem nat_le_of_succ_le : Π {a b : ℕ}, nat.succ a ≤ b → a ≤ b := 
λ a : ℕ, @nat.less_than_or_equal.drec (nat.succ a) (λ b : ℕ, λ a_le_b, a ≤ b)
(nat.less_than_or_equal.step nat.less_than_or_equal.refl)
(λ b : ℕ, λ suc_a_le_b, λ a_le_b, nat.less_than_or_equal.step a_le_b)

theorem nat_le_trans : Π {a b c : ℕ}, a ≤ b → b ≤ c → a ≤ c := 
λ a b c : ℕ, λ a_le_b, λ b_le_c, 
@nat.less_than_or_equal.drec a (λ b : ℕ, λ a_le_b, Π c : ℕ, b ≤ c → a ≤ c)
(λ c : ℕ, λ a_le_c, a_le_c) 
(λ b : ℕ, λ a_le_b, λ forall_c_b_le_c_imp_a_le_c, 
  λ c : ℕ, λ suc_b_le_c, 
  forall_c_b_le_c_imp_a_le_c _ (nat.le_of_succ_le suc_b_le_c)
) b a_le_b c b_le_c

def nat_le_prop : ℕ → ℕ → Prop := 
@nat.rec (λ a : ℕ, Π b : ℕ, Prop) 
(λ n : ℕ, true)
(λ k : ℕ, λ v, @nat.rec (λ b : ℕ, Prop) (false) (λ l : ℕ, λ w, k ≤ l))

#reduce nat_le_prop 2 3

def nat_le_no_confusion_prop : Π a : ℕ, Π b : ℕ, a ≤ b → nat_le_prop a b := 
@nat.rec (λ a : ℕ, Π b : ℕ, a ≤ b → nat_le_prop a b)
(λ b : ℕ, λ zero_le_b, trivial)
(λ n : ℕ, λ ih, 
  @nat.less_than_or_equal.drec (nat.succ n) 
  (λ b : ℕ, λ a_le_b, nat_le_prop (nat.succ n) b)
  (nat.less_than_or_equal.refl)
  (λ b : ℕ, λ suc_n_le_b, λ succ_n_le_b, nat_le_of_succ_le suc_n_le_b)
)

theorem nat_le_of_succ_le_succ : Π {a b : ℕ}, nat.succ a ≤ nat.succ b → a ≤ b :=
λ a : ℕ, λ b : ℕ, nat_le_no_confusion_prop (nat.succ a) (nat.succ b)

def nat_le_val : ℕ → ℕ → Prop := 
@nat.rec (λ a : ℕ, Π b : ℕ, Prop) 
(λ n : ℕ, true)
(λ k : ℕ, λ v, @nat.rec (λ b : ℕ, Prop) (false) (λ l : ℕ, λ w, v l))

def nat_le_no_confusion : Π a : ℕ, Π b : ℕ, a ≤ b → nat_le_val a b := 
@nat.rec (λ a : ℕ, Π b : ℕ, a ≤ b → nat_le_val a b) 
(λ b : ℕ, λ zero_le_b, trivial)
(λ n : ℕ, λ ih, 
  @nat.less_than_or_equal.drec (nat.succ n) 
  (λ b : ℕ, λ suc_n_le_b, nat_le_val (nat.succ n) b)
  (ih n nat.less_than_or_equal.refl)
  (λ b : ℕ, λ suc_n_le_b, λ v : nat_le_val (nat.succ n) b, 
  ih b $ nat_le_of_succ_le suc_n_le_b)
)

theorem not_succ_le_self : Π a : ℕ, nat.succ a ≤ a → false := 
@nat.rec (λ a : ℕ, nat.succ a ≤ a → false)
(nat_le_no_confusion 1 0)
(λ n : ℕ, λ ih, λ suc_suc_n_le_suc_n, ih 
  (nat_le_of_succ_le_succ suc_suc_n_le_suc_n)
)

#check @nat.less_than_or_equal.drec
theorem nat_le_antisymm : Π a : ℕ, Π b : ℕ, a ≤ b → b ≤ a → a = b := 
λ a : ℕ,@nat.less_than_or_equal.drec a (λ b : ℕ, λ hab : a ≤ b, b ≤ a → a = b)
(λ ha : a ≤ a, eq.refl _) 
(λ b : ℕ, λ a_le_b, λ b_le_a_imp_a_eq_b, λ suc_b_le_a, 
  false.elim $ not_succ_le_self b (nat.le_trans suc_b_le_a a_le_b)
)

def nat_eq : Π a : ℕ, Π b : ℕ, Prop := 
@nat.rec (λ a : ℕ, Π b : ℕ, Prop) -- inductive define on first component
(-- Case of a = 0, 
  @nat.rec (λ b : ℕ, Prop) -- induct on b
  true -- 0 = 0
  (λ n : ℕ, λ v, -- Suppose we know whether 0 = n or not. 
    false -- 0 ≠ n + 1 anyway. 
  ) 
)
(-- Case of a = n + 1, 
  λ n : ℕ, λ v, -- Suppose we know the {m : ℕ | nat_eq n m}
  -- we need to define {m : ℕ | nat_eq (n + 1) m}
  @nat.rec (λ b : ℕ, Prop) -- inductively define it. 
  false -- n + 1 ≠ 0
  (λ m : ℕ, λ w, -- Suppose we know whether n + 1 = m or not. 
    v m -- define n + 1 = m + 1 as same value as n = m
  )
)

def nat_no_confusion : Π a : ℕ, Π b : ℕ, a = b → nat_eq a b := 
@nat.rec (λ a : ℕ, Π b : ℕ, a = b → nat_eq a b) -- induct on a
(λ b : ℕ, λ zero_eq_b, zero_eq_b ▸ trivial) -- a = 0 
(λ n : ℕ, λ ih, λ b : ℕ, λ succ_n_eq_b, succ_n_eq_b ▸ ih n (eq.refl n))--a=n+1

example : 0 ≠ 1 := nat_no_confusion 0 1 -- why does this work... 

theorem nat_not_succ_le_zero : Π a : ℕ, nat.succ a ≠ 0 :=
@nat.rec (λ a : ℕ, nat.succ a ≠ 0)
(nat_no_confusion 1 0)
(λ n : ℕ, λ succ_n_ne_zero, nat_no_confusion (nat.succ (nat.succ n)) 0)