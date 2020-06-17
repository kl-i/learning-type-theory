import data.rat

universe u

#check Prop
#check Type

constants T U : Type 1

#check λ x : T, λ x : T, x
#check λ x : T, λ t : T, x
#check λ t : T, λ x : T, t

def test : T → T → T := 
λ x : T, λ x : T, x

constants t₁ t₂ : T

#reduce test t₁ t₂

constant t : T

-- #reduce (λ x : T, (λ y : x, U)) for some reason doesn't work

-- def tee : T := t what does this have to do with computability

variable x : T
#check x = x

#check ℕ 
#check ℤ 
#check ℚ 

variables (i : ℕ) (j : ℤ) (k : ℚ)

#check j + i
#check k + i
#check k + (j + i)

universes u v
constants (A : Type u) (B : Type v)

#check A → B
#check B → A

constant P : Prop
#check P → A
#check A → P

mutual inductive TREE, FOREST
with TREE : Type
| node : FOREST → TREE
with FOREST : Type
| emptyf : FOREST
| makef : TREE → FOREST → FOREST

#check TREE

inductive days : Type
| saturday : days
| sunday : days

#check @days.rec

def days_number : days → ℕ :=
@days.rec (λ d : days, ℕ) 0 1

inductive LIST : Type → Type 
| emptylist : Π A : Type, LIST A 
| append : Π A : Type, LIST A → A → LIST A

#check @LIST.rec
def length_of : Π A : Type, LIST A → ℕ := 
@LIST.rec (λ X : Type, λ x : LIST X, ℕ) 
(λ X : Type, 0)
(λ B : Type, λ L : LIST B, λ b : B, λ n : ℕ, n + 1)

#reduce length_of ℕ (LIST.append ℕ (LIST.emptylist ℕ) 2)

#check LIST

constant c : Type

mutual inductive list1, list2 (A : Type) (B : Type)
with list1 : Type → Type
| nil : list1 A
| cons : A → list1 A → list1 A
with list2 : Type → Type
| nil : list2 B
| cons : B → list2 B → list2 B

#check λ x : T, λ x : U, x
#check λ y : T, λ x : U, y

#check ℕ 

#print list

-- inductive LISTu : Sort u → Sort u
-- | emptylist : Π A : Sort u, LISTu A 
-- | append : Π A : Sort u, Π a : A, Π l : LISTu A, LISTu A

#check false.rec
#check @true.rec
#check @nat.rec
#check @list.rec

inductive NAT : Sort 0
| zero : NAT 
| succ : Π n : NAT, NAT

#check @NAT.rec

inductive myeq (α : Sort u) : Π a : α, Π b : α, Sort 0
| refl : Π a : α, myeq a a

#check @myeq.rec