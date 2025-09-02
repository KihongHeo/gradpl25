import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NthRewrite

inductive ListOfNats : Type where
  | Nil : ListOfNats
  | Cons : Nat → ListOfNats → ListOfNats

def nl1 := ListOfNats.Cons 1 (ListOfNats.Cons 2 ListOfNats.Nil)

inductive ListOfStrings : Type where
  | Nil : ListOfStrings
  | Cons : String → ListOfStrings → ListOfStrings

def sl1 := ListOfStrings.Cons "a" (ListOfStrings.Cons "2" ListOfStrings.Nil)

inductive MyList (A: Type) : Type where
  | Nil : MyList A
  | Cons : A → MyList A → MyList A

def sl2 := MyList.Cons "a" (MyList.Cons "2" MyList.Nil)
#check sl2

inductive Vec (A: Type) : Nat → Type where
  | Nil : Vec A 0
  | Cons : {n: Nat} → A -> Vec A n → Vec A (n + 1)

def v1 := Vec.Cons 1 (Vec.Cons 2 Vec.Nil)
#check v1

def head {A: Type} {n: Nat} : Vec A (n + 1) → A
  | Vec.Cons x _ => x

def tail {A: Type} {n: Nat} : Vec A (n + 1) → Vec A n
  | Vec.Cons _ xs => xs

def append {A: Type} : {n m: Nat} → Vec A n → Vec A m → Vec A (n + m)
  | 0, m, Vec.Nil, ys => by simp [Nat.zero_add]; exact ys
  | n + 1, m, Vec.Cons x xs, ys => by simp [Nat.add_assoc]; nth_rewrite 2 [Nat.add_comm]; exact Vec.Cons x (append xs ys)

#check append (Vec.Cons 1 (Vec.Cons 2 Vec.Nil)) (Vec.Cons 3 Vec.Nil)

def filterLen {A: Type} {n : Nat} : (A → Bool) → Vec A n → Nat
  | _, Vec.Nil => 0
  | f, Vec.Cons x xs =>
    if f x then filterLen f xs + 1 else filterLen f xs

def filter {A: Type} {n : Nat} : (f : A → Bool) → (l : Vec A n) → Vec A (filterLen f l)
  | _, Vec.Nil => Vec.Nil
  | p, Vec.Cons x xs => by
    /- if p x then Vec.Cons x (filter p xs) else filter p xs -/
    by_cases h : p x
    . simp [filterLen, h]; exact Vec.Cons x (filter p xs)
    . simp [filterLen, h]; exact filter p xs

def nary : Type → Nat → Type
  | A, 0 => A
  | A, n + 1 => A → nary A n

#check nary Nat 3

def apply {A: Type} {n: Nat} : nary A n → Vec A n → A
  | x, Vec.Nil => x
  | f, Vec.Cons x xs => apply (f x) xs

def three_add : nary Nat 3 := fun x y z => x + y + z

def x := apply three_add (Vec.Cons 1 (Vec.Cons 2 (Vec.Cons 3 Vec.Nil)))
#eval x

/- type error -/
-- def filterAll {A: Type} {n : Nat} : Vec A n → Vec A 0 := filter (fun _ => false)

inductive equiv {A: Type} : A → A → Type where
  | refl (x: A) : equiv x x

def lemma1 {A: Type} {n : Nat}: (l : Vec A n) → equiv (filterLen (fun _ => false) l) 0
  | Vec.Nil => equiv.refl 0
  | Vec.Cons _ xs => lemma1 xs

def lemma2 {A: Type} {n : Nat}: (l : Vec A n) → equiv (1+1) 2
  | Vec.Nil => equiv.refl 2
  | Vec.Cons _ xs => lemma2 xs

#check equiv.refl 0

def subst {A: Type} {x y: A} {P: A → Type} : equiv x y → P x → P y
  | equiv.refl _, px => px

#check subst

def filterAll {A: Type} {n : Nat} (l : Vec A n) : Vec A 0 :=
  subst (lemma1 l) (filter (fun _ => false) l)
