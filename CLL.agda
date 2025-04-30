module CLL where

open import Agda.Builtin.Equality
  using (_≡_; refl)

data Nat : Set where
 zero : Nat
 suc : Nat → Nat

data Nat= : Nat → Nat → Set where
  zero= : Nat= zero zero
  suc= : {m n : Nat} → Nat= m n → Nat= (suc m) (suc n)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A


-- example to use to test
example : List Nat
-- [0, 1, 2]
example = cons zero (cons (suc zero) (cons (suc (suc zero)) nil))

-- append to end of list
append : {A : Set} → List A → List A → List A
append nil y = y
append (cons x xs) y = cons x (append xs y)

-- reverse a list
reverse : {A : Set} → List A → List A
reverse nil = nil
reverse (cons x xs) = append (reverse xs) (cons x nil)

-- apply a function to each element of a list
map : {A B : Set} → (A → B) → List A → List B
map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)

-- get the length of a list
length : {A : Set} → List A → Nat
length nil = zero
length (cons _ xs) = suc (length xs)

-- increases the length of a list by one
length-one : {A : Set} → (xs : List A) → (x : A) → Nat= (length (append xs (cons x nil))) (suc (length xs))
length-one nil _ = suc= zero=
length-one (cons _ xs) x = suc= (length-one xs x)


record CList (A : Set) : Set where
  field
    full : List A
    current : List A

-- circular list
clist : {A : Set} → List A → CList A
clist nil = record { full = nil ; current = nil }
clist (cons x xs) = record { full = xs ; current = xs }

-- takes circular list and returns next list
next : {A : Set} → CList A → CList A
next record { full = f ; current = nil } = record { full = f ; current = f }
next record { full = f ; current = cons _ xs } = record { full = f ; current = xs }

-- circlular list to list
clistToList : {A : Set} → CList A → List A
clistToList record { full = full ; current = current } = full


-- create List= using same ideas as Nat=
data List= {A : Set} : List A → List A → Set where
  nil=  : List= nil nil
  cons= : ∀ {x xs y ys} → x ≡ y → List= xs ys → List= (cons x xs) (cons y ys)

-- my attempt at a proof that append is associative
-- append-assoc : {A : Set} → (xs ys zs : List A) → List= (append (append xs ys) zs) (append xs (append ys zs))
-- thought this line would be nil= or refl but that wasnt working
-- append-assoc nil ys zs = {!   !}
-- append-assoc (cons x xs) ys zs = cons= refl (append-assoc xs ys zs)