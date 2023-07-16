module lists where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong ; cong-app)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+ ; *-distribˡ-+ ; *-comm ; +-comm ; +-∸-assoc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List ; _∷_ ; [] ; _++_ ; length ; map ; foldr)
open import Data.List.Properties using (++-assoc ; ++-identityˡ ; ++-identityʳ )
open import Function using (_∘_)
open import Level using (Level)
open import isomorphism using (_≃_; _⇔_ ; extensionality)


pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

reverse-++-distrib : ∀ { A : Set } (xs ys : List A) →  reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) =  refl
reverse-++-distrib (x ∷ xs) ys =  
  begin
    reverse (x ∷ xs ++ ys)
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-distrib (reverse xs) [ x ] | reverse-involutive xs = refl

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

map-compose-x : ∀ {A B C : Set} {f : A → B} {g : B → C} (x : List A) → map (g ∘ f) x ≡ (map g ∘ map f) x
map-compose-x [] = refl
map-compose-x  {A} {B} {C} {f} {g} (x ∷ xs) =
  begin
    g (f x) ∷ map (g ∘ f) xs
  ≡⟨ cong (_∷_ (g (f x))) (map-compose-x xs)  ⟩
    g (f x) ∷ (map g ∘ map f) xs
  ∎

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C} → map (g ∘ f) ≡ map g ∘ map f
map-compose = extensionality map-compose-x

map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A) →  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys rewrite (cong (_∷_ (f x)) (map-++-distribute f xs ys)) = refl

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node tree x tree₁) = node (map-Tree f g tree) (g x) (map-Tree f g tree₁)

product : ∀ (xs : List ℕ) → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

foldr-++ : ∀ {A : Set} {e : A} {_⊗_ : A → A → A} (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ [] ys = refl
foldr-++ {A} {e} {_⊗_} (x ∷ xs) ys rewrite (cong (_⊗_  x) (foldr-++ {A} {e} {_⊗_} xs ys)) = refl

foldr-∷ : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-∷ [] ys = refl
foldr-∷ {A} (x ∷ xs) ys rewrite (cong (_∷_  x) (foldr-∷ {A} xs ys)) = refl

map-is-foldr-x : ∀ {A B : Set} (f : A → B) (x : List A) → map f x ≡ foldr (λ x xs → f x ∷ xs) [] x
map-is-foldr-x f [] = refl
map-is-foldr-x f (x ∷ xs) rewrite (cong (_∷_  (f x)) (map-is-foldr-x f xs)) = refl

map-is-foldr : ∀ {A B : Set} (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (map-is-foldr-x f)

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

sum : List ℕ → ℕ
sum = foldr _+_ 0

brutal-assoc1 : ∀ (n : ℕ) → (n * 2) + n * (n ∸ 1) ≡ (suc n * n)
brutal-assoc1 zero = refl
brutal-assoc1 (suc n)
  rewrite +-comm n (suc (n + n * suc n))
  | *-comm n (suc n)
  | *-comm n 2
  | +-identityʳ n =
  begin
    suc (suc (n + n + (n + n * n)))
  ≡⟨ cong (suc ∘ suc) (+-assoc n n (n + n * n)) ⟩
    suc (suc (n + (n + (n + n * n))))
  ≡⟨ cong (suc ∘ suc ∘ _+_ n) (+-comm n (n + n * n)) ⟩
    suc (suc (n + ((n + n * n) + n)))
  ≡⟨ cong (suc ∘ suc) (sym (+-assoc n (n + n * n) n)) ⟩
    suc (suc (n + (n + n * n) + n))
  ∎

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) =
  begin
    sum (downFrom (suc n)) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩
    (n * 2) + (sum (downFrom n) * 2)
  ≡⟨ cong (_+_ (n * 2)) (sum-downFrom n) ⟩
    (n * 2) + n * (n ∸ 1)
  ≡⟨ brutal-assoc1 n ⟩
    (suc n * n)
  ∎
