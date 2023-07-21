module lists where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong ; cong-app ; subst)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+ ; *-distribˡ-+ ; *-comm ; +-comm ; +-∸-assoc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Data.List using (List ; _∷_ ; [] ; _++_ ; length ; map ; foldr)
open import Data.List.Properties using (++-assoc ; ++-identityˡ ; ++-identityʳ )
open import Function using (_∘_)
open import Level using (Level)
open import isomorphism using (_≃_; _⇔_ ; extensionality)


pattern [_] z = z ∷ []

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

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎


foldl : ∀ {A : Set} → (A → A → A) → A → List A → A
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

foldl-outside : {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → (x : A) → (xs : List A) → foldl _⊗_ x xs ≡ x ⊗ (foldl _⊗_ e xs)
foldl-outside _⊗_ e monoid x [] =  sym (IsMonoid.identityʳ monoid x)
foldl-outside _⊗_ e monoid x (y ∷ xs)
  rewrite IsMonoid.identityˡ monoid y
  | foldl-outside _⊗_ e monoid (x ⊗ y) xs
  | foldl-outside _⊗_ e monoid y xs
  | IsMonoid.assoc monoid x y (foldl _⊗_ e xs)
  = refl

foldr-monoid-foldl-x : {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → (x : List A) → foldr _⊗_ e x ≡ foldl _⊗_ e x
foldr-monoid-foldl-x _⊗_ e monoid [] = refl
foldr-monoid-foldl-x _⊗_ e monoid (x ∷ xs)
  rewrite IsMonoid.identityˡ monoid x
  | foldr-monoid-foldl-x _⊗_ e monoid xs
  | foldl-outside _⊗_ e monoid x xs
  = refl

foldr-monoid-foldl : {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e monoid = extensionality (foldr-monoid-foldl-x _⊗_ e monoid)

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys = record {
  to = to xs ys ;
  from = from xs ys
  }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] yx ap = inj₂ ap
    to (x ∷ xs) _ (here x₁) = inj₁ (here x₁)
    to (x ∷ xs) ys (there ap) = [ inj₁ ∘ there , inj₂ ] (to xs ys ap)
    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
    from [] ys (inj₂ y) = y
    from (x ∷ xs) ys (inj₁ (here y)) = here y
    from (x ∷ xs) ys (inj₁ (there y)) = there (from xs ys (inj₁ y))
    from (x ∷ xs) ys (inj₂ y) = there (from xs ys (inj₂ y))

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)


--Any-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P (xs ++ ys) ≃ (Any P xs ⊎ Any P ys)
--Any-++-≃ {A} {P} xs ys = ?

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ {A} {P} xs = record {
  to = to xs ;
  from = from xs
  }
  where
    to :  (xs : List A) → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
    to [] p = []
    to (x ∷ xs) p = (p ∘ here) ∷ to xs (p ∘ there)
    from :  (xs : List A) → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
    from [] p = λ ()
    from (x ∷ xs) (¬x ∷ allNP) = λ {(here p) → ¬x p ; (there p) → (from xs allNP) p }

All-∀ : ∀ {A : Set} {P : A → Set} (x : A) (xs : List A) → (All P xs) ⇔ (∀ x → x ∈ xs → P x)
All-∀ {A} {P} x xs = record {
  to = to x xs;
  from = from x xs
  }
  where
   to : ∀ {A : Set} {P : A → Set} (x : A) (xs : List A) → (All P xs) → (∀ x → x ∈ xs → P x)
   to {A} {P} x .(_ ∷ _) (xin ∷ allPxs) y (here xeqy) = subst P (sym xeqy) xin
   to {A} {P} x .(_ ∷ _) (x₁ ∷ allPxs) y (there xeqy) = to x _ allPxs y xeqy
   from : ∀ {A : Set} {P : A → Set} (x : A) (xs : List A) → (∀ x → x ∈ xs → P x) → (All P xs)
   from {A} {P} x [] allin = []
   from {A} {P} x (y ∷ xs) allin = allin y (here refl) ∷ from y xs (λ x z → allin x (there z))

exists-add : ∀ {A : Set} {P : A → Set} (x y : A) (xs : List A) → (∃[ x ] (x ∈ xs × P x) → (∃[ x ] (x ∈ (y ∷ xs) × P x)))
exists-add x y xs ⟨ x₁ , ⟨ xInxs , Px ⟩ ⟩ = ⟨ x₁ , ⟨ (there xInxs) , Px ⟩ ⟩


All-∃ : ∀ {A : Set} {P : A → Set} (x : A) (xs : List A) → (Any P xs) ⇔ (∃[ x ] (x ∈ xs × P x))
All-∃ {A} {P} x xs = record {
  to = to x xs;
  from = from x xs
  }
  where
    to : ∀ {A : Set} {P : A → Set} (x : A) (xs : List A) → (Any P xs) → (∃[ x ] (x ∈ xs × P x))
    to {A} {P} x .(_ ∷ _) (here p) = ⟨ _ , ⟨ here refl , p ⟩ ⟩
    to {A} {P} x .(_ ∷ _) (there anyPxs) = exists-add x _ _ (to x _ anyPxs)
    from : ∀ {A : Set} {P : A → Set} (x : A) (xs : List A) → (∃[ x ] (x ∈ xs × P x)) → (Any P xs)
    from {A} {P} x [ h ] ⟨ x₁ , ⟨ here heq , Px ⟩ ⟩ = here (subst P heq Px)
    from {A} {P} x (h ∷ h₂ ∷ xs) ⟨ x₁ , ⟨ here heq , Px ⟩ ⟩ = here (subst P heq Px)
    from {A} {P} x (h ∷ h₂ ∷ xs) ⟨ x₁ , ⟨ there xInxs , Px ⟩ ⟩
      = there (from x (h₂ ∷ xs) ⟨ x₁ , ⟨ xInxs , Px ⟩ ⟩)

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p  =  foldr _∨_ false ∘ map p


Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no (λ ())
Any? P? (x ∷ xs) with P? x   | Any? P? xs
Any? P? (x ∷ xs) | yes q | r = yes (here q)
Any? P? (x ∷ xs) | no ¬q | yes r = yes (there r)
Any? P? (x ∷ xs) | no ¬q | no ¬r = no (λ {(here x) → ¬q x ; (there xs) → ¬r xs})


data merge {A : Set} : (xs ys zs : List A) → Set where

  []-m : merge [] [] []
  left-∷ : ∀ {x xs ys zs} → merge xs ys zs → merge (x ∷ xs) ys (x ∷ zs)
  right-∷ : ∀ {y xs ys zs} → merge xs ys zs → merge xs (y ∷ ys) (y ∷ zs)

_ : merge (1 ∷ 4 ∷ []) (2 ∷ 3 ∷ []) [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ []-m)))

split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A) → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )
split P? [] = ⟨ [] , ⟨ [] , ⟨ []-m , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩
split P? (x ∷ zs) with P? x | split P? zs
split P? (x ∷ zs) | yes q | ⟨ xs₁ , ⟨ ys₁ , ⟨ m₁ , ⟨ p₁ , p₂ ⟩ ⟩ ⟩ ⟩ = ⟨ (x ∷ xs₁) , ⟨ ys₁ , ⟨ left-∷ m₁ , ⟨ q ∷ p₁ , p₂ ⟩ ⟩ ⟩ ⟩
split P? (x ∷ zs) | no r | ⟨ xs₁ , ⟨ ys₁ , ⟨ m₁ , ⟨ p₁ , p₂ ⟩ ⟩ ⟩ ⟩ = ⟨ xs₁ , ⟨ (x ∷ ys₁) , ⟨ right-∷ m₁ , ⟨ p₁ , r ∷ p₂ ⟩ ⟩ ⟩ ⟩
