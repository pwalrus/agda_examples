module decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; cong)
open Eq.≡-Reasoning
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool using (Bool ; true ; false ; T ; _∨_ ; _∧_ ; not)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import relations using (_<_; z<s; s<s)
open import isomorphism using (_⇔_)


T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt   =  refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s {m} {n} p (s<s p1) = p p1

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no (λ ())
zero <? suc n = yes z<s
suc m <? zero = no (λ ())
suc m <? suc n with (m <? n)
... | yes x = yes (s<s x)
... | no x = no (¬s<s x)

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no (λ ())
suc m ≡ℕ? zero = no (λ ())
suc m ≡ℕ? suc n with (m ≡ℕ? n)
... | yes x = yes (cong suc x)
... |  no x = no (x ∘ suc-inj)

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ( x , y )
no ¬x ×-dec _     = no λ{ ( x , y ) → ¬x x }
_     ×-dec no ¬y = no λ{ ( x , y ) → ¬y y }

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes x) (yes y) = refl
∧-× (yes x) (no ¬y) = refl
∧-× (no ¬x) _ = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes x) y = refl
∨-⊎ (no ¬x) (yes y) = refl
∨-⊎ (no ¬x) (no ¬y) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes x) = refl
not-¬ (no ¬x) = refl


_iff_ : Bool → Bool → Bool
false iff false = true
false iff true = false
true iff false = false
true iff true = true

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
_⇔-dec_ (yes x) (yes y) = yes (record { to = λ _ → y ; from = λ _ → x })
_⇔-dec_ (no ¬x) (no ¬y) = yes (record { to = λ a → ⊥-elim (¬x a) ; from = λ b → ⊥-elim (¬y b) })
_⇔-dec_ (yes x) (no ¬y) = no (λ x₁ → ¬y (_⇔_.to x₁ x))
_⇔-dec_ (no ¬x) (yes y) = no (λ x → ¬x (_⇔_.from x y))

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes x) (yes y) = refl
iff-⇔ (yes x) (no ¬y) = refl
iff-⇔ (no ¬x) (yes y) = refl
iff-⇔ (no ¬x) (no ¬y) = refl

True : ∀ {Q : Set} → Dec Q → Set
True Q = T ⌊ Q ⌋

False : ∀ {Q : Set} → Dec Q → Set
False Q  = T ⌊ ¬? Q ⌋

_ : True (1 <? 2)
_ = tt

_ : False (2 <? 1)
_ = tt

toWitnessFalse : ∀ {A : Set} {D : Dec (¬ A) } → T ⌊ D ⌋ → ¬ A
toWitnessFalse {A} {yes ¬x} tt = ¬x
toWitnessFalse {A} {no x} ()

fromWitnessFalse : ∀ {A : Set} {D : Dec (¬ A) } → ¬ A → T ⌊ D ⌋
fromWitnessFalse {A} {yes x} _  =  tt
fromWitnessFalse {A} {no ¬x} x  =  ¬x x
