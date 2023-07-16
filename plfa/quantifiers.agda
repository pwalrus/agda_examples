module quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂ ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import isomorphism using (_≃_; extensionality ; ∀-extensionality)
open import Function using (_∘_)


∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record {
  to = λ x →  proj₁ ∘ x , proj₂ ∘ x  ;
  from = λ x y → (proj₁ x y) , (proj₂ x y) ;
  from∘to = λ x → refl ;
  to∘from = λ y → refl
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ x) = inj₁ ∘ x
⊎∀-implies-∀⊎ (inj₂ y) = inj₂ ∘ y

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× {B} = record {
  to = λ x → (x aa) , ((x bb) , (x cc)) ;
  from = λ x → λ {aa → proj₁ x ; bb → proj₁ (proj₂ x) ; cc → proj₂ (proj₂ x) } ;
  from∘to = λ x → ∀-extensionality (λ { aa → refl ; bb → refl ; cc → refl}) ;
  to∘from = λ y → refl
  }
