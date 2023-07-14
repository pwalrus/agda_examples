module connective where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; assocʳ′ ; assocˡ′ ; swap ; proj₁; proj₂)
open import Data.Sum using (_⊎_ ; [_,_] ; inj₁; inj₂)
open import Function using (_∘_)
open import isomorphism using (_≃_; _≲_; extensionality; _⇔_ ; ≃-trans ; ≃-refl)


module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B  → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record {
  to = λ x → _⇔_.to x , _⇔_.from x;
  from =  λ x → record { to = proj₁ x ; from = proj₂ x };
  from∘to = λ x → refl ;
  to∘from = λ y → refl
  }

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ (tt , x)  → x }
    ; from    = λ{ x → tt , x }
    ; from∘to = λ{ (tt , x) → refl }
    ; to∘from = λ{ x → refl }
    }

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

⊎-comm : ∀ {A B : Set} → A ⊎ B → B ⊎ A
⊎-comm A⊎B = case-⊎ inj₂ inj₁ A⊎B

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc (inj₁ (inj₁ x)) = inj₁ x
⊎-assoc (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
⊎-assoc (inj₂ y) = inj₂ (inj₂ y)

data ⊥ : Set where
  -- no clauses!

⊥-elim : ∀ {A : Set}  → ⊥ → A
⊥-elim = λ () 

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A → A
⊥-identityˡ {A} p = case-⊎ (⊥-elim {A}) (λ x → x) p

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ → A
⊥-identityʳ {A} p = case-⊎ (λ z → z) (⊥-elim {A})  p

→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M


×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ( inj₁ x , z ) → (inj₁ ( x , z ))
                 ; ( inj₂ y , z ) → (inj₂ ( y , z ))
                 }
    ; from    = λ{ (inj₁ ( x , z )) → ( inj₁ x , z )
                 ; (inj₂ ( y , z )) → ( inj₂ y , z )
                 }
    ; from∘to = λ{ ( inj₁ x , z ) → refl
                 ; ( inj₂ y , z ) → refl
                 }
    ; to∘from = λ{ (inj₁ ( x , z )) → refl
                 ; (inj₂ ( y , z )) → refl
                 }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ( x , y )) → ( inj₁ x , inj₁ y )
                 ; (inj₂ z)         → ( inj₂ z , inj₂ z )
                 }
    ; from    = λ{ ( inj₁ x , inj₁ y ) → (inj₁ ( x , y ))
                 ; ( inj₁ x , inj₂ z ) → (inj₂ z)
                 ; ( inj₂ z , _      ) → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ( x , y )) → refl
                 ; (inj₂ z)         → refl
                 }
    }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× (inj₁ x , snd) = inj₁ x
⊎-weak-× (inj₂ y , snd) = inj₂ (y , snd)

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ (fst , snd)) = inj₁ fst , inj₁ snd
⊎×-implies-×⊎ (inj₂ (fst , snd)) = inj₂ fst , inj₂ snd
