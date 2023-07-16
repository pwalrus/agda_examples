module quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; sym ; cong ; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_ ; _≤_)
open import Data.Nat.Properties using (*-comm ; +-comm ; +-identityʳ ; +-assoc ; +-suc ; ≤-refl ; +-monoʳ-≤ ; +-monoˡ-≤)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂ ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂ ; [_,_])
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


data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) → ∃[ x ] B x → C
∃-elim f ⟨ x , y ⟩ = f x y

lem1 : ∀ {A : Set} {B C : A → Set} → (x : A) → B x ⊎ C x → (∃[ x ] B x) ⊎ (∃[ x ] C x)
lem1 x (inj₁ b) =  inj₁ ⟨ x , b ⟩
lem1 x (inj₂ c) = inj₂ ⟨ x , c ⟩

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record {
  to = λ { ⟨ x , y ⟩ → lem1 x y };
  from = λ { (inj₁ ⟨ x , b ⟩) → ⟨ x , (inj₁ b) ⟩ ; (inj₂ ⟨ x , c ⟩) → ⟨ x , (inj₂ c) ⟩ };
  from∘to = λ { ⟨ a , (inj₁ Bx) ⟩ → refl  ; ⟨ a , (inj₂ Cx) ⟩ → refl} ;
  to∘from = λ { (inj₁ ⟨ x , Bx ⟩ ) → refl ; (inj₂ ⟨ x , Cx ⟩) → refl }
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ( Bx , Cx ) ⟩ = ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩

∃-⊎-to : ∀ {B : Tri → Set} → ∃[ x ] B x → B aa ⊎ B bb ⊎ B cc
∃-⊎-to ⟨ aa , Ba ⟩ = inj₁ Ba
∃-⊎-to ⟨ bb , Bb ⟩ = inj₂ (inj₁ Bb)
∃-⊎-to ⟨ cc , Bc ⟩ = inj₂ (inj₂ Bc)

∃-⊎-from : ∀ {B : Tri → Set} → B aa ⊎ B bb ⊎ B cc → ∃[ x ] B x
∃-⊎-from {B} (inj₁ x) = ⟨ aa , x ⟩
∃-⊎-from {B} (inj₂ (inj₁ x)) = ⟨ bb , x ⟩
∃-⊎-from {B} (inj₂ (inj₂ y)) = ⟨ cc , y ⟩

∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ {B} = record {
  to = ∃-⊎-to {B};
  from = ∃-⊎-from {B} ;
  from∘to = λ {⟨ aa , Ba ⟩ → refl ; ⟨ bb , Bb ⟩ → refl ; ⟨ cc , Bc ⟩ → refl } ;
  to∘from = λ { (inj₁ a) → refl ; (inj₂ (inj₁ b)) → refl ; (inj₂ (inj₂ c)) → refl }
  }

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ} → odd n → even (suc n)
data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

el-lem1 : ∀ (m : ℕ) → 2 * m + 1 ≡ m + 1 * suc m
el-lem1 m rewrite  +-comm (m + m) 1 | +-identityʳ m | +-comm (m + m) 1 | +-comm m (suc m)  = refl 

el-lem2 : ∀ (m : ℕ) → 2 * m + 1 ≡ suc (m + m)
el-lem2 m  rewrite +-identityʳ m | +-comm (m + m) 1 | *-comm m 2 = refl

el-lem3 : ∀ (m : ℕ) → 2 * m + 1 ≡ 1 + m * 2
el-lem3 m rewrite *-comm m 2 | +-identityʳ (m + m) | +-identityʳ m | +-comm (m + m) 1 = refl

∃-even2 : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd2  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

∃-even2 ⟨  zero , refl ⟩ =  even-zero
∃-even2 ⟨ suc m , refl ⟩ = even-suc (∃-odd2 ⟨ m , el-lem1 m ⟩)
∃-odd2  ⟨     m , refl ⟩ rewrite el-lem3 m =  odd-suc (∃-even ⟨ m , refl ⟩)

∃-+-≤-to : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-+-≤-to ⟨ zero , xyz ⟩ rewrite xyz = ≤-refl
∃-+-≤-to {y} {z} ⟨ suc x , xyz ⟩ rewrite (sym xyz) = +-monoˡ-≤ y _≤_.z≤n

∃-+-≤-from : ∀ {y z : ℕ} → y ≤ z → ∃[ x ] (x + y ≡ z)
∃-+-≤-from {zero} {z} yz = ⟨ z , +-identityʳ z ⟩
∃-+-≤-from {suc y} {suc z} (_≤_.s≤s yz) with (∃-+-≤-from yz)
... | ⟨ x , xyz ⟩ = ⟨ x , trans (+-suc x y) (cong suc xyz) ⟩


∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set} → ∃[ x ] (¬ B x) → ¬ (∀ x → B x)
∃¬-implies-¬∀ {A} {B} ⟨ x , nBx ⟩ y = nBx (y x)
