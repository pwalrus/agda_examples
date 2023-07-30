module lambdaprop where


open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import isomorphism using (_≃_)
open import lambda 


V¬—→ : ∀ {M N} → Value M → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N} → M —→ N → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N

infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where
  C-ƛ : ∀ {x A N B} → ∅ , x ⦂ A ⊢ N ⦂ B → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)
  C-zero : Canonical `zero ⦂ `ℕ
  C-suc : ∀ {V} → Canonical V ⦂ `ℕ → Canonical `suc V ⦂ `ℕ


Canonical-≃ : ∀ (V : Term) (A : Type) → Canonical V ⦂ A ≃ (∅ ⊢ V ⦂ A) × (Value V)
Canonical-≃ V A = record {
  to = to V A ;
  from = from V A ;
  from∘to = from∘to V A ;
  to∘from = to∘from V A
  }
  where
    to : ∀ (V : Term) (A : Type) → Canonical V ⦂ A → (∅ ⊢ V ⦂ A) × (Value V)
    to .(ƛ _ ⇒ _) .(_ ⇒ _) (C-ƛ x) = ⊢ƛ x , V-ƛ
    to .`zero .`ℕ C-zero = ⊢zero , V-zero
    to (`suc V) .`ℕ (C-suc x) = (⊢suc (proj₁ (to V `ℕ x))) , V-suc (proj₂ (to V `ℕ x))
    from : ∀ (V : Term) (A : Type) → (∅ ⊢ V ⦂ A) × (Value V) → Canonical V ⦂ A
    from .(ƛ _ ⇒ _) .(_ ⇒ _) (⊢ƛ j , v) = C-ƛ j
    from .`zero .`ℕ (⊢zero , v) = C-zero
    from .(`suc _) .`ℕ (⊢suc j , V-suc v) = C-suc (from _ _ (j , v))
    from∘to : ∀ (V : Term) (A : Type) (x : Canonical V ⦂ A) → from V A (to V A x) ≡ x
    from∘to .(ƛ _ ⇒ _) .(_ ⇒ _) (C-ƛ x) = refl
    from∘to .`zero .`ℕ C-zero = refl
    from∘to .(`suc _) .`ℕ (C-suc x) rewrite from∘to _ _ x = refl
    to∘from : ∀ (V : Term) (A : Type) (x : (∅ ⊢ V ⦂ A) × (Value V)) → to V A (from V A x) ≡ x
    to∘from .(ƛ _ ⇒ _) .(_ ⇒ _) (⊢ƛ j , V-ƛ) = refl
    to∘from .`zero .`ℕ (⊢zero , V-zero) = refl
    to∘from .(`suc _) .`ℕ (⊢suc j , V-suc v) rewrite to∘from _ _ (j , v) = refl

data Progress (M : Term) : Set where

  step : ∀ {N} → M —→ N → Progress M
  done : Value M → Progress M

progress : ∀ {M A} → ∅ ⊢ M ⦂ A → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                             =  step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done (V-zero)                         =  step β-zero
... | done (V-suc VL)                       =  step (β-suc VL)
progress (⊢μ ⊢M)                            =  step β-μ


Progress-≃ : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
Progress-≃ {M} = record {
  to = to;
  from = from;
  from∘to = λ {(step x) → refl ; (done x) → refl} ;
  to∘from = λ {(inj₁ y) → refl ; (inj₂ (_ , _)) → refl}
  }
  where
    to : ∀ {M} → Progress M → Value M ⊎ ∃[ N ](M —→ N)
    to (step x) = inj₂ (_ , x)
    to (done x) = inj₁ x
    from : ∀ {M} → Value M ⊎ ∃[ N ](M —→ N) → Progress M
    from (inj₁ x) = done x
    from (inj₂ (_ , red)) = step red


progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ (` x) (⊢` ())
progress′ (ƛ x ⇒ M) (⊢ƛ J) = inj₁ V-ƛ
progress′ (M · M₁) (J · J₁) with progress′ M J | progress′ M₁ J₁
progress′ ((ƛ x₁ ⇒ M) · M₁) (J · J₁) | inj₁ x | inj₁ y = inj₂ (M [ x₁ := M₁ ] , β-ƛ y)
progress′ (M · M₁) (J · J₁) | inj₁ x | inj₂ (t , red) = inj₂ (M · t , ξ-·₂ x red)
progress′ (M · M₁) (J · J₁) | inj₂ (t , red) | _ = inj₂ (t · M₁ , ξ-·₁ red)
progress′ `zero J = inj₁ V-zero
progress′ (`suc M) (⊢suc J) with progress′ M J
progress′ (`suc M) (⊢suc J) | inj₁ x = inj₁ (V-suc x)
progress′ (`suc M) (⊢suc J) | inj₂ (j , red) = inj₂ (`suc j , ξ-suc red)
progress′ case L [zero⇒ M |suc x ⇒ N ] (⊢case J J₁ J₂) with progress′ L J
progress′ case .`zero [zero⇒ M |suc x ⇒ N ] (⊢case J J₁ J₂) | inj₁ V-zero = inj₂ (M , β-zero)
progress′ case .(`suc _) [zero⇒ M |suc x ⇒ N ] (⊢case J J₁ J₂) | inj₁ (V-suc z) = inj₂ (N [ x := _ ] , β-suc z)
progress′ case L [zero⇒ M |suc x ⇒ N ] (⊢case J J₁ J₂) | inj₂ (fst , snd) = inj₂ (case fst [zero⇒ M |suc x ⇒ N ] , ξ-case snd)
progress′ (μ x ⇒ M) (⊢μ J) = inj₂ (M [ x := μ x ⇒ M ] ,  β-μ )

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? (⊢ƛ t) = yes V-ƛ
value? (t · t₁) = no (λ ())
value? ⊢zero = yes V-zero
value? (⊢suc t) with (value? t)
value? (⊢suc t) | yes q = yes (V-suc q)
value? (⊢suc t) |  no q = no λ {(V-suc r) → q r}
value? (⊢case t t₁ t₂) = no (λ ())
value? (⊢μ t) = no (λ ())

