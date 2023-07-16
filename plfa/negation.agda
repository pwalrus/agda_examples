module negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc ; _<_ ; z≤n ; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂ ; [_,_] ; swap)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Function using (_∘_ ; id ; const)
open import isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive {zero} = λ ()
<-irreflexive {suc n} (s≤s p) = (<-irreflexive {n}) p

id-cases : ∀ {A B : Set} (q : ¬(A ⊎ B)) → [ q ∘ inj₁ , q ∘ inj₂ ] ≡ q
id-cases x = extensionality (λ {(inj₁ l) → refl ; (inj₂ r) → refl })

lambda-circ : ∀ {A B C : Set} {q : B → C} {f : A → B} → (λ x → q (f x)) ≡ q ∘ f
lambda-circ {q} {f} = extensionality (λ x → refl)

id-sides : ∀ {A B : Set} (q : ¬ A × ¬ B) → ( proj₁ q , proj₂ q )  ≡ q
id-sides x = refl


⊎-dual-× : ∀ {A B : Set} →  ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = record {
  to = λ x → x ∘ inj₁ , x ∘ inj₂;
  from = λ x → [ proj₁ x  ,  proj₂ x ];
  from∘to = λ q → id-cases q ;
  to∘from = λ q → id-sides q
  }

⊎-dual-×-weak : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
⊎-dual-×-weak (inj₁ x) = λ z → x (proj₁ z)
⊎-dual-×-weak (inj₂ y) = λ z → y (proj₂ z)

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))


ax1-excluded-middle : (A : Set) → Set
ax1-excluded-middle A = A ⊎ ¬ A

ax2-double-neg : (A : Set) → Set
ax2-double-neg A = ¬ ¬ A → A

ax3-pierce :  (A B : Set) → Set
ax3-pierce A B = ((A → B) → A) → A


ax4-imp-as-disj : (A B : Set) → Set
ax4-imp-as-disj A B = (A → B) → ¬ A ⊎ B


ax5-demorgan : (A B : Set) → Set
ax5-demorgan A B = ¬ ( ¬ A × ¬ B) → A ⊎ B


classic0 : ∀ {A : Set} → ax1-excluded-middle A → ax2-double-neg A
classic0 {A} em = λ x → ([ id , (λ x₁ → (⊥-elim (x x₁))) ] em)

classic1 : ∀ {A : Set} → ax2-double-neg (A ⊎ ¬ A) → ax1-excluded-middle A
classic1 {A} dn = dn em-irrefutable

classic2 : ∀ {A : Set} → ax4-imp-as-disj A A → ax1-excluded-middle A
classic2 {A} iad = swap (iad id)

classic3 : ∀ {A : Set} → ax1-excluded-middle A → ax4-imp-as-disj A A
classic3 {A} (inj₁ x) = λ x₁ → inj₂ (x₁ x)
classic3 {A} (inj₂ y) = const (inj₁ y)

classic4 : ∀ {A B : Set} → ax1-excluded-middle A → ax1-excluded-middle B → ax5-demorgan A B
classic4 {A} (inj₁ x) emb nab = inj₁ x
classic4 {A} (inj₂ y) (inj₁ x) nab = inj₂ x
classic4 {A} (inj₂ y) (inj₂ y₁) nab = ⊥-elim (nab (y , y₁))

classic5 : ∀ {A : Set} → ax5-demorgan A (¬ A) → ax1-excluded-middle A
classic5 {A} dem = dem (λ z → proj₂ z (proj₁ z))

classic6 : ∀ {A B : Set} →  ax1-excluded-middle A → ax1-excluded-middle B → ax3-pierce A B
classic6 {A} (inj₁ x) emb = const x
classic6 {A} (inj₂ y) (inj₁ x) = λ z → z (const x)
classic6 {A} (inj₂ y) (inj₂ y₁) = λ x → x (λ x₁ → ⊥-elim (y x₁))

pierce-lemma : ∀ (P : Set) → (P ⊎ ¬ P → ⊥) → ¬ P
pierce-lemma P x y = x (inj₁ y)

classic7 : ∀ {A : Set} → ax3-pierce (A ⊎ ¬ A) ⊥ → ax1-excluded-middle A
classic7 {A} pier = pier (inj₂ ∘ pierce-lemma A)

Stable : Set → Set
Stable A = ¬ ¬ A → A

stb-thm1 : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
stb-thm1 {A} {B} sta stb AB = sta (λ z → z (sta (λ z₁ → AB (λ z₂ → z₁ (proj₁ z₂))))) , stb λ z → z (stb (λ z₁ → AB (λ z₂ → z₁ (proj₂ z₂))))

stb-thm2 : ∀ {A : Set} → Stable (¬ A)
stb-thm2 {A} = λ x x₁ → x (λ z → z x₁)

