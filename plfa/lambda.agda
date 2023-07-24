module lambda where


open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_ ; _,_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import isomorphism using (_≃_; _⇔_ ; extensionality)


Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_


data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]


sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ `zero
           |suc "m" ⇒ (plus · ` "n" · (` "*" · ` "m" · ` "n")) ]

var? : (t : Term) → Bool
var? (` _)  =  true
var? _      =  false

ƛ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
ƛ′_⇒_ (` x) N = ƛ x ⇒ N

case′_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (var? t)} → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]

μ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N


data Value : Term → Set where
  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)
  V-zero : Value `zero
  V-suc : ∀ {V} → Value V → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _         = V
... | no  _         = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ N
... | no  _         = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]  = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = μ x ⇒ N
... | no  _         = μ x ⇒ N [ y := V ]


infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·₁ : ∀ {L L′ M} → L —→ L′ → L · M —→ L′ · M
  ξ-·₂ : ∀ {V M M′} → Value V → M —→ M′ → V · M —→ V · M′
  β-ƛ : ∀ {x N V} → Value V → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′} → M —→ M′ → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′ → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N} → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M} → μ x ⇒ M —→ M [ x := μ x ⇒ M ]


_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]
      ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M → M —↠ M
  _—→⟨_⟩_ : ∀ L {M N} → L —→ M → M —↠ N → L —↠ N

begin_ : ∀ {M N} → M —↠ N → M —↠ N
begin M—↠N = M—↠N


postulate
  confluence : ∀ {L M N} → ((L —↠ M) × (L —↠ N)) → ∃[ P ] ((M —↠ P) × (N —↠ P))
  diamond :    ∀ {L M N} → ((L —→ M) × (L —→ N)) → ∃[ P ] ((M —↠ P) × (N —↠ P))
  deterministic : ∀ {L M N} → L —→ M → L —→ N → M ≡ N

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context


Context-≃ : Context ≃ List (Id × Type)
Context-≃ = record {
  to = to ;
  from = from ;
  from∘to = from∘to;
  to∘from = to∘from
  }
  where
    to : Context → List (Id × Type)
    to ∅ = []
    to (c , i ⦂ t) = (i , t) ∷ (to c)
    from : List (Id × Type) → Context
    from [] = ∅
    from ((i , t) ∷ xs) = (from xs) , i ⦂ t
    from∘to : ∀ (c : Context) → from ( to c) ≡ c
    from∘to ∅ = refl
    from∘to (c , i ⦂ t) rewrite from∘to c = refl
    to∘from : ∀ (xs : List (Id × Type)) → to (from xs) ≡ xs
    to∘from [] = refl
    to∘from (x ∷ xs) rewrite to∘from xs = refl


infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A} → Γ , x ⦂ A ∋ x ⦂ A
  S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ⦂ A → Γ , y ⦂ B ∋ x ⦂ A

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A} → Γ ∋ x ⦂ A  → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}  → Γ , x ⦂ A ⊢ N ⦂ B → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B} → Γ ⊢ L ⦂ A ⇒ B → Γ ⊢ M ⦂ A  → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ} → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M} → Γ ⊢ M ⦂ `ℕ → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A} → Γ ⊢ L ⦂ `ℕ → Γ ⊢ M ⦂ A → Γ , x ⦂ `ℕ ⊢ N ⦂ A
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A} → Γ , x ⦂ A ⊢ M ⦂ A → Γ ⊢ μ x ⇒ M ⦂ A

S′ : ∀ {Γ x y A B} → {x≢y : False (x ≟ y)} → Γ ∋ x ⦂ A → Γ , y ⦂ B ∋ x ⦂ A
S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x


⊢two : ∀ {Γ} → (Γ ⊢ two ⦂ `ℕ)
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
         (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
  where
  ∋+  = S′ (S′ (S′ Z))
  ∋m  = S′ Z
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = S′ Z

∋-functional : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-functional Z        Z          =  refl
∋-functional Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-functional (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-functional (S _ ∋x) (S _ ∋x′)  =  ∋-functional ∋x ∋x′

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′))  =  contradiction (∋-functional ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) ⊢zero rec-case)))
  where
  ∋m = (S′ Z)
  ∋* = (S′ (S′ (S′ Z)))
  ∋m′ = Z
  ∋n = S′ Z
  rec-case = (⊢plus · (⊢` ∋n)) · ((⊢` ∋* · ⊢` ∋m′) · (⊢` ∋n))
