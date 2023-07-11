
module equality where


data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_


sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import relations using (_≤_ ; z≤n ; s≤s ; ≤-trans)
import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat.Properties using (+-comm; +-identityʳ ; +-suc)

infix  1 ≤-begin_
infixr 2 _≤⟨⟩_ _≤⟨_⟩_
infix  3 _≤-∎


≤-begin_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
≤-begin_ x≤y = x≤y

_≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
_≤⟨⟩_  x x≤y = x≤y

_≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
_≤⟨_⟩_  x x≤y y≤z = ≤-trans x≤y y≤z 

_≤-∎ : ∀ (x : ℕ) → x ≤ x
zero ≤-∎ = z≤n
suc x ≤-∎ = s≤s (x ≤-∎)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q =
  ≤-begin
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤-∎

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n zero m≤n rewrite +-identityʳ m | +-identityʳ n = m≤n
+-monoˡ-≤ m n (suc p) m≤n rewrite +-suc n p | +-suc m p = sp
  where
    sp : suc(m + p) ≤ suc(n + p)
    sp =
      ≤-begin
        suc(m + p)
      ≤⟨ s≤s (+-monoˡ-≤ m n p m≤n ) ⟩
        suc(n + p)
      ≤-∎

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  ≤-begin
    m + p
  ≤⟨ +-monoʳ-≤ m p q p≤q ⟩
    m + q
  ≤⟨ +-monoˡ-≤ m n q m≤n ⟩
    n + q
  ≤-∎

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px  = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P  = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P  =  subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

