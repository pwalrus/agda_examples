
module relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong ; sym)
open import induct using (Bin ; ⟨⟩ ; _I ; _O ; inc-bin ; to-bin ; from-bin)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)
open import Data.Nat using (ℕ; pred; zero; suc; _+_ ; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ ; *-comm)
open import Function using (_∘_)


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n  → n ≤ p → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n  rewrite *-comm m p | *-comm n p  = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ {m n p : ℕ} → m < n  → n < p → m < p
<-trans z<s (s<s y) = z<s
<-trans (s<s x) (s<s y) = s<s (<-trans x y)

_>_ : ℕ → ℕ → Set
x > y = y < x

>-suc : ∀ {m n : ℕ} → m > n → suc m > suc n
>-suc {m} {n} m>n = s<s m>n

≡-suc : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
≡-suc {m} {n} m≡n = cong suc m≡n

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

tri-suc : ∀ {m n : ℕ} → m < n ⊎ m ≡ n ⊎ m > n → suc m < suc n ⊎ suc m ≡ suc n ⊎ suc m > suc n
tri-suc (inj₁ x) = inj₁ (s<s x)
tri-suc (inj₂ (inj₁ x)) = inj₂ (inj₁ (≡-suc x))
tri-suc (inj₂ (inj₂ y)) = inj₂ (inj₂ (>-suc y))

trichotomy : ∀ {m n : ℕ} → m < n ⊎ m ≡ n ⊎ m > n
trichotomy {zero} {zero} = inj₂ (inj₁ refl)
trichotomy {zero} {suc n} = inj₁ (z<s)
trichotomy {suc m} {zero} = inj₂ (inj₂ z<s)
trichotomy {suc m} {suc n} =  tri-suc (trichotomy {m} {n})

+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n zero m<n rewrite +-comm m zero | +-comm n zero = m<n
+-monoˡ-< m n (suc p) m<n rewrite +-comm m (suc p) | +-comm n (suc p) = +-monoʳ-< (suc p) m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans {m + p} {n + p} {n + q} (+-monoˡ-< m n p m<n)(+-monoʳ-< n p q p<q)

ord-thm1 : ∀ {m n : ℕ} → suc m ≤ n → m < n
ord-thm1 {zero} {suc n} sm≤n = z<s
ord-thm1 {suc m} {suc n} (s≤s sm≤n) = s<s (ord-thm1 sm≤n)

ord-thm2 : ∀ {m n : ℕ} → m < n → suc m ≤ n
ord-thm2 {zero} {suc n} m<n = s≤s z≤n
ord-thm2 {suc m} {suc n} (s<s m<n) = s≤s (ord-thm2 m<n)

≤-low-suc : ∀ {m n : ℕ} → suc m ≤ n → m ≤ n
≤-low-suc {zero} {n} sm≤n = z≤n
≤-low-suc {suc m} {suc n} (s≤s sm≤n) = s≤s (≤-low-suc sm≤n)

<-trans-revisited : ∀ {m n p : ℕ} → m < n  → n < p →  m < p
<-trans-revisited {m} {n} {p} m<n n<p = ord-thm1 (≤-low-suc (≤-trans (ord-thm2 (s<s m<n)) (ord-thm2 n<p)))

suc-injective : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-injective refl = refl

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc  : ∀ {n : ℕ}  → odd n → even (suc n)

data odd where
  suc  : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)
o+e≡o (suc em) en  =  suc (e+e≡e em en)

even-sub : ∀ {m n : ℕ} → m ≡ n → even (m) → even (n)
odd-sub : ∀ {m n : ℕ} → m ≡ n → odd (m) → odd (n)

even-sub {.zero} {zero} eq zero = zero
even-sub {.(suc _)} {suc n} eq (suc x) = suc(odd-sub (suc-injective eq) x)
odd-sub {.(suc _)} {suc n} eq (suc x) = suc(even-sub (suc-injective eq) x)


+-id : ∀ (n : ℕ) → n + zero ≡ n
+-id zero = refl
+-id (suc n) = cong suc (+-id n)


even-id : ∀ {n : ℕ} → even (n + zero) → even n
even-id {n} ev = even-sub (+-id n) ev

odd-id : ∀ {n : ℕ} → odd (n + zero) → odd n
odd-id {n} od = odd-sub (+-id n) od

even-id-rev : ∀ {n : ℕ} → even n → even (n + zero)
even-id-rev {n} ev = even-sub (sym (+-id n)) ev

odd-id-rev : ∀ {n : ℕ} →  odd n → odd (n + zero)
odd-id-rev {n} od = odd-sub (sym (+-id n)) od

even-comm : ∀ {m n : ℕ} → even (m + n) → even (n + m)
even-comm {m} {n} ev = even-sub (+-comm m n) ev

odd-comm : ∀ {m n : ℕ} → odd (m + n) → odd (n + m)
odd-comm {m} {n} od = odd-sub (+-comm m n) od

+-suc′ : ∀ {m n : ℕ} → m + suc n ≡ suc (m + n)
+-suc′ {zero} {n} = refl
+-suc′ {suc m} {n} rewrite +-suc′ {m} {n} = refl

odd-rev-suc : ∀ {m n : ℕ} → odd (suc(m + n)) → odd (m + suc n)
odd-rev-suc {m} {n} od = odd-sub (sym +-suc′) od

e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)
e+o≡o em (suc en) = odd-rev-suc(suc (e+e≡e em en))

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc em) on = suc(e+o≡o em on)


data One : Bin → Set where
  So : One (⟨⟩ I)
  Io : ∀ (x : Bin) → One x → One (x I)
  Oo : ∀ (x : Bin) → One x → One (x O)

data Can : Bin → Set where
  ⟨⟩c : Can ⟨⟩
  Oc : ∀ (x : Bin) → One x → Can (x)

inc-one : ∀ {q : Bin} → One q → One (inc-bin q)
inc-one {b O} (Oo .b p) = Io b p
inc-one {.⟨⟩ I} So = Oo (⟨⟩ I) So
inc-one {b I} (Io .b p) = Oo (inc-bin b) (inc-one p)

inc-can : ∀ {b : Bin} → Can b → Can (inc-bin b)
inc-can {⟨⟩} p = Oc (⟨⟩ I) So
inc-can {b O} (Oc .(b O) (Oo .b x)) = Oc (b I) (Io b x)
inc-can {.⟨⟩ I} (Oc .(⟨⟩ I) So) = Oc ((⟨⟩ I) O) (Oo (⟨⟩ I) So)
inc-can {b I} (Oc .(b I) (Io .b x)) = Oc (inc-bin b O) (inc-one (Io b x))

to-can : ∀ (n : ℕ) → Can (to-bin n)
to-can zero = ⟨⟩c
to-can (suc m) = inc-can (to-can m)

--to-from-can : ∀ (b : Bin) → Can b → to-bin (from-bin b) ≡ b
--to-from-can ⟨⟩ p = refl
--to-from-can (b O) p = {!!}
--to-from-can (b I) p = {!!}
