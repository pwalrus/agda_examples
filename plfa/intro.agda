import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Nat using (mod-helper)

open import Data.Nat using (ℕ; zero; suc; pred;_+_; _*_; _∸_;_^_ ; ⌊_/2⌋)
open import Data.Bool using (Bool ; true ; false)
open import Data.Product using (_×_ ; _,_)
open import Function using (_∘_)

+-id' : ∀ (n : ℕ) → n + 0 ≡ n
+-id' 0 =
  begin
    0 + 0
  ≡⟨⟩
    0
  ∎
+-id' (suc m) =
  begin
    (suc m) + 0
  ≡⟨⟩
    suc (m + 0)
  ≡⟨ cong suc (+-id' m) ⟩
    suc (m)
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ 0 n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

+-swap : ∀ (n m p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero m p rewrite +-identity′ m = refl
+-swap (suc n) m p =
  begin
    m + ((suc n) + p)
  ≡⟨⟩
    m + suc (n + p)
  ≡⟨ +-suc′ m (n + p) ⟩
    suc (m + (n + p))
  ≡⟨ cong suc (+-swap n m p) ⟩
    suc (n + (m + p))
  ≡⟨⟩
    suc n + (m + p)
  ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    p + (m + n) * p
  ≡⟨ cong (_+_ p) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc′ p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc 0 n p = refl
*-assoc (suc m) n p = 
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong (_+_ (n * p)) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ≡⟨⟩
    (suc m) * (n * p)
  ∎

*-zero : ∀ (n : ℕ) → n * 0 ≡ 0
*-zero 0 = refl
*-zero (suc n) rewrite *-zero n = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zero n = refl
*-comm (suc m) zero rewrite *-zero m = refl
*-comm (suc m) (suc n) =
  begin
    suc (n + m * suc n)
  ≡⟨ cong suc (cong (_+_ n) (*-comm m (suc n))) ⟩
    suc (n + suc n * m)
  ≡⟨⟩
    suc (n + (m + n * m))
  ≡⟨ cong suc (sym (+-assoc′ n m (n * m))) ⟩
    suc ((n + m) + n * m)
  ≡⟨ cong suc (cong (_+_ (n + m)) (*-comm n m)) ⟩
    suc ((n + m) + m * n)
  ≡⟨ cong suc (cong (_+ (m * n)) (+-comm′ n m))⟩
    suc ((m + n) + m * n)
  ≡⟨ cong suc (+-assoc′ m n (m * n)) ⟩
    suc (m + (n + m * n))
  ≡⟨⟩
    suc (m + (suc m) * n)
  ≡⟨ cong suc (cong (_+_ m) (*-comm (suc m) n)) ⟩
    suc (m + n * suc m)
  ∎

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite 0∸n≡0 (n + p) rewrite 0∸n≡0 n rewrite 0∸n≡0 p = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) →  m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identity′ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p =
  begin
    m * (m ^ (n + p))
    ≡⟨ cong (_*_ m) (^-distribˡ-+-* m n p) ⟩
    m * ((m ^ n) * (m ^ p))
    ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * (m ^ n) * (m ^ p)
  ∎

bad-assoc1 : ∀ (a b ap bp : ℕ) → (a * b) * (ap * bp) ≡ (a * ap) * (b * bp)
bad-assoc1 a b ap bp = 
  begin
    (a * b) * (ap * bp)
  ≡⟨ *-assoc a b (ap * bp) ⟩
    a * (b * (ap * bp))
  ≡⟨ cong (_*_ a) (sym (*-assoc b ap bp)) ⟩
    a * (b * ap * bp)
  ≡⟨ cong (_*_ a) (cong (_* bp) ( (*-comm b ap))) ⟩
    a * (ap * b * bp)
  ≡⟨ cong (_*_ a) (*-assoc ap b  bp) ⟩
    a * (ap * (b * bp))
  ≡⟨ sym (*-assoc a ap (b * bp)) ⟩
    a * ap * (b * bp)
  ∎

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p) 
^-distribʳ-* zero n zero = refl
^-distribʳ-* zero n (suc p) = refl
^-distribʳ-* (suc m) n zero = refl
^-distribʳ-* (suc m) n (suc p) =
  begin
    (suc m * n) * ((suc m * n) ^ p)
  ≡⟨ cong (_*_ (suc m * n)) (^-distribʳ-* (suc m) n p) ⟩
    (suc m * n) * (suc m ^ p * (n ^ p))
  ≡⟨ bad-assoc1 (suc m) n (suc m ^ p) (n ^ p) ⟩
    (suc m) * (suc m ^ p) * (n * (n ^ p))
  ∎

exp-one : ∀ (p : ℕ) → 1 ^ p ≡ 1
exp-one zero = refl
exp-one (suc p) rewrite exp-one p = refl

siml-mult-comm : ∀ (n m : ℕ) →  n * suc m ≡ n + n * m 
siml-mult-comm n m =
  begin
    n * suc m
  ≡⟨ *-comm n  (suc m) ⟩
    n + m * n
  ≡⟨ cong (_+_ n) (*-comm m n) ⟩
    n + n * m
  ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc zero n zero rewrite *-comm n zero = refl
^-*-assoc zero zero (suc p) rewrite exp-one p = refl
^-*-assoc zero (suc n) (suc p) = refl
^-*-assoc (suc m) zero p rewrite exp-one p = refl
^-*-assoc (suc m) (suc n) zero rewrite *-comm n zero = refl
^-*-assoc m n (suc p) =
  begin
    (m ^ n) * (m ^ n) ^ p
  ≡⟨ cong (_*_ (m ^ n)) (^-*-assoc m n (p)) ⟩
    (m ^ n) * (m ^ (n * p))
  ≡⟨ sym (^-distribˡ-+-* (m) (n) (n * p)) ⟩
    m ^ (n + n * p)
  ≡⟨ cong (_^_ m) (sym (siml-mult-comm n p)) ⟩
    m ^ (n * suc p)
  ∎

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc-bin : Bin → Bin
inc-bin ⟨⟩ = ⟨⟩ I
inc-bin (x O) = x I
inc-bin (x I) = (inc-bin x) O

mod-nat : ℕ → ℕ → ℕ
mod-nat x y = mod-helper 0 (pred y) x (pred y)

to-bin : ℕ → Bin
to-bin zero = ⟨⟩
to-bin (suc x) = inc-bin (to-bin x)

from-bin : Bin → ℕ
from-bin ⟨⟩ = 0
from-bin (x O) = 2 * from-bin x
from-bin (x I) = 2 * from-bin x + 1

_ : from-bin (⟨⟩) ≡ 0
_ = refl

_ : from-bin (inc-bin ⟨⟩) ≡ 1
_ = refl

_ : from-bin ((inc-bin ∘ inc-bin) ⟨⟩) ≡ 2
_ = refl

_ : from-bin ((inc-bin ∘ inc-bin ∘ inc-bin) ⟨⟩) ≡ 3
_ = refl

_ : from-bin (to-bin 0) ≡ 0
_ = refl

_ : from-bin (to-bin 1) ≡ 1
_ = refl

_ : from-bin (to-bin 2) ≡ 2
_ = refl

_ : from-bin (to-bin 3) ≡ 3
_ = refl

bin-thm1 : ∀ (b : Bin) → from-bin (inc-bin b) ≡ suc (from-bin b)
bin-thm1 ⟨⟩ = refl
bin-thm1 (b O) rewrite +-identity′ (from-bin b) rewrite +-comm′ (from-bin b + from-bin b) 1 = refl
bin-thm1 (b I) rewrite +-identity′ (from-bin b)
  rewrite bin-thm1 b
  rewrite +-comm′ (from-bin b + from-bin b) 1
  rewrite +-identity′ (from-bin b)
  rewrite +-suc′ (from-bin b) (from-bin b) = refl

--bin-thm2 : ∀ (b : Bin) → to-bin (from-bin b) ≡ b
--bin-thm2 b = {!!}
--not true, expressions with leading zeros break uniqueness, ex: ⟨⟩ O O

bin-thm3 : ∀ (n : ℕ) → from-bin (to-bin n) ≡ n
bin-thm3 zero = refl
bin-thm3 (suc n) rewrite bin-thm1 (to-bin n) rewrite (bin-thm3 n) = refl
