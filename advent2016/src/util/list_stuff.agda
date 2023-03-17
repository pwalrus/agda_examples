
module util.list_stuff where

open import Agda.Builtin.String using (String)
open import Data.String.Base using (fromList ; toList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using () renaming (_==_ to _==s_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Char.Base as Char using (Char)
open import Data.Char.Properties using (_==_)
open import Data.List.Base as List using (List; [_]; _∷_; [] ; reverse ; map ; concat ; foldr ; length ; zip ; head ; tail ; applyUpTo)
open import Data.List.NonEmpty.Base as NE using (List⁺)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Agda.Builtin.Nat using (_<_)
open import Data.Nat.Base using (ℕ; _∸_; ⌊_/2⌋; ⌈_/2⌉ ; suc)
open import Data.Nat.Show using (readMaybe ; show)
open import Function.Base using (_on_; _∘′_; _∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

add-front-list : {A : Set} → List (List A) → A → List (List A)
add-front-list [] ch = (ch ∷ []) ∷ []
add-front-list (x ∷ xs) ch with x
add-front-list (x ∷ xs) ch    | [] = (ch ∷ []) ∷ xs
add-front-list (x ∷ xs) ch    | (y ∷ ys) = (ch ∷ y ∷ ys) ∷ xs

find-parts : Char → List Char → List (List Char)
find-parts delim [] = []
find-parts delim (x ∷ xs) = if x == delim then [] ∷ (find-parts delim xs) else add-front-list (find-parts delim xs) x

split : Char → String → List String
split delim  = (map fromList) ∘ (find-parts delim) ∘ toList

unique-insert-str : List String → String → List String
unique-insert-str [] l = l ∷ []
unique-insert-str (x ∷ xs) l = if (x ==s l)
   then x ∷ xs
   else x ∷ (unique-insert-str xs l)

nat-range : ℕ → List ℕ
nat-range 0 = []
nat-range (suc x) = concat ((nat-range x) ∷ (x ∷ []) ∷ [])

enumerate : {A : Set} → List A → List (ℕ × A)
enumerate x = zip (nat-range (length x)) x

min-by-f : {A : Set} → (A → ℕ) → List A → Maybe A
min-by-f _ [] = nothing
min-by-f _ (x ∷ []) = just x
min-by-f f (x ∷ xs) with (min-by-f f xs)
min-by-f f (x ∷ xs) | nothing = nothing
min-by-f f (x ∷ xs) | (just b) = if (f x < f b) then (just x) else (just b)

min-by-fm : {A : Set} → ℕ → List A → (A → Maybe ℕ) → Maybe A
min-by-fm 0 _ _ = nothing
min-by-fm (suc l) [] f = nothing
min-by-fm (suc l) (x ∷ []) f = just x
min-by-fm (suc l) (x ∷ y ∷ xs) f with (f x)
min-by-fm (suc l) (x ∷ y ∷ xs) f | (just xr) with (f y)
min-by-fm (suc l) (x ∷ y ∷ xs) f | (just xr) | (just yr) = if (xr < yr) then (min-by-fm l (x ∷ xs) f) else (min-by-fm l (y ∷ xs) f)
min-by-fm (suc l) (x ∷ y ∷ xs) f | (just xr) | nothing = nothing
min-by-fm (suc l) (x ∷ y ∷ xs) f | nothing = nothing

starts-with-ch : List Char → List Char → Bool
starts-with-ch [] _ = true
starts-with-ch _ [] = false
starts-with-ch (x ∷ xs) (y ∷ ys) with (x == y)
starts-with-ch (x ∷ xs) (y ∷ ys) | true = starts-with-ch xs ys
starts-with-ch (x ∷ xs) (y ∷ ys) | false = false

starts-with : String → String → Bool
starts-with x y = starts-with-ch (toList x) (toList y)

two-parts-h : ℕ → (List Char × List Char) → (List Char × List Char)
two-parts-h 0 (lhs , rhs) = lhs , rhs
two-parts-h _ (lhs , []) = lhs , []
two-parts-h (suc l) (xs , (y ∷ ys)) = two-parts-h l ((y ∷ xs) , ys)

two-parts : ℕ → String → (String × String)
two-parts d x with (two-parts-h d ([] , toList x))
two-parts d x | (lhs , rhs) = fromList (reverse lhs) , fromList rhs

append-front-all : {A : Set} → A → List (List A) → List (List A)
append-front-all x inp = map (λ {q → x ∷ q}) inp

all-replacements-ch : (List Char × List Char) → List Char → List (List Char)
all-replacements-ch _ [] = []
all-replacements-ch (f , t) (x ∷ xs) with (starts-with-ch f (x ∷ xs))
all-replacements-ch (f , t) (x ∷ xs) | false with (all-replacements-ch (f , t) xs)
all-replacements-ch (f , t) (x ∷ xs) | false | tail = append-front-all x tail
all-replacements-ch (f , t) (x ∷ xs) | true with (two-parts-h (length f) ([] , (x ∷ xs)))
all-replacements-ch (f , t) (x ∷ xs) | true | (_ , rest) with (all-replacements-ch (f , t) xs)
all-replacements-ch (f , t) (x ∷ xs) | true | (_ , rest) | tail = (concat (t ∷ rest ∷ [])) ∷ (append-front-all x tail)


all-replacements : (String × String) → String → List String
all-replacements (f , t) x with (all-replacements-ch (toList f , toList t) (toList x))
all-replacements (f , t) x | output = map fromList output

trim-leading : List Char → List Char
trim-leading [] = []
trim-leading (' ' ∷ xs) = trim-leading xs
trim-leading ('\t' ∷ xs) = trim-leading xs
trim-leading ('\n' ∷ xs) = trim-leading xs
trim-leading ('\r' ∷ xs) = trim-leading xs
trim-leading (x ∷ xs) = x ∷ xs

trim-trailing : List Char → List Char
trim-trailing [] = []
trim-trailing (x ∷ xs) with (trim-trailing xs)
trim-trailing (x ∷ xs) | [] = x ∷ []
trim-trailing (x ∷ xs) | (' ' ∷ []) = x ∷ []
trim-trailing (x ∷ xs) | ('\t' ∷ []) = x ∷ []
trim-trailing (x ∷ xs) | ('\n' ∷ []) = x ∷ []
trim-trailing (x ∷ xs) | ('\r' ∷ []) = x ∷ []
trim-trailing (x ∷ xs) | (y ∷ ys) = x ∷ y ∷ ys

rem-dot : Char → List Char → List Char
rem-dot ch [] = []
rem-dot ch (x ∷ xs) with (rem-dot ch xs)
rem-dot ch (x ∷ xs) | [] = x ∷ []
rem-dot ch (x ∷ xs) | (q ∷ []) with (q == ch)
rem-dot ch (x ∷ xs) | (q ∷ []) | false = x ∷ q ∷ []
rem-dot ch (x ∷ xs) | (q ∷ []) | true = x ∷ []
rem-dot ch (x ∷ xs) | (y ∷ ys) = x ∷ y ∷ ys

rem-dot-s : String → String
rem-dot-s = fromList ∘ (rem-dot '.') ∘ toList

trim : List Char → List Char
trim = trim-trailing ∘ trim-leading

add-one-inner : {A : Set} → A → (A × List A) → (A × List A)
add-one-inner x (y , xs) = (y , x ∷ xs)

each-one : {A : Set} →  List A → List (A × List A)
each-one [] = []
each-one (x ∷ []) = (x , []) ∷ []
each-one (x ∷ xs) with (each-one xs)
each-one (x ∷ xs) | (y , inner) ∷ outer = (x , y ∷ inner) ∷ (map (λ {q → add-one-inner x q}) (each-one xs))
each-one (y ∷ xs) | [] = []

make-perms-h : {A : Set} → ℕ → List A → List (List A)
make-perms-h 0 _ = [] ∷ []
make-perms-h _ [] = [] ∷ []
make-perms-h (suc l) inp with (each-one inp)
make-perms-h (suc l) inp | pairs = concat (map
  (λ {(a , xs) → map (λ {q → a ∷ q}) (make-perms-h l xs)})
   pairs)

make-perms : {A : Set} → List A → List (List A)
make-perms inp = make-perms-h (suc (length inp)) inp

-- Almost completed copied from std-lib. Its in the online version, but not the installed version?


filterᵇ : {A : Set} → (A → Bool) → List A → List A
filterᵇ p []       = []
filterᵇ p (x ∷ xs) = if p x then x ∷ filterᵇ p xs else filterᵇ p xs

parse-nat : String → ℕ
parse-nat x = def-zero (readMaybe 10 x)
  where
    def-zero : Maybe ℕ → ℕ
    def-zero (just q) = q
    def-zero _ = 0

ListlinesByᵇ : {A : Set} → (A → Bool) → List A → List (List A)
ListlinesByᵇ {A = A} p = go nothing
  where
  go : Maybe (List A) → List A → List (List A)
  go acc []       = maybe′ ([_] ∘′ reverse) [] acc
  go acc (c ∷ cs) with p c
  ... | true  = reverse (Maybe.fromMaybe [] acc) ∷ go nothing cs
  ... | false = go (just (c ∷ Maybe.fromMaybe [] acc)) cs

ListwordsByᵇ : {A : Set} → (A → Bool) → List A → List (List A)
ListwordsByᵇ {A = A} p = go []
  where
  cons : List A → List (List A) → List (List A)
  cons [] ass = ass
  cons as ass = reverse as ∷ ass

  go : List A → List A → List (List A)
  go acc []       = cons acc []
  go acc (c ∷ cs) with p c
  ... | true  = cons acc (go [] cs)
  ... | false = go (c ∷ acc) cs

wordsByᵇ : (Char → Bool) → String → List String
wordsByᵇ p = List.map fromList ∘ ListwordsByᵇ p ∘ toList

words : String → List String
words = wordsByᵇ Char.isSpace

-- `words` ignores contiguous whitespace
_ : words " abc  b   " ≡ "abc" ∷ "b" ∷ []
_ = refl

linesByᵇ : (Char → Bool) → String → List String
linesByᵇ p = List.map fromList ∘ ListlinesByᵇ p ∘ toList

lines : String → List String
lines = linesByᵇ ('\n' Char.≈ᵇ_)

unmaybe : {A : Set} → List (Maybe A) → List A
unmaybe [] = []
unmaybe ((just x) ∷ xs) = x ∷ (unmaybe xs)
unmaybe (nothing ∷ xs) = unmaybe xs

cartproduct : {A B : Set} → List A → List B → List (A × B)
cartproduct [] _ = []
cartproduct _ [] = []
cartproduct (x ∷ xs) ys = concat ((map (λ {y → (x , y)}) ys) ∷ (cartproduct xs ys) ∷ [])

head-of-each : {A : Set} → List (List A) → List A
head-of-each = unmaybe ∘ (map head)

tail-of-each : {A : Set} → List (List A) → List (List A)
tail-of-each = unmaybe ∘ (map tail)

transpose-h : {A : Set} → ℕ → List (List A) → List (List A)
transpose-h 0 _ = []
transpose-h _ [] = []
transpose-h (suc l) xs with (head-of-each xs)
transpose-h (suc l) xs | [] = []
transpose-h (suc l) xs | h with (tail-of-each xs)
transpose-h (suc l) xs | h | [] = h ∷ []
transpose-h (suc l) xs | h | t = h ∷ (transpose-h l t)

transpose : {A : Set} → List (List A) → List (List A)
transpose [] = []
transpose (x ∷ xs) = transpose-h (suc (length x)) (x ∷ xs)

empty-row : {A : Set} → A → ℕ → List A
empty-row def size = applyUpTo (λ {_ → def}) size

empty-table : {A : Set} → A → ℕ → ℕ → List (List A) 
empty-table def h w = applyUpTo (λ {_ → empty-row def w}) h

show-row : {A : Set} → (A → String) → List A → String
show-row f row = intersperse " " (map f row)

show-table : {A : Set} → (A → String) → List (List A) → String
show-table f tab = unlines (map (show-row f) tab)

test-trim : (fromList ∘ trim ∘ toList) "    abc d   " ≡ "abc d"
test-trim = refl

test-each-one : each-one ("A" ∷ "B" ∷ "C" ∷ []) ≡
  ("A" , "B" ∷ "C" ∷ []) ∷
  ("B" , "A" ∷ "C" ∷ []) ∷
  ("C" , "A" ∷ "B" ∷ []) ∷ []
test-each-one = refl

test-make-perms : map (λ {x → foldr _++_ "" x}) (make-perms ("B" ∷ "A" ∷ [])) ≡ "BA" ∷ "AB" ∷ []
test-make-perms = refl

test-starts-with : starts-with "abc" "abcdef" ≡ true
test-starts-with = refl

test-starts-with-f : starts-with "abc" "acdef" ≡ false
test-starts-with-f = refl

test-two-parts : two-parts 3 "abcdef" ≡ ("abc" , "def")
test-two-parts = refl

test-all-replacements : all-replacements ("ab" , "cdf") "ab1ab23ab" ≡ "cdf1ab23ab" ∷ "ab1cdf23ab" ∷ "ab1ab23cdf" ∷ []
test-all-replacements = refl

test-cart-product : cartproduct (1 ∷ 2 ∷ []) ("a" ∷ "b" ∷ []) ≡
  (1 , "a") ∷ (1 , "b") ∷ (2 , "a") ∷ (2 , "b") ∷ []
test-cart-product = refl

test-min-by-f : min-by-f (λ {q → q}) (2 ∷ 1 ∷ 3 ∷ []) ≡ (just 1)
test-min-by-f = refl

test-enumerate : enumerate ("A" ∷ "B" ∷ []) ≡ (0 , "A") ∷ (1 , "B") ∷ []
test-enumerate = refl

test-split : split ',' "abc,def,ghi" ≡ "abc" ∷ "def" ∷ "ghi" ∷ []
test-split = refl

test-show-table : show-table show ((1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ []) ≡ "1 2 3\n4 5 6"
test-show-table = refl

test-transpose : show-table show (transpose ((1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ [])) ≡ "1 4\n2 5\n3 6"
test-transpose = refl
