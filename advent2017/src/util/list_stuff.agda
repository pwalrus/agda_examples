
module util.list_stuff where


open import util.nat_stuff using (div-nat ; mod-nat)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (fromList ; toList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using () renaming (_==_ to _==s_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_ ; not)
open import Data.Char.Base as Char using (Char)
open import Data.Char.Properties using (_==_)
open import Data.List.Base as List using (List; [_]; _∷_; [] ; reverse ; map ; concat ; foldr ; length ; zip ; head ; tail ; applyUpTo ; take ; drop ; replicate ; _∷ʳ_)
open import Data.List.NonEmpty.Base as NE using (List⁺)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Agda.Builtin.Nat using (_<_ ; _+_ ; _-_) renaming (_==_ to _==n_)
open import Data.Nat using (ℕ; _∸_; ⌊_/2⌋; ⌈_/2⌉ ; suc ; pred)
open import Data.Nat.Show using (readMaybe ; show)
open import Function.Base using (_on_; _∘′_; _∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; map₂)
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

unique-insert : {A : Set} → (A → A → Bool) →  List A → A → List A
unique-insert _ [] l = l ∷ []
unique-insert eq (x ∷ xs) l = if (eq x l)
   then x ∷ xs
   else x ∷ (unique-insert eq xs l)

unique-insert-str : List String → String → List String
unique-insert-str xs l = unique-insert _==s_ xs l

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

is-in : {A : Set} → (A → A → Bool) → List A → A → Bool
is-in _ [] _ = false
is-in eq (x ∷ xs) y with (eq x y)
is-in eq (x ∷ xs) y | true = true
is-in eq (x ∷ xs) y | false = is-in eq xs y


conseq : {A : Set} → List A → List (A × A)
conseq [] = []
conseq (_ ∷ []) = []
conseq (a ∷ b ∷ xs) = (a , b) ∷ (conseq (b ∷ xs))



get-sub-wrap : {A : Set} → ℕ → ℕ → List A → List A
get-sub-wrap _ _ [] = []
get-sub-wrap {A} srt len xs = output
  where
    full-copies : ℕ
    full-copies = div-nat (pred len) (length xs)
    tail-wrap : ℕ
    tail-wrap = mod-nat (len + srt) (length xs)
    output : List A
    output with (srt + len < length xs)
    output | true = take len (drop srt xs)
    output | false = concat ((drop srt xs) ∷ (replicate full-copies xs) ∷ʳ (take tail-wrap xs))

set-sub-wrap : {A : Set} → ℕ → List A → List A → List A
set-sub-wrap _ [] xs = xs
set-sub-wrap _ _ [] = []
set-sub-wrap {A} srt newval xs = output
  where
    len : ℕ
    len = length newval
    tail-wrap : ℕ
    tail-wrap = (length xs - srt)
    inner-untouched : List A
    inner-untouched = drop (length newval - tail-wrap) (take srt xs)
    output : List A
    output with (srt + len < length xs)
    output | true = concat ((take srt xs) ∷ newval ∷ (drop (srt + len) xs) ∷ [])
    output | false = concat ((drop tail-wrap newval) ∷ [ inner-untouched ] ∷ʳ (take (length xs - srt) newval))


atIdx : {A : Set} → ℕ → List A → Maybe A
atIdx _ [] = nothing
atIdx 0 (x ∷ _) = just x
atIdx (suc lm) (x ∷ xs) = atIdx lm xs

setIdx : {A : Set} → ℕ → A → List A → List A
setIdx _ c [] = c ∷ []
setIdx 0 c (_ ∷ xs) = c ∷ xs
setIdx (suc lm) c (x ∷ xs) = x ∷ (setIdx lm c xs)

idxOf : {A : Set} → (A → A → Bool) → ℕ → A → List A → Maybe ℕ
idxOf eq _ _ [] = nothing
idxOf eq idx c (x ∷ xs) = if (eq x c) then just idx else idxOf eq (suc idx) c xs

popIdx : {A : Set} → ℕ → List A → List A
popIdx _ [] = []
popIdx 0 (x ∷ xs) = xs
popIdx (suc idx) (x ∷ xs) = x ∷ (popIdx idx xs)

insIdx : {A : Set} → ℕ → A → List A → List A
insIdx _ c [] = c ∷ []
insIdx 0 c xs = c ∷ xs
insIdx (suc idx) c (x ∷ xs) = x ∷ (insIdx idx c xs)

unmaybe : {A : Set} → List (Maybe A) → List A
unmaybe [] = []
unmaybe ((just x) ∷ xs) = x ∷ (unmaybe xs)
unmaybe (nothing ∷ xs) = unmaybe xs

hard-unmaybe : {A : Set} → List (Maybe A) → Maybe (List A)
hard-unmaybe [] = just []
hard-unmaybe ((just x) ∷ xs) with (hard-unmaybe xs)
hard-unmaybe ((just x) ∷ xs) | (just ys) = just (x ∷ ys)
hard-unmaybe ((just x) ∷ xs) | nothing = nothing
hard-unmaybe (nothing ∷ xs) = nothing

apply-perm-to-perm : {A : Set} → List ℕ → List A → List A
apply-perm-to-perm perm base = (unmaybe ∘ map (λ {q → atIdx q base})) perm

private
  exp-perm-h : {A : Set} → ℕ → ℕ → (A → A → A) → A → List A → List A
  exp-perm-h 0 _ _ _ _ = []
  exp-perm-h _ 0 _ _ _ = []
  exp-perm-h {A} (suc lm) n func inp accum = new-inp
    where
      rem : ℕ
      rem = mod-nat n 2
      div : ℕ
      div = div-nat n 2
      new-base : A
      new-base = func inp inp
      new-accum : List A
      new-accum with (rem)
      new-accum | 0 = accum
      new-accum | _ = inp ∷ accum
      new-inp : List A
      new-inp with (div ==n 0)
      new-inp | true = new-accum
      new-inp | false = exp-perm-h lm div func new-base new-accum

exp-perm : {A : Set} → ℕ → (A → A → A) → A → A
exp-perm {A} n func base = output
  where
    parts : List A
    parts = exp-perm-h n n func base []
    output : A
    output with (head parts)
    output | (just x) with (tail parts)
    output | (just x) | (just t) = foldr func x t
    output | (just x) | _ = base
    output | _ = base

-- Almost completed copied from std-lib. Its in the online version, but not the installed version?


filterᵇ : {A : Set} → (A → Bool) → List A → List A
filterᵇ p []       = []
filterᵇ p (x ∷ xs) = if p x then x ∷ filterᵇ p xs else filterᵇ p xs

list-minus : {A : Set} → (A → A → Bool) → List A → List A → List A
list-minus eq xs ys = filterᵇ (not ∘ (is-in eq ys)) xs

deduplicateᵇ : {A : Set} → (A → A → Bool) → List A → List A
deduplicateᵇ r [] = []
deduplicateᵇ r (x ∷ xs) = x ∷ filterᵇ (not ∘ r x) (deduplicateᵇ r xs)


index-of-h : {A : Set} → ℕ → (A → A → Bool) → List A → A → Maybe ℕ
index-of-h _ _ [] _ = nothing
index-of-h idx eq (x ∷ xs) k = if (eq x k) then (just idx) else index-of-h (suc idx) eq xs k

index-of : {A : Set} → (A → A → Bool) → List A → A → Maybe ℕ
index-of eq xs k = index-of-h 0 eq xs k

set-at-h : {A : Set} → List A → List A → ℕ → A → List A
set-at-h xs [] _ _ = reverse xs
set-at-h h (x ∷ xs) 0 val = concat ((reverse h) ∷ (val ∷ xs) ∷ [])
set-at-h h (x ∷ xs) (suc idx) val = set-at-h (x ∷ h) xs idx val

set-at : {A : Set} → List A → ℕ → A → List A
set-at xs n val = set-at-h [] xs n val


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

map₂′ : {A B C : Set} → (B → C) → A × B → A × C
map₂′ f = map₂ f

partitionᵇ : {A : Set} → (A → Bool) → List A → List A × List A
partitionᵇ p []       = ([] , [])
partitionᵇ p (x ∷ xs) = (if p x then map₁ else map₂′) (x ∷_) (partitionᵇ p xs)

eq-classes-h : {A : Set} → ℕ → (A → A → Bool) → List A → List (List A)
eq-classes-h {A} 0 _ _ = []
eq-classes-h {A} (suc lm) f [] = []
eq-classes-h {A} (suc lm) f (x ∷ xs) = (proj₁ fst-div) ∷ (eq-classes-h lm f (proj₂ fst-div))
  where
    fst-div : List A × List A
    fst-div = partitionᵇ (f x) (x ∷ xs)

eq-classes : {A : Set} → (A → A → Bool) → List A → List (List A)
eq-classes f xs = eq-classes-h (length xs) f xs

rem-match : {A : Set} → (A → Bool) → List A → List A
rem-match f [] = []
rem-match f (x ∷ xs) with (f x)
rem-match f (x ∷ xs) | true = rem-match f xs
rem-match f (x ∷ xs) | false = x ∷ (rem-match f xs)

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

test-eq-classes : eq-classes _==_ ('a' ∷ 'a' ∷ 'c' ∷ 'b' ∷ 'c' ∷ []) ≡ (('a' ∷ 'a' ∷ []) ∷ ('c' ∷ 'c' ∷ []) ∷ ('b' ∷ []) ∷ [])
test-eq-classes = refl

test-rem-match : rem-match (λ {q → q == 'c'}) ('a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ []) ≡ ('a' ∷ 'b' ∷ 'd' ∷ [])
test-rem-match = refl

test-conseq : conseq (1 ∷ 2 ∷ 3 ∷ []) ≡ (1 , 2) ∷ (2 , 3) ∷ []
test-conseq = refl

test-set-at : set-at (1 ∷ 2 ∷ 3 ∷ []) 1 5 ≡ (1 ∷ 5 ∷ 3 ∷ [])
test-set-at = refl


test-get-sub-wrap-a : (fromList ∘ get-sub-wrap 1 3 ∘ toList) "abcdef" ≡ "bcd"
test-get-sub-wrap-a = refl

test-get-sub-wrap-b : (fromList ∘ get-sub-wrap 5 3 ∘ toList) "abcdef" ≡ "fab"
test-get-sub-wrap-b = refl

test-get-sub-wrap-c : (fromList ∘ get-sub-wrap 5 9 ∘ toList) "abcdef" ≡ "fabcdefab"
test-get-sub-wrap-c = refl

test-set-sub-wrap-a : (fromList ∘ set-sub-wrap 1 (toList "qrst") ∘ toList) "abcdef" ≡ "aqrstf"
test-set-sub-wrap-a = refl

test-set-sub-wrap-b : (fromList ∘ set-sub-wrap 5 (toList "qr") ∘ toList) "abcdef" ≡ "rbcdeq"
test-set-sub-wrap-b = refl

test-set-sub-wrap-c : (fromList ∘ set-sub-wrap 5 (toList "qrs") ∘ toList) "abcdef" ≡ "rscdeq"
test-set-sub-wrap-c = refl

test-set-sub-wrap-d : (fromList ∘ set-sub-wrap 5 (toList "qrst") ∘ toList) "abcdef" ≡ "rstdeq"
test-set-sub-wrap-d = refl

test-apply-perm : (fromList ∘ apply-perm-to-perm (1 ∷ 2 ∷ 0 ∷ []) ∘ toList) "abc" ≡ "bca"
test-apply-perm = refl

test-exp-perm-a : exp-perm 7 _+_ 3 ≡ 21
test-exp-perm-a = refl

test-exp-perm-b : exp-perm 4 _+_ 3 ≡ 12
test-exp-perm-b = refl
