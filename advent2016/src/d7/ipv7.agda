module d7.ipv7 where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair ; str-lt ; quick-sort ; counter) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; take ; head ; last; tail ; any ; cartesianProductWith)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties renaming (_==_ to _==c_ ; _<?_ to _<c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


data Addr : Set where
  addr : List String → List String → Addr

show-addr : Addr → String
show-addr (addr outs ins) = foldr _++_ "" (map (λ {(x , y) → x ++ "[" ++ y ++ "]"}) (zip outs ins)) ++ (fromMaybe "" (last outs))

comb-addr : Addr → Addr → Addr
comb-addr (addr lhs rhs) (addr lhs2 rhs2) = addr (concat (lhs ∷ lhs2 ∷ [])) (concat (rhs ∷ rhs2 ∷ []))

empty-addr : Addr → Bool
empty-addr (addr outs ins) with (head outs)
empty-addr (addr outs ins) | nothing = false
empty-addr (addr outs ins) | _ = true

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

rm-blanks : List String → List String
rm-blanks = filterᵇ (λ {q → not (trim q == "")})

addr-from-list : List String → Addr
addr-from-list [] = addr [] []
addr-from-list (x ∷ []) = addr (x ∷ []) []
addr-from-list (x ∷ y ∷ _) = addr (y ∷ []) (x ∷ [])

parse-line : String → Maybe Addr
parse-line x = output
  where
    parts : List (List String)
    parts = map (split ']') (split '[' x)
    pot-addr : Addr
    pot-addr = foldr comb-addr (addr [] []) (map (addr-from-list ∘ rm-blanks) parts)
    output : Maybe Addr
    output with (empty-addr pot-addr)
    output | false = nothing
    output | true = just pot-addr

has-palid-ch : Nat → List Char → Bool
has-palid-ch 0 _ = false
has-palid-ch (suc l) (a ∷ b ∷ c ∷ d ∷ xs) with ((a ==c d) ∧ (b ==c c) ∧ not (a ==c b))
has-palid-ch (suc l) (a ∷ b ∷ c ∷ d ∷ xs) | true = true
has-palid-ch (suc l) (a ∷ b ∷ c ∷ d ∷ xs) | false = has-palid-ch l (b ∷ c ∷ d ∷ xs)
has-palid-ch _ _ = false

has-palid : String → Bool
has-palid x = ((has-palid-ch (suc (length (toList x)))) ∘ toList) x

data ChTrip : Set where
  chtrip : Char → Char → ChTrip

is-inv : ChTrip → ChTrip → Bool
is-inv (chtrip a b) (chtrip x y) = (a ==c y) ∧ (b ==c x)

has-inv : List ChTrip → List ChTrip → Bool
has-inv a b = any (λ {q → q}) (cartesianProductWith is-inv a b)

find-triples-ch : Nat → List Char → List ChTrip
find-triples-ch 0 _ = []
find-triples-ch (suc l) (x ∷ y ∷ z ∷ xs) with ((x ==c z) ∧ not (x ==c y))
find-triples-ch (suc l) (x ∷ y ∷ z ∷ xs) | true = (chtrip x y) ∷ (find-triples-ch l (y ∷ z ∷ xs))
find-triples-ch (suc l) (x ∷ y ∷ z ∷ xs) | false = (find-triples-ch l (y ∷ z ∷ xs))
find-triples-ch _ _ = []

find-triples : List String → List ChTrip
find-triples xs = concat individ
  where
    individ : List (List ChTrip)
    individ = map (λ {x → (find-triples-ch ((suc ∘ length ∘ toList) x) (toList x)) }) xs


addr-has-inv : Addr → Bool
addr-has-inv (addr outs ins) = has-inv (find-triples outs) (find-triples ins)

valid-addr : Addr → Bool
valid-addr (addr outs ins) = (any has-palid outs) ∧ not (any has-palid ins) 

count-valid-addr : String → String
count-valid-addr x = "count: " ++ (show ∘ (foldr _+_ 0) ∘ (map (λ {q → if valid-addr q then 1 else 0})) ∘ unmaybe ∘ (map parse-line) ∘ lines) x ++ "\n"

count-ssl-addr : String → String
count-ssl-addr x = "count: " ++ (show ∘ (foldr _+_ 0) ∘ (map (λ {q → if addr-has-inv q then 1 else 0})) ∘ unmaybe ∘ (map parse-line) ∘ lines) x ++ "\n"

test-parse-line : show-addr (fromMaybe (addr [] []) (parse-line "abba[mnop]qrst")) ≡ "abba[mnop]qrst"
test-parse-line = refl

test-has-palid-a : has-palid "abba" ≡ true
test-has-palid-a = refl

test-valid-addr-a : valid-addr (fromMaybe (addr [] []) (parse-line "abba[mnop]qrst")) ≡ true
test-valid-addr-a = refl

test-valid-addr-b : valid-addr (fromMaybe (addr [] []) (parse-line "abcd[bddb]xyyx")) ≡ false
test-valid-addr-b = refl

test-valid-addr-c : valid-addr (fromMaybe (addr [] []) (parse-line "aaaa[qwer]tyui")) ≡ false
test-valid-addr-c = refl

test-valid-addr-d : valid-addr (fromMaybe (addr [] []) (parse-line "ioxxoj[asdfgh]zxcvbn")) ≡ true
test-valid-addr-d = refl

test-addr-has-inv-a : addr-has-inv (fromMaybe (addr [] []) (parse-line "aba[bab]xyz")) ≡ true
test-addr-has-inv-a = refl

test-addr-has-inv-b : addr-has-inv (fromMaybe (addr [] []) (parse-line "xyx[xyx]xyx")) ≡ false
test-addr-has-inv-b = refl

test-addr-has-inv-c : addr-has-inv (fromMaybe (addr [] []) (parse-line "aaa[kek]eke")) ≡ true
test-addr-has-inv-c = refl

test-addr-has-inv-d : addr-has-inv (fromMaybe (addr [] []) (parse-line "zazbz[bzb]cdb")) ≡ true
test-addr-has-inv-d = refl
