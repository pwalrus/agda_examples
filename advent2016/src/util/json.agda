

module util.json where


open import util.list_stuff using (unmaybe ; trim-leading ; trim)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (fromList ; toList ; _++_ ; intersperse)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties using (_==_)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.List.Base using (length ; concat ; reverse ; map ; foldr) renaming (_++_ to _++c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∨_ ; _∧_)
open import Agda.Builtin.Nat using (Nat ; suc)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (readMaybe)
open import Data.Nat.Properties using (_≟_)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_+_ ; _-_)
open import Data.Integer.Show using (show)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)
open import Function.Base using (_∘_)


data JsonObj : Set where
  null : JsonObj
  boolean : Bool → JsonObj
  num : Int → JsonObj
  str : String → JsonObj
  lst : List JsonObj → JsonObj
  dict : List (String × JsonObj) → JsonObj

unescape : List Char → List Char
unescape [] = []
unescape ('\\' ∷ '"' ∷ xs) = '"' ∷ (unescape xs)
unescape ('\\' ∷ '\\' ∷ xs) = '\\' ∷ (unescape xs)
unescape ('\\' ∷ 'x' ∷ a ∷ b ∷ xs) with (readMaybe 16 (fromList (a ∷ b ∷ [])))
unescape ('\\' ∷ 'x' ∷ a ∷ b ∷ xs) | nothing = a ∷ b ∷ (unescape xs)
unescape ('\\' ∷ 'x' ∷ a ∷ b ∷ xs) | (just x) = (primNatToChar x) ∷ (unescape xs)
unescape (x ∷ xs) = x ∷ (unescape xs)

escape : List Char → List Char
escape [] = []
escape ('"' ∷ xs) = '\\' ∷ '"' ∷ (escape xs)
escape ('\\' ∷ xs) = '\\' ∷ '\\' ∷ (escape xs)
escape (x ∷ xs) = x ∷ (escape xs)

requote : List Char → List Char
requote x = ('"' ∷ x) ++c ('"' ∷ [])

show-json-h : Nat → JsonObj → String
show-json-h 0 _ = ""
show-json-h _ null = "null"
show-json-h _ (boolean false) = "false"
show-json-h _ (boolean true) = "true"
show-json-h _ (num k) = show k
show-json-h _ (str k) = (fromList ∘ requote ∘ escape ∘ toList) k
show-json-h (suc l) (lst d) = "[" ++ intersperse "," (map (show-json-h l) d) ++ "]"
show-json-h (suc l) (dict d) = "{" ++ (intersperse "," dict-parts) ++ "}"
  where
    dict-parts : List String
    dict-parts = map (λ {(k , v) → ((fromList ∘ requote ∘ escape ∘ toList) k) ++ ": " ++ (show-json-h l v)}) d

show-json : JsonObj → String
show-json = show-json-h 1000

readIntMaybe : List Char → Maybe Int
readIntMaybe [] = nothing
readIntMaybe ('-' ∷ xs) with (readMaybe 10 (fromList xs))
readIntMaybe ('-' ∷ xs) | nothing = nothing
readIntMaybe ('-' ∷ xs) | (just k) = just (negsuc (pred k))
readIntMaybe xs with (readMaybe 10 (fromList xs))
readIntMaybe xs | nothing = nothing
readIntMaybe xs | (just k) = just (pos k)

is-balanced-h : List Char → Bool → List Char → Bool
is-balanced-h [] false [] = true
is-balanced-h [] _ (_ ∷ _) = false
is-balanced-h [] true _ = false
is-balanced-h ('[' ∷ xs) false stack = is-balanced-h xs false ('[' ∷ stack)
is-balanced-h ('{' ∷ xs) false stack = is-balanced-h xs false ('{' ∷ stack)
is-balanced-h (']' ∷ xs) false ('[' ∷ stack) = is-balanced-h xs false stack
is-balanced-h ('}' ∷ xs) false ('{' ∷ stack) = is-balanced-h xs false stack
is-balanced-h (']' ∷ xs) false _ = false
is-balanced-h ('}' ∷ xs) false _ = false
is-balanced-h ('"' ∷ xs) false stack = is-balanced-h xs true stack
is-balanced-h ('"' ∷ xs) true stack = is-balanced-h xs false stack
is-balanced-h ('\\' ∷ '"' ∷ xs) true stack = is-balanced-h xs true stack
is-balanced-h (x ∷ xs) true stack = is-balanced-h xs true stack
is-balanced-h (x ∷ xs) false stack = is-balanced-h xs false stack

is-balanced : List Char → Bool
is-balanced inp = is-balanced-h inp false []

take-sect-h : Nat → Char → Char → (List Char) × (List Char) → (List Char) × (List Char)
take-sect-h 0 _ _ (x , y) = (x , y)
take-sect-h _ _ _ (x , []) = (x , [])
take-sect-h (suc l) o c ([] , x ∷ xs) with (o == x)
take-sect-h (suc l) o c ([] , x ∷ xs) | true = take-sect-h l o c (x ∷ [] , xs)
take-sect-h (suc l) o c ([] , x ∷ xs) | false = take-sect-h l o c ([] , xs)
take-sect-h (suc l) o c (ys , x ∷ xs) with ((c == x) ∧ (is-balanced (reverse (c ∷ ys))))
take-sect-h (suc l) o c (ys , x ∷ xs) | true = (reverse (c ∷ ys) , xs)
take-sect-h (suc l) o c (ys , x ∷ xs) | false = take-sect-h l o c (x ∷ ys , xs)

take-string : (List Char) → (List Char) × (List Char)
take-string x = take-sect-h (length x) '"' '"' ([] , x)

take-list : (List Char) → (List Char) × (List Char)
take-list x = take-sect-h (length x) '[' ']' ([] , x)

take-dict : (List Char) → (List Char) × (List Char)
take-dict x = take-sect-h (length x) '{' '}' ([] , x)


rem-lst-c : Char → List Char → List Char
rem-lst-c _ [] = []
rem-lst-c c (x ∷ []) = if (c == x) then [] else (x ∷ [])
rem-lst-c c (x ∷ xs) = x ∷ (rem-lst-c c xs)

rem-fst-c : Char → List Char → List Char
rem-fst-c c (x ∷ xs) = if (x == c) then xs else (x ∷ xs)
rem-fst-c c x = x

remove-quotes : List Char → List Char
remove-quotes = (rem-fst-c '"') ∘ (rem-lst-c '"')

remove-sq : List Char → List Char
remove-sq = (rem-fst-c '[') ∘ (rem-lst-c ']')

remove-cl : List Char → List Char
remove-cl = (rem-fst-c '{') ∘ (rem-lst-c '}')

read-char-h : List Char → Char → List Char → Maybe (List Char × List Char)
read-char-h x _ [] = if (is-balanced (reverse x)) then (just(reverse x , [])) else nothing
read-char-h x delim (y ∷ ys) with ((y == delim) ∧ (is-balanced (reverse x)))
read-char-h x delim (y ∷ ys) | true = just (reverse x , ys)
read-char-h x delim (y ∷ ys) | false = read-char-h (y ∷ x) delim ys

read-comma-h : List Char → List Char → Maybe (List Char × List Char)
read-comma-h x y = read-char-h x ',' y

break-comma-h : Nat → List Char → Maybe (List (List Char))
break-comma-h 0 _ = nothing
break-comma-h (suc l) inp with (read-comma-h [] inp)
break-comma-h (suc l) inp | (just (h , t)) with (trim-leading t)
break-comma-h (suc l) inp | (just (h , t)) | [] = just (h ∷ [])
break-comma-h (suc l) inp | (just (h , t)) | k with (break-comma-h l k)
break-comma-h (suc l) inp | (just (h , t)) | k | (just parts) = just (h ∷ parts)
break-comma-h (suc l) inp | (just (h , t)) | k | nothing = nothing
break-comma-h (suc l) inp | nothing = nothing

break-comma : List Char → Maybe (List (List Char))
break-comma x = break-comma-h (suc (length x)) x

parse-colon : (List Char → Maybe JsonObj) → List Char → Maybe (String × JsonObj)
parse-colon f inp with (read-char-h [] ':' inp)
parse-colon f inp | nothing = nothing
parse-colon f inp | (just (h , t)) with ((f ∘ trim) h)
parse-colon f inp | (just (h , t)) | (just (str key)) with ((f ∘ trim) t)
parse-colon f inp | (just (h , t)) | (just (str key)) | (just val) = just (key , val)
parse-colon f inp | (just (h , t)) | (just (str key)) | nothing = nothing
parse-colon f inp | (just (h , t)) | _ = nothing


parse-json-h : Nat → List Char → Maybe JsonObj
parse-json-h 0 _ = nothing
parse-json-h _ [] = just null
parse-json-h _ ('n' ∷ 'u' ∷ 'l' ∷ 'l' ∷ []) = just null
parse-json-h _ ('t' ∷ 'r' ∷ 'u' ∷ 'e' ∷ []) = just (boolean true)
parse-json-h _ ('f' ∷ 'a' ∷ 'l' ∷ 's' ∷ 'e' ∷ []) = just (boolean false)
parse-json-h _ ('"' ∷ xs) = just (str ((fromList ∘ remove-quotes ∘ proj₁ ∘ take-string) ('"' ∷ xs)))
parse-json-h (suc l) ('[' ∷ xs) with ((break-comma ∘ remove-sq ∘ proj₁ ∘ take-list) ('[' ∷ xs))
parse-json-h (suc l) ('[' ∷ xs) | (just parts) with (unmaybe (map ((parse-json-h l) ∘ trim) parts))
parse-json-h (suc l) ('[' ∷ xs) | (just parts) | real-parts = just (lst real-parts)
parse-json-h (suc l) ('[' ∷ xs) | nothing = nothing
parse-json-h (suc l) ('{' ∷ xs) with ((break-comma ∘ remove-cl ∘ proj₁ ∘ take-dict) ('{' ∷ xs))
parse-json-h (suc l) ('{' ∷ xs) | (just parts) with (unmaybe (map ((parse-colon (parse-json-h l) ∘ trim) ) parts))
parse-json-h (suc l) ('{' ∷ xs) | (just parts) | keys = just (dict keys)
parse-json-h (suc l) ('{' ∷ xs) | nothing = nothing
parse-json-h _ (x ∷ xs) with ((readIntMaybe ∘ trim) (x ∷ xs))
parse-json-h _ (x ∷ xs) | nothing = nothing
parse-json-h _ (x ∷ xs) | (just k) = just (num k)

parse-json : String → Maybe JsonObj
parse-json y = parse-json-h (length x) (trim x)
  where
  x : List Char
  x = toList y

show-maybe : Maybe JsonObj → String
show-maybe nothing = "nothing"
show-maybe (just x) = show-json x

test-take-string : (fromList ∘ proj₁) (take-string (toList "\"abc\": 1")) ≡ "\"abc\""
test-take-string = refl

test-take-list : (fromList ∘ proj₁) (take-list (toList "[[[3]]]")) ≡ "[[[3]]]"
test-take-list = refl

test-parse-false : parse-json "false" ≡ just (boolean false)
test-parse-false = refl

test_parse-true : parse-json "true" ≡ just (boolean true)
test_parse-true = refl

test-parse-null : parse-json "null" ≡ just (null)
test-parse-null = refl

test-parse-str : parse-json "\"abc\"" ≡ just (str "abc")
test-parse-str = refl

test-read-comma-blank : read-comma-h  [] (toList "123") ≡ just ((toList "123") , [])
test-read-comma-blank = refl

test-read-comma : read-comma-h  [] (toList "123,456") ≡ just ((toList "123") , (toList "456"))
test-read-comma = refl

test-break-comma_a : break-comma (toList "123,456") ≡ just ((toList "123") ∷ (toList "456") ∷ [])
test-break-comma_a = refl

test-break-comma_b : ((break-comma ∘ remove-sq ∘ proj₁ ∘ take-list ∘ toList) "[123,456]") ≡ just ((toList "123") ∷ (toList "456") ∷ [])
test-break-comma_b = refl

test-break-comma_c : read-comma-h [] (toList "[123,456]") ≡ just ((toList "[123,456]") , [])
test-break-comma_c = refl

test-parse-list : parse-json "[\"abc\",\"q\"]" ≡ just (lst ((str "abc") ∷ (str "q") ∷ []))
test-parse-list = refl

test-parse-dict : parse-json "{\"abc\":\"q\"}" ≡ just (dict (("abc", (str "q")) ∷ []))
test-parse-dict = refl

test-parse-dict-num : parse-json "{\"abc\": 5 }" ≡ just (dict (("abc", (num (pos 5))) ∷ []))
test-parse-dict-num = refl

test-is-balanceda : (is-balanced ∘ toList) "\"abc\"" ≡ true
test-is-balanceda = refl

test-is-balancedb : (is-balanced ∘ toList) "\"abc" ≡ false
test-is-balancedb = refl

test-is-balancedc : (is-balanced ∘ toList) "[{\"abc\"}]" ≡ true
test-is-balancedc = refl

test-is-balancedd : (is-balanced ∘ toList) "[\"abc\"}]" ≡ false
test-is-balancedd = refl

test-serial : (show-maybe ∘ parse-json) "{\"a\":[1,2,3],\"b\":[4,5,6]}" ≡ "{\"a\": [1,2,3],\"b\": [4,5,6]}"
test-serial = refl

test-serial-spaces-a : (show-maybe ∘ parse-json) "  [ 1 , 2 , 3 ] " ≡ "[1,2,3]"
test-serial-spaces-a = refl

test-serial-spaces-b : (show-maybe ∘ parse-json) " { \"a\" :  1 ,  \"b\" :  4  } " ≡ "{\"a\": 1,\"b\": 4}"
test-serial-spaces-b = refl

test-serial-spaces-c : (show-maybe ∘ parse-json) " { \"a\" : [ 1 , 2 , 3 ] , \"b\" : [ 4 , 5 , 6 ] } " ≡ "{\"a\": [1,2,3],\"b\": [4,5,6]}"
test-serial-spaces-c = refl

