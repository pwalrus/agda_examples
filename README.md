

# agda_examples

Practice problems in Agda, mostly Advent of Code problems 

## advent of code

The chosen approach to side step Agda's IO difficulties is to import Haskell's `interact` function as a postulate:

```haskell
interact :: (String -> String) -> IO ()
```

as a postulate with the othe pragma it looks like: 

```agda
postulate interact : (String → String) → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC interact = \ f -> interact ( T.unpack . f . T.pack ) #-}
```
 
Then every advent solution can be represented as a single function `my-sol : String →  String`.

Where the solution is compiled like so,

```bash
advent2017/src$ agda -c advent2017.agda
```

The code (with puzzle input in a text file: `input.txt`) can be run as:

```bash
advent2017/src$ cat input.txt | ./advent2017
```

