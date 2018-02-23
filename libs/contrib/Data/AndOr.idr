||| Result. Ported from https://github.com/isomorphism/these

module Data.Result

import Data.Combinators
import Data.Combinators.Arrow
import Control.Isomorphism
import Control.Pipeline

%default total
%access public export

||| a + b + ab.
||| The constructors can be thought of as follows:
||| - `Failed error`: Unrecoverable error.
||| - `Success value`: Success.
||| - `Recovered error value`: Warings/Recoverable error
data Result a b = Failed a | Success b | Recovered a b

||| Produces a tuple, using a function from the other value if one value is unavailable
toTuple : (b -> a) -> (a -> b) -> Result a b -> (a, b)
toTuple _ f (Failed x) = (x, f x)
toTuple g _ (Success y) = (g y, y)
toTuple _ _ (Recovered x y) = (x, y)

||| Takes two default values and produces a tuple.
fromAndOr : a -> b -> Result a b -> (a, b)
fromAndOr a b x = toTuple (const a) (const b) x

||| Get the `a` value, if available
first : Result a b -> Maybe a
first (Failed x) = Just x
first (Success _) = Nothing
first (Recovered x _) = Just x

||| Get the `b` value, if available
second : Result a b -> Maybe b
second (Failed _) = Nothing
second (Success y) = Just y
second (Recovered _ y) = Just y

catFirst : List (Result a b) -> List a
catFirst = mapMaybe first

catSecond : List (Result a b) -> List b
catSecond = mapMaybe second

partition : List (Result a b) -> (List a, List b)
partition = catFirst &&& catSecond

mapAndOr : (a -> c) -> (b -> d) -> Result a b -> Result c d
mapAndOr f _ (Failed x) = Failed (f x)
mapAndOr _ g (Success y) = Success (g y)
mapAndOr f g (Recovered x y) = Recovered (f x) (g y)

mapFirst : (a -> b) -> Result a c -> Result b c
mapFirst f = mapAndOr f id

mapSecond : (b -> c) -> Result a b -> Result a c
mapSecond g = mapAndOr id g

private
combine : Semigroup a => Maybe a -> Maybe a -> Maybe a
combine (Just x) y = (x <+>) <$> y
combine Nothing y = y

(Semigroup e, Semigroup v) => Semigroup (Result e v) where
  a <+> b with (((combine `on` first) a b, (combine `on` second) a b))
    | (Just x, Nothing) = Failed x
    | (Nothing, Just y) = Success y
    | (Just x, Just y) = Recovered x y
    | (Nothing, Nothing) = assert_unreachable

Functor (Result e) where
  map _ (Failed a) = Failed a
  map f (Success x) = Success (f x)
  map f (Recovered a x) = Recovered a (f x)

Semigroup e => Applicative (Result e) where
  pure = Success
  (<*>) l r = let
      errors = first l `combine` first r
      result = second l <*> second r
    in case (errors, result) of
      (Just a, Nothing) => Failed a
      (Just a, Just x) => Recovered a x
      (Nothing, Just x) => Success x
      (Nothing, Nothing) => assert_unreachable

[monadApplicativeAndOr] Semigroup e => Applicative (Result e) where
  pure = Success
  (Failed   a  ) <*> _            = Failed  a
  (Success    _) <*> (Failed   b  ) = Failed  b
  (Success    f) <*> (Success    x) = Success (f x)
  (Success    f) <*> (Recovered   b x) = Recovered  b (f x)
  (Recovered   a _) <*> (Failed   b  ) = Failed (a <+> b)
  (Recovered   a f) <*> (Success    x) = Recovered a (f x)
  (Recovered   a f) <*> (Recovered   b x) = Recovered (a <+> b) (f x)

propagate : Semigroup a => a -> Result a b -> Result a b
propagate a (Failed b) = Failed (a <+> b)
propagate a (Success y) = Recovered a y
propagate a (Recovered b y) = Recovered (a <+> b) y

Semigroup e => Monad (Result e) using monadApplicativeAndOr where
  join (Failed a) = Failed a
  join (Success x) = x
  join (Recovered a x) = propagate a x
