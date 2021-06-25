data Divisibleby3 : Nat -> Type where
  Three: Divisibleby3 3
  ThreeMultiple: Divisibleby3 x -> Divisibleby3 (3+x)

divBy9: Divisibleby3 9
divBy9 = ThreeMultiple (ThreeMultiple Three)

data DivisiblebyX : Nat -> Nat -> Type where
  Base:DivisiblebyX x x
  Multiple: DivisiblebyX x y -> DivisiblebyX x (x+y)

divBy10: DivisiblebyX 5 15
divBy10 = Multiple (Multiple Base)

data FizzBuzzProofSimple: Nat -> Type where
  Fizz: DivisiblebyX 3 x -> FizzBuzzProofSimple x
  Buzz: DivisiblebyX 5 x -> FizzBuzzProofSimple x
  FizzBuzz: DivisiblebyX 3 x -> DivisiblebyX 5 x -> FizzBuzzProofSimple x
  Normal: FizzBuzzProofSimple x

Show (FizzBuzzProofSimple x) where
  show (Fizz x) = "fizz"
  show (Buzz x) = "buzz"
  show (FizzBuzz x y) = "fizzbuzz"
  show (Normal {x}) = show x

proof5: FizzBuzzProofSimple 5
proof5 = Buzz Base

proof3: FizzBuzzProofSimple 3
proof3 = Fizz Base

proof7: FizzBuzzProofSimple 7
proof7 = Normal

divisbleby3: (y: Nat) -> Maybe (DivisiblebyX 3 y)
divisbleby3  (S (S (S Z))) = Just Base
divisbleby3 (S (S (S x))) = case divisbleby3 x of
  Nothing => Nothing
  Just y => Just (Multiple y)
divisbleby3 _ = Nothing

divisbleby5: (y: Nat) -> Maybe (DivisiblebyX 5 y)
divisbleby5 (S (S (S (S (S Z))))) = Just(Base)
divisbleby5 (S (S (S (S (S x))))) = case divisbleby5 x of
  Nothing => Nothing
  Just y => Just (Multiple y)
divisbleby5 _ = Nothing

fizzbuzz: (x: Nat) -> FizzBuzzProofSimple x
fizzbuzz x = case (divisbleby3 x, divisbleby5 x) of
  (Nothing, Nothing) => Normal
  (Just fizz_prf, Just buzz_prf) => FizzBuzz fizz_prf buzz_prf
  (Nothing, Just buzz_prf) => Buzz buzz_prf
  (Just fizz_prf, Nothing) => Fizz fizz_prf

wrongfizzbuzz: (x: Nat) -> FizzBuzzProofSimple x
wrongfizzbuzz x = case (divisbleby3 x, divisbleby5 x) of
  (Nothing, Nothing) => Normal
  (_, Just buzz_prf) => Buzz buzz_prf
  (Just fizz_prf, _) => Fizz fizz_prf
  (Just fizz_prf, Just buzz_prf) => FizzBuzz fizz_prf buzz_prf
