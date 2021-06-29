data Divisibleby3 : Nat -> Type where
  Three: Divisibleby3 3
  ThreeMultiple: Divisibleby3 x -> Divisibleby3 (3+x)

divBy9: Divisibleby3 9
divBy9 = ThreeMultiple (ThreeMultiple Three)

data DivisiblebyX : Nat -> Nat -> Type where
  Base:DivisiblebyX x x
  Multiple: DivisiblebyX x y -> DivisiblebyX x (x+y)

divBy5_15: DivisiblebyX 5 15
divBy5_15 = Multiple (Multiple Base)

divBy3_15: DivisiblebyX 3 15
divBy3_15 = Multiple (Multiple (Multiple (Multiple Base)))

data FizzBuzzProofSimple: Nat -> Type where
  Fizz: DivisiblebyX 3 x -> FizzBuzzProofSimple x
  Buzz: DivisiblebyX 5 x -> FizzBuzzProofSimple x
  FizzBuzz: DivisiblebyX 3 x -> DivisiblebyX 5 x -> FizzBuzzProofSimple x
  Normal: (x: Nat) -> FizzBuzzProofSimple x

Show (FizzBuzzProofSimple x) where
  show (Fizz _) = "fizz"
  show (Buzz _) = "buzz"
  show (FizzBuzz _ _) = "fizzbuzz"
  show (Normal x) = show x

proof5: FizzBuzzProofSimple 5
proof5 = Buzz Base

proof3: FizzBuzzProofSimple 3
proof3 = Fizz Base

proof7: FizzBuzzProofSimple 7
proof7 = Normal 7

proof15: FizzBuzzProofSimple 15
proof15 = FizzBuzz (Multiple (Multiple (Multiple (Multiple Base)))) (Multiple (Multiple Base))

divisibleby3: (y: Nat) -> Maybe (DivisiblebyX 3 y)
divisibleby3  (S (S (S Z))) = Just Base
divisibleby3 (S (S (S x))) = case divisibleby3 x of
  Nothing => Nothing
  Just y => Just (Multiple y)
divisibleby3 _ = Nothing

divisibleby5: (y: Nat) -> Maybe (DivisiblebyX 5 y)
divisibleby5 (S (S (S (S (S Z))))) = Just(Base)
divisibleby5 (S (S (S (S (S x))))) = case divisibleby5 x of
  Nothing => Nothing
  Just y => Just (Multiple y)
divisibleby5 _ = Nothing

fizzbuzz: (x: Nat) -> FizzBuzzProofSimple x
fizzbuzz x = case (divisibleby3 x, divisibleby5 x) of
  (Nothing, Nothing) => Normal x
  (Just fizz_prf, Just buzz_prf) => FizzBuzz fizz_prf buzz_prf
  (Nothing, Just buzz_prf) => Buzz buzz_prf
  (Just fizz_prf, Nothing) => Fizz fizz_prf

wrongfizzbuzz: (x: Nat) -> FizzBuzzProofSimple x
wrongfizzbuzz x = case (divisibleby3 x, divisibleby5 x) of
  (Nothing, Nothing) => Normal x
  (_, Just buzz_prf) => Buzz buzz_prf
  (Just fizz_prf, _) => Fizz fizz_prf
