import Decidable.Equality

data DivisiblebyX : Nat -> Nat -> Type where
  Base: DivisiblebyX x x
  Multiple: DivisiblebyX x y -> DivisiblebyX x (x+y)

data FizzBuzzProof: Nat -> Type where
  Fizz: DivisiblebyX 3 x -> (DivisiblebyX 5 x -> Void) -> FizzBuzzProof x
  Buzz: DivisiblebyX 5 x -> (DivisiblebyX 3 x -> Void) -> FizzBuzzProof x
  FizzBuzz: DivisiblebyX 3 x -> DivisiblebyX 5 x -> FizzBuzzProof x
  Normal: (x: Nat) -> (DivisiblebyX 3 x -> Void) ->(DivisiblebyX 5 x -> Void) -> FizzBuzzProof x

Show (FizzBuzzProof x) where
  show (Fizz _ _) = "fizz"
  show (Buzz _ _) = "buzz"
  show (FizzBuzz _ _) = "fizzbuzz"
  show (Normal x _ _) = show x

threeLessNotDivisible3 : (notdiv : DivisiblebyX 3 (S y) -> Void) -> DivisiblebyX 3 (3 + (S y)) -> Void
threeLessNotDivisible3 notdiv (Multiple x) = notdiv x

zeroNotDivisible3 : DivisiblebyX 3 0 -> Void
zeroNotDivisible3 Base impossible
zeroNotDivisible3 (Multiple _) impossible

oneNotDivisible3 : DivisiblebyX 3 1 -> Void
oneNotDivisible3 Base impossible
oneNotDivisible3 (Multiple _) impossible

twoNotDivisible3 : DivisiblebyX 3 2 -> Void
twoNotDivisible3 Base impossible
twoNotDivisible3 (Multiple _) impossible

divisibleby3: (y: Nat) -> Dec (DivisiblebyX 3 y)
divisibleby3 Z = No zeroNotDivisible3
divisibleby3 (S Z) = No oneNotDivisible3
divisibleby3 (S (S Z)) = No twoNotDivisible3
divisibleby3 (S (S (S Z))) = Yes Base
divisibleby3 (S (S (S (S y)))) = case divisibleby3 (S y) of
  Yes prf => Yes (Multiple prf)
  No notdiv => No (threeLessNotDivisible3 notdiv)

zeroNotDivisible5 : DivisiblebyX 5 0 -> Void
zeroNotDivisible5 Base impossible
zeroNotDivisible5 (Multiple _) impossible

oneNotDivisible5 : DivisiblebyX 5 1 -> Void
oneNotDivisible5 Base impossible
oneNotDivisible5 (Multiple _) impossible

twoNotDivisible5 : DivisiblebyX 5 2 -> Void
twoNotDivisible5 Base impossible
twoNotDivisible5 (Multiple _) impossible

threeNotDivisible5 : DivisiblebyX 5 3 -> Void
threeNotDivisible5 Base impossible
threeNotDivisible5 (Multiple _) impossible

fourNotDivisible5 : DivisiblebyX 5 4 -> Void
fourNotDivisible5 Base impossible
fourNotDivisible5 (Multiple _) impossible

fiveLessNotDivisible5 : (notdiv : DivisiblebyX (fromInteger 5) (S y) -> Void) -> DivisiblebyX 5 (S (S (S (S (S (S y)))))) -> Void
fiveLessNotDivisible5 notdiv (Multiple x) = notdiv x

divisibleby5: (y: Nat) -> Dec (DivisiblebyX 5 y)
divisibleby5 Z = No zeroNotDivisible5
divisibleby5 (S Z) = No oneNotDivisible5
divisibleby5 (S (S Z)) = No twoNotDivisible5
divisibleby5 (S (S (S Z))) = No threeNotDivisible5
divisibleby5 (S (S (S (S Z)))) = No fourNotDivisible5
divisibleby5 (S (S (S (S (S Z))))) = Yes Base
divisibleby5 (S (S (S (S (S (S y)))))) = case divisibleby5 (S y) of
  Yes prf => Yes (Multiple prf)
  No notdiv => No (fiveLessNotDivisible5 notdiv)

fizzbuzz: (x: Nat) -> FizzBuzzProof x
fizzbuzz x = case (divisibleby3 x, divisibleby5 x) of
  (No not_fizz, No not_buzz) => Normal x not_fizz not_buzz
  (Yes fizz_prf, Yes buzz_prf) => FizzBuzz fizz_prf buzz_prf
  (No not_fizz, Yes buzz_prf) => Buzz buzz_prf not_fizz
  (Yes fizz_prf, No not_buzz) => Fizz fizz_prf not_buzz

fizzbuzz_string: (x: Nat) -> String
fizzbuzz_string x = show $ fizzbuzz x


fizzbuzz_loop: (n: Nat) -> (end: Nat) -> IO ()
fizzbuzz_loop n end with (decEq n end)
  fizzbuzz_loop n end | Yes prf = pure ()
  fizzbuzz_loop n end | No contra =  do
    putStrLn $ show $ fizzbuzz n
    fizzbuzz_loop (S n) end

main: IO ()
main = fizzbuzz_loop 1 101
