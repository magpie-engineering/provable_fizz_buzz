data NotDivisibleby3 : Nat -> Type where
  Zero: NotDivisibleby3 0
  One: NotDivisibleby3 1
  Two: NotDivisibleby3 2
  ThreeMultiple: NotDivisibleby3 x -> NotDivisibleby3 (3+x)

divBy9: NotDivisibleby3 4
divBy9 = ThreeMultiple (One)

data NotDivisiblebyX : Nat -> Nat -> Type where
  NotBase: y `LT` x -> NotDivisiblebyX x y
  NotMultiple: NotDivisiblebyX x y -> NotDivisiblebyX x (x+y)

divBy6: NotDivisiblebyX 5 6
divBy6 = NotMultiple (NotBase (LTESucc (LTESucc LTEZero)))

data DivisiblebyX : Nat -> Nat -> Type where
  Base:DivisiblebyX x x
  Multiple: DivisiblebyX x y -> DivisiblebyX x (x+y)

data FizzBuzzProof: Nat -> Type where
  Fizz: DivisiblebyX 3 x -> NotDivisiblebyX 5 x -> FizzBuzzProof x
  Buzz: DivisiblebyX 5 x -> NotDivisiblebyX 3 x -> FizzBuzzProof x
  FizzBuzz: DivisiblebyX 3 x -> DivisiblebyX 5 x -> FizzBuzzProof x
  Normal: NotDivisiblebyX 3 x -> NotDivisiblebyX 5 x -> FizzBuzzProof x

Show (FizzBuzzProof x) where
  show (Fizz divBy3 notDivBy5) = "fizz"
  show (Buzz divBy5 notDivBy3) = "buzz"
  show (FizzBuzz divBy3 divBy5) = "fizzbuzz"
  show (Normal notDivBy3 notDivBy5 {x}) = show x

sh6: FizzBuzzProof 6
sh6 = Fizz (Multiple Base)
     (NotMultiple(NotBase (LTESucc (LTESucc LTEZero))))

data DecDiv: Nat -> Nat -> Type where
  Yes: DivisiblebyX x y -> DecDiv x y
  No: NotDivisiblebyX x y -> DecDiv x y


divisbleby3: (y: Nat) -> DecDiv 3 y
divisbleby3  (S (S (S Z))) = Yes Base
divisbleby3 (S (S (S x))) = case divisbleby3 x of
  Yes prf => Yes (Multiple prf)
  No notprf => No (NotMultiple notprf)
divisbleby3 Z = No (NotBase (LTESucc LTEZero))
divisbleby3 (S Z) = No (NotBase (LTESucc (LTESucc LTEZero)))
divisbleby3 (S (S Z)) = No(NotBase (LTESucc (LTESucc (LTESucc LTEZero))))

divisbleby5: (y: Nat) -> DecDiv 5 y
divisbleby5  (S (S (S (S (S Z))))) = Yes Base
divisbleby5 (S (S (S (S (S x))))) = case divisbleby5 x of
  Yes prf => Yes (Multiple prf)
  No notprf => No (NotMultiple notprf)
divisbleby5 Z = No (NotBase (LTESucc LTEZero))
divisbleby5 (S Z) = No (NotBase (LTESucc (LTESucc LTEZero)))
divisbleby5 (S (S Z)) = No (NotBase (LTESucc (LTESucc (LTESucc LTEZero))))
divisbleby5 (S (S (S Z))) = No (NotBase (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))
divisbleby5 (S (S (S (S Z)))) = No (NotBase (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))))

fizzbuzz: (x: Nat) -> FizzBuzzProof x
fizzbuzz x = case (divisbleby3 x, divisbleby5 x) of
  (No notfizz, No notbuzz) => Normal notfizz notbuzz
  (Yes fizz_prf, Yes buzz_prf) => FizzBuzz fizz_prf buzz_prf
  (No notfizz, Yes buzz_prf) => Buzz buzz_prf notfizz
  (Yes fizz_prf, No notbuzz) => Fizz fizz_prf notbuzz

fizzbuzz_string: (x: Nat) -> String
fizzbuzz_string x = show $ fizzbuzz x
