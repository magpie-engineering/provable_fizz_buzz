import Data.Nat
data FizzBuzzReturn =
  Fizz
  | Buzz
  | FizzBuzz
  | Normal Nat

Show FizzBuzzReturn where
  show Fizz = "fizz"
  show Buzz = "buzz"
  show FizzBuzz = "fizzbuzz"
  show (Normal x) = show x


partial fizzBuzzReturn: (x: Nat) -> FizzBuzzReturn
fizzBuzzReturn x with (modNat x (the Nat 3), modNat x (the Nat 5))
  fizzBuzzReturn x | (Z, Z) = FizzBuzz
  fizzBuzzReturn x | (Z, _) = Fizz
  fizzBuzzReturn x | (_, Z) = Buzz
  fizzBuzzReturn x | _ = Normal x

partial fizzBuzzReturnString: (x: Nat) -> String
fizzBuzzReturnString x = show(fizzBuzzReturn x)
