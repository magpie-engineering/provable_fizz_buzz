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

fizzBuzzReturn: (x: Nat) -> FizzBuzzReturn
fizzBuzzReturn x with (modNat x (the Nat 3), modNat x (the Nat 5))
  | (Z, Z) = FizzBuzz
  | (Z, _) = Fizz
  | (_, Z) = Buzz
  | _ = Normal x

fizzBuzzReturnString: (x: Nat) -> String
fizzBuzzReturnString x = show(fizzBuzzReturn x)
