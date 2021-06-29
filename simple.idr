import Data.Nat

partial fizzBuzzSimple: (x: Nat) -> String
fizzBuzzSimple x with (modNat x (the Nat 3), modNat x (the Nat 5))
  fizzBuzzSimple x | (Z, Z) = "fizzbuzz"
  fizzBuzzSimple x | (Z, _) = "fizz"
  fizzBuzzSimple x | (_, Z) = "buzz"
  fizzBuzzSimple x | _ = show x
