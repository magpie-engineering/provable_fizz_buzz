fizzBuzzSimple: (x: Nat) -> String
fizzBuzzSimple x with (modNat x (the Nat 3), modNat x (the Nat 5))
  | (Z, Z) = "fizzbuzz"
  | (Z, _) = "fizz"
  | (_, Z) = "buzz"
  | _ = show x
