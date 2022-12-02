structure Point where
  x : Float
  y : Float
deriving Repr

def p : Point := { x := 0.0, y := 0.0 }

#eval p

inductive MBool where
  | true : MBool
  | false : MBool
