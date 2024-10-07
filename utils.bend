unchecked PChannel: (P, P -> None) 
PChannel = ($x, λ$x(*))

type Bits = (I ~v) | (O ~v) | E
def Bits/to_u24(value):
  fold value:
    case Bits/O:
      return value.v * 2
    case Bits/I:
      return value.v * 2 + 1
    case Bits/E:
      return 1

def Bits/split(bits: Bits) -> (Bits, Bits):
  return (Bits/O(bits), Bits/I(bits))

def Bits/duplicate(bits: Bits) -> (Bits, Bits):
  return (bits, bits)

def String/duplicate(str: String) -> (String, String):
  return (str, str)

def u24/duplicate(n: u24) -> (u24, u24):
  return (n, n)

(String/concat (String/Cons head tail) other) = (String/Cons head (String/concat tail other))
(String/concat String/Nil other) = other

(List/join List/Nil)         = ""
(List/join (List/Cons x xs)) = (String/concat x (List/join xs))
