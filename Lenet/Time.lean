namespace Lenet.Time

/--
24 hours in milliseconds (86,400,000 ms).
ENet uses this threshold to disambiguate 32-bit millisecond timer wrap-arounds.
-/
def overflow : UInt32 := 86400000

/-- Returns true if `a` is earlier in time than `b`, accounting for timer wrap-around. -/
@[inline]
def less (a b : UInt32) : Bool :=
  (a - b) >= overflow

/-- Returns true if `a` is later in time than `b`, accounting for timer wrap-around. -/
@[inline]
def greater (a b : UInt32) : Bool :=
  (b - a) >= overflow

/-- Returns true if `a` is earlier than or equal to `b`. -/
@[inline]
def lessEqual (a b : UInt32) : Bool :=
  !greater a b

/-- Returns true if `a` is later than or equal to `b`. -/
@[inline]
def greaterEqual (a b : UInt32) : Bool :=
  !less a b

/-- Computes the elapsed millisecond difference between two timestamps `a` and `b`. -/
@[inline]
def difference (a b : UInt32) : UInt32 :=
  if (a - b) >= overflow then b - a else a - b

/-- The earlier of two timestamps under the wrap-aware order (`less`); ties
keep `a`. Plain `min` is wrong here: across the 2^32 wrap a numerically
smaller timestamp can be the *later* one. -/
@[inline]
def earliest (a b : UInt32) : UInt32 :=
  if less b a then b else a

/-- Fold step for "earliest of a set of timestamps": `acc` is the earliest so
far (`none` for the empty set). -/
@[inline]
def earliestSome (acc : Option UInt32) (t : UInt32) : Option UInt32 :=
  some (match acc with
    | some v => earliest v t
    | none => t)

end Lenet.Time