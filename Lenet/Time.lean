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

end Lenet.Time