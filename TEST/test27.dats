#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload UN = "prelude/SATS/unsafe.sats"

fn test0():void = {
  val s1 = $BS.pack "true"
  val s2 = $BS.pack true
  val () = assertloc( s1 = s2)
  val () = free s1
  val () = free s2
}

implement main0() = {
  val () = test0()
}