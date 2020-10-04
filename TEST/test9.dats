#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "SATS/bytestring.sats"

fn
  test()
  :
  $BS.Bytestring1 = bs where {
  val s = "hello"
  val bs = $BS.pack s
}

implement main0() = {
  val s = test()
  val () = assertloc( $BS.isnot_shared s)
  val s1 = $BS.pack "hello"
  val () = assertloc( s = s1)
  val () = $BS.free s
  val () = $BS.free s1
}