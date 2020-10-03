#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "DATS/bytestring_flat.dats"

fn test(): $BS.Bytestring0 = bs where {
  var s = "hello"
  val bs = $BS.pack s
}

implement main0() = {
  val s = test()
  val () = assertloc( $BS.isnot_shared s)
  val () = $BS.free s
}