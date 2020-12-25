#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload BS="SATS/bytestring.sats"

fn test(): $BS.BytestringNSH0 = bs where {
  var s = "hello"
  val bs = $BS.pack s
}

implement main0() = {
  val s = test()
  val () = $BS.free s
}