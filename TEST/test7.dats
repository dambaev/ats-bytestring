#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload BS="SATS/bytestring.sats"

implement main0() = {
  val s1 = $BS.pack "test1"
  val s2 = $BS.dropC(i2sz 1, s1)
  val () = $BS.println( s2)
  prval _ = $showtype s2
  val () = $BS.free(s2)
}