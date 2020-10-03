#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "DATS/bytestring_flat.dats"

implement main0() = {
  val s1 = $BS.pack "test1"
  val s2 = $BS.dropC(i2sz 1, s1)
  val () = $BS.println( s2)
  prval _ = $showtype s2
  val () = $BS.free(s2)
}