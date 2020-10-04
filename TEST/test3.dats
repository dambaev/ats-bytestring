#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "SATS/bytestring.sats"

implement main0() = {
  val l = $BS.pack "test1"
  val r = $BS.pack "test1"
  val r1 = $BS.pack "test2"
  val e1 = $BS.empty()
  val e2 = $BS.empty()
  val () = assertloc( l = r)
  val () = assertloc( e1 = e2)
  val () = assertloc( l != r1)
  val () = $BS.free(l)
  val () = $BS.free(r)
  val () = $BS.free(r1)
  val () = $BS.free(e1)
  val () = $BS.free(e2)
}