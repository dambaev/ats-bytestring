#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload BS="SATS/bytestring.sats"

implement main0() = {
  val s = $BS.pack "hello"
  val () = assertloc( s[0] = 'h')
  val () = assertloc( s[1] = 'e')
  val () = assertloc( s[2] = 'l')
  val () = assertloc( s[3] = 'l')
  val () = assertloc( s[4] = 'o')
  val () = $BS.free( s)
}