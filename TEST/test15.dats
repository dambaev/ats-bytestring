#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "SATS/bytestring.sats"

extern castfn
  c2b
  (i: char
  ):<> uchar

implement main0() = {
  val s = $BS.pack "hello"
  val () = assertloc( s[0] = c2b 'h')
  val () = assertloc( s[1] = c2b 'e')
  val () = assertloc( s[2] = c2b 'l')
  val () = assertloc( s[3] = c2b 'l')
  val () = assertloc( s[4] = c2b 'o')
  val () = $BS.free( s)
}