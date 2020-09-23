#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "DATS/bytestring_flat.dats"

implement main0() = {
  var arr = @[char]( 'h', 'e', 'l', 'l', 'o')
  val s1 = $BS.pack ( view@arr | addr@arr, i2sz(5))
  val s2 = $BS.pack "hello"
  val () = assertloc( s1 =  s2)
  val () = $BS.free(s1)
  val () = $BS.free(s2)
}