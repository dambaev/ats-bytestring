#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "DATS/bytestring_flat.dats"

implement main0() = {
  var arr = @[char]( 'h', 'e', 'l', 'l', 'o')
  val s1 = $BS.pack ( view@arr | addr@arr, i2sz(5))
  val s2 = $BS.pack "hello"
  val () = assertloc( s1 =  s2)
  val s3 = $BS.takeC( i2sz(5), s1)
  val () = assertloc( s3 =  s2)
  val s4 = $BS.takeC( i2sz(1), s3)
  val s5 = $BS.pack "h"
  val tmp = $BS.create( i2sz 1024)
  val () = $BS.printlnC( tmp + $BS.takeC( i2sz(4), $BS.pack( view@arr | addr@arr, i2sz(5))) + $BS.pack " world" + $BS.pack " and others" )
  val () = $BS.free(s2)
  val () = $BS.free(s4)
  val () = $BS.free(s5)
}