#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

symintr ++
infixl (+) ++
  
staload BS="SATS/bytestring.sats"
staload "SATS/bytestring.sats"

implement main0() = {
  var arr = @[char]( 'h', 'e', 'l', 'l', 'o')
  var s1: $BS.Bytestring0
  val () = s1 := $BS.pack ( view@arr | addr@arr, i2sz 5, i2sz 5)
  val s2 = $BS.pack "hello"
  val () = assertloc( s1 =  s2)
  var s3: $BS.Bytestring0
  val () = s3 := $BS.take( i2sz(5), s1)
  val () = assertloc( s3 =  s2)
  val s4 = $BS.take( i2sz(1), s3)
  val () = $BS.free( s4, s3)
  val () = $BS.free( s3, s1)
  val () = $BS.free( view@arr | s1)
  val s5 = $BS.pack "h"
  val tmp = $BS.create( i2sz 1024)
  val () = $BS.printlnC( tmp ++ $BS.takeC( i2sz(4), $BS.pack( view@arr | addr@arr, i2sz(5), i2sz 5)) ++ $BS.pack " world" ++ $BS.pack " and others" )
  val () = $BS.free(s2)
  val () = $BS.free(s5)
}