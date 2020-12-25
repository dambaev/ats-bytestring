#include "share/atspre_staload.hats"

#include "HATS/bytestring.hats"
staload BS="SATS/bytestring.sats"

#define ATS_DYNLOADFLAG 0


implement main0() = {
  val s1 = $BS.create( i2sz(100)) ++ $BS.pack "test1"
  val s2 = $BS.pack "test2"
  val s3 = $BS.pack "test3"
  var r1: $BS.Bytestring0
  val () = r1 := $BS.pack "test1test2test3"
  var r2: $BS.Bytestring0
  val () = $BS.println( s1)
  val () = r2 := s1 + s2 + s3 
  val () = $BS.println( r1)
  val () = $BS.println( r2)
  val () = assertloc( r1 = r2)
  val r3 = $BS.drop( i2sz(1), r2) // 1
  val r4 = $BS.drop( i2sz(1), r1)
  val () = assertloc( r3 = r4)
  val r5 = $BS.take( i2sz(4), r1)
  var r6: $BS.Bytestring0
  val () = r6 := $BS.take( i2sz(4), r2) // 2
  val () = assertloc( r5 = r6)
  val r7 = $BS.take( i2sz( 1), r6)
  val r8 = $BS.pack "t"
  val () = assertloc( r7 = r8)
  val () = $BS.free( r7, r6)
  val () = $BS.free( r6, r2)
  val () = $BS.free( r3, r2)
  val () = $BS.printlnC( $BS.pack "r2 = " + r2)
  val () = $BS.free( r5, r1)
  val () = $BS.free( r4, r1)
  val () = $BS.free(r1)
  val () = $BS.free(r8)
}