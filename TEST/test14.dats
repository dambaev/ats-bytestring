#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "SATS/bytestring.sats"

fn
  test(): $BS.BytestringNSH0 = bs where {
  val s = $BS.pack "hello"
  val s1 = $BS.pack " world"
  val bs = s + s1
}
fn
  test1(): $BS.BytestringNSH0 = bs1 where {
  var bs: $BS.Bytestring0
  val () = bs := $BS.pack "hello world"
  var bs1: $BS.Bytestring0
  val () = bs1 := $BS.take1( i2sz 11, bs)
  val () = $BS.decref_bs( bs, bs1) // consume bs and decref for bs1
}

implement main0() = {
  val s1 = $BS.pack "hello world"
  val s = test()
  val () = assertloc( s = s1)
  val () = $BS.free( s)
  val s = test1()
  val () = assertloc( s = s1)
  val () = $BS.free( s)
  val () = $BS.free s1
}