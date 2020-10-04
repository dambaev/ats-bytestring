#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "SATS/bytestring.sats"

fn
  test(): $BS.BytestringNSH0 = bs where {
  val s = $BS.pack "hello"
  val s1 = $BS.pack " world"
  val bs = $BS.appendC( s, s1)
}
fn
  test1(): $BS.BytestringNSH0 = bs where {
  val (pf, fpf | p) = array_ptr_alloc<char>( i2sz 100)
  val bs = $BS.pack ( pf, fpf | p, i2sz 0, i2sz 100)
  val s = $BS.pack "hello"
  val bs = $BS.appendC( bs, s)
  val bs = $BS.appendC( bs, $BS.pack " world")
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