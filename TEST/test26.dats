#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload UN = "prelude/SATS/unsafe.sats"

fn test0():void = {
  val s1 = $BS.create( i2sz 256)
  val s2 = $BS.pack "test"
  val s3 = s1 ++! s2
  val () = assertloc( s3 = s2)
  val () = free s2
  val () = free s3
}


implement main0() = {
  val () = test0()
}