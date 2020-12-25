#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload BS="SATS/bytestring.sats"

fn test0():void = {
  var s: $BS.Bytestring0?
  val () = s := $BS.create( i2sz(100))
  val s1 = s ++ $BS.pack "hello" ++ $BS.pack " " ++ $BS.pack "world"
  val s2 = $BS.pack "hello world"
  val () = assertloc( s1 = s2)
  val () = $BS.free s1
  val () = $BS.free s2
}

implement main0() = {
  val () = test0()
}