#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"

fn test0():void = {
  val s1 = pack "z"
  val s2 = $BS.empty() + 'z'
  val () = assertloc( s1 = s2)
  val () = free s1
  val () = free s2
}

implement main0() = {
  val () = test0()
}