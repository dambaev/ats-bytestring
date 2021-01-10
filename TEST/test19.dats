#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"

fn test0():void = {
  val s1 = pack "12345"
  val s2 = pack "54321"
  val s3 = $BS.reverse s1
  val () = assertloc( s3 = s2)
  val () = free s3
  val () = free s1
  val () = free s2
}

fn test1():void = {
  val s1 = pack "12345"
  val s2 = pack "54321"
  val s3 = $BS.reverseC (copy s1) // in-place reverse require heap allocated memory, otherwise it will segfault
  val () = assertloc( s3 = s2)
  val () = free s3
  val () = free s2
  val () = free s1
}

implement main0() = {
  val () = test0()
  val () = test1()
}