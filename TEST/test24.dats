#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload UN = "prelude/SATS/unsafe.sats"

fn test0():void = {
  val s1 = $BS.pack "1234"
  val () = assertloc( $BS.elem( '1', s1))
  val () = free s1
}

fn test1():void = {
  val s1 = $BS.pack "1234"
  val () = assertloc( $BS.not_elem( 'a', s1))
  val () = free s1
}

fn test2():void = {
  val s1 = $BS.pack "1234"
  val () = assertloc( not( $BS.elem( 'a', s1)))
  val () = free s1
}


implement main0() = {
  val () = test0()
  val () = test1()
  val () = test2()
}