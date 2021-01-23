#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload UN = "prelude/SATS/unsafe.sats"

fn test0():void = {
  val s1 = $BS.pack "1234"
  val p = $BS.pack "12"
  val () = assertloc( $BS.is_prefix_of( p, s1))
  val () = free s1
  val () = free p
}

fn test1():void = {
  val s1 = $BS.pack "1234"
  val p = $BS.pack "2"
  val () = assertloc( not( $BS.is_prefix_of( p, s1)))
  val () = free s1
  val () = free p
}

fn test2():void = {
  val s1 = $BS.pack "1234"
  val p = $BS.pack "34"
  val () = assertloc( $BS.is_suffix_of( p, s1))
  val () = free s1
  val () = free p
}

fn test3():void = {
  val s1 = $BS.pack "1234"
  val p = $BS.pack "12"
  val () = assertloc( not( $BS.is_suffix_of( p, s1)))
  val () = free s1
  val () = free p
}

fn test4():void = {
  val s1 = $BS.pack "1234"
  val p = $BS.pack "23"
  val () = assertloc( $BS.is_infix_of( p, s1))
  val () = free s1
  val () = free p
}

fn test5():void = {
  val s1 = $BS.pack "1234"
  val p = $BS.pack "5"
  val () = assertloc( not( $BS.is_suffix_of( p, s1)))
  val () = free s1
  val () = free p
}

fn test6():void = {
  val s1 = $BS.pack "1234"
  val p = $BS.pack "12"
  val () = assertloc( $BS.is_infix_of( p, s1))
  val () = free s1
  val () = free p
}

fn test7():void = {
  val s1 = $BS.pack "1234"
  val p = $BS.pack "9"
  val () = assertloc( not( $BS.is_infix_of( p, s1)))
  val () = free s1
  val () = free p
}

implement main0() = {
  val () = test0()
  val () = test1()
  val () = test2()
  val () = test3()
  val () = test4()
  val () = test5()
  val () = test6()
  val () = test7()
}