#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload UN = "prelude/SATS/unsafe.sats"

fn test0():void = {
  val s1 = $BS.pack "1234"
  var idx: size_t?
  val () = assertloc( $BS.find_index0( '1', idx, s1))
  prval () = opt_unsome( idx)
  val () = assertloc( idx = i2sz 0)
  val () = free s1
}

fn test1():void = {
  val s1 = $BS.pack "1234"
  var idx: size_t?
  val () = assertloc( $BS.find_index0( '0', idx, s1) = false)
  prval () = opt_unnone( idx)
  val () = free s1
}

fn test2():void = {
  val s1 = $BS.pack "1234"
  var idx: size_t?
  val () = assertloc( $BS.find_index0( '4', idx, s1))
  prval () = opt_unsome( idx)
  val () = assertloc( idx = i2sz 3)
  val () = free s1
}

fn test3():void = {
  val s1 = $BS.pack "1234"
  var idx: size_t?
  val () = assertloc( $BS.find_index0( '3', idx, s1))
  prval () = opt_unsome( idx)
  val () = assertloc( idx = i2sz 2)
  val () = free s1
}

implement main0() = {
  val () = test0()
  val () = test1()
  val () = test2()
  val () = test3()
}