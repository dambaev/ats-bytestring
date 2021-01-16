#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload UN = "prelude/SATS/unsafe.sats"

fn test0():void = {
  val s1 = pack "123"
  val-~Some_vt(v) = $BS.parse_uint32 s1
  val () = assertloc( v = $UN.cast{uint32} 123)
  val () = free s1
}

fn test1():void = {
  val s1 = pack "asd"
  val-~None_vt() = $BS.parse_uint32 s1
  val () = free s1
}

fn test2():void = {
  val s1 = pack "-123"
  val-~None_vt() = $BS.parse_uint32 s1
  val () = free s1
}

fn test3():void = {
  val s1 = pack "4294967294"
  val-~Some_vt(v) = $BS.parse_uint32 s1
  val () = assertloc( v = $UN.cast{uint32}4294967294)
  val () = free s1
}

fn test4():void = {
  val s1 = pack "4294967295"
  val-~Some_vt(v) = $BS.parse_uint32 s1
  val () = assertloc( v = $UN.cast{uint32}4294967295)
  val () = free s1
}

implement main0() = {
  val () = test0()
  val () = test1()
  val () = test2()
  val () = test3()
  val () = test4()
}