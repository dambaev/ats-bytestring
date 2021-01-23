#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload UN = "prelude/SATS/unsafe.sats"

fn test0():void = {
  val s1 = $BS.empty()
  val env = 0
  val s2 = $BS.drop_while<int>( env, lam (env, ch)=<fun> isdigit ch, s1)
  val () = assertloc( $BS.is_empty s2)
  val () = free (s2, s1)
  val () = free s1
}
fn test1():void = {
  val s1 = pack "123"
  val env = 0
  val s2 = $BS.drop_while<int>( env, lam (env, ch)=<fun> isdigit ch, s1)
  val () = assertloc( $BS.is_empty s2)
  val () = free (s2, s1)
  val () = free s1
}

fn test2():void = {
  val env = 0
  val s1 = pack "123"
  val s2 = $BS.drop_while<int>( env, lam (env, ch)=<fun> not( isdigit ch), s1)
  val () = assertloc( s2 \$BS.eq_bytestring_bytestringC ($BS.pack "123" ))
  val () = free (s2, s1)
  val () = free s1
}

fn test3():void = {
  val env = 0
  val s1 = pack "123asd"
  val s2 = $BS.drop_while<int>( env, lam (env, ch)=<fun> not( isdigit ch), s1)
  val () = assertloc( s2 \$BS.eq_bytestring_bytestringC ($BS.pack "123asd" ))
  val () = free (s2, s1)
  val () = free s1
}

fn test4():void = {
  val env = 0
  val s1 = pack "123asd"
  val s2 = $BS.drop_while<int>( env, lam (env, ch)=<fun> isdigit ch, s1)
  val () = assertloc( s2 \$BS.eq_bytestring_bytestringC ($BS.pack "asd" ))
  val () = free (s2, s1)
  val () = free s1
}


implement main0() = {
  val () = test0()
  val () = test1()
  val () = test2()
  val () = test3()
  val () = test4()
}