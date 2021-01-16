#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"

fn test0():void = {
  val s1 = pack "123a45"
  val s2 = pack "123"
  val env: int = 0
  val s3 = $BS.take_while<int>( env, lam (env, ch)=<fun> ch <> 'a', s1)
  val () = assertloc( s3 = s2)
  val () = free( s3, s1)
  val () = free s1
  val () = free s2
}

fn test1():void = {
  val s1 = pack "a123a45"
  val s2 = $BS.empty()
  val env: int = 0
  val s3 = $BS.take_while<int>( env, lam (env, ch)=<fun> ch <> 'a', s1)
  val () = assertloc( s3 = s2)
  val () = free( s3, s1)
  val () = free s1
  val () = free s2
}

fn test2():void = {
  val s1 = pack "12345"
  val s2 = pack "12345"
  val env: int = 0
  val s3 = $BS.take_while<int>( env, lam (env, ch)=<fun> ch <> 'a', s1)
  val () = assertloc( s3 = s2)
  val () = free( s3, s1)
  val () = free s1
  val () = free s2
}
fn test3():void = {
  val s1 = pack ""
  val s2 = $BS.empty()
  val env: int = 0
  val s3 = $BS.take_while<int>( env, lam (env, ch)=<fun> ch <> 'a', s1)
  val () = assertloc( s3 = s2)
  val () = free( s3, s1)
  val () = free s1
  val () = free s2
}

implement main0() = {
  val () = test0()
  val () = test1()
  val () = test2()
  val () = test3()
}