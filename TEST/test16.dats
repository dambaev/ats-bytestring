#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload BS="SATS/bytestring.sats"

fn test0():void = {
  var s: $BS.Bytestring0?
  val () = s := $BS.pack "abacada"
  var elements: List_vt($BS.Bytestring0)?
  val () = elements := $BS.split_on( 'a', s)
  val () = assertloc( list_vt_length( elements) = 5)
  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( $BS.eq_bytestring_bytestringC( v, $BS.empty()))
  val () = $BS.free( v, s)

  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( $BS.eq_bytestring_bytestringC( v, $BS.pack "b"))
  val () = $BS.free( v, s)

  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( $BS.eq_bytestring_bytestringC( v, $BS.pack "c"))
  val () = $BS.free( v, s)

  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( $BS.eq_bytestring_bytestringC( v, $BS.pack "d"))
  val () = $BS.free( v, s)

  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( $BS.eq_bytestring_bytestringC( v, $BS.empty()))
  val () = $BS.free( v, s)

  val ~list_vt_nil() = elements
  val () = $BS.free( s)
}

fn test1(): void = {
  var s: $BS.Bytestring0?
  val () = s := $BS.pack "bbb"
  var elements: List_vt($BS.Bytestring0)?
  val () = elements := $BS.split_on( 'a', s)
  val () = assertloc( list_vt_length( elements) = 1)

  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( $BS.eq_bytestring_bytestringC( v, $BS.pack "bbb"))
  val () = $BS.free( v, s)

  val ~list_vt_nil() = elements
  val () = $BS.free( s)
}

fn test2(): void = {
  var s: $BS.Bytestring0?
  val () = s := $BS.pack ""
  var elements: List_vt($BS.Bytestring0)?
  val () = elements := $BS.split_on( 'a', s)
  val () = assertloc( list_vt_length( elements) = 0)

  val ~list_vt_nil() = elements
  val () = $BS.free( s)
}

implement main0() = {
  val () = test0()
  val () = test1()
  val () = test2()
}