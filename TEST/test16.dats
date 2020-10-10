#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "SATS/bytestring.sats"

extern castfn
  c2uc
  {c:int | c > 0}
  ( i: char(c)
  ):<> uchar(c)

implement main0() = {
  var s: $BS.Bytestring0?
  val () = s := $BS.pack "abacada"
  var elements: List_vt($BS.Bytestring0)?
  val () = elements := $BS.split_on( c2uc 'a', s)
  val () = assertloc( list_vt_length( elements) = 5)
  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( eq_bytestring_bytestringC( v, $BS.empty()))
  val () = $BS.free( v, s)

  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( eq_bytestring_bytestringC( v, $BS.pack "b"))
  val () = $BS.free( v, s)

  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( eq_bytestring_bytestringC( v, $BS.pack "c"))
  val () = $BS.free( v, s)

  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( eq_bytestring_bytestringC( v, $BS.pack "d"))
  val () = $BS.free( v, s)

  val v = list_vt_takeout_at( elements, 0)
  val () = assertloc( eq_bytestring_bytestringC( v, $BS.empty()))
  val () = $BS.free( v, s)

  val () = __free( elements) where {
    extern castfn __free( i: List_vt( $BS.Bytestring0)): void
  }
  val () = $BS.free( s)
}