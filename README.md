# Bytestring

State: WORK IN PROGRESS.

This library is an attemp to provide an easy to use library for manipulating arrays of chars, similar to ByteString library in Haskell or Bytes in OCaml.

The motivation behind it is to reduce a complexity of handling too much service code for working with strings. Yet, the goal is to use resources efficiently.

# Example

You can look in TEST directory for examples of usage

```ats
#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "DATS/bytestring_flat.dats"

implement main0() = {
  val s1 = $BS.create( i2sz(100)) + $BS.pack "test1" (* create uninitialized buffer of size 100 and fill first 5 of them with "test1" *)
  val s2 = $BS.pack "test2"
  val s3 = $BS.pack "test3"
  val r1 = $BS.pack "test1test2test3"
  val r2 = s1 + s2 + s3 (* + operator is an alias to appendC, which consumes arguments. In this particular situation + operator will see, that s1 has big enough buffer to fill s2 and s3, so it will use it instead of allocation of new buffer *)
  val () = assertloc( r1 = r2)
  val r3 = $BS.drop( i2sz(1), r2)
  val r4 = $BS.drop( i2sz(1), r1)
  val () = assertloc( r3 = r4)
  val r5 = $BS.take( i2sz(4), r1)
  val r6 = $BS.take( i2sz(4), r2)
  val () = assertloc( r5 = r6)
  val () = $BS.printlnC( $BS.pack "r2 = " + r2) (* *C functions are meant to consume it's arguments *)
  val () = $BS.free(r1)
  val () = $BS.free(r3)
  val () = $BS.free(r4)
  val () = $BS.free(r5)
  val () = $BS.free(r6)
}

```
