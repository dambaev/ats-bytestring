(* this file's goal is to be included in order to introduce infix operators and overloads *)

(* staload the SATS file *)
staload BS="./../SATS/bytestring.sats"

overload = with $BS.eq_bytestring_bytestring
overload <> with $BS.neq_bytestring_bytestring
overload != with $BS.neq_bytestring_bytestring

overload + with $BS.appendC

(* introduce the ++ operator *)
infixl (+) ++
overload ++ with $BS.growC

infixl (+) +!
overload +! with $BS.append_bsC_bs

infixl (+) !+!
overload !+! with $BS.append_bs_bs

infixl (+) !+
overload !+ with $BS.append_bs_bsC

overload length with $BS.length_bs

overload [] with $BS.get_byte_at_uint
overload [] with $BS.get_byte_at_int

overload pack with $BS.pack_string
overload pack with $BS.pack_chars_static
overload pack with $BS.pack_chars_dynamic

overload free with $BS.free_bs
overload free with $BS.free_static_array
overload free with $BS.unref_bs


overload copy with $BS.copy